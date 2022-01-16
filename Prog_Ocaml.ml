type ide = string;;
type exp = Eint of int | Ebool of bool |Estring of string | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | Dict of (ide * exp)list | ApplyOver of Dict * exp | Get of  Dict * ide | Remove of Dict * ide
	| Clear of Dict | Set of Dict * ide * exp;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun | DictVal of (ide * evT) list| String of string
and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;



(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	Estring s-> String s |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
    Letrec(f, funDef, letBody) ->
        (match funDef with
            Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            _ -> failwith("non functional def"))|

	Dict(lst) -> (if (contrDict lst) then DictVal(evalList lst r) 
    							else failwith("keys duplicated") )|

	Get(d,i) -> (match (eval d r) with (*Controllo che d sia un dizionario*)
    	|DictVal(lst) -> lookup i lst (*applico la funzione lookup*)
    	|_-> failwith("invalid dictionary")) |

	Remove(d,i) -> (match (eval d r) with (*Controllo che d sia un dizionario*)
    	|DictVal(lst) -> DictVal(rm i lst) (*applico la funzione rm per eliminare i*)
    	|_-> failwith("invalid dictionary")) |

	Clear(d)-> (match (eval d r) with (*Controllo che d sia un dizionario*)
    	|DictVal(lst)->DictVal([]) (*DictVal([]) mi permette di creare un dizionario vuoto*)
    	|_-> failwith("invalid dictionary")) |

	ApplyOver(exf,exd) -> let d = eval exd r in
    	(match d with (*Controllo che d sia un dizionario*)
    	|DictVal(lst) -> DictVal(apply (eval exf r) lst) (*applico la funzione apply passandogli la funzione da applicare exf e la lista su cui applicarla*)
    	|_->failwith("invalid dictionary")) |

    Set(dexp,id,exval) -> let v1 = eval exval r in
        let dval = (eval dexp r) in
    	(match dval with (*Controllo che d sia un dizionario*)
    	|DictVal(lst) -> if (contiene id lst) then (DictVal(aggiornaVal id v1 lst)) else (DictVal((id,v1)::lst)) (*se il dizionario contiene il campo id allora aggiorno il suo valore chiamando la funzione aggironaVal altriementri aggiungo in testa alla lista la nuova coppia*)
    	|_-> failwith("invalid dictionary"))


    (*restituisce false se ci sono campi uguali nella stessa lista, altrimenti restituisce true*)
    and contrDict (lst: (ide * exp)list) : bool =
	match lst with
	[]-> true
	|(id,v)::rest -> if (cerca id rest) then false else contrDict rest

	(*Valuta una lista*)
	and  evalList (lst:(ide * exp) list) (r: evT env) : (ide * evT) list =
	match lst with
	[]->[]
	|(i,e)::rest -> (i,eval e r):: (evalList rest r)

	(*restituisce true se l'identificatore i è contenuto in lst, false altrimenti*)
	and contiene (i:ide) (lst: (ide * evT)list) : bool =
	(match lst with
	[]->false
	|x::rest -> (match x with
        (a,b) -> if(i = a) then true else (contiene i rest)))

	(*restituisce true se l'identificatore i è contenuto in lst, false altrimenti*)
	and cerca (i:ide) (lst: (ide * exp)list) : bool =
	(match lst with
	[]->false
	|x::rest -> (match x with
        (a,b) -> if(i = a) then true else (cerca i rest)))

	(*restituisce il valore associato a i se presente in lst, altrimenti Unbound*)
	and lookup (i: ide) (lst:(ide * evT)list) : evT=
	match lst with
	[] -> Unbound
	|(id,v)::rest -> if (id=i) then v else lookup i rest

	(*se presente in lst elimino la coppia <i,v>*)
	and rm (i:ide) (lst:( ide * evT)list) : (ide * evT) list =
	match lst with
	[]->[]
	|(id,v)::rest -> if (id=i) then rest else (id,v)::(rm  i rest)

	(*applico la funzione exf ai campi di lst*)
	and apply (exf : evT) (lst : (ide*evT)list) : (ide*evT)list =
	(match (exf,lst) with
	(exf1,[])->[]
	|(FunVal(arg,fbody,r),((i,e)::rest)) -> let k = try eval fbody (bind r arg e) with excep -> e in (i,k)::(apply exf rest) 
	|(RecFunVal(g,(arg,fbody,r)),((i,e)::rest)) -> let k = try (let rEnv = (bind r g exf) in
														let aEnv = (bind rEnv arg e) in
															eval fbody aEnv) with excep -> e in (i,k)::(apply exf rest)
	|(_,_)->failwith("funzione non valida"))

	(*se i è presente in lst modifico il suo valore con v*)
	and aggiornaVal (i:ide) (v:evT) (lst: (ide * evT) list) : (ide * evT) list  =
	(match lst with
	|[]->[]
	|(id,v1)::rest -> if (id = i) then (i,v)::rest else (id,v1)::(aggiornaVal i v rest));;

	

	(* =============================  TESTS  ================= *)

	(* basico: no let *)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;


	(*==========================TESTS DIZIONARI=================*)

 	let env0 = emptyenv Unbound;;

	(*Dizionario vuoto*)
	let diz0 = Dict([]);;

	(*Dizionario 1*)
	let diz1 = (Dict([("name", Estring "Giovanni");("matricola",Eint 546091)]));;

	(*Dizionario2*)
	let diz2 =(Dict([("name", Estring "Selene");("età",Eint 28)]));;

	(*Dizionario3*)
	let diz3 = (Dict([("name", Estring "Mario");("matricola", Eint 65271)]));;

	
	(*FUNZIONI*)

	(*Funzione che incrementa il parametro x*)
	let inc1 = Fun("x", Sum(Den "x", Eint 1));;

	(*Funzione che decrementa il parametro x*)
	let dec1 = Fun("x", Diff(Den "x", Eint 1));;


	
	(*Aggiungo il campo età ai campi del dizionario1 creando un nuovo dizionario4*)
	let diz4 =(Set(diz1, "età", Eint 22));;
	eval diz4 env0;;
 	
 	(*Accedo al campo età del dizionario4*)
 	eval (Get(diz4,"età")) env0;;

	(*Rimuovo al diz2 il campo età creando un nuovo dizionario5*)
	let diz5 = (Remove(diz2,"età"));;
	eval diz5 env0;;

	(*Cerco di accedere al campo età del dizionario5 ma ottengo Unbound perche l'ho appena rimosso*)
	eval (Get(diz5,"età")) env0;;

	(*Estraggo il campo età dal dizionario1*)
	eval (Get(diz2,"età")) env0;;

	(*Applico la funzione inc1 al dizionario1 creando un nuovo dizionario6*)
	let diz6 =(ApplyOver(inc1,diz4));;
	eval diz6 env0;;

	(*Accedo al campo matricola del dizionario6*)
	eval (Get(diz6,"matricola")) env0;;

	(*Elimino tutti i campi del dizionario4 creando un nuovo dizionario7 senza campi*)
	let diz7 = (Clear(diz4));;
	eval diz7 env0;;

	(*Aggiungo il campo telefono ai campi del dizionario4 creando un nuovo dizionario8*)
	let diz8 = (Set(diz4,"telefono", Eint 12345));;
	eval diz8 env0;;

	(*Creo un nuovo dizionario9 con i campi del dizionario8 decrementati di 1*)
	let diz9 =(ApplyOver(dec1,diz8));;
	eval diz9 env0;;

	(*Accedo al campo telefono del dizionario9*)
	eval (Get(diz9,"telefono")) env0;;


	











