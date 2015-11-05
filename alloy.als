abstract sig Person{ 
	}

sig Taxi_driver extends Person{
	incoming:lone Call	}

sig User extends Person{
	locations:set Location,
	past_call:set Call,
	blank_call:set Call}

abstract sig Call{

	}

sig Delayed_call extends Call{
	caller:one User,
	start: one Address,
	destination: one Address
	}

sig Immediate_call extends Call{
	caller:one User
	}

sig Shared_call extends Call{
	start: some Address,
	destination: some Address,
	caller: some User}

sig Zone{
	address: some Address	}

sig Queue {
	zone:one Zone,
	drivers: set Taxi_driver}

sig Location{
	address: one Address}

sig Address{
	zone: one Zone
	}

//FACTS

fact OneDriverPerCall{
	//ad ogni call deve corrispondere un tassista se attiva oppure essere un past call di un utente
	all c:Call | ((one t:Taxi_driver | t.incoming=c )<=> !(some u:User | c in  u.past_call))
}

fact BlankCalls {
	//le chiamate perse non possono essere più di quelle effettuate e devono essere contenute in quelle passate
	all u:User|(all c: Call |(c in u.blank_call implies c in u.past_call))}

fact NotEmptyQueue{
	//in ogni coda deve contenere almeno un tassista
	all q:Queue | (some t:Taxi_driver | t in q.drivers)}

fact NumberAdressesShared{
	//partenze e arrivi al massimo uguali al numero di utenti
 all c:Shared_call | (#c.start <=#c.caller && #c.destination<=#c.caller)}

fact SameStartZone{
	//tutti gli utenti devono partire dalla stessa zona
	all c:Shared_call | (all a: Address | (a in c.start => (no b: Address | (b in c.start && b.zone !=a.zone)))) 
}

fact AddressInZone{
	//se un'indirizzo è in una zona allora deve essere contenuto negli indirizzi di quella zona
	all a:Address |( a in a.zone.address)}

fact QueueInZone {
	//ogni zona deve avere una queue
	all z:Zone, q:Queue, n:Queue |(q!=n implies (z = q.zone <=>z!=n.zone))
	all z:Zone, q:Queue	|( #z=#q)}

fact OnlyMyCalls {
	//ogni utente ha in lista solo le sue calls
	all u:User |(all c:Immediate_call|(c in u.past_call implies c.caller=u))
	all u:User |(all c:Delayed_call|(c in u.past_call implies c.caller=u))
	all u:User |(all c:Shared_call | (c in u.past_call implies u in c.caller))
	}	
fact OneQueuePerTaxi{
	//un tassista deve essere in una sola coda
	all t:Taxi_driver |(all q:Queue, n:Queue |( q!=n implies ( t in q.drivers <=> t not in n.drivers)))}

//ASSERTIONS

assert NoOrphanCalls {
	//controlla che non ci siano chiamate senza tassista o utente
	no c: Call | ((no u: User | c in u.past_call) && (no t: Taxi_driver | t.incoming=c))  
}
//check NoOrphanCalls

assert NoDifferentStart {
	//controlla che non ci siano utenti che partono da zone diverse
	all c : Shared_call |(no a: Address, b:Address |( a in c.start && b in c.start && a.zone!=b.zone))}
//check NoDifferentStart

assert MaxBlank {
	//controlla che le chiamate perse non siano maggiori di quelle effettuate
 	all u:User | (#u.blank_call<=#u.past_call)}
//check MaxBlank

//PREDICATES

//un mondo senza utenti
pred ShowOnlyTaxi {
	some u:User, c:Immediate_call | c in u.past_call 
#Queue =3
 }
run ShowOnlyTaxi 
