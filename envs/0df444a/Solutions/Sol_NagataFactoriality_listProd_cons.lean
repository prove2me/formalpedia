-- Prove2me | solution 1 for NagataFactoriality.listProd_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:30.74266+00:00
-- url     : https://prove2.me/submissions/5a146ccc-ed00-40ca-9ee8-1bf5628e2f4a

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] (a : α) (as : List α) :
    listProd (a :: as) = a * listProd as := rfl
end NagataFactoriality
