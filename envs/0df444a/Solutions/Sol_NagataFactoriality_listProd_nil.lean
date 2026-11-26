-- Prove2me | solution 1 for NagataFactoriality.listProd_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:30.302132+00:00
-- url     : https://prove2.me/submissions/761e6e3e-08a5-46a3-b2a6-ded18f7b8f6f

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] : listProd ([] : List α) = 1 := rfl
end NagataFactoriality
