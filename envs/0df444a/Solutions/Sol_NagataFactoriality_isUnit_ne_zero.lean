-- Prove2me | solution 1 for NagataFactoriality.isUnit_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:41.035362+00:00
-- url     : https://prove2.me/submissions/37fd9bf7-a344-4c9c-9b56-b612d264de3f

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α] {a : α} (ha : IsUnit a) : a ≠ 0 :=
  ha.ne_zero
end NagataFactoriality
