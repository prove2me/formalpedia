-- Prove2me | solution 1 for NagataFactoriality.Submonoid.le_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:56.204414+00:00
-- url     : https://prove2.me/submissions/2616982f-60b5-4fb6-8be4-3731c64b3977

import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Theorems.Thm_NagataFactoriality_Submonoid_mem_ne_zero

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Submonoid
variable {α : Type*} [CommRing α] [IsDomain α]
namespace NagataFactoriality.Submonoid
theorem _root_.solution {S : Submonoid α} [Fact ((0 : α) ∉ S)] :
    S ≤ nonZeroDivisors α := by
  intro s hs
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact mem_ne_zero hs
end NagataFactoriality.Submonoid
