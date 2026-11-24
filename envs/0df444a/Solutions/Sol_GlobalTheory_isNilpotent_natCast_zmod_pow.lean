-- Prove2me | solution 1 for GlobalTheory.isNilpotent_natCast_zmod_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:04:53.627059+00:00
-- url     : https://prove2.me/submissions/e729f57f-b781-4b1b-baae-d4ef194b6a44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsNeZeroHalfStandardAltFormConstOfExponentOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
open GlobalTheory
variable {n k : ℕ}
namespace GlobalTheory
theorem _root_.solution (n k : ℕ) : IsNilpotent (n : ZMod (n ^ k)) :=
  ⟨k, by rw [← Nat.cast_pow, ZMod.natCast_self]⟩
end GlobalTheory
