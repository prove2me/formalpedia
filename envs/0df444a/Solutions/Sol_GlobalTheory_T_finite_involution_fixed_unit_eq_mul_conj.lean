-- Prove2me | solution 1 for GlobalTheory.T.finite_involution_fixed_unit_eq_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:24.524468+00:00
-- url     : https://prove2.me/submissions/e855721c-a51d-4dfe-a464-482884a75517

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteInvolutionFixedUnitEqMulConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteInvolutionFixedUnitEqMulConjStatement
import Theorems.Thm_GlobalTheory_finite_involution_fixed_unit_isNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [CommRing S] [Finite S] (c : S →+* S), (∀ x, c (c x) = x) → (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  first | exact @GlobalTheory.finite_involution_fixed_unit_isNorm | exact GlobalTheory.finite_involution_fixed_unit_isNorm | (intros; apply GlobalTheory.finite_involution_fixed_unit_isNorm <;> assumption)
end _root_.GlobalTheory.T
