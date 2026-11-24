-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:59.446916+00:00
-- url     : https://prove2.me/submissions/f5fda3f5-94d5-4808-988a-2bcf57dab943

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralWeierstrassTorsionQCoefficients
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralWeierstrassTorsionQCoefficientsStatement
import Theorems.Thm_GlobalTheory_WpFam_isIntegral_coefficients


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ), 0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * cB N x k) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * cP N x k) ∧ IsIntegral ℤ (12 * cG N k) := by
  first | exact @GlobalTheory.WpFam.isIntegral_coefficients | exact GlobalTheory.WpFam.isIntegral_coefficients | (intros; apply GlobalTheory.WpFam.isIntegral_coefficients <;> assumption)
end _root_.GlobalTheory.T
