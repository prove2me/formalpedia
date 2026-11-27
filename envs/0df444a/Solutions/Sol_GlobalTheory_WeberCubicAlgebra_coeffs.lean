-- Prove2me | solution 1 for GlobalTheory.WeberCubicAlgebra.coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:39:24.177587+00:00
-- url     : https://prove2.me/submissions/c9a5bf7f-ddb1-4787-8ba4-4c4e328cf733

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeberFunctionsRootsOfCubicOfHalfPeriodDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Polynomial
open UpperHalfPlane hiding I
noncomputable section
open GlobalTheory GlobalTheory.WeberCubicAlgebra
namespace GlobalTheory.WeberCubicAlgebra
theorem _root_.solution (A B D j F0 F1 F2 : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (hs : A = B + D)
    (h0 : F0 * (B * D) = 16 * A ^ 2) (h1 : F1 * (A * D) = 16 * B ^ 2)
    (h2 : F2 * (A * B) = 16 * D ^ 2) (hj : j * (A * B * D) ^ 2 = 32 * (A ^ 2 + B ^ 2 + D ^ 2) ^ 3) :
    F0 - F1 - F2 = 48 ∧ -(F0 * F1) - F0 * F2 + F1 * F2 = 768 - j ∧ F0 * F1 * F2 = 4096 := by
  have e0 : F0 = 16 * A ^ 2 / (B * D) := by rw [eq_div_iff (mul_ne_zero hB hD)]; exact h0
  have e1 : F1 = 16 * B ^ 2 / (A * D) := by rw [eq_div_iff (mul_ne_zero hA hD)]; exact h1
  have e2 : F2 = 16 * D ^ 2 / (A * B) := by rw [eq_div_iff (mul_ne_zero hA hB)]; exact h2
  have ej : j = 32 * (A ^ 2 + B ^ 2 + D ^ 2) ^ 3 / (A * B * D) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hA hB) hD))]; exact hj
  subst e0 e1 e2 ej hs
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring
end GlobalTheory.WeberCubicAlgebra
