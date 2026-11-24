-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ConvTest.norm_cv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:39:24.781553+00:00
-- url     : https://prove2.me/submissions/6794196b-06cc-412f-814d-929d0821ea21

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableReflect
import Theorems.Thm_GlobalTheory_CompanionTheory_ConvTest_integrable_reflect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ConvTest
variable (X : Ctx)
namespace GlobalTheory.CompanionTheory.ConvTest
theorem _root_.solution {φ ψ : X.G → ℂ} (hψ : Tst ψ) (B : ℝ) (hB : ∀ z, ‖φ z‖ ≤ B) (y : X.G) :
    ‖cv X.μ φ ψ y‖ ≤ B * ∫ z, ‖ψ z⁻¹‖ ∂X.μ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  have hshift : ∫ z, ‖ψ (z⁻¹ * y)‖ ∂X.μ = ∫ z, ‖ψ z⁻¹‖ ∂X.μ := by
    have h := integral_mul_left_eq_self (μ := X.μ) (fun z => ‖ψ z⁻¹‖) y⁻¹
    simpa [mul_inv_rev] using h
  have hle : ‖cv X.μ φ ψ y‖ ≤ ∫ z, B * ‖ψ (z⁻¹ * y)‖ ∂X.μ := by
    refine norm_integral_le_of_norm_le ((integrable_reflect X hψ y).const_mul B) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)
  rw [integral_const_mul, hshift] at hle
  exact hle
end GlobalTheory.CompanionTheory.ConvTest
