-- Prove2me | solution 1 for GlobalTheory.HCA.dw_contDiff_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:54:10.783217+00:00
-- url     : https://prove2.me/submissions/1e6788ae-c1a2-4819-b1b0-844c549f4c09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution {d : ℕ} (w : List (Fin d)) {φ : E d → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (dw w φ) ∧ tsupport (dw w φ) ⊆ tsupport φ := by
  induction w with
  | nil => exact ⟨hφ, subset_rfl⟩
  | cons j w ih =>
    refine ⟨(ih.1.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, ?_⟩
    refine (closure_mono ?_).trans ((tsupport_fderiv_subset (𝕜 := ℝ) (f := dw w φ)).trans ih.2)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h; apply hx; show fderiv ℝ (dw w φ) x (ev j) = 0; simp [h]
end GlobalTheory.HCA
