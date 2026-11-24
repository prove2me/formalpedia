-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneParamFourier.integral_translate_mul_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:54:08.654723+00:00
-- url     : https://prove2.me/submissions/172f1fe0-18fc-47e5-8eb8-ce11664925ca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneParamFourier
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]
namespace GlobalTheory.CompanionTheory.OneParamFourier
theorem _root_.solution (lam : Measure A) [lam.IsAddHaarMeasure] (H : A → ℂ)
    (χ : AddChar A ℂ) (a : A) :
    ∫ b, H (b + a) * χ b ∂lam = χ (-a) * ∫ b, H b * χ b ∂lam := by
  have h := integral_add_right_eq_self (μ := lam) (fun b => H b * χ (b + -a)) a
  simp only [add_neg_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [AddChar.map_add_eq_mul]
  ring
end GlobalTheory.CompanionTheory.OneParamFourier
