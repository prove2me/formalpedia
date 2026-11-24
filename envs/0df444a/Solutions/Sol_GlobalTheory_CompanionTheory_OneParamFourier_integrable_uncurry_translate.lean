-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OneParamFourier.integrable_uncurry_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:54:07.142184+00:00
-- url     : https://prove2.me/submissions/0616c5b9-8862-4142-9ef4-20aabeb4dd2c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierOneParameterIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_OneParamFourier_integrable_mul_char

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
theorem _root_.solution (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam]
    (c : ℝ →+ A) (hc : Continuous c) {G : A → ℂ} (hG : Continuous G) (hGi : Integrable G lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (K : ℂ) (s : ℝ) :
    Integrable (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b)
      ((volume.restrict (Set.uIoc 0 s)).prod lam) := by
  have hcont : Continuous (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) := by
    unfold Function.uncurry
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) s)) := by
    unfold Set.uIoc
    infer_instance
  refine (integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨ae_of_all _ fun u => ?_, ?_⟩
  · have h1 : Integrable (fun b => G (b + c u)) lam := hGi.comp_add_right (c u)
    have h2 := integrable_mul_char (h1.const_mul K) hχ hn
    simpa [Function.uncurry, mul_assoc] using h2
  · have hconst : ∀ u : ℝ, ∫ b, ‖Function.uncurry (fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) (u, b)‖ ∂lam
        = ‖K‖ * ∫ b, ‖G b‖ ∂lam := by
      intro u
      have h := integral_add_right_eq_self (μ := lam) (fun b => ‖G b‖) (c u)
      rw [← h, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp [Function.uncurry, hn]
    simp_rw [hconst]
    exact integrable_const _
end GlobalTheory.CompanionTheory.OneParamFourier
