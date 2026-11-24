-- Prove2me | solution 1 for GlobalTheory.GallagherLemma.plancherel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:47.526809+00:00
-- url     : https://prove2.me/submissions/a95ca323-2478-4112-893d-f2ddb1f3a668

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Theorems.Thm_GlobalTheory_GallagherLemma_fourier_ae_eq
import Theorems.Thm_GlobalTheory_GallagherLemma_integral_norm_sq_Lp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma
namespace GlobalTheory.GallagherLemma
theorem _root_.solution {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    Integrable (fun x => ‖𝓕 f x‖ ^ 2) ∧ ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := fourier_ae_eq hf h2
  constructor
  · have h3 : MemLp (𝓕 f) 2 volume :=
      (memLp_congr_ae h).2 (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)))
    exact (memLp_two_iff_integrable_sq_norm h3.aestronglyMeasurable).1 h3
  · calc ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖(𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [h] with x hx
          rw [hx]
      _ = ∫ x, ‖(h2.toLp f) x‖ ^ 2 := by
          rw [integral_norm_sq_Lp, integral_norm_sq_Lp, Lp.norm_fourier_eq]
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [h2.coeFn_toLp] with x hx
          rw [hx]
end GlobalTheory.GallagherLemma
