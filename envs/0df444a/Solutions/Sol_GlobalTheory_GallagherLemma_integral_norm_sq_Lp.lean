-- Prove2me | solution 1 for GlobalTheory.GallagherLemma.integral_norm_sq_Lp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:18.789289+00:00
-- url     : https://prove2.me/submissions/7199d83a-247a-435f-ae7c-53b7d959439d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp

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
theorem _root_.solution (F : Lp ℂ 2 (volume : Measure ℝ)) : ∫ x, ‖F x‖ ^ 2 = ‖F‖ ^ 2 := by
  have := L2.inner_def (𝕜 := ℂ) F F
  rw [inner_self_eq_norm_sq_to_K] at this
  simp only [inner_self_eq_norm_sq_to_K] at this
  have h : ((∫ x, ‖F x‖ ^ 2 : ℝ) : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    exact this.symm
  exact_mod_cast h
end GlobalTheory.GallagherLemma
