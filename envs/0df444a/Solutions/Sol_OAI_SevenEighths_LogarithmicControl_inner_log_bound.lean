-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.inner_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:54:28.511498+00:00
-- url     : https://prove2.me/submissions/b7bdcb9f-4e70-4456-8a2b-f7bf4c068d95

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_three_circles_power_bound
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_three_circles_exponent_uniform
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_outerConstant_ge_one
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_outer_log_bound

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex
open OAI.SevenEighths OAI.SevenEighths.LogarithmicControl
namespace OAI.SevenEighths.LogarithmicControl
theorem _root_.solution {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hin : ∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c (2 - a - 6 * e)) :
    ‖g z‖ ≤ A * outerConstant e A M * T ^ uniformTheta e := by
  have hB := outerConstant_ge_one he he' hA hM
  have hb : ∀ w ∈ closedBall c (2 - a - 4 * e), ‖g w‖ ≤ outerConstant e A M * T :=
    fun w hw ↦ outer_log_bound ha ha' he he' hA hM hT hg hRe
      (hin c (mem_closedBall_self (by norm_num))) hw
  have h := three_circles_power_bound (by norm_num : (0 : ℝ) < 49 / 100)
    (by linarith : 49 / 100 < 2 - a - 6 * e)
    (by linarith : 2 - a - 6 * e < 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 2 * e)
    hA hB hT hg hin hb hz
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT (three_circles_exponent_uniform ha ha' he he'))
    (by positivity))
end OAI.SevenEighths.LogarithmicControl
