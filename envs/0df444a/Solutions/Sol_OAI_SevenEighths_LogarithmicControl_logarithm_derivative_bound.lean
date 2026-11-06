-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.logarithm_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:54:29.09795+00:00
-- url     : https://prove2.me/submissions/7a734b2b-a5ed-4695-ace4-983523774c1f

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl
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
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 8 * e)) :
    ‖deriv g z‖ ≤ (outerConstant e A M / (2 * e)) * T := by
  have hzn : dist z c ≤ 2 - a - 8 * e := hz
  have hsub : closedBall z (2 * e) ⊆ ball c (2 - a - 2 * e) := by
    intro w hw
    have hw' : dist w z ≤ 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c < _
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < 2 * e)
    (hg.diffContOnCl_ball hsub) (C := outerConstant e A M * T) ?_
  · exact h.trans_eq (by ring)
  · intro w hw
    apply outer_log_bound ha ha' he he' hA hM hT hg hRe hc
    have hw' : dist w z = 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c ≤ _
    linarith
end OAI.SevenEighths.LogarithmicControl
