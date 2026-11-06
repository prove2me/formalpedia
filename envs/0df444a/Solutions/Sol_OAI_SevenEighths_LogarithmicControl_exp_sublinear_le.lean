-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.exp_sublinear_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:05.377287+00:00
-- url     : https://prove2.me/submissions/158ade6b-bd73-4ef3-93f2-7ec3cc4227bd

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex
open OAI.SevenEighths OAI.SevenEighths.LogarithmicControl
namespace OAI.SevenEighths.LogarithmicControl
theorem _root_.solution {θ K ε : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      Real.exp (K * x ^ θ) ≤ D * Real.exp (ε * x) := by
  have ht : Tendsto (fun x : ℝ ↦ K * x ^ (-(1 - θ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).const_mul K
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let Y := max 1 X
  refine ⟨Real.exp (K * Y ^ θ), Real.exp_pos _, ?_⟩
  intro x hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hYp : 0 < Y := zero_lt_one.trans_le (le_max_left _ _)
  by_cases hxy : x ≤ Y
  · have h1 : Real.exp (K * x ^ θ) ≤ Real.exp (K * Y ^ θ) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxp.le hxy hθ) hK
    exact h1.trans (le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_exp (by positivity)))
  · have hlarge := hX x ((le_max_right 1 X).trans (lt_of_not_ge hxy).le)
    have heq : K * x ^ θ = (K * x ^ (-(1 - θ))) * x := by
      have hp := Real.rpow_add hxp (-(1 - θ)) 1
      rw [Real.rpow_one] at hp
      rw [mul_assoc, ← hp]
      congr 2
      ring
    have hlin : K * x ^ θ ≤ ε * x := by
      rw [heq]
      exact mul_le_mul_of_nonneg_right hlarge.le hxp.le
    exact (Real.exp_le_exp.mpr hlin).trans (le_mul_of_one_le_left
      (Real.exp_pos _).le (Real.one_le_exp (mul_nonneg hK (Real.rpow_nonneg hYp.le _))))
end OAI.SevenEighths.LogarithmicControl
