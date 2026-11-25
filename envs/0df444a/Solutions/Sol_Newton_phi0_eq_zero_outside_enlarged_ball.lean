-- Prove2me | solution 1 for Newton.phi0_eq_zero_outside_enlarged_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:25:12.805855+00:00
-- url     : https://prove2.me/submissions/27760ae8-a17c-4d0f-a36c-1923e4b20fae

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (φ₀ : (Fin n → ℝ) → ℂ) (R : ℝ)
    (h_support : tsupport φ₀ ⊆ Metric.closedBall (0 : Fin n → ℝ) (R + 1)) :
    ∀ ⦃x : Fin n → ℝ⦄, R + 1 < ‖x‖ → φ₀ x = 0 := by
  intro x hx_norm
  have hx_not_tsupport : x ∉ tsupport φ₀ := by
    intro hx
    have hx_le : dist x (0 : (Fin n → ℝ)) ≤ R + 1 :=
      (Metric.mem_closedBall.mp (h_support hx))
    have hx_norm_le : ‖x‖ ≤ R + 1 := by
      simpa [dist_eq_norm] using hx_le
    exact (not_le_of_gt hx_norm) hx_norm_le
  by_contra h_nonzero
  have hx_support : x ∈ Function.support φ₀ := by
    simp [Function.support, h_nonzero]
  have hx_tsupport : x ∈ tsupport φ₀ := by
    have hx_closure : x ∈ closure (Function.support φ₀) := subset_closure hx_support
    simpa [tsupport] using hx_closure
  exact hx_not_tsupport hx_tsupport
end Newton
