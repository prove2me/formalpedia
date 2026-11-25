-- Prove2me | solution 1 for Newton.tsupport_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:08.13489+00:00
-- url     : https://prove2.me/submissions/9dd8686a-c78c-4c2d-b24e-0bf59ed5b794

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
    (g : (Fin n → ℝ) → ℂ) (hg_compact : HasCompactSupport g) :
    ∃ R : ℝ, tsupport g ⊆ Metric.closedBall (0 : Fin n → ℝ) R ∧ 1 ≤ R := by
  -- tsupport g is compact by assumption
  have h_compact : IsCompact (tsupport g) := hg_compact
  -- Compact sets in ℝⁿ are bounded
  have h_bounded : Bornology.IsBounded (tsupport g) := h_compact.isBounded
  -- Bounded sets can be covered by a closed ball
  obtain ⟨R₀, hR₀⟩ := h_bounded.subset_closedBall (0 : Fin n → ℝ)
  -- Take R = max(R₀, 1) to ensure R ≥ 1
  refine ⟨max R₀ 1, ?_, le_max_right R₀ 1⟩
  exact hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left R₀ 1))
end Newton
