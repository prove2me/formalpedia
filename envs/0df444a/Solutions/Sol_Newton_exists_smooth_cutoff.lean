-- Prove2me | solution 1 for Newton.exists_smooth_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:22.366856+00:00
-- url     : https://prove2.me/submissions/c4a7c781-008b-4a2f-8250-e6189a63dcbe

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Definitions.Def_Newton_Analysis_Convolution_ApproximateIdentity
import Definitions.Def_Newton_Analysis_Convolution_Bounds
import Definitions.Def_Newton_Analysis_Distribution_SchwartzDensity

set_option autoImplicit false
open MeasureTheory SchwartzMap Complex NNReal
open scoped ENNReal ContDiff Topology Convolution ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (r R : ℝ) (hr : 0 < r) (hR : r < R) :
    ∃ χ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (∞ : WithTop ℕ∞) χ ∧
      (∀ x, ‖x‖ ≤ r → χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.closedBall (0 : Fin n → ℝ) R := by
  let χ_bump : ContDiffBump (0 : Fin n → ℝ) := ⟨r, R, hr, hR⟩
  let χ : (Fin n → ℝ) → ℝ := fun x => χ_bump x
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [χ] using χ_bump.contDiff
  · intro x hx
    have hx_mem : x ∈ Metric.closedBall (0 : Fin n → ℝ) χ_bump.rIn := by
      simpa [χ, Metric.mem_closedBall, dist_eq_norm] using hx
    simpa [χ] using χ_bump.one_of_mem_closedBall hx_mem
  · intro x
    have h_nonneg : 0 ≤ χ_bump x := by
      simpa [χ] using χ_bump.nonneg' x
    have h_le_one : χ_bump x ≤ 1 := by
      simpa [χ] using (χ_bump.le_one (x := x))
    exact ⟨h_nonneg, h_le_one⟩
  · simpa [χ] using χ_bump.hasCompactSupport
  · have h_tsupp_eq : tsupport χ =
        Metric.closedBall (0 : Fin n → ℝ) χ_bump.rOut := by
      simpa [χ] using χ_bump.tsupport_eq
    have h_rOut : χ_bump.rOut = R := rfl
    simp [χ, h_rOut, h_tsupp_eq]
end Newton
