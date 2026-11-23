-- Prove2me | solution 1 for Kyprianou.Ch01.zeroRightDerivativeOfLinearSmallFactor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:17:33.58086+00:00
-- url     : https://prove2.me/submissions/4a765cda-7389-46b4-82e7-bf6ce27b77e2

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f h : ℝ → ℝ) (c : ℝ)
    (hSmall : Tendsto h
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hBound : ∀ t : ℝ, 0 ≤ t →
      0 ≤ f t ∧ f t ≤ c * t * h t) :
    HasDerivWithinAt f 0 (Set.Ici 0) 0 := by
  have hz : f 0 = 0 := by
    have hh := hBound 0 le_rfl
    have hle : f 0 ≤ 0 := by
      calc
        f 0 ≤ c * (0 : ℝ) * h 0 := hh.2
        _ = 0 := by ring
    exact le_antisymm hle hh.1
  have hupper : Tendsto (fun t : ℝ => c * h t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hSmall)
  have hquot : Tendsto (fun t : ℝ => f t / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_nonneg (hBound t ht.le).1 ht.le
    · filter_upwards [self_mem_nhdsWithin] with t ht
      apply (div_le_iff₀ ht).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (hBound t ht.le).2
  have hder : HasDerivWithinAt f 0 (Set.Ioi 0) 0 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).2
    have hslope : (slope f 0 : ℝ → ℝ) =
        (fun t : ℝ => f t / t) := by
      funext t
      rw [slope_def_field]
      simp [hz]
    rw [hslope]
    exact hquot
  exact hder.Ici_of_Ioi
