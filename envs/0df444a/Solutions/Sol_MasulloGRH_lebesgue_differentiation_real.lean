-- Prove2me | solution 1 for MasulloGRH.lebesgue_differentiation_real
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:57:00.551914+00:00
-- url     : https://prove2.me/submissions/c2b5a742-b056-41a6-a4de-4d9ebe17af7a

import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Filter
open scoped Topology

theorem solution (f : ℝ → ℂ) (hf : LocallyIntegrable f volume) :
    ∀ᵐ x : ℝ, Filter.Tendsto (fun r : ℝ => (1 / (2 * r)) • ∫ y in (x - r)..(x + r), f y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average hf] with x hx
  have h := hx.comp (Besicovitch.tendsto_filterAt volume x)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : 0 < r := hr
  have hle : x - r ≤ x + r := by linarith
  change (⨍ y in Metric.closedBall x r, f y) = _
  rw [Real.closedBall_eq_Icc, setAverage_eq, Real.volume_real_Icc_of_le hle,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hle, one_div,
    show x + r - (x - r) = 2 * r by ring]
