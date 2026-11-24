-- Prove2me | solution 1 for Kyprianou.Ch02.negativeSupportFixedCutoffFromMarginalTestsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:59:01.289345+00:00
-- url     : https://prove2.me/submissions/490377ae-1cdc-4a77-83a3-4daaf7e285b8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_boundedContinuousNegativeCutoffV1
import Theorems.Thm_Kyprianou_Ch02_levyBoundedContinuousVanishingNearZeroIntegrableV1
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem solution
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (hS : ∀ t, (M t : Measure ℝ) (Set.Iio (0 : ℝ)) = 0)
    (ts : ℕ → {t : ℝ // 0 < t})
    (hjump : ∀ f : BoundedContinuousFunction ℝ ℝ,
      (∃ r > 0, ∀ x, |x| < r → f x = 0) →
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x, f x ∂(M (ts n) : Measure ℝ))
        atTop (nhds (∫ x, f x ∂ν)))
    (r : ℝ) (hr : 0 < r) :
    ∀ᵐ x ∂ν, -r ≤ x := by
  obtain ⟨f, hf0, hfzero, hfpos⟩ := Kyprianou.Ch02.boundedContinuousNegativeCutoffV1 r hr
  have hv (x : ℝ) (hx : |x| < r) : f x = 0 := hfzero x (abs_lt.mp hx).1.le
  have hM (t : {t : ℝ // 0 < t}) : ∫ x, f x ∂(M t : Measure ℝ) = 0 := by
    have hn : ∀ᵐ x ∂(M t : Measure ℝ), 0 ≤ x := by
      rw [ae_iff]
      simpa only [Set.Iio, not_le] using hS t
    calc
      _ = ∫ x, (0 : ℝ) ∂(M t : Measure ℝ) :=
        integral_congr_ae (hn.mono (fun x hx => hfzero x (by linarith)))
      _ = 0 := by simp
  have hlim := hjump f ⟨r, hr, hv⟩
  simp only [hM, mul_zero] at hlim
  have hz : ∫ x, f x ∂ν = 0 := tendsto_nhds_unique hlim tendsto_const_nhds
  have hfi := Kyprianou.Ch02.levyBoundedContinuousVanishingNearZeroIntegrableV1
    ν hν f r hr hv
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hf0) hfi).1 hz
  filter_upwards [hae] with x hx
  by_contra! hneg
  exact (ne_of_gt (hfpos x hneg)) hx
