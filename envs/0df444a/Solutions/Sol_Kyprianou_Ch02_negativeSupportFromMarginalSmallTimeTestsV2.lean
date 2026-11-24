-- Prove2me | solution 1 for Kyprianou.Ch02.negativeSupportFromMarginalSmallTimeTestsV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:58:47.814978+00:00
-- url     : https://prove2.me/submissions/907001ec-3fa0-4e1c-bb67-59d75260127d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Theorems.Thm_Kyprianou_Ch02_negativeSupportFixedCutoffFromMarginalTestsV1
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
        atTop (nhds (∫ x, f x ∂ν))) :
    ν (Set.Iio (0 : ℝ)) = 0 := by
  have hall : ∀ᵐ x ∂ν, ∀ n : ℕ, -(1 / (n+1 : ℝ)) ≤ x := by
    rw [ae_all_iff]
    exact fun n => Kyprianou.Ch02.negativeSupportFixedCutoffFromMarginalTestsV1
      M ν hν hS ts hjump _ (by positivity)
  have hnon : ∀ᵐ x ∂ν, 0 ≤ x := by
    filter_upwards [hall] with x hx
    by_contra! hneg
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hneg)
    linarith [hx n]
  rw [ae_iff] at hnon
  simpa only [Set.Iio, not_le] using hnon
