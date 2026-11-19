-- Prove2me | solution 1 for Kyprianou.Ch01.gammaArrivalDensityRenewalMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:35:26.239868+00:00
-- url     : https://prove2.me/submissions/4b622f05-0fd8-48da-a22b-42fa9866e928

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Theorems.Thm_Kyprianou_Ch01_gammaArrivalPointwiseENNRealSum
import Theorems.Thm_Kyprianou_Ch01_gammaArrivalDensityMeasurablePublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- The Erlang arrival-time density measure series has total mass βx on [0,x]. -/
theorem solution (beta : ℝ) (hbeta : 0 < beta) :
    ∀ x : ℝ, 0 ≤ x →
      Summable (fun n : ℕ =>
        ((volume.withDensity (LevyFoundations.arrivalGammaDensity beta n))
          (Set.Icc (0 : ℝ) x)).toReal) ∧
      (∑' n : ℕ,
        ((volume.withDensity (LevyFoundations.arrivalGammaDensity beta n))
          (Set.Icc (0 : ℝ) x)).toReal) = beta * x := by
  intro x hx
  let f : ℕ → ℝ → ℝ≥0∞ := LevyFoundations.arrivalGammaDensity beta
  let masses : ℕ → ℝ≥0∞ :=
    fun n => (volume.withDensity (f n)) (Set.Icc (0 : ℝ) x)
  have hmeas (n : ℕ) : Measurable (f n) := by
    exact Kyprianou.Ch01.gammaArrivalDensityMeasurablePublic beta n
  have hpoint (z : ℝ) (hz : 0 ≤ z) :
      (∑' n : ℕ, f n z) = ENNReal.ofReal beta := by
    exact Kyprianou.Ch01.gammaArrivalPointwiseENNRealSum beta z hbeta hz
  have hsumENN : (∑' n : ℕ, masses n) =
      ENNReal.ofReal (beta * x) := by
    have hm (n : ℕ) :
        masses n = ∫⁻ z in Set.Icc (0 : ℝ) x, f n z ∂volume :=
      withDensity_apply (f n) measurableSet_Icc
    simp_rw [hm]
    rw [← lintegral_tsum
      (fun n => (hmeas n).aemeasurable)]
    have hp : (∫⁻ z in Set.Icc (0 : ℝ) x, (∑' n : ℕ, f n z) ∂volume) =
        ∫⁻ _z in Set.Icc (0 : ℝ) x, ENNReal.ofReal beta ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact hpoint z hz.1
    rw [hp, lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Icc]
    simp only [sub_zero]
    rw [ENNReal.ofReal_mul (le_of_lt hbeta)]
  have ht : (∑' n : ℕ, masses n) ≠ ∞ := by
    rw [hsumENN]
    exact ENNReal.ofReal_ne_top
  have hne (n : ℕ) : masses n ≠ ∞ :=
    ENNReal.ne_top_of_tsum_ne_top ht n
  refine ⟨ENNReal.summable_toReal ht, ?_⟩
  change (∑' n : ℕ, (masses n).toReal) = beta * x
  rw [← ENNReal.tsum_toReal_eq hne, hsumENN,
    ENNReal.toReal_ofReal (mul_nonneg hbeta.le hx)]
