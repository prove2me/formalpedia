-- Prove2me | solution 1 for Kyprianou.Ch04.clockMeanLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:45:31.628866+00:00
-- url     : https://prove2.me/submissions/226d644d-90b0-476c-92b5-027ff44ed34d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_clockAverageBoundsNNReal
import Theorems.Thm_Kyprianou_Ch04_clockAverageLimitOfSqueeze
import Theorems.Thm_Kyprianou_Ch04_expClockEarlyMassUpper
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A slowly discounted exponential clock preserves the limiting bounded antitone mean. -/
theorem solution
    (f : NNReal → ℝ) (hm : Measurable f) (ha : Antitone f)
    (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1)
    (ell : ℝ) (hlow : ∀ t, ell ≤ f t) (hlim : Tendsto f atTop (nhds ell))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (herr : ∀ T : NNReal, Tendsto (fun n => 1 - Real.exp (-(q n * (T : ℝ)))) atTop (nhds 0)) :
    Tendsto (fun n => ∫ t, f t ∂((expMeasure (q n)).map Real.toNNReal)) atTop (nhds ell) := by
  let A : ℕ → ℝ := fun n => ∫ t, f t ∂((expMeasure (q n)).map Real.toNNReal)
  have hbounds (n : ℕ) (T : NNReal) : ell ≤ A n ∧
      A n ≤ f T + (1 - Real.exp (-(q n * (T : ℝ)))) := by
    let Q := expMeasure (q n)
    let mu := Q.map Real.toNNReal
    let : IsProbabilityMeasure Q := isProbabilityMeasure_expMeasure (hq n)
    let : IsProbabilityMeasure mu :=
      Measure.isProbabilityMeasure_map (by fun_prop : Measurable Real.toNNReal).aemeasurable
    have hfi : Integrable f mu :=
      (integrable_const (1 : ℝ)).mono hm.aestronglyMeasurable
        (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs,abs_of_nonneg (h0 t),Real.norm_eq_abs,abs_one]
          exact h1 t)
    obtain ⟨hlo,hhi⟩ := Kyprianou.Ch04.clockAverageBoundsNNReal mu f ell hfi ha hlow h0 h1 T
    have hmass : (mu (Iio T)).toReal ≤ 1 - Real.exp (-(q n * (T : ℝ))) :=
      Kyprianou.Ch04.expClockEarlyMassUpper (q n) (hq n) T
    exact ⟨hlo, by linarith⟩
  exact Kyprianou.Ch04.clockAverageLimitOfSqueeze f A
    (fun n T => 1 - Real.exp (-(q n * (T : ℝ)))) ell hlim
    (fun n => (hbounds n 0).1) (fun n T => (hbounds n T).2) herr
