-- Prove2me | solution 1 for MinBuying.affiliated_threshold_comparison
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:09:43.665306+00:00
-- url     : https://prove2.me/submissions/cc5971c1-ddc2-4ffa-96c3-e2f592e54159

import Theorems.Thm_MinBuying_finite_affiliated_coarsening
import Theorems.Thm_MinBuying_pmf_threshold_comparison

open MeasureTheory Set MinBuying
noncomputable section

private lemma maximum_measurable {n : ℕ} (t : ℝ) :
    MeasurableSet (upperMaximumEvent (n := n) t) := by
  simp only [upperMaximumEvent,setOf_exists]
  exact MeasurableSet.iUnion (fun i => measurableSet_le measurable_const (measurable_pi_apply i))

private lemma mixed_measurable {n : ℕ} (i : Fin n) (a t : ℝ) :
    MeasurableSet (coordinateBelowAndUpperMaximumEvent i a t) :=
  (measurableSet_lt (measurable_pi_apply i) measurable_const).inter (maximum_measurable t)

theorem solution (n : ℕ) (hn : 0 < n) (μ : JointLaw n)
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (i : Fin n) (a b : ℝ) (hab : a ≤ b)
    (hb : 0 < μ (upperMaximumEvent b)) :
    (μ (coordinateBelowAndUpperMaximumEvent i a b)).toReal /
        (μ (upperMaximumEvent b)).toReal ≤
      (μ (coordinateBelowAndUpperMaximumEvent i a a)).toReal /
        (μ (upperMaximumEvent a)).toReal := by
  classical
  let S : Finset ℝ := {a,b}
  obtain ⟨q,w,hq,hq0,hcompare,hw,hwvalid,hwex,hwmtp⟩ :=
    finite_affiliated_coarsening n μ hμ hex haff S
  have haS : a ∈ S := by simp [S]
  have hbS : b ∈ S := by simp [S]
  have hQ : Measurable (fun v : Valuations n => fun j => q (v j)) :=
    measurable_pi_lambda _ (fun j => hq.comp (measurable_pi_apply j))
  have hmax : ∀ t ∈ S, w.toMeasure (upperMaximumEvent t) = μ (upperMaximumEvent t) := by
    intro t ht
    rw [hw,Measure.map_apply hQ (maximum_measurable t)]
    apply measure_congr
    filter_upwards [hμ.2] with v hv
    apply propext
    change (∃ j,t ≤ q (v j)) ↔ ∃ j,t ≤ v j
    exact exists_congr (fun j => hcompare t ht (v j) (hv j))
  have hmix : ∀ t ∈ S, w.toMeasure (coordinateBelowAndUpperMaximumEvent i a t) =
      μ (coordinateBelowAndUpperMaximumEvent i a t) := by
    intro t ht
    rw [hw,Measure.map_apply hQ (mixed_measurable i a t)]
    apply measure_congr
    filter_upwards [hμ.2] with v hv
    apply propext
    change (q (v i) < a ∧ ∃ j,t ≤ q (v j)) ↔ (v i < a ∧ ∃ j,t ≤ v j)
    rw [← not_le,← not_le, hcompare a haS (v i) (hv i)]
    exact and_congr_right (fun _ => exists_congr (fun j => hcompare t ht (v j) (hv j)))
  have hwb : 0 < w.toMeasure (upperMaximumEvent b) := by rw [hmax b hbS];exact hb
  have h := pmf_threshold_comparison n hn w hwvalid hwex hwmtp i a b hab hwb
  simpa only [hmix b hbS,hmix a haS,hmax b hbS,hmax a haS] using h
