-- Prove2me | solution 1 for Kyprianou.Ch01.strictMono_of_dense_rightContinuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:01:20.14661+00:00
-- url     : https://prove2.me/submissions/4aa41985-22ef-4455-b68a-34e810920ee1

import Mathlib
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.NNReal.Lemmas
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Dense strict increase plus right continuity forces strict increase
    at every physical time, including the endpoint zero. -/
theorem solution
    (f : ℝ≥0 → ℝ)
    (hcont : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t)
    (S : Set ℝ≥0) (hDense : Dense S)
    (hstrict : ∀ s ∈ S, ∀ t ∈ S, s < t → f s < f t) :
    StrictMono f := by
  intro s t hst
  obtain ⟨u, huS, hsu, hut⟩ := hDense.exists_between hst
  obtain ⟨v, hvS, huv, hvt⟩ := hDense.exists_between hut
  have huvStrict : f u < f v := hstrict u huS v hvS huv
  have hsuLe : f s ≤ f u := by
    obtain ⟨p, hpanti, hpmem, hplim⟩ :=
      hDense.exists_seq_strictAnti_tendsto_of_lt hsu
    have hpWithin : Tendsto p atTop (𝓝[Set.Ici s] s) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hplim, Filter.Eventually.of_forall (fun n => (hpmem n).1.1.le)⟩
    have hlimit : Tendsto (fun n => f (p n)) atTop (𝓝 (f s)) :=
      (hcont s).tendsto.comp hpWithin
    have hpLe (n : ℕ) : f (p n) ≤ f u :=
      (hstrict (p n) (hpmem n).2 u huS (hpmem n).1.2).le
    exact le_of_tendsto' hlimit hpLe
  have hvtLe : f v ≤ f t := by
    obtain ⟨q, hqanti, hqmem, hqlim⟩ :=
      hDense.exists_seq_strictAnti_tendsto t
    have hqgt (n : ℕ) : t < q n := (hqmem n).1
    have hqWithin : Tendsto q atTop (𝓝[Set.Ici t] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hqlim, Filter.Eventually.of_forall (fun n => show q n ∈ Set.Ici t from
          le_of_lt (hqgt n))⟩
    have hlimit : Tendsto (fun n => f (q n)) atTop (𝓝 (f t)) :=
      (hcont t).tendsto.comp hqWithin
    have hqGe (n : ℕ) : f v ≤ f (q n) :=
      (hstrict v hvS (q n) (hqmem n).2
        (hvt.trans (hqmem n).1)).le
    exact ge_of_tendsto' hlimit hqGe
  exact lt_of_le_of_lt hsuLe (lt_of_lt_of_le huvStrict hvtLe)
