-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:05.412115+00:00
-- url     : https://prove2.me/submissions/ca38e00c-b862-4a65-86d6-36dd1103112e

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
omit [MeasurableSpace E] [IsProbabilityMeasure P] in
/-- The glued path map is progressively measurable: below any time only finitely many members
of the family are read, on measurable pieces of the time axis. -/
theorem solution
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ k, ∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Y k s ω i)
    (i : Fin n) :
    LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => LevyStochCalc.Ito.Picard.globalPatch Y s ω i := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hsum : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => LevyStochCalc.Ito.Picard.globalPatch Y s p.1 i) p.2)
      = ∑ k ∈ Finset.range (⌈t⌉₊ + 1),
          (fun p : Ω × ℝ => Set.indicator {q : Ω × ℝ | ⌈q.2⌉₊ = k}
            (fun q : Ω × ℝ => (Set.Iic t).indicator (fun s => Y k s q.1 i) q.2) p) := by
    funext p
    rw [Finset.sum_apply]
    by_cases hp : p.2 ≤ t
    · have hmem : ⌈p.2⌉₊ ∈ Finset.range (⌈t⌉₊ + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono hp))
      rw [Finset.sum_eq_single_of_mem ⌈p.2⌉₊ hmem]
      · rw [Set.indicator_of_mem (by simp : p ∈ {q : Ω × ℝ | ⌈q.2⌉₊ = ⌈p.2⌉₊})]
        simp [Set.indicator_of_mem (Set.mem_Iic.mpr hp), LevyStochCalc.Ito.Picard.globalPatch]
      · intro b _ hb
        exact Set.indicator_of_notMem (by simpa [eq_comm] using hb) _
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      by_cases hq : p ∈ {q : Ω × ℝ | ⌈q.2⌉₊ = k}
      · rw [Set.indicator_of_mem hq, Set.indicator_of_notMem (by simpa using hp)]
      · exact Set.indicator_of_notMem hq _
  have hterm : ∀ k : ℕ, StronglyMeasurable
      (fun p : Ω × ℝ => Set.indicator {q : Ω × ℝ | ⌈q.2⌉₊ = k}
        (fun q : Ω × ℝ => (Set.Iic t).indicator (fun s => Y k s q.1 i) q.2) p) := fun k =>
    (hY k i t).indicator
      ((measurable_snd (α := Ω) (β := ℝ)).nat_ceil (measurableSet_singleton k))
  rw [hsum]
  exact Finset.stronglyMeasurable_sum _ fun k _ => hterm k
