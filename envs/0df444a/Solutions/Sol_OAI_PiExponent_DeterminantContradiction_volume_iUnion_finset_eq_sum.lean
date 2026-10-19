-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.volume_iUnion_finset_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:38:46.329584+00:00
-- url     : https://prove2.me/submissions/c227c107-a624-4fec-b564-64721a95a785

import Mathlib

open scoped BigOperators

theorem solution
    {m : ℕ} {ι : Type} [DecidableEq ι] (S : Finset ι)
    (A : ι → Set (Fin m → ℝ))
    (hmeas : ∀ a ∈ S, MeasurableSet (A a))
    (hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (A a) (A b)) :
    MeasureTheory.volume (⋃ a ∈ S, A a) =
      ∑ a ∈ S, MeasureTheory.volume (A a) := by
  apply MeasureTheory.measure_biUnion_finset
  · intro a ha b hb hab
    exact hdisj a ha b hb hab
  · exact hmeas