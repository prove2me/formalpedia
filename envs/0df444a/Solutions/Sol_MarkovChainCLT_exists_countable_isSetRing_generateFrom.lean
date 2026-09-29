-- Prove2me | solution 1 for MarkovChainCLT.exists_countable_isSetRing_generateFrom
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T21:43:37.538692+00:00
-- url     : https://prove2.me/submissions/13a9003f-3330-4093-a655-45d04ae31be7

import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.SetSemiring

open MeasureTheory MeasurableSpace Set

set_option maxHeartbeats 1000000

/-- A countably generated measurable space carries a countable generating ring of sets. -/
theorem solution {X : Type*} [mX : MeasurableSpace X] [MeasurableSpace.CountablyGenerated X] :
    ∃ C : Set (Set X), C.Countable ∧ IsSetRing C ∧ (∀ s ∈ C, MeasurableSet s) ∧
      Set.univ ∈ C ∧ generateFrom C = mX := by
  classical
  -- the levels increase
  have hmono : ∀ (n m : ℕ), n ≤ m → ∀ (s : Set X),
      MeasurableSet[generateFrom (countablePartition X n)] s →
      MeasurableSet[generateFrom (countablePartition X m)] s := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro s hs; exact hs
    | succ k hk ih => intro s hs; exact generateFrom_countablePartition_le_succ X k _ (ih s hs)
  refine ⟨⋃ n : ℕ, {s : Set X | MeasurableSet[generateFrom (countablePartition X n)] s},
    ?_, ?_, ?_, ?_, ?_⟩
  · -- countable: each level is finite
    refine Set.countable_iUnion (fun n => Set.Finite.countable ?_)
    have hsub : {s : Set X | MeasurableSet[generateFrom (countablePartition X n)] s}
        ⊆ (fun t : Set (Set X) => ⋃₀ t) '' {t | t ⊆ countablePartition X n} := by
      intro s hs
      obtain ⟨S, hS, rfl⟩ := (measurableSet_generateFrom_countablePartition_iff n s).mp hs
      exact ⟨↑S, hS, rfl⟩
    exact Set.Finite.subset (((finite_countablePartition X n).finite_subsets).image _) hsub
  · -- a ring of sets
    refine ⟨?_, ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨0, @MeasurableSet.empty X (generateFrom (countablePartition X 0))⟩
    · rintro s t hs ht
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
      obtain ⟨n, hn⟩ := hs
      obtain ⟨m, hm⟩ := ht
      exact ⟨max n m, (hmono n _ (le_max_left n m) s hn).union (hmono m _ (le_max_right n m) t hm)⟩
    · rintro s t hs ht
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs ht ⊢
      obtain ⟨n, hn⟩ := hs
      obtain ⟨m, hm⟩ := ht
      exact ⟨max n m, (hmono n _ (le_max_left n m) s hn).diff (hmono m _ (le_max_right n m) t hm)⟩
  · -- every member is measurable
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs
    obtain ⟨n, hn⟩ := hs
    exact generateFrom_countablePartition_le X n _ hn
  · simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨0, @MeasurableSet.univ X (generateFrom (countablePartition X 0))⟩
  · -- it generates
    refine le_antisymm (generateFrom_le ?_) ?_
    · intro s hs
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hs
      obtain ⟨n, hn⟩ := hs
      exact generateFrom_countablePartition_le X n _ hn
    · refine le_trans (le_of_eq (generateFrom_iUnion_countablePartition X).symm) ?_
      refine generateFrom_mono (fun s hs => ?_)
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hs
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨n, measurableSet_generateFrom hn⟩
