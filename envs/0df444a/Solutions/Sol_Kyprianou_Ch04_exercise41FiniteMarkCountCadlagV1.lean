-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteMarkCountCadlagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:49:15.044982+00:00
-- url     : https://prove2.me/submissions/51202d5a-bdde-4e6e-9703-16f9439c3f1a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41SingleVisitStepCadlagV1
open Set Filter Topology
open scoped NNReal
set_option autoImplicit false

theorem solution (S : Finset NNReal) :
    (∀ t : NNReal, ContinuousWithinAt
      (fun u : NNReal => ∑ s ∈ S, if s ≤ u then (1 : ℝ) else 0)
      (Ici t) t) ∧
    (∀ t : NNReal, 0 < t → ∃ l : ℝ, Tendsto
      (fun u : NNReal => ∑ s ∈ S, if s ≤ u then (1 : ℝ) else 0)
      (nhdsWithin t (Iio t)) (nhds l)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    constructor
    · intro t
      simpa using (continuousWithinAt_const (b := (0 : ℝ)))
    · intro t ht
      exact ⟨0, by simpa using (tendsto_const_nhds (x := (0 : ℝ)))⟩
  | @insert s S hs ih =>
    obtain ⟨hr, hl⟩ :=
      Kyprianou.Ch04.exercise41SingleVisitStepCadlagV1 s
    have hEq :
        (fun u : NNReal => ∑ v ∈ insert s S,
          if v ≤ u then (1 : ℝ) else 0) =
        (fun u : NNReal => if s ≤ u then (1 : ℝ) else 0) +
          (fun u : NNReal => ∑ v ∈ S,
            if v ≤ u then (1 : ℝ) else 0) := by
      funext u
      simp only [Finset.sum_insert hs, Pi.add_apply]
    constructor
    · intro t
      rw [hEq]
      exact (hr t).add (ih.1 t)
    · intro t ht
      obtain ⟨a, ha⟩ := hl t ht
      obtain ⟨b, hb⟩ := ih.2 t ht
      refine ⟨a + b, ?_⟩
      rw [hEq]
      exact ha.add hb
