-- Prove2me | solution 1 for Kyprianou.Ch06.finiteObservationTimesStrictGrid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:59:02.580208+00:00
-- url     : https://prove2.me/submissions/c6969d9a-79ad-4b12-a417-f92715c74039

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
set_option autoImplicit false

theorem solution
    (m : Nat) (times : Fin m → NNReal) :
    ∃ (k : Nat) (grid : Fin k → NNReal),
      StrictMono grid ∧
      (∀ i : Fin m, ∃ j : Fin k, grid j = times i) ∧
      (∃ j : Fin k, grid j = 0) := by
  classical
  let s : Finset NNReal := insert 0 (Finset.univ.image times)
  let e := s.orderIsoOfFin rfl
  refine ⟨s.card, (fun j => (e j).val), ?_, ?_, ?_⟩
  · intro i j hij
    exact e.strictMono hij
  · intro i
    have hmem : times i ∈ s := by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    refine ⟨e.symm ⟨times i, hmem⟩, ?_⟩
    simp [e]
  · have hmem : (0 : NNReal) ∈ s := by
      simp [s]
    refine ⟨e.symm ⟨0, hmem⟩, ?_⟩
    simp [e]
