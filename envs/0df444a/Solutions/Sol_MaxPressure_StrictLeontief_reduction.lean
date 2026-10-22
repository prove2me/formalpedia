-- Prove2me | solution 1 for MaxPressure.StrictLeontief.reduction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:29:24.02646+00:00
-- url     : https://prove2.me/submissions/90b89995-c5d9-49ae-bd9d-b14c1bb106da

import Mathlib
import Definitions.Def_MaxPressure_StrictLeontief_Network



namespace MaxPressure.StrictLeontief

theorem reduction_core {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (h : ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i := by
  obtain ⟨a, ha, hmax, hvan⟩ := h
  refine ⟨a, ha, hmax, ?_⟩
  intro i hi
  have hapos : ∀ j, 0 ≤ a j := fun j => ha.1.1 j
  obtain ⟨-, hB01, -, hio, -⟩ := hN
  simp only [constituentBuffers, Set.mem_setOf_eq] at hi
  have : ∃ j, 0 < a j * N.B j i.succ := by
    by_contra hcon
    push_neg at hcon
    exact absurd hi (not_lt.2 (Finset.sum_nonpos (fun j _ => hcon j)))
  obtain ⟨j, hj⟩ := this
  have hBj : N.B j i.succ = 1 := by
    rcases hB01 j i.succ with h0 | h1
    · rw [h0] at hj; simp at hj
    · exact h1
  have haj : a j ≠ 0 := by
    intro h0; rw [h0] at hj; simp at hj
  rcases (hz i).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply haj
    apply hvan
    refine ⟨?_, i, hBj, heq.symm⟩
    rcases hio j with hin | hs
    · have := hin.2 i; rw [this] at hBj; norm_num at hBj
    · exact hs

end MaxPressure.StrictLeontief

open MaxPressure.StrictLeontief


theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hSL : IsStrictLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (h : ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ j ∈ J0 N z, a j = 0) :
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i := by
  exact reduction_core N hN hSL z hz h
