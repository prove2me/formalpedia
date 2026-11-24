-- Prove2me | solution 1 for Kyprianou.Ch03.finiteOrderedGridCoversV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:25:30.485946+00:00
-- url     : https://prove2.me/submissions/50740758-2657-4435-8eaf-d795b90a93ee

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
theorem solution
    (t : NNReal) (J : Finset {s : NNReal // s ≤ t}) :
    ∃ n : Nat, ∃ q : Fin (n + 1) → NNReal,
      Monotone q ∧ q 0 = 0 ∧ (∀ i, q i ≤ t) ∧
      ∀ s ∈ J, ∃ i, q i = (s : NNReal) := by
  classical
  let S : Finset NNReal := insert 0 (Finset.image (fun s : {s : NNReal // s ≤ t} => s.val) J)
  have hzero : 0 ∈ S := by simp [S]
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨0, hzero⟩
  let n := S.card - 1
  have hn : S.card = n + 1 := by dsimp [n]; omega
  let e := S.orderIsoOfFin hn
  let q (i : Fin (n + 1)) : NNReal := (e i : NNReal)
  have hq : Monotone q := fun i j hij => e.monotone hij
  have hmem (i : Fin (n + 1)) : q i ∈ S := (e i).property
  have hz : q 0 = 0 := by
    let j := e.symm ⟨0, hzero⟩
    have hj : q j = 0 := congrArg Subtype.val (e.apply_symm_apply ⟨0, hzero⟩)
    have h := hq (show (0 : Fin (n + 1)) ≤ j from Fin.zero_le _)
    rw [hj] at h
    exact le_antisymm h zero_le
  refine ⟨n, q, hq, hz, ?_, ?_⟩
  · intro i
    have h := hmem i
    simp only [S, Finset.mem_insert, Finset.mem_image] at h
    rcases h with h | ⟨s, hs, h⟩
    · rw [h]; exact zero_le
    · rw [← h]; exact s.property
  · intro s hs
    have h : (s : NNReal) ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
    exact ⟨e.symm ⟨s, h⟩, congrArg Subtype.val (e.apply_symm_apply ⟨s, h⟩)⟩
