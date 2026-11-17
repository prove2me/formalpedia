-- Prove2me | solution 1 for KnodelPrimeCordial.count_selected_residue_partition__p2m_26f020af_5673_4287_8efa_c1124a20bf65_a1
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T12:42:00.310075+00:00
-- url     : https://prove2.me/submissions/d4c34cf0-1440-4774-aed0-b7033e562cc7

import Mathlib

theorem solution (k : ℕ) :
    (Finset.univ.filter fun j : Fin (6 * k + 3) =>
      j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ)).card =
      (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 1).card +
        (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 2).card +
        (Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 4).card := by
  classical
  let S := Finset.univ.filter fun j : Fin (6 * k + 3) =>
    j.val ≠ 0 ∧ j.val % 6 ∈ ({1, 2, 4} : Finset ℕ)
  let A := Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 1
  let B := Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 2
  let C := Finset.univ.filter fun j : Fin (6 * k + 3) => j.val ≠ 0 ∧ j.val % 6 = 4
  have hS : S = A ∪ B ∪ C := by
    ext j
    simp only [S, A, B, C, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjA hjB
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
    omega
  have hABC : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.mpr ?_
    intro j hj hC
    simp only [Finset.mem_union] at hj
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hC
    rcases hj with hjA | hjB
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
      omega
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
      omega
  change S.card = A.card + B.card + C.card
  rw [hS, Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB]
