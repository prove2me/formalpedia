-- Prove2me | solution 1 for MatousekLP.DIntervals.exists_endpoint_in_many
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T05:20:56.707876+00:00
-- url     : https://prove2.me/submissions/0870f09d-e280-4560-b8b6-c80fdf7297f3

import Definitions.Def_MatousekLP_DIntervals_DInterval
import Mathlib

open Finset MatousekLP.DIntervals

namespace DIntCore

variable {d : ℕ}

/-- The left endpoints of a d-interval. -/
noncomputable def lefts (J : DInterval d) : Finset ℝ := Finset.univ.image J.left

lemma lefts_subset (J : DInterval d) : lefts J ⊆ J.endpoints :=
  Finset.subset_union_left

lemma card_lefts_le (J : DInterval d) : (lefts J).card ≤ d := by
  have := Finset.card_image_le (s := (Finset.univ : Finset (Fin d))) (f := J.left)
  simpa [lefts] using this

lemma left_mem (J : DInterval d) (k : Fin d) : J.left k ∈ J.toSet :=
  Set.mem_iUnion.mpr ⟨k, Set.left_mem_Icc.mpr (J.left_le_right k)⟩

/-- Two intersecting d-intervals: a left endpoint of one lies in the other. -/
lemma left_in_other (J J' : DInterval d) (h : (J.toSet ∩ J'.toSet).Nonempty) :
    (∃ p ∈ lefts J, p ∈ J'.toSet) ∨ (∃ p ∈ lefts J', p ∈ J.toSet) := by
  obtain ⟨x, hx, hx'⟩ := h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k', hk'⟩ := Set.mem_iUnion.mp hx'
  rcases le_total (J'.left k') (J.left k) with hle | hle
  · left
    exact ⟨J.left k, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Set.mem_iUnion.mpr ⟨k', hle, hk.1.trans hk'.2⟩⟩
  · right
    exact ⟨J'.left k', Finset.mem_image_of_mem _ (Finset.mem_univ _),
      Set.mem_iUnion.mpr ⟨k, hle, hk'.1.trans hk.2⟩⟩

end DIntCore

open Classical DIntCore in
theorem solution {d n : ℕ} (hd : 1 ≤ d) (hn : 0 < n) (J : Fin n → DInterval d)
    (hJ : ∀ i j, ((J i).toSet ∩ (J j).toSet).Nonempty) :
    ∃ i : Fin n, ∃ p ∈ (J i).endpoints,
      (n : ℝ) / (2 * d) ≤ ((univ.filter fun j => p ∈ (J j).toSet).card : ℝ) := by
  by_contra hcon
  push_neg at hcon
  set c : ℝ → ℝ := fun p => ((univ.filter fun j => p ∈ (J j).toSet).card : ℝ)
  set I : Fin n → Fin n → ℝ := fun i j => if ∃ p ∈ lefts (J i), p ∈ (J j).toSet then 1 else 0
  set S := ∑ i, ∑ j, I i j
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- lower bound: every ordered pair is covered from one side
  have hlow : (n : ℝ) ^ 2 ≤ 2 * S := by
    have hpair : ∀ i j, 1 ≤ I i j + I j i := by
      intro i j
      rcases left_in_other (J i) (J j) (hJ i j) with h | h
      · have : I i j = 1 := if_pos h
        have : 0 ≤ I j i := by simp only [I]; split_ifs <;> norm_num
        linarith
      · have : I j i = 1 := if_pos h
        have : 0 ≤ I i j := by simp only [I]; split_ifs <;> norm_num
        linarith
    have hsym : ∑ i, ∑ j, I j i = S := Finset.sum_comm
    calc (n : ℝ) ^ 2 = ∑ i : Fin n, ∑ j : Fin n, (1 : ℝ) := by simp [sq]
      _ ≤ ∑ i, ∑ j, (I i j + I j i) := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
      _ = 2 * S := by simp only [Finset.sum_add_distrib, hsym]; ring
  -- upper bound: count through left endpoints
  have hup : S < (n : ℝ) ^ 2 / 2 := by
    have hrow : ∀ i, ∑ j, I i j ≤ ∑ p ∈ lefts (J i), c p := by
      intro i
      calc ∑ j, I i j ≤ ∑ j, ∑ p ∈ lefts (J i), (if p ∈ (J j).toSet then (1 : ℝ) else 0) := by
            refine Finset.sum_le_sum fun j _ => ?_
            simp only [I]
            split_ifs with h
            · obtain ⟨p, hp, hpj⟩ := h
              exact (Finset.single_le_sum (f := fun p => if p ∈ (J j).toSet then (1 : ℝ) else 0)
                (fun q _ => by split_ifs <;> norm_num) hp).trans' (by simp [hpj])
            · exact Finset.sum_nonneg fun q _ => by split_ifs <;> norm_num
        _ = ∑ p ∈ lefts (J i), c p := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun p _ => ?_
            simp [c, Finset.sum_boole]
    have hrow' : ∀ i, ∑ p ∈ lefts (J i), c p < (n : ℝ) / 2 := by
      intro i
      have hne : (lefts (J i)).Nonempty := ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hd⟩)⟩
      calc ∑ p ∈ lefts (J i), c p < ∑ p ∈ lefts (J i), (n : ℝ) / (2 * d) :=
            Finset.sum_lt_sum_of_nonempty hne fun p hp => hcon i p (lefts_subset _ hp)
        _ = (lefts (J i)).card * ((n : ℝ) / (2 * d)) := by simp
        _ ≤ d * ((n : ℝ) / (2 * d)) := by
            gcongr; exact_mod_cast card_lefts_le (J i)
        _ = (n : ℝ) / 2 := by field_simp
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    calc S ≤ ∑ i : Fin n, ∑ p ∈ lefts (J i), c p := Finset.sum_le_sum fun i _ => hrow i
      _ < ∑ i : Fin n, (n : ℝ) / 2 := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hrow' i
      _ = (n : ℝ) ^ 2 / 2 := by simp; ring
  linarith
