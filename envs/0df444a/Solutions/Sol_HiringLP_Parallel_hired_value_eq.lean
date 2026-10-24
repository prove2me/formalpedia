-- Prove2me | solution 1 for HiringLP.Parallel.hired_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:20:06.404004+00:00
-- url     : https://prove2.me/submissions/09cb6295-a448-4928-b23d-e0a1b28f249c

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

open HiringLP.Parallel Finset

theorem solution {n k : ℕ} (I : Instance n k) (hI : I.Valid)
    (acc : Fin n → Finset (Fin k) → ℝ) (y : Fin n → Fin k → ℝ) (hy : LPFeasible I y)
    (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ)
    (ord : Fin k → Equiv.Perm (Fin n)) (hord : IsValueOrder I ord) (j : Fin k) :
    Lpos I acc μ ord j = EvD I acc μ j := by
  classical
  unfold Lpos EvD
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  by_cases hY : μ Y = 0
  · simp [hY]
  -- list `j` has at most `T` members
  have hlist : (univ.filter (fun l => (l, j) ∈ Y)).card ≤ I.T := by
    have hc : ⌈∑ i, y i j⌉ ≤ (I.T : ℤ) := by
      rw [Int.ceil_le]; exact_mod_cast hy.1 j
    have hf : ⌊∑ i, y i j⌋ ≤ ⌈∑ i, y i j⌉ := Int.floor_le_ceil _
    have := hμ.degree_right Y hY j
    have h2 : (degRight Y j : ℤ) ≤ (I.T : ℤ) := by
      rcases this with h | h <;> rw [h] <;> omega
    have h3 : degRight Y j ≤ I.T := by exact_mod_cast h2
    have h4 : (univ.filter (fun l => (l, j) ∈ Y)).card = degRight Y j := by
      unfold degRight
      refine Finset.card_bij (fun l _ => (l, j)) ?_ ?_ ?_
      · intro l hl; simp only [mem_filter, mem_univ, true_and] at hl
        simp [hl]
      · intro a _ b _ h; simpa using h
      · intro e he
        simp only [mem_filter] at he
        refine ⟨e.1, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]; rw [← he.2]; exact he.1
        · rw [← he.2]
    omega
  congr 1
  refine Finset.sum_congr rfl (fun A _ => ?_)
  congr 1
  set D := univ.filter (fun i => (i, j) ∈ Y ∧ j ∈ A i) with hD
  by_cases hne : D.Nonempty
  · obtain ⟨i0, hi0D, hmin⟩ := Finset.exists_min_image D (fun i => (ord j).symm i) hne
    have hi0 : (i0, j) ∈ Y ∧ j ∈ A i0 := by simpa [hD] using hi0D
    have hbefore : ∀ l ∈ D, l ≠ i0 → before ord j i0 l := by
      intro l hl hne'
      have := hmin l hl
      show (ord j).symm i0 < (ord j).symm l
      rcases lt_or_eq_of_le this with h | h
      · exact h
      · exact absurd ((ord j).symm.injective h).symm hne'
    have hhired : hired I ord Y A i0 j := by
      refine ⟨hi0.1, hi0.2, ?_, ?_⟩
      · intro l hlY hlb hlA
        have hlD : l ∈ D := by simp [hD, hlY, hlA]
        have := hmin l hlD
        exact absurd hlb (not_lt.mpr this)
      · refine lt_of_lt_of_le (Finset.card_lt_card ?_) hlist
        refine ⟨?_, ?_⟩
        · intro l hl; simp only [mem_filter, mem_univ, true_and] at hl ⊢; exact hl.1
        · intro hsub
          have := hsub (show i0 ∈ univ.filter (fun l => (l, j) ∈ Y) by simp [hi0.1])
          simp at this
    have huniq : ∀ i, hired I ord Y A i j → i = i0 := by
      intro i hi
      by_contra hne'
      have hiD : i ∈ D := by simp [hD, hi.1, hi.2.1]
      exact hi.2.2.1 i0 hi0.1 (hbefore i hiD hne') hi0.2
    rw [Finset.sum_eq_single i0]
    · rw [if_pos hhired]
      unfold vstar
      rw [dif_pos hne]
      refine le_antisymm (Finset.le_sup' (fun i => I.v i j) hi0D) ?_
      refine Finset.sup'_le _ _ (fun l hl => ?_)
      by_cases hl0 : l = i0
      · rw [hl0]
      · exact hord j i0 l (hbefore l hl hl0)
    · intro i _ hi
      rw [if_neg (fun h => hi (huniq i h))]
    · intro h; exact absurd (mem_univ i0) h
  · have hD0 : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold vstar
    rw [dif_neg hne]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg]
    intro hi
    have : i ∈ D := by simp [hD, hi.1, hi.2.1]
    rw [hD0] at this; simp at this
