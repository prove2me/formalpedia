-- Prove2me | solution 1 for LassoDantzig.Dantzig.eq_B29
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:59:03.96846+00:00
-- url     : https://prove2.me/submissions/9fb9c4e3-fa93-461d-9125-d3102bc0fcb3

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

theorem aux_b29_tail {M : ℕ} (δ : Fin M → ℝ) (J0 J1 : Finset (Fin M)) (m : ℕ)
    (hJ1 : IsTopBlock δ J0 J1 m) :
    (m : ℝ) * ∑ k ∈ (J0 ∪ J1)ᶜ, δ k ^ 2 ≤ (l1On δ J0ᶜ) ^ 2 := by
  obtain ⟨hsub, hcard, htop⟩ := hJ1
  have hT : (J0 ∪ J1)ᶜ = J0ᶜ \ J1 := by
    ext x; simp [Finset.mem_sdiff, Finset.mem_compl]
  have hk : ∀ k ∈ (J0 ∪ J1)ᶜ, (m : ℝ) * |δ k| ≤ l1On δ J1 := by
    intro k hk
    rw [hT] at hk
    have : ∑ _j ∈ J1, |δ k| ≤ ∑ j ∈ J1, |δ j| := Finset.sum_le_sum (fun j hj => htop j hj k hk)
    simpa [Finset.sum_const, hcard, l1On] using this
  have hdisj : Disjoint J1 (J0 ∪ J1)ᶜ := by
    rw [Finset.disjoint_left]; intro a ha; simp [ha]
  have hunion : J1 ∪ (J0 ∪ J1)ᶜ ⊆ J0ᶜ := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact hsub h
    · simp at h ⊢; exact h.1
  have hA : l1On δ J1 + l1On δ (J0 ∪ J1)ᶜ ≤ l1On δ J0ᶜ := by
    unfold l1On
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hunion (fun _ _ _ => abs_nonneg _)
  have h1 : (m : ℝ) * ∑ k ∈ (J0 ∪ J1)ᶜ, δ k ^ 2 ≤ l1On δ J1 * l1On δ (J0 ∪ J1)ᶜ := by
    rw [Finset.mul_sum]
    rw [show l1On δ (J0 ∪ J1)ᶜ = ∑ k ∈ (J0 ∪ J1)ᶜ, |δ k| from rfl, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hkT
    have e : (m : ℝ) * δ k ^ 2 = ((m : ℝ) * |δ k|) * |δ k| := by
      rw [mul_assoc, ← sq, sq_abs]
    rw [e]
    exact mul_le_mul_of_nonneg_right (hk k hkT) (abs_nonneg _)
  have ha : 0 ≤ l1On δ J1 := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb : 0 ≤ l1On δ (J0 ∪ J1)ᶜ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  nlinarith

end LassoDantzig.Dantzig

open LassoDantzig.Dantzig

theorem solution {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (s m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (hκ : 0 < κ) (hRE : REm X s m 1 κ)
    (J0 J1 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) (hcone : ConeCond 1 J0 δ)
    (hJ1 : IsTopBlock δ J0 J1 m) (r : ℝ) (hr : 0 ≤ r)
    (hB25 : (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ J0) :
    (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ (J0 ∪ J1) ∧
    l2On δ (J0 ∪ J1) ≤ 4 * r * Real.sqrt s / κ ^ 2 ∧
    ∑ j, δ j ^ 2 ≤
      16 * (1 + Real.sqrt ((s : ℝ) / m)) ^ 2 * (r * Real.sqrt s / κ ^ 2) ^ 2 := by
  have hc : 0 ≤ 4 * r * Real.sqrt s := by positivity
  have hS0le : ∑ j ∈ J0, δ j ^ 2 ≤ ∑ j ∈ J0 ∪ J1, δ j ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun _ _ _ => sq_nonneg _)
  have hmono : l2On δ J0 ≤ l2On δ (J0 ∪ J1) := Real.sqrt_le_sqrt hS0le
  have part1 : (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ (J0 ∪ J1) :=
    hB25.trans (mul_le_mul_of_nonneg_left hmono hc)
  set L := l2On δ (J0 ∪ J1) with hLdef
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hLsq : L ^ 2 = ∑ j ∈ J0 ∪ J1, δ j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have part2 : L ≤ 4 * r * Real.sqrt s / κ ^ 2 := by
    by_cases hδ : δ = 0
    · have : L = 0 := by simp [hLdef, l2On, hδ]
      rw [this]; positivity
    · have hre := hRE J0 hJ0 δ hδ hcone J1 hJ1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      set E := ∑ i, X.mulVec δ i ^ 2 with hE
      have hE0 : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have hlhs0 : 0 ≤ κ * Real.sqrt n * L := by positivity
      have hsq : (κ * Real.sqrt n * L) ^ 2 ≤ E := by
        have := pow_le_pow_left₀ hlhs0 hre 2
        rwa [euclNorm, Real.sq_sqrt hE0] at this
      have hsq' : κ ^ 2 * n * L ^ 2 ≤ E := by
        have : (κ * Real.sqrt n * L) ^ 2 = κ ^ 2 * n * L ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le]
        linarith
      have hkey : κ ^ 2 * L ^ 2 ≤ (1 / (n : ℝ)) * E := by
        rw [one_div, le_inv_mul_iff₀ hnpos]
        linarith
      have hk2 : κ ^ 2 * L ^ 2 ≤ 4 * r * Real.sqrt s * L := hkey.trans part1
      rcases hL0.lt_or_eq with hLpos | hLz
      · rw [le_div_iff₀ (by positivity)]
        have : κ ^ 2 * L * L ≤ 4 * r * Real.sqrt s * L := by nlinarith
        have := le_of_mul_le_mul_right this hLpos
        linarith
      · rw [← hLz]; positivity
  refine ⟨part1, part2, ?_⟩
  -- part 3
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have htail := aux_b29_tail δ J0 J1 m hJ1
  have hA : l1On δ J0ᶜ ≤ l1On δ J0 := by simpa [ConeCond] using hcone
  have hA0 : 0 ≤ l1On δ J0ᶜ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hCS : (l1On δ J0) ^ 2 ≤ (s : ℝ) * ∑ j ∈ J0, δ j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := J0) (f := fun j => |δ j|)
    simp only [sq_abs] at h
    have hcard : ((J0.card : ℕ) : ℝ) ≤ s := by exact_mod_cast hJ0
    have hS0 : 0 ≤ ∑ j ∈ J0, δ j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc (l1On δ J0) ^ 2 = (∑ j ∈ J0, |δ j|) ^ 2 := rfl
      _ ≤ (J0.card : ℝ) * ∑ j ∈ J0, δ j ^ 2 := h
      _ ≤ (s : ℝ) * ∑ j ∈ J0, δ j ^ 2 := mul_le_mul_of_nonneg_right hcard hS0
  have hA2 : (l1On δ J0ᶜ) ^ 2 ≤ (s : ℝ) * L ^ 2 := by
    have : (l1On δ J0ᶜ) ^ 2 ≤ (l1On δ J0) ^ 2 := pow_le_pow_left₀ hA0 hA 2
    rw [hLsq]
    have hs0 : (0 : ℝ) ≤ s := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hS0le hs0]
  have hsplit : ∑ j, δ j ^ 2 = ∑ j ∈ J0 ∪ J1, δ j ^ 2 + ∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2 :=
    (Finset.sum_add_sum_compl _ _).symm
  have htail' : ∑ j ∈ (J0 ∪ J1)ᶜ, δ j ^ 2 ≤ ((s : ℝ) / m) * L ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
    linarith
  have htot : ∑ j, δ j ^ 2 ≤ (1 + (s : ℝ) / m) * L ^ 2 := by
    rw [hsplit, ← hLsq]; linarith
  set t := Real.sqrt ((s : ℝ) / m) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t ^ 2 = (s : ℝ) / m := Real.sq_sqrt (by positivity)
  have h1t : (1 + (s : ℝ) / m) ≤ (1 + t) ^ 2 := by nlinarith
  have hL2 : L ^ 2 ≤ (4 * r * Real.sqrt s / κ ^ 2) ^ 2 := pow_le_pow_left₀ hL0 part2 2
  have hfin : (1 + t) ^ 2 * (4 * r * Real.sqrt s / κ ^ 2) ^ 2 =
      16 * (1 + t) ^ 2 * (r * Real.sqrt s / κ ^ 2) ^ 2 := by ring
  rw [← hfin]
  calc ∑ j, δ j ^ 2 ≤ (1 + (s : ℝ) / m) * L ^ 2 := htot
    _ ≤ (1 + t) ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right h1t (sq_nonneg _)
    _ ≤ (1 + t) ^ 2 * (4 * r * Real.sqrt s / κ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (sq_nonneg _)
