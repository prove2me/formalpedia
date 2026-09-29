-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.shapley_eq_sum_of_unanimity_expansion
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:55:25.914657+00:00
-- url     : https://prove2.me/submissions/a192cd92-b369-47b6-a46b-d28ada7bb250

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Unanimity

namespace MonotonicSolutions.StrongMono

theorem aux_shu_count {α : Type*} [DecidableEq α] (T U : Finset α) (hTU : T ⊆ U)
    (g : ℕ → ℝ) :
    ∑ S ∈ U.powerset, (if T ⊆ S then g S.card else 0) =
      ∑ k ∈ Finset.range ((U \ T).card + 1), ((U \ T).card.choose k : ℝ) * g (T.card + k) := by
  rw [← Finset.sum_filter]
  have hfilt : U.powerset.filter (fun S => T ⊆ S) = (U \ T).powerset.image (T ∪ ·) := by
    rw [← Finset.Icc_eq_filter_powerset, Finset.Icc_eq_image_powerset hTU]
  rw [hfilt, Finset.sum_image]
  · have : ∀ A ∈ (U \ T).powerset, g (T ∪ A).card = g (T.card + A.card) := by
      intro A hA
      rw [Finset.mem_powerset] at hA
      rw [Finset.card_union_of_disjoint]
      exact Finset.disjoint_of_subset_right hA Finset.disjoint_sdiff
    rw [Finset.sum_congr rfl this, Finset.sum_powerset_apply_card (fun k => g (T.card + k))]
    simp [nsmul_eq_mul]
  · intro A hA B hB hAB
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hA hB
    have hA' : Disjoint T A := Finset.disjoint_of_subset_right hA Finset.disjoint_sdiff
    have hB' : Disjoint T B := Finset.disjoint_of_subset_right hB Finset.disjoint_sdiff
    simp only at hAB
    calc A = (T ∪ A) \ T := by rw [Finset.union_sdiff_cancel_left hA']
      _ = (T ∪ B) \ T := by rw [hAB]
      _ = B := by rw [Finset.union_sdiff_cancel_left hB']

theorem aux_shu_nat (m t k : ℕ) (hk : k ≤ m) :
    m.choose k * ((t + k).factorial * (m - k).factorial) =
      m.factorial * t.factorial * (k + t).choose t := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  have h2 := Nat.add_choose_mul_factorial_mul_factorial k t
  rw [add_comm t k, ← h2, ← h1]; ring

theorem aux_shu_real (m t n : ℕ) (hn : n = m + t + 1) :
    ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) *
      (((t + k).factorial * (n - (t + k) - 1).factorial : ℝ) / n.factorial)) =
      1 / ((t : ℝ) + 1) := by
  have hterm : ∀ k ∈ Finset.range (m + 1), ((m.choose k : ℝ) *
      (((t + k).factorial * (n - (t + k) - 1).factorial : ℝ) / n.factorial)) =
      ((m.factorial * t.factorial * (k + t).choose t : ℕ) : ℝ) / n.factorial := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hnk : n - (t + k) - 1 = m - k := by omega
    rw [hnk, ← aux_shu_nat m t k (by omega)]
    push_cast; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← Nat.cast_sum, ← Finset.mul_sum,
    Nat.sum_range_add_choose]
  have hfac := Nat.add_choose_mul_factorial_mul_factorial m (t + 1)
  rw [← add_assoc, ← hn, Nat.factorial_succ] at hfac
  have hn' : (n.factorial : ℝ) =
      ((m + t + 1).choose (t + 1) : ℝ) * m.factorial * ((t + 1) * t.factorial) := by
    rw [← hfac, ← hn]; push_cast; ring
  rw [div_eq_div_iff (by positivity) (by positivity), hn']
  push_cast; ring

theorem aux_shu_unan {n : ℕ} (R : Finset (Fin n)) (hR : R.Nonempty) (i : Fin n) :
    ∑ S ∈ (Finset.univ.erase i).powerset,
      (S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial *
        (unanimity R (insert i S) - unanimity R S) =
      if i ∈ R then 1 / (R.card : ℝ) else 0 := by
  split_ifs with hi
  · have hterm : ∀ S ∈ (Finset.univ.erase i).powerset,
        (S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial *
          (unanimity R (insert i S) - unanimity R S) =
        if R.erase i ⊆ S then
          (S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial else 0 := by
      intro S hS
      rw [Finset.mem_powerset] at hS
      have hiS : i ∉ S := fun h => by simpa using hS h
      have h1 : ¬ R ⊆ S := fun h => hiS (h hi)
      unfold unanimity
      rw [if_neg h1]
      by_cases h2 : R.erase i ⊆ S
      · rw [if_pos h2, if_pos (Finset.subset_insert_iff.mpr h2)]; ring
      · rw [if_neg h2, if_neg (fun h => h2 (Finset.subset_insert_iff.mp h))]; ring
    rw [Finset.sum_congr rfl hterm]
    have hsub : R.erase i ⊆ Finset.univ.erase i :=
      Finset.erase_subset_erase i (Finset.subset_univ R)
    rw [aux_shu_count (R.erase i) (Finset.univ.erase i) hsub
      (fun s => (s.factorial * (n - s - 1).factorial : ℝ) / n.factorial)]
    have hRc : R.card ≤ n := by simpa using Finset.card_le_univ R
    have hR1 : 1 ≤ R.card := Finset.card_pos.mpr hR
    have hTc : (R.erase i).card = R.card - 1 := Finset.card_erase_of_mem hi
    have hUc : (Finset.univ.erase i).card = n - 1 := by simp [Finset.card_erase_of_mem]
    have hm : ((Finset.univ.erase i) \ (R.erase i)).card = n - R.card := by
      rw [Finset.card_sdiff_of_subset hsub, hUc, hTc]; omega
    rw [hm, hTc]
    have key := aux_shu_real (n - R.card) (R.card - 1) n (by omega)
    rw [key]
    congr 1
    push_cast [Nat.cast_sub hR1]; ring
  · apply Finset.sum_eq_zero
    intro S _
    have : unanimity R (insert i S) = unanimity R S := by
      unfold unanimity
      simp only [Finset.subset_insert_iff_of_notMem hi]
    rw [this, sub_self, mul_zero]

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (v : Game n)
    (c : Finset (Fin n) → ℝ)
    (hv : ∀ S : Finset (Fin n),
      v.1 S = ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * unanimity R S)
    (i : Fin n) :
    Supermodularity.Cooperative.ShapleyValue v.1 i =
      ∑ R ∈ Finset.univ.powerset.filter (fun R => i ∈ R), c R / R.card := by
  unfold Supermodularity.Cooperative.ShapleyValue
  simp only [hv]
  have step : ∀ S ∈ (Finset.univ.erase i).powerset,
      (S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial *
        (∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
            c R * unanimity R (insert i S) -
          ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty), c R * unanimity R S) =
      ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
        c R * ((S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial *
          (unanimity R (insert i S) - unanimity R S)) := by
    intro S _
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R _
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  have step2 : ∀ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty),
      ∑ S ∈ (Finset.univ.erase i).powerset,
        c R * ((S.card.factorial * (n - S.card - 1).factorial : ℝ) / n.factorial *
          (unanimity R (insert i S) - unanimity R S)) =
      c R * (if i ∈ R then 1 / (R.card : ℝ) else 0) := by
    intro R hR
    rw [← Finset.mul_sum, aux_shu_unan R (Finset.mem_filter.mp hR).2 i]
  rw [Finset.sum_congr rfl step2, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro R _
  by_cases hi : i ∈ R
  · have hne : R.Nonempty := ⟨i, hi⟩
    simp [hi, hne, div_eq_mul_inv]
  · simp [hi]
