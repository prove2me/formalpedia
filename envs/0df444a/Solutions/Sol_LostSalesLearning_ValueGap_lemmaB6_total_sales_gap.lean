-- Prove2me | solution 1 for LostSalesLearning.ValueGap.lemmaB6_total_sales_gap
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:43:43.462794+00:00
-- url     : https://prove2.me/submissions/3edac25c-b101-4ff6-80e0-ae075f1b8fd0

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory Finset
open scoped NNReal
open LostSalesLearning.ValueGap

lemma LSx_step_zero {L : ℕ} (hL : 1 ≤ L) (s : Fin (L + 1) → ℝ) (dt : ℝ) :
    step s dt 0 = s 0 - min (s 0) dt + s ⟨1, by omega⟩ := by
  unfold step
  rw [Function.update_self]
  have h0 : (0 : Fin (L + 1)) = Fin.castSucc ⟨0, hL⟩ := by ext; simp
  rw [h0, Fin.snoc_castSucc]
  rfl

lemma LSx_step_mid {L : ℕ} (s : Fin (L + 1) → ℝ) (dt : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hk : k < L) :
    step s dt ⟨k, by omega⟩ = s ⟨k + 1, by omega⟩ := by
  unfold step
  rw [Function.update_of_ne (by
    intro h
    simp only [Fin.ext_iff, Fin.val_zero] at h
    omega)]
  have e : (⟨k, by omega⟩ : Fin (L + 1)) = Fin.castSucc ⟨k, hk⟩ := rfl
  rw [e, Fin.snoc_castSucc]
  rfl

lemma LSx_step_last {L : ℕ} (hL : 1 ≤ L) (s : Fin (L + 1) → ℝ) (dt : ℝ) :
    step s dt ⟨L, by omega⟩ = min (s 0) dt := by
  unfold step
  rw [Function.update_of_ne (by
    intro h
    simp only [Fin.ext_iff, Fin.val_zero] at h
    omega)]
  have e : (⟨L, by omega⟩ : Fin (L + 1)) = Fin.last L := rfl
  rw [e, Fin.snoc_last]

noncomputable def LSx_v {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t k : ℕ) : ℝ :=
  if h : k < L + 1 then traj s d t ⟨k, h⟩ else 0

lemma LSx_v_zero {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    LSx_v s d t 0 = traj s d t 0 := by
  unfold LSx_v
  rw [dif_pos (Nat.succ_pos L)]
  exact congrArg (traj s d t) (Fin.ext (by simp))

lemma LSx_v_succ_zero {L : ℕ} (hL : 1 ≤ L) (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    LSx_v s d (t + 1) 0 = LSx_v s d t 0 - min (LSx_v s d t 0) (d t) + LSx_v s d t 1 := by
  rw [LSx_v_zero, LSx_v_zero, traj_succ, LSx_step_zero hL]
  unfold LSx_v
  rw [dif_pos (by omega)]

lemma LSx_v_succ_mid {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t k : ℕ) (hk1 : 1 ≤ k)
    (hk : k < L) : LSx_v s d (t + 1) k = LSx_v s d t (k + 1) := by
  unfold LSx_v
  rw [dif_pos (by omega), dif_pos (by omega), traj_succ]
  exact LSx_step_mid _ _ k hk1 hk

lemma LSx_v_succ_last {L : ℕ} (hL : 1 ≤ L) (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    LSx_v s d (t + 1) L = min (LSx_v s d t 0) (d t) := by
  rw [LSx_v_zero]
  unfold LSx_v
  rw [dif_pos (by omega), traj_succ]
  exact LSx_step_last hL _ _

lemma LSx_shift {L : ℕ} (hL : 1 ≤ L) (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t i : ℕ) (hi : i < L) :
    ∑ k ∈ Ico (i + 1) (L + 1), LSx_v s d (t + 1) k =
      ∑ k ∈ Ico (i + 2) (L + 1), LSx_v s d t k + min (LSx_v s d t 0) (d t) := by
  rw [Finset.sum_Ico_succ_top (by omega : i + 1 ≤ L), LSx_v_succ_last hL]
  congr 1
  rw [Finset.sum_congr rfl (fun k hk => LSx_v_succ_mid s d t k (by
      have := (Finset.mem_Ico.1 hk).1; omega) (Finset.mem_Ico.1 hk).2)]
  exact Finset.sum_Ico_add' (fun k => LSx_v s d t k) (i + 1) L 1

lemma LSx_v_nonneg0 {L : ℕ} {x : ℝ} (s : Fin (L + 1) → ℝ) (hs : s ∈ Sx L x) (d : ℕ → ℝ≥0) (k : ℕ) :
    0 ≤ LSx_v s d 0 k := by
  unfold LSx_v
  split_ifs
  · exact hs.1 _
  · exact le_refl 0

lemma LSx_sum0 {L : ℕ} {x : ℝ} (s : Fin (L + 1) → ℝ) (hs : s ∈ Sx L x) (d : ℕ → ℝ≥0) :
    ∑ k ∈ range (L + 1), LSx_v s d 0 k = x := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => LSx_v s d 0 k) (L + 1), ← hs.2]
  apply Finset.sum_congr rfl
  intro i _
  unfold LSx_v
  rw [dif_pos i.isLt]
  rfl

lemma LSx_inv {L : ℕ} (hL : 1 ≤ L) {x : ℝ} (s : Fin (L + 1) → ℝ) (hs : s ∈ Sx L x) (d : ℕ → ℝ≥0) :
    ∀ t, LSx_v s d t 0 + ∑ k ∈ Ico 1 (L + 1), LSx_v s d t k = x := by
  intro t
  induction t with
  | zero =>
    rw [← LSx_sum0 s hs d, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < L + 1)]
  | succ t ih =>
    rw [LSx_v_succ_zero hL, LSx_shift hL s d t 0 hL]
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < L + 1)] at ih
    linarith

lemma LSx_sales_succ {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    totalSales s d (t + 1) = totalSales s d t + min (LSx_v s d t 0) (d t) := by
  unfold totalSales sales
  rw [Finset.sum_range_succ, LSx_v_zero]

noncomputable def LSx_W {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t i : ℕ) : ℝ :=
  totalSales s d t - ∑ k ∈ Ico (i + 1) (L + 1), LSx_v s d t k

lemma LSx_W_last {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    LSx_W s d t L = totalSales s d t := by
  unfold LSx_W; simp

lemma LSx_W_succ_lt {L : ℕ} (hL : 1 ≤ L) (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t i : ℕ)
    (hi : i < L) : LSx_W s d (t + 1) i = LSx_W s d t (i + 1) := by
  unfold LSx_W
  rw [LSx_sales_succ, LSx_shift hL s d t i hi]
  ring

lemma LSx_W_succ_last {L : ℕ} (s : Fin (L + 1) → ℝ) (d : ℕ → ℝ≥0) (t : ℕ) :
    LSx_W s d (t + 1) L = totalSales s d t + min (LSx_v s d t 0) (d t) := by
  rw [LSx_W_last, LSx_sales_succ]

lemma LSx_W_zero_eq {L : ℕ} (hL : 1 ≤ L) {x : ℝ} (s : Fin (L + 1) → ℝ) (hs : s ∈ Sx L x)
    (d : ℕ → ℝ≥0) (t : ℕ) : LSx_W s d t 0 = totalSales s d t - x + LSx_v s d t 0 := by
  unfold LSx_W
  have := LSx_inv hL s hs d t
  simp only [zero_add]
  linarith

lemma LSx_key {L : ℕ} (hL : 1 ≤ L) {x : ℝ} (s s' : Fin (L + 1) → ℝ) (hs : s ∈ Sx L x)
    (hs' : s' ∈ Sx L x) (d : ℕ → ℝ≥0) :
    ∀ t, ∀ i ≤ L, LSx_W s' d t i - LSx_W s d t i ≤ x := by
  intro t
  induction t with
  | zero =>
    intro i hi
    unfold LSx_W
    have h1 : ∑ k ∈ Ico (i + 1) (L + 1), LSx_v s d 0 k ≤ x := by
      rw [← LSx_sum0 s hs d, Finset.range_eq_Ico]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (Nat.zero_le _))
        (fun k _ _ => LSx_v_nonneg0 s hs d k)
    have h2 : 0 ≤ ∑ k ∈ Ico (i + 1) (L + 1), LSx_v s' d 0 k :=
      Finset.sum_nonneg (fun k _ => LSx_v_nonneg0 s' hs' d k)
    simp only [totalSales, Finset.range_zero, Finset.sum_empty]
    linarith
  | succ t ih =>
    intro i hi
    rcases Nat.lt_or_ge i L with hlt | hge
    · rw [LSx_W_succ_lt hL s d t i hlt, LSx_W_succ_lt hL s' d t i hlt]
      exact ih (i + 1) hlt
    · have hiL : i = L := le_antisymm hi hge
      subst hiL
      rw [LSx_W_succ_last, LSx_W_succ_last]
      have h0 := ih 0 (Nat.zero_le _)
      have hL' := ih i le_rfl
      rw [LSx_W_zero_eq hL s hs, LSx_W_zero_eq hL s' hs'] at h0
      rw [LSx_W_last, LSx_W_last] at hL'
      rcases min_choice (LSx_v s d t 0) (d t : ℝ) with hm | hm
      · rw [hm]
        have := min_le_left (LSx_v s' d t 0) (d t : ℝ)
        linarith
      · rw [hm]
        have := min_le_right (LSx_v s' d t 0) (d t : ℝ)
        linarith

lemma LSx_x_nonneg {L : ℕ} {x : ℝ} (s : Fin (L + 1) → ℝ) (hs : s ∈ Sx L x) : 0 ≤ x := by
  rw [← hs.2]; exact Finset.sum_nonneg (fun i _ => hs.1 i)

theorem solution {L : ℕ} (hL : 1 ≤ L) (x : ℝ) (s s' : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) (hs' : s' ∈ Sx L x) (hdom : Dominates s' s) (d : ℕ → ℝ≥0)
    (T : ℕ) :
    |totalSales s' d T - totalSales s d T| ≤ 3 * x := by
  have h1 := LSx_key hL s s' hs hs' d T L le_rfl
  have h2 := LSx_key hL s' s hs' hs d T L le_rfl
  rw [LSx_W_last, LSx_W_last] at h1 h2
  have hx := LSx_x_nonneg s hs
  rw [abs_le]
  constructor <;> linarith
