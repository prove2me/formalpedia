-- Prove2me | solution 1 for MultiSecretary.BR.binomial_overshoot
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:36:50.84182+00:00
-- url     : https://prove2.me/submissions/5e7b250f-4d82-4348-9a82-b6fe3b4598e4

import Mathlib
set_option autoImplicit false

open Finset

noncomputable def msw (p : ℝ) {n : ℕ} (b : Fin n → Bool) : ℝ := ∏ t, if b t = true then p else 1 - p

noncomputable def msc {n : ℕ} (b : Fin n → Bool) : ℝ := ((univ.filter (fun t => b t = true)).card : ℝ)

lemma msc_cons (n : ℕ) (x : Bool) (b : Fin n → Bool) :
    msc (Fin.cons x b : Fin (n+1) → Bool) = (if x = true then 1 else 0) + msc b := by
  unfold msc
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp [Fin.cons_succ]

lemma msw_cons (p : ℝ) (n : ℕ) (x : Bool) (b : Fin n → Bool) :
    msw p (Fin.cons x b : Fin (n+1) → Bool) = (if x = true then p else 1 - p) * msw p b := by
  unfold msw
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_succ]

lemma ms_step (n : ℕ) (p : ℝ) (f : ℝ → ℝ) :
    ∑ b : Fin (n+1) → Bool, msw p b * f (msc b)
    = p * ∑ b : Fin n → Bool, msw p b * f (msc b + 1)
      + (1 - p) * ∑ b : Fin n → Bool, msw p b * f (msc b) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, msc_cons, msw_cons, Finset.mul_sum]
  simp only [if_true, Bool.false_eq_true, if_false, add_zero, mul_assoc, add_comm]

lemma ms_mom (n : ℕ) (p : ℝ) :
    (∑ b : Fin n → Bool, msw p b = 1) ∧
    (∑ b : Fin n → Bool, msw p b * msc b = n * p) ∧
    (∑ b : Fin n → Bool, msw p b * msc b ^ 2 = n * p * (1 - p) + (n * p) ^ 2) := by
  induction n with
  | zero => simp [msw, msc]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have e0 := ms_step n p (fun _ => 1)
    have e1 := ms_step n p (fun x => x)
    have e2 := ms_step n p (fun x => x ^ 2)
    simp only [mul_one] at e0
    have a1 : ∑ b : Fin n → Bool, msw p b * (msc b + 1)
        = ∑ b : Fin n → Bool, msw p b * msc b + ∑ b : Fin n → Bool, msw p b := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun b _ => by ring)
    have a2 : ∑ b : Fin n → Bool, msw p b * (msc b + 1) ^ 2
        = ∑ b : Fin n → Bool, msw p b * msc b ^ 2 + 2 * ∑ b : Fin n → Bool, msw p b * msc b
          + ∑ b : Fin n → Bool, msw p b := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [a1] at e1
    rw [a2] at e2
    refine ⟨?_, ?_, ?_⟩
    · rw [e0, h0]; ring
    · rw [e1, h0, h1]; push_cast; ring
    · rw [e2, h0, h1, h2]; push_cast; ring

lemma ms_pt (y z cc : ℝ) (hcc : 0 < cc) (h : y + cc ≤ z) : max y 0 ≤ z ^ 2 / (4 * cc) := by
  apply max_le
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (z - 2 * cc)]
  · positivity

lemma ms_var (n : ℕ) (p : ℝ) :
    ∑ b : Fin n → Bool, msw p b * (msc b - n * p) ^ 2 = n * p * (1 - p) := by
  obtain ⟨h0, h1, h2⟩ := ms_mom n p
  have : ∑ b : Fin n → Bool, msw p b * (msc b - n * p) ^ 2
      = ∑ b : Fin n → Bool, msw p b * msc b ^ 2 - 2 * (n * p) * ∑ b : Fin n → Bool, msw p b * msc b
        + (n * p) ^ 2 * ∑ b : Fin n → Bool, msw p b := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [this, h0, h1, h2]; ring

lemma ms_bound (n : ℕ) (p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hn : 0 < n)
    (g : (Fin n → Bool) → ℝ) (hg : ∀ b, g b ≤ (msc b - n * p) ^ 2 / (4 * (ε * n))) :
    ∑ b : Fin n → Bool, msw p b * g b ≤ 1 / (4 * ε) := by
  have hw : ∀ b : Fin n → Bool, 0 ≤ msw p b := fun b =>
    Finset.prod_nonneg (fun t _ => by split_ifs <;> linarith)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc ∑ b : Fin n → Bool, msw p b * g b
      ≤ ∑ b : Fin n → Bool, msw p b * ((msc b - n * p) ^ 2 / (4 * (ε * n))) :=
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hg b) (hw b))
    _ = (∑ b : Fin n → Bool, msw p b * (msc b - n * p) ^ 2) / (4 * (ε * n)) := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun b _ => by ring)
    _ = p * (1 - p) / (4 * ε) := by
        rw [ms_var]; field_simp
    _ ≤ 1 / (4 * ε) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg (p - 1/2)]

theorem solution (n k : ℕ) (p ε : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) :
    ((p + ε) * n ≤ k →
      ∑ b : Fin n → Bool, (∏ t, if b t = true then p else 1 - p) *
        max (((univ.filter (fun t => b t = true)).card : ℝ) - k) 0 ≤ 1 / (4 * ε)) ∧
    ((k : ℝ) ≤ (p - ε) * n →
      ∑ b : Fin n → Bool, (∏ t, if b t = true then p else 1 - p) *
        max ((k : ℝ) - (univ.filter (fun t => b t = true)).card) 0 ≤ 1 / (4 * ε)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hpos : 0 ≤ 1 / (4 * ε) := by positivity
    constructor
    · intro _; simpa using hpos
    · intro h
      have : (k : ℝ) = 0 := le_antisymm (by simpa using h) hk
      simp [this]; exact hε.le
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hcc : 0 < ε * n := by positivity
    constructor
    · intro h
      exact ms_bound n p ε hp0 hp1 hε hn _ (fun b => ms_pt _ (msc b - n * p) _ hcc (by
        unfold msc at *; nlinarith))
    · intro h
      exact ms_bound n p ε hp0 hp1 hε hn _ (fun b => by
        have := ms_pt (k - msc b) (-(msc b - n * p)) _ hcc (by nlinarith)
        rw [neg_sq] at this; exact this)
