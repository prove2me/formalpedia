-- Prove2me | solution 1 for MLRPCake.EnvyFree.coalesce_envy_free
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:51:33.571332+00:00
-- url     : https://prove2.me/submissions/a446f4be-2140-44e5-8d93-e0bc2211df9d

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Theorems.Thm_MLRPCake_EnvyFree_theorem_6

open MLRPCake.EnvyFree MeasureTheory

namespace MLRPCoalesceAux

lemma dens_eq {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (hk : k < n) : dens f k = f ⟨k, hk⟩ := by
  simp [dens, hk]

lemma integrable_sub {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (k : ℕ) (hk : k < n)
    (a b : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1) :
    IntervalIntegrable (dens f k) volume a b := by
  rw [dens_eq f k hk]
  apply (hf ⟨k, hk⟩).2.2.1.mono_set
  rw [Set.uIcc_of_le zero_le_one]
  intro u hu
  rcases le_total a b with h | h
  · rw [Set.uIcc_of_le h] at hu; exact ⟨le_trans ha.1 hu.1, le_trans hu.2 hb.2⟩
  · rw [Set.uIcc_of_ge h] at hu; exact ⟨le_trans hb.1 hu.1, le_trans hu.2 ha.2⟩

lemma val_nonneg {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (k : ℕ) (hk : k < n)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : 0 ≤ val f k a b := by
  unfold val
  rw [dens_eq f k hk]
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  exact (hf ⟨k, hk⟩).1 u ⟨le_trans ha hu.1, le_trans hu.2 hb⟩

lemma val_add {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (k : ℕ) (hk : k < n)
    (a b c : ℝ) (ha : a ∈ Set.Icc (0:ℝ) 1) (hb : b ∈ Set.Icc (0:ℝ) 1)
    (hc : c ∈ Set.Icc (0:ℝ) 1) : val f k a b + val f k b c = val f k a c := by
  unfold val
  exact intervalIntegral.integral_add_adjacent_intervals (integrable_sub f hf k hk a b ha hb)
    (integrable_sub f hf k hk b c hb hc)

lemma eval_eq_val {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (a b : ℝ) (hab : a ≤ b) :
    eval f k a b = val f k a b := by
  unfold eval val
  rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

lemma eval_self {n : ℕ} (f : Fin n → ℝ → ℝ) (k : ℕ) (a : ℝ) : eval f k a a = 0 := by
  rw [eval_eq_val f k a a le_rfl]
  simp [val]

end MLRPCoalesceAux

open MLRPCoalesceAux

theorem solution (n : ℕ) (f : Fin n → ℝ → ℝ) (lam η : ℝ) (x : ℕ → ℝ) (hn : 1 ≤ n)
    (hf : IsInstance f) (hmlrp : IsMLRP f) (hlam : 1 ≤ lam) (hL : QueriesLipschitz f lam)
    (hη : 0 < η) (hx : IsRipple f (η / lam) x) :
    IsAllocation (n := n) (coalesce n x) ∧ EnvyFreeUpTo f η (coalesce n x) := by
  have hEF := MLRPCake.EnvyFree.theorem_6 n f (η / lam) x hf hmlrp
    (div_nonneg hη.le (by linarith)) hx
  obtain ⟨hx0, hmono, hxn, hxnl, _⟩ := hx
  have hbd : ∀ k, k ≤ n → 0 ≤ x k ∧ x k ≤ x n := by
    have h1 : ∀ k, k ≤ n → 0 ≤ x k := by
      intro k
      induction k with
      | zero => intro _; rw [hx0]
      | succ k ih => intro hk; exact le_trans (ih (by omega)) (hmono k (by omega))
    have h2 : ∀ m k, k + m = n → x k ≤ x n := by
      intro m
      induction m with
      | zero => intro k hk; simp at hk; subst hk; exact le_refl _
      | succ m ih =>
        intro k hk
        exact le_trans (hmono k (by omega)) (ih (k + 1) (by omega))
    intro k hk
    exact ⟨h1 k hk, h2 (n - k) k (by omega)⟩
  have hin : ∀ k, k ≤ n → x k ∈ Set.Icc (0:ℝ) 1 := fun k hk =>
    ⟨(hbd k hk).1, le_trans (hbd k hk).2 hxn⟩
  have h1in : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc : ∀ k, k ≠ n → coalesce n x k = x k := by
    intro k hk; simp [coalesce, hk]
  have hcn : coalesce n x n = 1 := by simp [coalesce]
  -- the leftover piece is worth at most η to everybody
  have htail : ∀ i, i < n → val f i (x n) 1 ≤ η := by
    intro i hi
    have hlip := (hL ⟨i, hi⟩).1 (x n) 1 1 1 (hin n le_rfl) h1in h1in h1in
    simp only [Fin.val_mk] at hlip
    rw [eval_self, eval_eq_val f i (x n) 1 hxn] at hlip
    have hlam0 : 0 < lam := by linarith
    have hmax : max |1 - x n| |(1:ℝ) - 1| = 1 - x n := by
      rw [sub_self, abs_zero, abs_of_nonneg (by linarith)]
      exact max_eq_left (by linarith)
    rw [hmax] at hlip
    have h2 : lam * (1 - x n) ≤ η := by
      have : 1 - x n ≤ η / lam := by linarith
      calc lam * (1 - x n) ≤ lam * (η / lam) := by gcongr
        _ = η := by field_simp
    have := le_abs_self (0 - val f i (x n) 1)
    have := neg_abs_le (0 - val f i (x n) 1)
    linarith
  refine ⟨⟨?_, ?_, hcn⟩, ?_⟩
  · rw [hc 0 (by omega), hx0]
  · intro k hk
    rw [hc k (by omega)]
    by_cases hk1 : k + 1 = n
    · rw [hk1, hcn]; exact (hin k (by omega)).2
    · rw [hc (k + 1) hk1]; exact hmono k hk
  · intro i j hi hj
    rw [hc j (by omega), hc i (by omega)]
    -- own piece only grows
    have hown : val f i (x i) (x (i + 1)) ≤ val f i (x i) (coalesce n x (i + 1)) := by
      by_cases hi1 : i + 1 = n
      · rw [hi1, hcn, ← val_add f hf i hi (x i) (x n) 1 (hin i (by omega)) (hin n le_rfl) h1in]
        have := val_nonneg f hf i hi (x n) 1 (hin n le_rfl).1 hxn le_rfl
        linarith
      · rw [hc (i + 1) hi1]
    have hE := hEF i j hi hj
    by_cases hj1 : j + 1 = n
    · rw [hj1, hcn, ← val_add f hf i hi (x j) (x n) 1 (hin j (by omega)) (hin n le_rfl) h1in]
      rw [hj1] at hE
      have := htail i hi
      linarith
    · rw [hc (j + 1) hj1]
      linarith
