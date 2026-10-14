-- Prove2me | solution 1 for LambdaCoalescent.Rates.consistent_of_succ
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:43:15.475201+00:00
-- url     : https://prove2.me/submissions/fe383d10-05d7-43f2-a7e8-d2e9964820a4

import Definitions.Def_LambdaCoalescent_Rates_Setting



namespace LambdaCoalescent.Rates

open MeasureTheory

theorem restrictLE_restrictLE' {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) (π : Setoid (Fin c)) :
    restrictLE h1 (restrictLE h2 π) = restrictLE (h1.trans h2) π := by
  ext i j
  exact Iff.rfl

theorem sum_regroup' {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (g : α → β) (f : β → γ) (σ : γ) (w : α → ℝ) :
    (∑ a, if f (g a) = σ then w a else 0) =
      ∑ b, if f b = σ then (∑ a, if g a = b then w a else 0) else 0 := by
  have : ∀ b, (if f b = σ then (∑ a, if g a = b then w a else 0) else 0) =
      ∑ a, (if g a = b then (if f b = σ then w a else 0) else 0) := by
    intro b
    split_ifs with hb
    · refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> rfl
    · symm; refine Finset.sum_eq_zero fun a _ => ?_
      split_ifs <;> rfl
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem consistent_of_succ_core (lam : ℕ → ℕ → ℝ)
    (hsucc : ∀ (n : ℕ) (π : Setoid (Fin (n + 1))) (σ : Setoid (Fin n))
      (t : ℝ), 0 ≤ t →
        (∑ π' : Setoid (Fin (n + 1)),
          if restrictLE (Nat.le_succ n) π' = σ then
            NormedSpace.exp (t • rateMatrix lam (n + 1)) π π' else 0) =
        NormedSpace.exp (t • rateMatrix lam n)
          (restrictLE (Nat.le_succ n) π) σ) :
    Consistent lam := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => intro π σ t ht; exact hsucc n π σ t ht
  | succ m hm ih =>
    intro π σ t ht
    have h1 : n ≤ m := by omega
    have h2 : m ≤ m + 1 := by omega
    have e : ∀ π' : Setoid (Fin (m + 1)),
        restrictLE (Nat.lt_succ_of_lt hm).le π' = restrictLE h1 (restrictLE h2 π') := by
      intro π'; rw [restrictLE_restrictLE']
    simp_rw [e]
    rw [sum_regroup' (restrictLE h2) (restrictLE h1) σ]
    have hs := hsucc m π
    simp_rw [hs _ t ht]
    rw [ih (restrictLE h2 π) σ t ht, restrictLE_restrictLE']

end LambdaCoalescent.Rates

open LambdaCoalescent.Rates


theorem solution (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k)
    (hsucc : ∀ (n : ℕ) (π : Setoid (Fin (n + 1))) (σ : Setoid (Fin n))
      (t : ℝ), 0 ≤ t →
        (∑ π' : Setoid (Fin (n + 1)),
          if restrictLE (Nat.le_succ n) π' = σ then
            NormedSpace.exp (t • rateMatrix lam (n + 1)) π π' else 0) =
        NormedSpace.exp (t • rateMatrix lam n)
          (restrictLE (Nat.le_succ n) π) σ) :
    Consistent lam := by
  exact consistent_of_succ_core lam hsucc
