-- Prove2me | solution 1 for IgnallSchrage.Invariance.sumCompletion_shift
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:05:47.116834+00:00
-- url     : https://prove2.me/submissions/ff2d5353-d030-40d4-841b-416a8edb557d

import Mathlib
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine
open IgnallSchrage.Invariance JohnsonFlowShop.TwoStage

private theorem shift_completion {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (G : ℝ) (hG : 0 ≤ G) (σ : Equiv.Perm (Fin n)) :
    ∀ m, 0 < m → m ≤ n →
    asapC2 (fun i => a i+G) (fun i => b i+G) σ m =
      asapC2 a b σ m + G*(m+1) := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
    intro hm hn
    have hmn : m < n := by omega
    simp only [asapC2, dif_pos hmn]
    have hs : (∑ l ∈ Finset.Iic (⟨m,hmn⟩ : Fin n), (a (σ l)+G)) =
        (∑ l ∈ Finset.Iic (⟨m,hmn⟩ : Fin n), a (σ l)) + G*(m+1) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
      push_cast
      ring
    rw [hs]
    by_cases hz : m=0
    · subst m
      simp only [asapC2]
      have hsum : 0 ≤ ∑ l ∈ Finset.Iic (⟨0,hmn⟩ : Fin n), a (σ l) :=
        Finset.sum_nonneg (fun i hi => ha _)
      rw [max_eq_left hsum, max_eq_left (by positivity)]
      norm_num
      ring
    · rw [ih (by omega) (by omega), max_add_add_right]
      push_cast
      ring

private theorem sum_positions (n : ℕ) :
    (∑ k : Fin n, ((k.val : ℝ)+2)) = (n:ℝ)*(n+3)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

theorem solution {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) :
    sumCompletion (fun i => a i + G) (fun i => b i + G) σ =
      sumCompletion a b σ + G * n * (n + 3) / 2 := by
  unfold sumCompletion
  have he : (∑ k : Fin n, asapC2 (fun i => a i+G) (fun i => b i+G) σ (k.val+1)) =
      ∑ k : Fin n, (asapC2 a b σ (k.val+1) + G*((k.val:ℝ)+2)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [shift_completion a b ha G hG.le σ (k.val+1) (by omega) (by omega)]
    push_cast
    ring
  rw [he, Finset.sum_add_distrib, ← Finset.mul_sum, sum_positions]
  ring

#print axioms solution
