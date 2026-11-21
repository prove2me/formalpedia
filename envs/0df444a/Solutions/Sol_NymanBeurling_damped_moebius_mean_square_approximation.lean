-- Prove2me | solution 1 for NymanBeurling.damped_moebius_mean_square_approximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T01:12:04.880194+00:00
-- url     : https://prove2.me/submissions/e8fead82-1f31-461d-b599-2f573a7611d8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_damped_moebius_finite_head_approximation
import Theorems.Thm_NymanBeurling_damped_moebius_iterated_tail_bound

set_option autoImplicit false
open scoped BigOperators

theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ (N : ℕ) (ε : ℝ), 0 < ε ∧ ε < 1/2 ∧ ∀ H : ℕ,
      (∑ n ∈ Finset.range H,
        (1 + ∑ k : Fin N,
          ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
            (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by
  obtain ⟨H₀, ε₀, hε₀, htail⟩ :=
    NymanBeurling.damped_moebius_iterated_tail_bound (δ/2) (by positivity)
  obtain ⟨ε₁, hε₁, hhead⟩ :=
    NymanBeurling.damped_moebius_finite_head_approximation H₀ (δ/2) (by positivity)
  let ε : ℝ := min (ε₀/2) (min (ε₁/2) (1/4))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεa : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
  have hεb : ε < ε₁ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hεhalf : ε < 1/2 := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨N₀, hN₀⟩ := htail ε hε hεa
  obtain ⟨N₁, hN₁⟩ := hhead ε hε hεb
  let N : ℕ := max N₀ N₁
  let w (n : ℕ) : ℝ :=
    (1 + ∑ k : Fin N,
      ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
        (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
      ((n+1 : ℝ)*(n+2 : ℝ))
  have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have ha : (∑ n ∈ Finset.range H₀, w n) < δ/2 := hN₁ N (le_max_right _ _)
  have hb (H : ℕ) : (∑ n ∈ Finset.Ico H₀ H, w n) < δ/2 := hN₀ N (le_max_left _ _) H
  refine ⟨N, ε, hε, hεhalf, ?_⟩
  intro H
  change (∑ n ∈ Finset.range H, w n) < δ
  by_cases hH : H₀ ≤ H
  · rw [← Finset.sum_range_add_sum_Ico w hH]
    have := hb H
    linarith
  · have hle : (∑ n ∈ Finset.range H, w n) ≤ ∑ n ∈ Finset.range H₀, w n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun n _ _ => hw n)
    linarith
