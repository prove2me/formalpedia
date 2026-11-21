-- Prove2me | solution 1 for NymanBeurling.damped_moebius_iterated_tail_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T01:56:11.144621+00:00
-- url     : https://prove2.me/submissions/f299e8b1-0659-428b-a081-57253e9e397e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_damped_moebius_truncation_mean_square_convergence
import Theorems.Thm_NymanBeurling_damped_moebius_limit_profile_tail_tightness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ (H₀ : ℕ) (ε₀ : ℝ), 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
        (∑ n ∈ Finset.Ico H₀ H,
          (1 + ∑ k : Fin N,
            ((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε) *
              (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by
  obtain ⟨H₀, ε₀, hε₀, hhalf, hprofile⟩ :=
    NymanBeurling.damped_moebius_limit_profile_tail_tightness (δ/4) (by positivity)
  refine ⟨H₀, ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨N₀, htrunc⟩ :=
    NymanBeurling.damped_moebius_truncation_mean_square_convergence
      ε hε (hsmall.trans_le hhalf) (δ/4) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hN H
  let error (n : ℕ) : ℝ :=
    (NymanBeurling.dampedResidualFinite N ε (n+1) -
      NymanBeurling.dampedResidualProfile ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ))
  let profile (n : ℕ) : ℝ :=
    (NymanBeurling.dampedResidualProfile ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ))
  have herror (n : ℕ) : 0 ≤ error n := by dsimp [error]; positivity
  have herrorBound : (∑ n ∈ Finset.range H, error n) < δ/4 := htrunc N hN H
  have hprofileBound : (∑ n ∈ Finset.Ico H₀ H, profile n) < δ/4 :=
    hprofile ε hε hsmall H
  have hsub : (∑ n ∈ Finset.Ico H₀ H, error n) ≤ ∑ n ∈ Finset.range H, error n :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by intro n hn; exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2)
      (fun n _ _ => herror n)
  have hpoint (n : ℕ) :
      (NymanBeurling.dampedResidualFinite N ε (n+1))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ)) ≤ 2 * error n + 2 * profile n := by
    dsimp [error, profile]
    calc
      _ ≤ (2 * (NymanBeurling.dampedResidualFinite N ε (n+1) -
          NymanBeurling.dampedResidualProfile ε (n+1))^2 +
          2 * (NymanBeurling.dampedResidualProfile ε (n+1))^2) /
          ((n+1 : ℝ)*(n+2 : ℝ)) :=
        div_le_div_of_nonneg_right
          (by nlinarith [sq_nonneg (NymanBeurling.dampedResidualFinite N ε (n+1) -
            2 * NymanBeurling.dampedResidualProfile ε (n+1))]) (by positivity)
      _ = _ := by ring
  change (∑ n ∈ Finset.Ico H₀ H,
    (NymanBeurling.dampedResidualFinite N ε (n+1))^2 /
      ((n+1 : ℝ)*(n+2 : ℝ))) < δ
  calc
    _ ≤ ∑ n ∈ Finset.Ico H₀ H, (2 * error n + 2 * profile n) :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ = 2 * (∑ n ∈ Finset.Ico H₀ H, error n) +
        2 * (∑ n ∈ Finset.Ico H₀ H, profile n) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ < δ := by linarith
