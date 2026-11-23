-- Prove2me | solution 1 for KhintchineTwoRegime.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:40:29.331659+00:00
-- url     : https://prove2.me/submissions/eda3d58c-d502-41c0-a52f-8fca88ae5976
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_fourProfile
import Definitions.Def_KhintchineTwoRegime_pad
import Theorems.Thm_KhintchineTwoRegime_head_two_average_bound
import Theorems.Thm_KhintchineTwoRegime_fourProfile_attains_bound
import Theorems.Thm_KhintchineTwoRegime_four_regime_uniqueness
import Theorems.Thm_KhintchineTwoRegime_proper_unit_distance_sq

open KhintchineTwoRegime
open HighDimProb.SparseRecovery (l2Norm)

theorem solution :
    (∀ n : ℕ, 2 ≤ n → ∀ τ : ℝ, ∀ ω ∈ Cn n τ,
      1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) ≤ K n ω) ∧
    (∀ n : ℕ, 4 ≤ n → ∀ τ : ℝ, 0 ≤ τ → τ ≤ Real.sqrt (2 - Real.sqrt 2) →
      fourProfile n τ ∈ Cn n τ ∧
      K n (fourProfile n τ) =
        1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) ∧
      ∀ ω ∈ Cn n τ,
        K n ω = 1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) →
          ω = fourProfile n τ) := by
  constructor
  · intro n hn τ ω hω
    have hhead := head_two_average_bound hn ω hω.1
    have hq := proper_unit_distance_sq n hn τ ω hω
    have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsne : Real.sqrt 2 ≠ 0 := by positivity
    have hτ : 0 ≤ τ := by
      rw [← hω.2]
      exact Real.sqrt_nonneg _
    have hunit : ∑ i : Fin n, ω i ^ 2 = 1 := by
      have hnorm := hω.1.2.2
      unfold l2Norm at hnorm
      have hnonneg : 0 ≤ ∑ i : Fin n, ω i ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg (ω i))
      calc
        ∑ i : Fin n, ω i ^ 2 = (Real.sqrt (∑ i : Fin n, ω i ^ 2)) ^ 2 :=
          (Real.sq_sqrt hnonneg).symm
        _ = 1 := by rw [hnorm]; norm_num
    have hsplit : (∑ i : Fin n, ω i ^ 2) =
        pad ω 0 ^ 2 + pad ω 1 ^ 2 +
          ∑ i : Fin n, if 2 ≤ i.val then ω i ^ 2 else 0 := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      simp [Fin.sum_univ_succ, pad]
      ring
    have hc : 0 ≤ ∑ i : Fin n, if 2 ≤ i.val then ω i ^ 2 else 0 := by
      apply Finset.sum_nonneg
      intro i _
      split <;> positivity
    have hqscalar : Real.sqrt 2 * (pad ω 0 + pad ω 1) = 2 - τ ^ 2 := by
      linarith
    have hqsq : 2 * (pad ω 0 + pad ω 1) ^ 2 = (2 - τ ^ 2) ^ 2 := by
      have h := congrArg (fun z : ℝ => z ^ 2) hqscalar
      nlinarith
    have hrad : (pad ω 0 - pad ω 1) ^ 2 +
          (∑ i : Fin n, if 2 ≤ i.val then ω i ^ 2 else 0) =
        τ ^ 2 - τ ^ 4 / 4 + (pad ω 0 - pad ω 1) ^ 2 / 2 := by
      rw [hsplit] at hunit
      nlinarith
    have hsqrt : Real.sqrt (τ ^ 2 - τ ^ 4 / 4) ≤
        Real.sqrt ((pad ω 0 - pad ω 1) ^ 2 +
          ∑ i : Fin n, if 2 ≤ i.val then ω i ^ 2 else 0) := by
      apply Real.sqrt_le_sqrt
      rw [hrad]
      nlinarith [sq_nonneg (pad ω 0 - pad ω 1)]
    have hroot : Real.sqrt (τ ^ 2 - τ ^ 4 / 4) =
        τ * Real.sqrt (1 - τ ^ 2 / 4) := by
      have hfactor : τ ^ 2 - τ ^ 4 / 4 = τ ^ 2 * (1 - τ ^ 2 / 4) := by ring
      rw [hfactor, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq hτ]
    have hident :
        1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) =
          (pad ω 0 + pad ω 1) / 2 +
            Real.sqrt (τ ^ 2 - τ ^ 4 / 4) / (2 * Real.sqrt 2) := by
      have hq' : pad ω 0 + pad ω 1 = (2 - τ ^ 2) / Real.sqrt 2 := by
        apply (eq_div_iff hsne).mpr
        simpa [mul_comm] using hqscalar
      rw [hq', hroot]
      field_simp
      <;> ring
    rw [hident]
    have hsqrt' : Real.sqrt (τ ^ 2 - τ ^ 4 / 4) / (2 * Real.sqrt 2) ≤
        Real.sqrt ((pad ω 0 - pad ω 1) ^ 2 +
          ∑ i : Fin n, if 2 ≤ i.val then ω i ^ 2 else 0) / (2 * Real.sqrt 2) :=
      div_le_div_of_nonneg_right hsqrt (by positivity)
    linarith
  · intro n hn τ hτ₀ hτ₁
    have hattain := fourProfile_attains_bound n hn τ hτ₀ hτ₁
    exact ⟨hattain.1, hattain.2,
      four_regime_uniqueness n hn τ hτ₀ hτ₁⟩
