-- Prove2me | solution 1 for LindbladTolerant.Testing.copy_count_range_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:02:13.327908+00:00
-- url     : https://prove2.me/submissions/3e77f6ec-bc38-4b67-9fbf-345cd7228584

import Definitions.Def_LindbladTolerant_Testing_estimator

set_option autoImplicit false
open scoped ComplexOrder BigOperators
open LindbladTolerant.Testing
noncomputable section

private lemma approximationConstant_nonneg (k : ℕ) : 0 ≤ approximationConstant k := by
  unfold approximationConstant
  have h4 : (1 : ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have hn : 0 ≤ 2 * (16 : ℝ)^k * ((4 : ℝ)^k - 1) := by positivity
  exact div_nonneg hn (Real.exp_pos 1).le

private lemma recordLinear_nonneg (k : ℕ) :
    0 ≤ 32 * (6 : ℝ)^k * ((2 : ℝ)^k - 1) := by
  have h2 : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  positivity

theorem solution :
    ∀ k : ℕ, 1 ≤ k → 1 ≤ copyConstant k ∧
    ∀ n : ℕ, 1 ≤ n → ∀ delta : ℝ, 0 < delta → delta ≤ 1/16 →
      copyCount k delta ≤ ⌈copyConstant k * delta⁻¹^2⌉₊ ∧
      (∀ x : EstimatorSample n k delta,
        0 ≤ estimatorValue k delta x ∧ estimatorValue k delta x ≤ functionalBound k) := by
  intro k hk
  have copyConstant_ge_one : 1 ≤ copyConstant k := by
    let a : ℝ := 2 * approximationConstant k / beta
    let b : ℝ := 32 * (6 : ℝ)^k * ((2 : ℝ)^k - 1) / beta
    let d : ℝ := 8 * (6 : ℝ)^k * (4 : ℝ)^k / Real.sqrt beta
    have ha : 0 ≤ a := by
      exact div_nonneg (mul_nonneg (by norm_num) (approximationConstant_nonneg k))
        (by norm_num [beta])
    have hb : 0 ≤ b := div_nonneg (recordLinear_nonneg k) (by norm_num [beta])
    have hlog : 0 ≤ 16 * Real.log (2 / beta) := by
      have : 0 ≤ Real.log (2 / beta) := Real.log_nonneg (by norm_num [beta])
      positivity
    have hS : 1 ≤ a + 4 + max b (d * (a + 1)) + 16 * Real.log (2 / beta) := by
      have hm : 0 ≤ max b (d * (a + 1)) := le_max_of_le_left hb
      linarith
    exact hS.trans (Nat.le_ceil _)
  refine ⟨copyConstant_ge_one, fun n hn delta hdelta hdelta16 => ?_⟩
  constructor
  · let a : ℝ := 2 * approximationConstant k / beta
    let b : ℝ := 32 * (6 : ℝ)^k * ((2 : ℝ)^k - 1) / beta
    let d : ℝ := 8 * (6 : ℝ)^k * (4 : ℝ)^k / Real.sqrt beta
    have ha : 0 ≤ a := by
      exact div_nonneg (mul_nonneg (by norm_num) (approximationConstant_nonneg k))
        (by norm_num [beta])
    have hb : 0 ≤ b := div_nonneg (recordLinear_nonneg k) (by norm_num [beta])
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hlog : 0 ≤ Real.log (2 / beta) := Real.log_nonneg (by norm_num [beta])
    have hδ1 : delta ≤ 1 := by linarith
    have hi0 : 0 < delta⁻¹ := inv_pos.mpr hdelta
    have hi1 : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).mpr hδ1
    have hiy : delta⁻¹ ≤ delta⁻¹^2 := by
      calc
        delta⁻¹ = delta⁻¹ * 1 := by ring
        _ ≤ delta⁻¹ * delta⁻¹ := mul_le_mul_of_nonneg_left hi1 hi0.le
        _ = delta⁻¹^2 := by ring
    have hy0 : 0 ≤ delta⁻¹^2 := sq_nonneg _
    have hy1 : 1 ≤ delta⁻¹^2 := le_trans hi1 hiy
    have hma : 2 * approximationConstant k / (beta * delta) = a * delta⁻¹ := by
      dsimp [a]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    have hmb : 32 * (6 : ℝ)^k * ((2 : ℝ)^k - 1) / (beta * delta^2) =
        b * delta⁻¹^2 := by
      dsimp [b]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_pow]
      ring
    have hmd : 8 * (6 : ℝ)^k * (4 : ℝ)^k * (discoveryCount k delta : ℝ) /
        (Real.sqrt beta * delta) = d * (discoveryCount k delta : ℝ) * delta⁻¹ := by
      dsimp [d]
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
      ring
    have hm0 : (discoveryCount k delta : ℝ) ≤ a * delta⁻¹ + 1 := by
      rw [discoveryCount, ← hma]
      exact (Nat.ceil_lt_add_one (by
        apply div_nonneg
        · exact mul_nonneg (by norm_num) (approximationConstant_nonneg k)
        · exact mul_nonneg (by norm_num [beta]) hdelta.le)).le
    have hm : (discoveryCount k delta : ℝ) ≤ a * delta⁻¹^2 + 1 := by
      calc
        _ ≤ a * delta⁻¹ + 1 := hm0
        _ ≤ _ := by gcongr
    have hmi : (discoveryCount k delta : ℝ) * delta⁻¹ ≤ (a + 1) * delta⁻¹^2 := by
      calc
        (discoveryCount k delta : ℝ) * delta⁻¹ ≤ (a * delta⁻¹ + 1) * delta⁻¹ := by
          gcongr
        _ = a * delta⁻¹^2 + delta⁻¹ := by rw [inv_pow]; ring
        _ ≤ a * delta⁻¹^2 + delta⁻¹^2 := by gcongr
        _ = (a + 1) * delta⁻¹^2 := by ring
    have hN0 : (recordCount k delta : ℝ) ≤
        max (b * delta⁻¹^2)
          (d * (discoveryCount k delta : ℝ) * delta⁻¹) + 1 := by
      rw [recordCount]
      have hz : 0 ≤ max
          (32 * (6 : ℝ)^k * ((2 : ℝ)^k - 1) / (beta * delta^2))
          (8 * (6 : ℝ)^k * (4 : ℝ)^k * (discoveryCount k delta : ℝ) /
            (Real.sqrt beta * delta)) := by
        apply le_max_of_le_left
        exact div_nonneg (recordLinear_nonneg k)
          (mul_nonneg (by norm_num [beta]) (sq_nonneg delta))
      refine (Nat.ceil_lt_add_one hz).le.trans ?_
      rw [hmb, hmd]
    have hN : (recordCount k delta : ℝ) ≤
        max b (d * (a + 1)) * delta⁻¹^2 + 1 := by
      calc
        _ ≤ max (b * delta⁻¹^2)
            (d * (discoveryCount k delta : ℝ) * delta⁻¹) + 1 := hN0
        _ ≤ _ := by
          gcongr
          apply max_le
          · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hy0
          · calc
              d * (discoveryCount k delta : ℝ) * delta⁻¹ =
                  d * ((discoveryCount k delta : ℝ) * delta⁻¹) := by ring
              _ ≤ d * ((a + 1) * delta⁻¹^2) := by gcongr
              _ = (d * (a + 1)) * delta⁻¹^2 := by ring
              _ ≤ max b (d * (a + 1)) * delta⁻¹^2 := by
                gcongr
                exact le_max_right _ _
    have hs : (swapCount delta : ℝ) ≤ 8 * delta⁻¹^2 * Real.log (2/beta) + 1 := by
      rw [swapCount]
      exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 8 * delta⁻¹^2 *
        Real.log (2/beta))).le
    have htotal : (copyCount k delta : ℝ) ≤ copyConstant k * delta⁻¹^2 := by
      rw [copyCount]
      push_cast
      have hmain : (discoveryCount k delta : ℝ) + (recordCount k delta : ℝ) +
          2 * (swapCount delta : ℝ) ≤
          (a + 4 + max b (d * (a + 1)) + 16 * Real.log (2/beta)) * delta⁻¹^2 := by
        nlinarith [mul_nonneg hlog hy0]
      refine hmain.trans ?_
      rw [copyConstant]
      have hS : a + 4 + max b (d * (a + 1)) + 16 * Real.log (2/beta) ≤
          copyConstant k := Nat.le_ceil _
      exact mul_le_mul_of_nonneg_right hS hy0
    exact_mod_cast htotal.trans (Nat.le_ceil _)
  · intro x
    classical
    have hb : 0 ≤ functionalBound k := by
      unfold functionalBound
      positivity
    unfold estimatorValue
    split_ifs
    · exact ⟨le_rfl, hb⟩
    · exact ⟨le_min hb (le_max_left _ _), min_le_left _ _⟩
