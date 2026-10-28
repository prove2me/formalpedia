-- Prove2me | solution 1 for InventoryBounds.stationary_value_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:19:35.158997+00:00
-- url     : https://prove2.me/submissions/f581281a-d7c1-45e0-9acc-e68e81958cd5

import Definitions.Def_InventoryBounds_StationaryValuation
import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open InventoryBounds

namespace S214IBS

lemma sens (T : ℕ) (hT : 8 ≤ T) (ρ : ℝ)
    (hlo : 1 - 5 / (8 * (T : ℝ)) ≤ ρ)
    (hhi : ρ ≤ 1 - 3 / (8 * (T : ℝ))) :
    (T : ℝ) ^ 2 / 64 ≤ valueDerivative T ρ := by
  have ht : (8 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  have h5 : 5 / (8 * (T : ℝ)) ≤ 5 / 64 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hρ1 : ρ ≤ 1 := by
    have : 0 ≤ 3 / (8 * (T : ℝ)) := by positivity
    linarith
  have hpow : ∀ k : ℕ, k ≤ T → (3 / 8 : ℝ) ≤ ρ ^ k := by
    intro k hk
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ ρ - 1 by linarith) k
    have hk' : (k : ℝ) ≤ T := by exact_mod_cast hk
    have e : (T : ℝ) * (5 / (8 * (T : ℝ))) = 5 / 8 := by field_simp
    have : (k : ℝ) * (ρ - 1) ≥ -(5 / 8) := by
      have h1 : 0 ≤ 1 - ρ := by linarith
      have : (k : ℝ) * (1 - ρ) ≤ T * (5 / (8 * (T : ℝ))) := by
        apply mul_le_mul hk' (by linarith) h1 ht0.le
      nlinarith
    simp only [add_sub_cancel] at hb
    linarith
  have hS : (3 / 8 : ℝ) * T ≤ ∑ k ∈ Finset.range T, ρ ^ k := by
    calc (3 / 8 : ℝ) * T = ∑ k ∈ Finset.range T, (3 / 8 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun k hk => hpow k (Finset.mem_range.mp hk).le
  have hid : (∑ k ∈ Finset.range T, (k : ℝ)) * 2 = T * (T - 1) := by
    have := Finset.sum_range_id_mul_two T
    have h' : ((∑ i ∈ Finset.range T, i : ℕ) : ℝ) * 2 = ((T * (T - 1) : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_sum] at h'
    exact h'
  have hS' : (3 / 8 : ℝ) * ∑ k ∈ Finset.range T, (k : ℝ) ≤
      ∑ k ∈ Finset.range T, (k : ℝ) * ρ ^ (k - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have := hpow (k - 1) (by have := Finset.mem_range.mp hk; omega)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h2ρ : (27 / 32 : ℝ) ≤ 2 * ρ - 1 := by linarith
  unfold valueDerivative
  have hS'0 : 0 ≤ ∑ k ∈ Finset.range T, (k : ℝ) * ρ ^ (k - 1) := by
    have : (0 : ℝ) ≤ ∑ k ∈ Finset.range T, (k : ℝ) :=
      Finset.sum_nonneg fun k _ => Nat.cast_nonneg k
    linarith
  have hprod : (27 / 32 : ℝ) * ∑ k ∈ Finset.range T, (k : ℝ) * ρ ^ (k - 1) ≤
      (2 * ρ - 1) * ∑ k ∈ Finset.range T, (k : ℝ) * ρ ^ (k - 1) :=
    mul_le_mul_of_nonneg_right h2ρ hS'0
  nlinarith

end S214IBS

theorem solution (T : ℕ) (hT : 8 ≤ T) (ρ : ℝ)
    (hlo : 1 - 5 / (8 * (T : ℝ)) ≤ ρ)
    (hhi : ρ ≤ 1 - 3 / (8 * (T : ℝ))) :
    (T : ℝ) ^ 2 / 64 ≤ valueDerivative T ρ :=
  S214IBS.sens T hT ρ hlo hhi
