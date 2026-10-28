-- Prove2me | solution 1 for InventoryBounds.stationary_value_separation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:21:00.853324+00:00
-- url     : https://prove2.me/submissions/47559489-97c8-4c34-8fc5-c42d0dcdcd5f

import Definitions.Def_InventoryBounds_StationaryValuation
import Mathlib
import Theorems.Thm_InventoryBounds_stationary_value_derivative

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

theorem solution (T : ℕ) (hT : 8 ≤ T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ) / 1024) :
    4 * ε ≤ valueFormula T (rhoPlus T ε) - valueFormula T (rhoMinus T ε) := by
  have ht : (8 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  set δ := 128 * ε / (T : ℝ) ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδt : δ ≤ 1 / (8 * (T : ℝ)) := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by positivity)]
    have : ε * 1024 ≤ T := by linarith [(le_div_iff₀ (by norm_num : (0:ℝ) < 1024)).mp hεT]
    nlinarith
  have hP : rhoPlus T ε = 1 - 1 / (2 * (T : ℝ)) + δ := rfl
  have hM : rhoMinus T ε = 1 - 1 / (2 * (T : ℝ)) - δ := rfl
  have hlt : rhoMinus T ε < rhoPlus T ε := by rw [hP, hM]; linarith
  have hderiv := fun x => InventoryBounds.stationary_value_derivative T x
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (valueFormula T) (valueDerivative T) hlt
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt) (fun x _ => hderiv x)
  have e1 : 1 / (2 * (T : ℝ)) = 4 / (8 * (T : ℝ)) := by field_simp; norm_num
  have e2 : 1 / (8 * (T : ℝ)) = 1 / (8 * (T : ℝ)) := rfl
  have hlo : 1 - 5 / (8 * (T : ℝ)) ≤ c := by
    have : rhoMinus T ε ≥ 1 - 5 / (8 * (T : ℝ)) := by
      rw [hM, e1]
      have : 5 / (8 * (T : ℝ)) = 4 / (8 * (T : ℝ)) + 1 / (8 * (T : ℝ)) := by ring
      linarith
    linarith [hc.1]
  have hhi : c ≤ 1 - 3 / (8 * (T : ℝ)) := by
    have : rhoPlus T ε ≤ 1 - 3 / (8 * (T : ℝ)) := by
      rw [hP, e1]
      have : 3 / (8 * (T : ℝ)) = 4 / (8 * (T : ℝ)) - 1 / (8 * (T : ℝ)) := by ring
      linarith
    linarith [hc.2]
  have hs := S214IBS.sens T hT c hlo hhi
  have hwidth : rhoPlus T ε - rhoMinus T ε = 2 * δ := by rw [hP, hM]; ring
  rw [eq_div_iff (by linarith)] at hcd
  rw [← hcd, hwidth]
  have : (T : ℝ) ^ 2 / 64 * (2 * δ) = 4 * ε := by
    rw [hδdef]; field_simp; ring
  rw [← this]
  exact mul_le_mul_of_nonneg_right hs (by linarith)
