-- Prove2me | solution 1 for HermitekLEAN.qkn_top_term_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:11:17.744055+00:00
-- url     : https://prove2.me/submissions/84453a61-9092-4696-b809-a291eabbcb25

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.qkn_real
section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
namespace HermitekLEAN
private lemma zpow_neg_two_eq (r : ℝ) :
    r ^ (-2 : ℤ) = 1 / r ^ 2 := by
  have : r ^ (-2 : ℤ) = (r ^ (2 : ℕ))⁻¹ := by rw [zpow_neg]; rfl
  rw [this, inv_eq_one_div]
private lemma zpow_sub_mul {r : ℝ} (hr : r ≠ 0) (a b : ℤ) :
    r ^ a = r ^ b * r ^ (a - b) := by
  rw [← zpow_add₀ hr b (a - b), show b + (a - b) = a from by omega]
private lemma qkn_div_rn_bound (k n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ε : ℝ), 0 < ε →
      ∃ R0 : ℝ, 1 ≤ R0 ∧ ∀ r : ℝ, R0 ≤ r →
        ‖(qkn k n r : ℂ) / ((r : ℂ) ^ n) -
          ((1 / Real.sqrt (Nat.factorial n : ℝ) : ℝ) : ℂ)‖ ≤ ε := by
  set c := 1 / Real.sqrt (Nat.factorial n : ℝ) with hc_def
  have hc_pos : 0 < c := by positivity
  set M := c * ∑ j ∈ Finset.range (min k n + 1), (Nat.choose k j : ℝ) *
    ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) with hM_def
  have hM_nn : 0 ≤ M := by
    apply mul_nonneg (le_of_lt hc_pos)
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine ⟨M, hM_nn, fun ε hε => ?_⟩
  refine ⟨max (Real.sqrt (M / ε) + 1) 1, le_max_right _ _, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hrn_pos : 0 < r ^ n := pow_pos hr_pos n
  rw [show (qkn k n r : ℂ) / ((r : ℂ) ^ n) - ((c : ℝ) : ℂ) =
    ((qkn k n r / r ^ n - c : ℝ) : ℂ) from by push_cast; ring]
  rw [Complex.norm_real]
  have hqkn : qkn k n r / r ^ n = c *
      ∑ j ∈ Finset.range (min k n + 1),
        ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
          ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
          r ^ (((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ)) := by
    unfold qkn
    rw [mul_div_assoc, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have : r ^ ((n : ℤ) - 2 * (j : ℤ)) / r ^ n =
        r ^ (((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ)) := by
      rw [zpow_sub_mul (ne_of_gt hr_pos) ((n : ℤ) - 2 * (j : ℤ)) (n : ℤ), zpow_natCast]
      exact mul_div_cancel_left₀ _ (pow_ne_zero n (ne_of_gt hr_pos))
    rw [mul_div_assoc, this]
  set S := fun j => ((-1 : ℝ) ^ j) * (Nat.choose k j : ℝ) *
      ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
      r ^ (((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ)) with hS_def
  have h0_in : 0 ∈ Finset.range (min k n + 1) := Finset.mem_range.mpr (by omega)
  have hS0 : S 0 = 1 := by simp [hS_def, Nat.factorial_ne_zero]
  have hdiff : qkn k n r / r ^ n - c = c *
      (∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j) := by
    rw [hqkn]
    rw [show ∑ j ∈ Finset.range (min k n + 1), S j =
      S 0 + ∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j from
        (Finset.add_sum_erase _ S h0_in).symm]
    rw [hS0, mul_add, mul_one]
    ring
  have htail_bound : |∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j| ≤
      (∑ j ∈ Finset.range (min k n + 1), (Nat.choose k j : ℝ) *
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) / r ^ 2 := by
    calc |∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j|
        ≤ ∑ j ∈ (Finset.range (min k n + 1)).erase 0, |S j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ (Finset.range (min k n + 1)).erase 0,
            ((Nat.choose k j : ℝ) *
              ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) /
                r ^ 2) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj_pos : 1 ≤ j := by
            rw [Finset.mem_erase] at hj
            omega
          rw [hS_def]
          simp only []
          rw [abs_mul, abs_mul, abs_mul]
          calc |(-1 : ℝ) ^ j| * |(Nat.choose k j : ℝ)| *
                |(Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)| *
                |r ^ (((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ))|
              = (Nat.choose k j : ℝ) * ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
                |r ^ ((-2 : ℤ) * (j : ℤ))| := by
                rw [show ((n : ℤ) - 2 * (j : ℤ)) - (n : ℤ) = (-2 : ℤ) * (j : ℤ) from by omega,
                  abs_pow, abs_neg, abs_one, one_pow, one_mul,
                  abs_of_nonneg (Nat.cast_nonneg _),
                  abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
            _ ≤ (Nat.choose k j : ℝ) * ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
                |r ^ ((-2 : ℤ))| := by
                apply mul_le_mul_of_nonneg_left
                · rw [abs_zpow, abs_of_pos hr_pos, abs_zpow, abs_of_pos hr_pos]
                  apply zpow_le_zpow_right₀ hr1
                  omega
                · apply mul_nonneg (Nat.cast_nonneg _)
                    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            _ = (Nat.choose k j : ℝ) *
                ((Nat.factorial n : ℝ) /
                  (Nat.factorial (n - j) : ℝ)) / r ^ 2 := by
                rw [zpow_neg_two_eq, abs_of_nonneg (by positivity)]
                ring
      _ ≤ (∑ j ∈ Finset.range (min k n + 1), (Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) / r ^ 2 := by
          rw [Finset.sum_div]
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          intro j _ _
          apply div_nonneg
          · exact mul_nonneg (Nat.cast_nonneg _)
              (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          · positivity
  rw [hdiff, Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt hc_pos)]
  calc c * |∑ j ∈ (Finset.range (min k n + 1)).erase 0, S j|
      ≤ c * ((∑ j ∈ Finset.range (min k n + 1), (Nat.choose k j : ℝ) *
            ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))) / r ^ 2) :=
        mul_le_mul_of_nonneg_left htail_bound (le_of_lt hc_pos)
    _ = M / r ^ 2 := by ring
    _ ≤ ε := by
        rw [div_le_iff₀ (pow_pos hr_pos 2)]
        by_cases hM0 : M = 0
        · rw [hM0]; positivity
        · have hMpos : 0 < M := lt_of_le_of_ne hM_nn (Ne.symm hM0)
          have hge : r ≥ Real.sqrt (M / ε) + 1 := le_trans (le_max_left _ _) hr
          have hr_sq : r ^ 2 ≥ M / ε := by
            have : r ≥ Real.sqrt (M / ε) := by linarith only [hge]
            calc r ^ 2 = r * r := by ring
              _ ≥ Real.sqrt (M / ε) * Real.sqrt (M / ε) := by
                  apply mul_le_mul this this
                  · exact Real.sqrt_nonneg _
                  · linarith only [hr1]
              _ = M / ε := by rw [Real.mul_self_sqrt (le_of_lt (div_pos hMpos hε))]
          have : ε * r ^ 2 ≥ ε * (M / ε) :=
            mul_le_mul_of_nonneg_left hr_sq (le_of_lt hε)
          rw [mul_div_cancel₀ M (ne_of_gt hε)] at this
          linarith only [this]
end HermitekLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ k n : ℕ,
      ∃ c : ℝ,
        c ≠ 0 ∧
          ∀ ε : ℝ,
            0 < ε →
              ∃ R0 : ℝ,
                ∀ r ≥ R0, ‖(qkn k n r : ℂ) / (r ^ n : ℂ) - (c : ℂ)‖ ≤ ε := by
  intro k n
  refine ⟨1 / Real.sqrt (Nat.factorial n : ℝ), by positivity, ?_⟩
  intro ε hε
  obtain ⟨_, _, hbound⟩ := qkn_div_rn_bound k n
  obtain ⟨R₀, _, hR₀⟩ := hbound ε hε
  exact ⟨R₀, fun r hr => hR₀ r hr⟩
end HermitekLEAN
