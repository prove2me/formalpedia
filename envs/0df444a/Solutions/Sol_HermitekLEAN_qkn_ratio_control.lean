-- Prove2me | solution 1 for HermitekLEAN.qkn_ratio_control
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:55.481725+00:00
-- url     : https://prove2.me/submissions/66365574-d801-4f99-bf06-6cc6ca3b9ced

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Gamma
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_qkn_eventual_lower_bound
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
    ∀ {k n d : ℕ},
      n < d →
        ∃ C R0 : ℝ,
          0 < C ∧
            1 ≤ R0 ∧
              ∀ r : ℝ,
                R0 ≤ r →
                  ‖((qkn k n r : ℂ) / (qkn k d r : ℂ))‖ ≤ C / r := by
  intro k n d hnd
  -- Get upper bound on numerator: for large r, ‖qkn(k,n,r)/r^n - cn‖ ≤ 1
  obtain ⟨_, _, hbound_n⟩ := qkn_div_rn_bound k n
  obtain ⟨Rn, hRn1, hRn⟩ := hbound_n 1 one_pos
  -- Get lower bound on denominator: for large r, cd * r^d ≤ ‖qkn(k,d,r)‖
  obtain ⟨Rd, cd, hRd1, hcd, hRd⟩ := qkn_eventual_lower_bound k d
  set cn := 1 / Real.sqrt (Nat.factorial n : ℝ) with hcn_def
  have hcn_pos : 0 < cn := by positivity
  set C := (cn + 1) / cd
  refine ⟨C, max Rn Rd, by positivity, le_max_of_le_left hRn1, fun r hr => ?_⟩
  have hrRn : Rn ≤ r := le_trans (le_max_left _ _) hr
  have hrRd : Rd ≤ r := le_trans (le_max_right _ _) hr
  have hr1 : 1 ≤ r := le_trans hRn1 hrRn
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  -- Upper bound on numerator
  have hnum_spec := hRn r hrRn
  -- ‖qkn(k,n,r)/r^n - cn‖ ≤ 1, so ‖qkn(k,n,r)‖ ≤ (cn + 1) * r^n
  have hnum_upper : ‖(qkn k n r : ℂ)‖ ≤ (cn + 1) * r ^ n := by
    have h1 : ‖(qkn k n r : ℂ) / ((r : ℂ) ^ n)‖ ≤ cn + 1 := by
      have h2 := norm_sub_norm_le ((qkn k n r : ℂ) / ((r : ℂ) ^ n)) ((cn : ℝ) : ℂ)
      rw [Complex.norm_real] at h2
      have : ‖cn‖ = cn := Real.norm_of_nonneg (le_of_lt hcn_pos)
      linarith only [hnum_spec, h2, this]
    rw [norm_div, show ‖((r : ℂ) ^ n)‖ = r ^ n from by
      rw [show (r : ℂ) ^ n = ((r ^ n : ℝ) : ℂ) from by push_cast; ring]
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (le_of_lt hr_pos) n)]] at h1
    rwa [div_le_iff₀ (pow_pos hr_pos n)] at h1
  -- Lower bound on denominator
  have hden_lower : cd * r ^ d ≤ ‖(qkn k d r : ℂ)‖ := hRd r hrRd
  -- qkn k d r ≠ 0 since cd > 0 and r^d > 0
  have hden_ne : (qkn k d r : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden_lower
    linarith only [hcd, hr_pos, hden_lower, mul_pos hcd (pow_pos hr_pos d)]
  -- The ratio bound
  rw [norm_div, div_le_div_iff₀ (norm_pos_iff.mpr hden_ne) hr_pos]
  -- ‖qkn n‖ * r ≤ (cn+1)*r^(n+1) ≤ (cn+1)*r^d = C*cd*r^d ≤ C*‖qkn d‖
  calc ‖(qkn k n r : ℂ)‖ * r
      ≤ (cn + 1) * r ^ n * r := by
          simp_all only [ge_iff_le, norm_real, norm_eq_abs, one_div, ofReal_inv, inv_pos, sqrt_pos,
            Nat.cast_pos, sup_le_iff, and_self, ne_eq, ofReal_eq_zero, mul_le_mul_iff_left₀]
    _ = (cn + 1) * r ^ (n + 1) := by ring
    _ ≤ (cn + 1) * r ^ d := by
          apply mul_le_mul_of_nonneg_left
          · exact pow_le_pow_right₀ hr1 hnd
          · linarith only [hcn_pos]
    _ = C * (cd * r ^ d) := by
          simp only [C]
          field_simp
    _ ≤ C * ‖(qkn k d r : ℂ)‖ := by
          apply mul_le_mul_of_nonneg_left hden_lower
          positivity
end HermitekLEAN
