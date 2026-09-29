-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_mode_row_multinomial_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:10:49.783788+00:00
-- url     : https://prove2.me/submissions/f525dfc4-e97d-4a28-a49f-5bc97edd644e

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_fixed_outer_profile_arithmetic
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_target_joint_table_marginal
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_mode_conditional_entropy_maximal
import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MME.StothersFourth

private theorem fixedHashRowReduction_marginal_count_sum (m : ℕ) :
    ∑ j : Fin 9, fixedMarginalCount m j = fixedOuterLength m := by
  simp only [fixedMarginalCount]
  rw [← Finset.mul_sum,
    mme_stothers_fixed_outer_profile_arithmetic.2.2.2.2.1]
  simp only [fixedOuterLength]
  ac_rfl

private theorem fixedHashRowReduction_marginal_count_pos
    (m : ℕ) (hm : 0 < m) (j : Fin 9) :
    0 < fixedMarginalCount m j := by
  exact Nat.mul_pos hm (by
    fin_cases j <;> norm_num [fixedMarginalBaseCount])

private theorem fixedHashRowReduction_marginal_count_le_length
    (m : ℕ) (j : Fin 9) :
    fixedMarginalCount m j ≤ fixedOuterLength m := by
  rw [← fixedHashRowReduction_marginal_count_sum m]
  exact Finset.single_le_sum (fun r _ ↦ Nat.zero_le _)
    (Finset.mem_univ j)

private theorem fixedHashRowReduction_card_sum (i : Fin 3) :
    ∑ j : Fin 9,
        Fintype.card {sigma : FixedHashSupportTriple // sigma.1 i = j} =
      45 := by
  calc
    (∑ j : Fin 9,
        Fintype.card {sigma : FixedHashSupportTriple // sigma.1 i = j}) =
        Fintype.card
          (Sigma fun j : Fin 9 ↦
            {sigma : FixedHashSupportTriple // sigma.1 i = j}) := by
      exact (Fintype.card_sigma).symm
    _ = Fintype.card FixedHashSupportTriple :=
      Fintype.card_congr
        (Equiv.sigmaFiberEquiv
          (fun sigma : FixedHashSupportTriple ↦ sigma.1 i))
    _ = 45 := by decide

end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (m : ℕ) (hm : 0 < m) (i : Fin 3)
    (k : FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : FixedHashSupportTriple // sigma.1 l = j},
        k sigma.1) = fixedMarginalCount m j) :
    (∏ j : Fin 9,
        (Nat.multinomial Finset.univ
          (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1) : ℝ)) ≤
      (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 45 *
        ∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
              fixedHashTargetJointTable m sigma.1) : ℝ) := by
  classical
  let candidateExponent : Fin 9 → ℝ := fun j ↦
    (fixedMarginalCount m j : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
          (k sigma.1 : ℝ) / (fixedMarginalCount m j : ℝ))
  let targetExponent : Fin 9 → ℝ := fun j ↦
    (fixedMarginalCount m j : ℝ) * Real.log 2 *
      mme_modern_entropyBits
        (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
          (fixedHashTargetJointTable m sigma.1 : ℝ) /
            (fixedMarginalCount m j : ℝ))
  let rowPolynomial : Fin 9 → ℝ := fun j ↦
    (6 * (((fixedMarginalCount m j + 1 : ℕ) : ℝ))) ^
      Fintype.card {sigma : FixedHashSupportTriple // sigma.1 i = j}
  have hcandidateUpper (j : Fin 9) :
      (Nat.multinomial Finset.univ
          (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1) : ℝ) ≤
        Real.exp (candidateExponent j) := by
    have hrowPos :
        0 < ∑ sigma :
          {sigma : FixedHashSupportTriple // sigma.1 i = j},
            k sigma.1 := by
      rw [hkMarginal i j]
      exact fixedHashRowReduction_marginal_count_pos m hm j
    have h := mme_dwz_multinomial_entropy_upper
      (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
        k sigma.1) 1 (by decide) hrowPos
    rw [hkMarginal i j] at h
    simpa only [Nat.mul_one, Nat.cast_one, one_mul, candidateExponent] using h
  have htargetLower (j : Fin 9) :
      Real.exp (targetExponent j) ≤
        rowPolynomial j *
          (Nat.multinomial Finset.univ
            (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
              fixedHashTargetJointTable m sigma.1) : ℝ) := by
    have hrowPos :
        0 < ∑ sigma :
          {sigma : FixedHashSupportTriple // sigma.1 i = j},
            fixedHashTargetJointTable m sigma.1 := by
      rw [mme_stothers_fixed_target_joint_table_marginal m i j]
      exact fixedHashRowReduction_marginal_count_pos m hm j
    have h := mme_dwz_multinomial_entropy_polynomial_lower
      (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
        fixedHashTargetJointTable m sigma.1) 1 (by decide) hrowPos
    rw [mme_stothers_fixed_target_joint_table_marginal m i j] at h
    simpa only [Nat.mul_one, Nat.cast_one, one_mul, targetExponent,
      rowPolynomial] using h
  have hconditional :=
    mme_stothers_fixed_mode_conditional_entropy_maximal
      m hm i k hkMarginal
  have hlogNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hconditionalLog :=
    mul_le_mul_of_nonneg_right hconditional hlogNonneg
  have hcandidateExponentSum :
      (∑ j : Fin 9,
        (fixedMarginalCount m j : ℝ) *
          mme_modern_entropyBits
            (fun sigma :
              {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
                (k sigma.1 : ℝ) /
                  (fixedMarginalCount m j : ℝ))) * Real.log 2 =
        ∑ j, candidateExponent j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [candidateExponent]
    ring
  have htargetExponentSum :
      (∑ j : Fin 9,
        (fixedMarginalCount m j : ℝ) *
          mme_modern_entropyBits
            (fun sigma :
              {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
                (fixedHashTargetJointTable m sigma.1 : ℝ) /
                  (fixedMarginalCount m j : ℝ))) * Real.log 2 =
        ∑ j, targetExponent j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [targetExponent]
    ring
  rw [hcandidateExponentSum, htargetExponentSum] at hconditionalLog
  have hproductCandidate :
      (∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
                k sigma.1) : ℝ)) ≤
        Real.exp (∑ j, candidateExponent j) := by
    calc
      (∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
                k sigma.1) : ℝ)) ≤
          ∏ j : Fin 9, Real.exp (candidateExponent j) := by
        apply Finset.prod_le_prod
        · intro j _
          positivity
        · intro j _
          exact hcandidateUpper j
      _ = Real.exp (∑ j, candidateExponent j) :=
        (Real.exp_sum Finset.univ candidateExponent).symm
  have hproductTarget :
      Real.exp (∑ j, targetExponent j) ≤
        ∏ j : Fin 9,
          rowPolynomial j *
            (Nat.multinomial Finset.univ
              (fun sigma :
                {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
                  fixedHashTargetJointTable m sigma.1) : ℝ) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · intro j _
      positivity
    · intro j _
      exact htargetLower j
  have hrowPolynomial (j : Fin 9) :
      rowPolynomial j ≤
        (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^
          Fintype.card
            {sigma : FixedHashSupportTriple // sigma.1 i = j} := by
    dsimp only [rowPolynomial]
    gcongr
    exact_mod_cast fixedHashRowReduction_marginal_count_le_length m j
  have hpolynomialProduct :
      (∏ j : Fin 9, rowPolynomial j) ≤
        (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 45 := by
    calc
      (∏ j : Fin 9, rowPolynomial j) ≤
          ∏ j : Fin 9,
            (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^
              Fintype.card
                {sigma : FixedHashSupportTriple // sigma.1 i = j} := by
        apply Finset.prod_le_prod
        · intro j _
          positivity
        · intro j _
          exact hrowPolynomial j
      _ = (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^
          (∑ j : Fin 9,
            Fintype.card
              {sigma : FixedHashSupportTriple // sigma.1 i = j}) := by
        exact Finset.prod_pow_eq_pow_sum _ _ _
      _ = (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 45 := by
        rw [fixedHashRowReduction_card_sum i]
  calc
    (∏ j : Fin 9,
        (Nat.multinomial Finset.univ
          (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
            k sigma.1) : ℝ)) ≤
        Real.exp (∑ j, candidateExponent j) := hproductCandidate
    _ ≤ Real.exp (∑ j, targetExponent j) :=
      Real.exp_le_exp.mpr hconditionalLog
    _ ≤ ∏ j : Fin 9,
        rowPolynomial j *
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
                fixedHashTargetJointTable m sigma.1) : ℝ) := hproductTarget
    _ = (∏ j : Fin 9, rowPolynomial j) *
        ∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
                fixedHashTargetJointTable m sigma.1) : ℝ) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ (6 * (((fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 45 *
        ∏ j : Fin 9,
          (Nat.multinomial Finset.univ
            (fun sigma :
              {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
                fixedHashTargetJointTable m sigma.1) : ℝ) := by
      exact mul_le_mul_of_nonneg_right hpolynomialProduct (by positivity)
