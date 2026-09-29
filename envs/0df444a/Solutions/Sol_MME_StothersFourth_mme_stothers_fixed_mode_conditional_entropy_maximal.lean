-- Prove2me | solution 1 for MME.StothersFourth.mme_stothers_fixed_mode_conditional_entropy_maximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:12:16.837329+00:00
-- url     : https://prove2.me/submissions/f0c6566f-a9d6-4dd6-8805-e1f0ba03730f

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_stothers_fixed_outer_profile_arithmetic
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_target_joint_table_marginal
import Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_joint_entropy_maximal
import Mathlib.Algebra.BigOperators.Field

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MME.StothersFourth

private theorem fixedHashConditional_entropy_chain_rule
    {D J : Type*} [Fintype D] [Fintype J] [DecidableEq J]
    (coord : D → J) (p : D → ℝ) (q : J → ℝ)
    (hq : ∀ j, q j = ∑ x : {x : D // coord x = j}, p x.1)
    (hqpos : ∀ j, 0 < q j) :
    mme_modern_entropyBits p =
      mme_modern_entropyBits q +
        ∑ j, q j * mme_modern_entropyBits
          (fun x : {x : D // coord x = j} ↦ p x.1 / q j) := by
  classical
  have hrow (j : J) :
      (∑ x : {x : D // coord x = j}, Real.negMulLog (p x.1)) =
        Real.negMulLog (q j) +
          q j * ∑ x : {x : D // coord x = j},
            Real.negMulLog (p x.1 / q j) := by
    have hqne : q j ≠ 0 := ne_of_gt (hqpos j)
    calc
      (∑ x : {x : D // coord x = j}, Real.negMulLog (p x.1)) =
          ∑ x : {x : D // coord x = j},
            Real.negMulLog (q j * (p x.1 / q j)) := by
        apply Finset.sum_congr rfl
        intro x _
        congr 1
        field_simp
      _ = ∑ x : {x : D // coord x = j},
          ((p x.1 / q j) * Real.negMulLog (q j) +
            q j * Real.negMulLog (p x.1 / q j)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact Real.negMulLog_mul _ _
      _ = Real.negMulLog (q j) +
          q j * ∑ x : {x : D // coord x = j},
            Real.negMulLog (p x.1 / q j) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        have hsum :
            (∑ x : {x : D // coord x = j}, p x.1 / q j) = 1 := by
          rw [← Finset.sum_div, ← hq j]
          exact div_self hqne
        rw [hsum]
        ring
  unfold mme_modern_entropyBits
  rw [← Fintype.sum_fiberwise coord (fun x ↦ Real.negMulLog (p x))]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp only [div_eq_mul_inv]
  have hfactor :
      (∑ j, q j *
        ((∑ x : {x : D // coord x = j},
          Real.negMulLog (p x.1 * (q j)⁻¹)) * (Real.log 2)⁻¹)) =
        (∑ j, q j *
          ∑ x : {x : D // coord x = j},
            Real.negMulLog (p x.1 * (q j)⁻¹)) * (Real.log 2)⁻¹ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor]
  ring

private theorem fixedHashConditional_marginal_count_sum (m : ℕ) :
    ∑ j : Fin 9, fixedMarginalCount m j = fixedOuterLength m := by
  simp only [fixedMarginalCount]
  rw [← Finset.mul_sum,
    mme_stothers_fixed_outer_profile_arithmetic.2.2.2.2.1]
  simp only [fixedOuterLength]
  ac_rfl

private theorem fixedHashConditional_outer_length_pos
    (m : ℕ) (hm : 0 < m) : 0 < fixedOuterLength m := by
  simp only [fixedOuterLength]
  exact Nat.mul_pos (by norm_num) (Nat.mul_pos (by
    norm_num [fixedProfileScale]) hm)

private theorem fixedHashConditional_marginal_count_pos
    (m : ℕ) (hm : 0 < m) (j : Fin 9) :
    0 < fixedMarginalCount m j := by
  exact Nat.mul_pos hm (by
    fin_cases j <;> norm_num [fixedMarginalBaseCount])

private theorem fixedHashConditional_joint_table_sum
    (m : ℕ) (k : FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : FixedHashSupportTriple // sigma.1 l = j},
        k sigma.1) = fixedMarginalCount m j) :
    ∑ sigma, k sigma = fixedOuterLength m := by
  rw [← Fintype.sum_fiberwise
    (fun sigma : FixedHashSupportTriple ↦ sigma.1 0) k]
  simp_rw [hkMarginal 0]
  exact fixedHashConditional_marginal_count_sum m

private theorem fixedHashConditional_target_table_sum (m : ℕ) :
    ∑ sigma : FixedHashSupportTriple, fixedHashTargetJointTable m sigma =
      fixedOuterLength m := by
  rw [← Fintype.sum_fiberwise
    (fun sigma : FixedHashSupportTriple ↦ sigma.1 0)
    (fixedHashTargetJointTable m)]
  simp_rw [mme_stothers_fixed_target_joint_table_marginal m 0]
  exact fixedHashConditional_marginal_count_sum m

private theorem fixedHashConditional_target_table_scale
    (m : ℕ) (sigma : FixedHashSupportTriple) :
    fixedHashTargetJointTable m sigma =
      m * fixedHashTargetJointTable 1 sigma := by
  simp only [fixedHashTargetJointTable, fixedJointMultiplicity,
    fixedProfileCount]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  split <;> simp

private theorem fixedHashConditional_outer_length_scale (m : ℕ) :
    fixedOuterLength m = m * fixedOuterLength 1 := by
  simp only [fixedOuterLength]
  ac_rfl

end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (m : ℕ) (hm : 0 < m) (i : Fin 3)
    (k : FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : FixedHashSupportTriple // sigma.1 l = j},
        k sigma.1) = fixedMarginalCount m j) :
    (∑ j : Fin 9, (fixedMarginalCount m j : ℝ) *
      mme_modern_entropyBits
        (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
          (k sigma.1 : ℝ) / (fixedMarginalCount m j : ℝ))) ≤
      ∑ j : Fin 9, (fixedMarginalCount m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
            (fixedHashTargetJointTable m sigma.1 : ℝ) /
              (fixedMarginalCount m j : ℝ)) := by
  classical
  let N : ℕ := fixedOuterLength m
  let rho : FixedHashSupportTriple → ℝ := fun sigma ↦ (k sigma : ℝ) / N
  let target : FixedHashSupportTriple → ℝ := fun sigma ↦
    (fixedHashTargetJointTable m sigma : ℝ) / N
  let q : Fin 9 → ℝ := fun j ↦ (fixedMarginalCount m j : ℝ) / N
  have hNposNat : 0 < N := fixedHashConditional_outer_length_pos m hm
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hNposNat)
  have hqpos (j : Fin 9) : 0 < q j := by
    exact div_pos
      (by exact_mod_cast fixedHashConditional_marginal_count_pos m hm j)
      (by exact_mod_cast hNposNat)
  have hrhoSum : ∑ sigma, rho sigma = 1 := by
    dsimp only [rho]
    rw [← Finset.sum_div, ← Nat.cast_sum,
      fixedHashConditional_joint_table_sum m k hkMarginal]
    exact div_self hNne
  have htargetSum : ∑ sigma, target sigma = 1 := by
    dsimp only [target]
    rw [← Finset.sum_div, ← Nat.cast_sum,
      fixedHashConditional_target_table_sum m]
    exact div_self hNne
  have hrhoMarginal (l : Fin 3) (j : Fin 9) :
      q j = ∑ sigma : {sigma : FixedHashSupportTriple // sigma.1 l = j},
        rho sigma.1 := by
    dsimp only [q, rho]
    rw [← Finset.sum_div, ← Nat.cast_sum, hkMarginal l j]
  have htargetMarginal (l : Fin 3) (j : Fin 9) :
      q j = ∑ sigma : {sigma : FixedHashSupportTriple // sigma.1 l = j},
        target sigma.1 := by
    dsimp only [q, target]
    rw [← Finset.sum_div, ← Nat.cast_sum,
      mme_stothers_fixed_target_joint_table_marginal m l j]
  have htargetPublic : target = fun sigma : FixedHashSupportTriple ↦
      (fixedJointMultiplicity 1 sigma.1 : ℝ) /
        (fixedOuterLength 1 : ℝ) := by
    funext sigma
    dsimp only [target, N]
    change
      (fixedHashTargetJointTable m sigma : ℝ) /
          (fixedOuterLength m : ℝ) =
        (fixedHashTargetJointTable 1 sigma : ℝ) /
          (fixedOuterLength 1 : ℝ)
    rw [fixedHashConditional_target_table_scale,
      fixedHashConditional_outer_length_scale]
    push_cast
    field_simp
  have hmax : mme_modern_entropyBits rho ≤
      mme_modern_entropyBits target := by
    rw [htargetPublic]
    apply mme_stothers_fixed_joint_entropy_maximal rho
    · intro sigma
      positivity
    · exact hrhoSum
    · intro l j
      unfold mme_modern_marginal
      rw [← hrhoMarginal l j]
      rw [htargetPublic] at htargetMarginal
      exact htargetMarginal l j
  have hrhoChain := fixedHashConditional_entropy_chain_rule
    (fun sigma : FixedHashSupportTriple ↦ sigma.1 i) rho q
    (hrhoMarginal i) hqpos
  have htargetChain := fixedHashConditional_entropy_chain_rule
    (fun sigma : FixedHashSupportTriple ↦ sigma.1 i) target q
    (htargetMarginal i) hqpos
  have hconditional :
      (∑ j, q j * mme_modern_entropyBits
        (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
          rho sigma.1 / q j)) ≤
      ∑ j, q j * mme_modern_entropyBits
        (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
          target sigma.1 / q j) := by
    linarith
  have hrhoConditional (j : Fin 9) :
      (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
          rho sigma.1 / q j) =
        fun sigma ↦ (k sigma.1 : ℝ) /
          (fixedMarginalCount m j : ℝ) := by
    funext sigma
    dsimp only [rho, q]
    have hmargne : (fixedMarginalCount m j : ℝ) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt (fixedHashConditional_marginal_count_pos m hm j))
    field_simp
  have htargetConditional (j : Fin 9) :
      (fun sigma : {sigma : FixedHashSupportTriple // sigma.1 i = j} ↦
          target sigma.1 / q j) =
        fun sigma ↦ (fixedHashTargetJointTable m sigma.1 : ℝ) /
          (fixedMarginalCount m j : ℝ) := by
    funext sigma
    dsimp only [target, q]
    have hmargne : (fixedMarginalCount m j : ℝ) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt (fixedHashConditional_marginal_count_pos m hm j))
    field_simp
  simp_rw [hrhoConditional, htargetConditional] at hconditional
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hconditional hNnonneg
  dsimp only [q] at hscaled
  rw [Finset.mul_sum, Finset.mul_sum] at hscaled
  have hcancel (j : Fin 9) (x : ℝ) :
      (N : ℝ) * ((fixedMarginalCount m j : ℝ) / (N : ℝ) * x) =
        (fixedMarginalCount m j : ℝ) * x := by
    field_simp
  simpa only [hcancel] using hscaled
