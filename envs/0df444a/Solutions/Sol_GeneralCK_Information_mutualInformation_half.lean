-- Prove2me | solution 1 for GeneralCK.Information.mutualInformation_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T19:36:26.441433+00:00
-- url     : https://prove2.me/submissions/8d0d4c60-10da-4146-8cc9-da6e5aa4a0bd

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_information
import Theorems.Thm_GeneralCK_Information_mutualInformation_eq

open scoped BigOperators

/-! Precise target, not a proof of the Courtade--Kumar conjecture. -/
namespace GeneralCK
open scoped BigOperators





























end GeneralCK

namespace GeneralCK
open scoped BigOperators









end GeneralCK

namespace GeneralCK.Information
open scoped BigOperators







theorem weight_sum (n : ℕ) : (∑ _ : Cube n, cubeWeight n) = 1 := by
  simp [cubeWeight, Cube, zpow_neg, zpow_natCast]





























theorem kernel_half {n : ℕ} (x y : Cube n) :
    noiseKernel (1 / 2) x y = cubeWeight n := by
  have h : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [noiseKernel, h, ite_self, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, cubeWeight, zpow_neg, zpow_natCast]
  simp [one_div, inv_pow]

theorem posterior_half {n : ℕ} (f : Cube n → Bool) (y : Cube n) :
    posterior f (1 / 2) y = meanIndicator f := by
  classical
  simp only [posterior, kernel_half, meanIndicator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp





end GeneralCK.Information

open GeneralCK GeneralCK.Information in
theorem solution {n : ℕ} (f : Cube n → Bool) :
    mutualInformation f (1 / 2) = 0 := by
  rw [mutualInformation_eq]
  simp_rw [posterior_half]
  rw [Finset.mul_sum]
  simp_rw [← Finset.sum_mul, weight_sum, one_mul, sub_self]
