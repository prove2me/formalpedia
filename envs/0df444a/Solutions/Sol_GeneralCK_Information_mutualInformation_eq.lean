-- Prove2me | solution 1 for GeneralCK.Information.mutualInformation_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T19:35:38.100991+00:00
-- url     : https://prove2.me/submissions/0e3232f6-b7ee-4999-984e-6a65f9f99152

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_information
import Theorems.Thm_GeneralCK_jointMass_sum
import Theorems.Thm_GeneralCK_noiseKernel_sum

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









theorem kernel_symm {n : ℕ} (p : ℝ) (x y : Cube n) :
    noiseKernel p x y = noiseKernel p y x := by
  simp only [noiseKernel, eq_comm]

theorem kernel_column_sum {n : ℕ} (p : ℝ) (y : Cube n) :
    ∑ x, noiseKernel p x y = 1 := by
  simp_rw [kernel_symm p _ y]
  exact noiseKernel_sum p y

theorem joint_true {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    jointMass f p true y = cubeWeight n * posterior f p y := rfl

theorem joint_output {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    ∑ b, jointMass f p b y = cubeWeight n := by
  classical
  have hb (x : Cube n) :
      (∑ b : Bool, if f x = b then noiseKernel p x y else 0) = noiseKernel p x y := by
    cases f x <;> simp
  simp only [jointMass, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [hb, kernel_column_sum, mul_one, cubeWeight]

theorem joint_false {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    jointMass f p false y = cubeWeight n * (1 - posterior f p y) := by
  have h := joint_output f p y
  simp only [Fintype.sum_bool, joint_true] at h
  linarith

theorem marginal_true {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    ∑ y, jointMass f p true y = meanIndicator f := by
  classical
  simp only [jointMass, ← Finset.mul_sum, meanIndicator, cubeWeight]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with h
  · simp [noiseKernel_sum]
  · simp

theorem marginal_false {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    ∑ y, jointMass f p false y = 1 - meanIndicator f := by
  have h := jointMass_sum f p
  simp only [Fintype.sum_bool, marginal_true] at h
  linarith

theorem entropy_bool (q : Bool → ℝ) (hq : q false + q true = 1) :
    entropy q = H (q true) := by
  have hf : q false = 1 - q true := by linarith
  simp only [entropy, Fintype.sum_bool, hf, H,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem scaled_binary_entropy (w t : ℝ) :
    Real.negMulLog (w * t) + Real.negMulLog (w * (1 - t)) =
      Real.negMulLog w + w * Real.binEntropy t := by
  rw [Real.negMulLog_mul, Real.negMulLog_mul,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

theorem entropy_input {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    entropy (fun b => ∑ y, jointMass f p b y) = H (meanIndicator f) := by
  rw [entropy_bool]
  · rw [marginal_true]
  · rw [marginal_false, marginal_true]; ring

theorem entropy_joint {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    entropy (fun byPair : Bool × Cube n => jointMass f p byPair.1 byPair.2) =
      entropy (fun _ : Cube n => cubeWeight n) +
      cubeWeight n * ∑ y, H (posterior f p y) := by
  classical
  simp only [entropy, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_bool, joint_false, joint_true, scaled_binary_entropy]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_div]
  simp only [H, div_eq_mul_inv, ← Finset.sum_mul]
  ring















end GeneralCK.Information

open GeneralCK GeneralCK.Information in
theorem solution {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    mutualInformation f p = H (meanIndicator f) -
      cubeWeight n * ∑ y, H (posterior f p y) := by
  unfold mutualInformation
  rw [entropy_input, entropy_joint]
  simp_rw [joint_output]
  ring
