-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberExpSum_norm_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:53:05.482473+00:00
-- url     : https://prove2.me/submissions/3b6f2c39-fd35-4098-8080-559c7a927941

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberCoeff_norm_le
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖normFiberExpSum weight t‖ ≤
      (∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)) *
        Real.exp (-t / 2) := by
  have hmajor : Summable (fun n : ℕ =>
      (n : ℝ) * Real.exp (-(n : ℝ) / 2)) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1 / 2) using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  have hbound (n : ℕ) :
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖ ≤
        ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) := by
    by_cases hn : n = 0
    · subst n
      simp [ha0]
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hdiff : -(n : ℝ) * t ≤ -(n : ℝ) / 2 - t / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr ht)]
    have hexp : Real.exp (-(n : ℝ) * t) ≤
        Real.exp (-(n : ℝ) / 2) * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      convert hdiff using 1
      ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖normFiberCoeff weight n‖ * Real.exp (-(n : ℝ) * t) ≤
          (n : ℝ) * Real.exp (-(n : ℝ) * t) :=
        mul_le_mul_of_nonneg_right
          (normFiberCoeff_norm_le χ ψ weight hcoeff ha0 n) (Real.exp_pos _).le
      _ ≤ ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hexp
          (Nat.cast_nonneg (α := ℝ) n)]
  have hnormsum : Summable (fun n : ℕ =>
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖) :=
    (hmajor.mul_right (Real.exp (-t / 2))).of_nonneg_of_le
      (fun _ => norm_nonneg _) hbound
  calc
    ‖normFiberExpSum weight t‖ ≤
      ∑' n : ℕ, ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ,
        ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) :=
      hnormsum.tsum_le_tsum hbound (hmajor.mul_right _)
    _ = (∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)) *
        Real.exp (-t / 2) := by rw [tsum_mul_right]
end OAI.ShortDraftHeckeBridge
