-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveGaussianFourTerms_rational_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:17.389187+00:00
-- url     : https://prove2.me/submissions/a2dd86be-7f62-4c45-ad72-0f6f82078666

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_breveGaussianFourTerms_formula
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (m : ℕ) (hodd : Odd m) :
    breveGaussianFourTerms (m : ℤ) 0 = 1 := by
  have hsq : (Complex.I ^ m) ^ 2 = -1 := by
    calc
      (Complex.I ^ m) ^ 2 = Complex.I ^ (m * 2) := by rw [pow_mul]
      _ = Complex.I ^ (2 * m) := by rw [mul_comm]
      _ = (Complex.I ^ 2) ^ m := by rw [pow_mul]
      _ = (-1 : ℂ) ^ m := by rw [Complex.I_sq]
      _ = -1 := hodd.neg_one_pow
  have hinv : (Complex.I ^ m)⁻¹ = -(Complex.I ^ m) := by
    apply inv_eq_of_mul_eq_one_right
    calc
      (Complex.I ^ m) * -(Complex.I ^ m) = -((Complex.I ^ m) ^ 2) := by ring
      _ = 1 := by rw [hsq]; ring
  rw [breveGaussianFourTerms_formula]
  simp only [zero_sub,  zpow_neg, zpow_zero, inv_one, zpow_natCast]
  rw [hinv]
  ring
end OAI.ActualEisensteinCubic
