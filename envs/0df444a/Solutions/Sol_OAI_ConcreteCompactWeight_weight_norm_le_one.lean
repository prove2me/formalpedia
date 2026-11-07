-- Prove2me | solution 1 for OAI.ConcreteCompactWeight.weight_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:55:46.520243+00:00
-- url     : https://prove2.me/submissions/103d901c-6c1c-44ae-90e1-8ae72e82ffdf

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_ConcreteCompactWeight_bump_nonneg
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_support
import Theorems.Thm_OAI_ConcreteCompactWeight_weight_eq_cpow
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
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ConcreteCompactWeight
namespace OAI.ConcreteCompactWeight
theorem _root_.solution (ρ : ℂ) (hρ : 0 ≤ ρ.re) (y : ℝ) :
    ‖weight ρ y‖ ≤ 1 := by
  by_cases hylo : y ≤ 1
  · rw [weight_support ρ y (Or.inl hylo)]
    simp
  by_cases hyhi : 2 ≤ y
  · rw [weight_support ρ y (Or.inr hyhi)]
    simp
  have hy1 : 1 ≤ y := le_of_lt (lt_of_not_ge hylo)
  have hypos : 0 < y := by linarith
  rw [weight_eq_cpow ρ y hypos, Complex.norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hypos,
    Complex.neg_re, Complex.norm_of_nonneg (bump_nonneg y)]
  have hpow : y ^ (-ρ.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have hpowpos : 0 ≤ y ^ (-ρ.re) := Real.rpow_nonneg hypos.le _
  have hb : bump y ≤ 1 := bumpData.le_one
  nlinarith
end OAI.ConcreteCompactWeight
