-- Prove2me | solution 1 for OAI.SecondPassArithmetic.CanonicalStateCondition.fixed_factor_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:46:54.885204+00:00
-- url     : https://prove2.me/submissions/eee3aace-e4a8-4335-8b7f-1b72aec1133c

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ClosedRecursion
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalRankMargin_strict_reserve

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
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
namespace CanonicalStateCondition
theorem _root_.solution
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/80)
    (C : ℝ) (hC : 0≤C) (hCZ : C≤Z^((1:ℝ)/80)) :
    C*K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((1:ℝ)/40)) := by
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hXF : 0≤X*F:=mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one)
  have hm := canonicalRankMargin_strict_reserve η hη hbudget (fixedDepthRank Z K)
  have hi : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((3:ℝ)/80)) := by
    apply h.invariant.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (neg_le_neg hm)) hXF
  calc
    C*K*‖eisEmbedding m‖^2 = C*(K*‖eisEmbedding m‖^2) := by ring
    _ ≤ C*((X*F)*Z^(-((3:ℝ)/80))) := mul_le_mul_of_nonneg_left hi hC
    _ ≤ Z^((1:ℝ)/80)*((X*F)*Z^(-((3:ℝ)/80))) :=
      mul_le_mul_of_nonneg_right hCZ (mul_nonneg hXF (Real.rpow_nonneg hZ0.le _))
    _ = (X*F)*(Z^((1:ℝ)/80)*Z^(-((3:ℝ)/80))) := by ring
    _ = _ := by rw [←Real.rpow_add hZ0];norm_num
end CanonicalStateCondition
end OAI.SecondPassArithmetic
