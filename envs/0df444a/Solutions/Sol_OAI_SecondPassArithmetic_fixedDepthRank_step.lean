-- Prove2me | solution 1 for OAI.SecondPassArithmetic.fixedDepthRank_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:22:30.581494+00:00
-- url     : https://prove2.me/submissions/95669a5e-f905-4592-8054-0c326962a705

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (Z K K' : ℝ) (hZ : 1 < Z) (hK : 0 < K)
    (hK' : 1 ≤ K') (hstep : K' ≤ K/Z^((1:ℝ)/1000)) :
    fixedDepthRank Z K'+1 ≤ fixedDepthRank Z K := by
  have hz0 : 0 < Z := lt_trans zero_lt_one hZ
  have hz := Real.log_pos hZ
  have hk0 : 0 < K' := lt_of_lt_of_le zero_lt_one hK'
  have hl := Real.log_le_log hk0 hstep
  rw [Real.log_div hK.ne' (Real.rpow_pos_of_pos hz0 _).ne',Real.log_rpow hz0] at hl
  have ha : 0 ≤ 1000*Real.log K'/Real.log Z := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hK')) hz.le
  have hb : 1000*Real.log K'/Real.log Z+1 ≤ 1000*Real.log K/Real.log Z := by
    apply (le_div_iff₀ hz).mpr
    field_simp
    nlinarith
  have hn := Nat.ceil_mono hb
  rw [Nat.ceil_add_one ha] at hn
  exact hn
end OAI.SecondPassArithmetic
