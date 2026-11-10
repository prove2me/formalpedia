-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_bin_invariant_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:28:51.799449+00:00
-- url     : https://prove2.me/submissions/b3a91124-b783-4231-a5eb-238f81fe11c8

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_NormalizedMass
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Theorems.Thm_OAI_InitialMeanSquare_initial_bin_invariant
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_pos


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
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open SecondPassArithmetic
namespace OAI.InitialMeanSquare
theorem _root_.solution (Z H B R c : ℝ) (j : SecondLogIndex)
    (hZ : 0<Z) (hH : 0<H) (hB : 0<B) (hR : R≤c*B) :
    (secondLogK j*Real.exp 2)*R/(initialLogColumn Z B j*initialLogLabel j)≤
      c*(Z/H)*(H*secondLogK j*B^2/Z^2) := by
  rw [initial_bin_invariant Z H B R j hZ.ne' hH.ne' hB.ne']
  have hr : R/B≤c := (div_le_iff₀ hB).mpr hR
  have hk : 0<secondLogK j := normLogScale_pos _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hr (div_nonneg hZ.le hH.le)) (by positivity)
end OAI.InitialMeanSquare
