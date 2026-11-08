-- Prove2me | solution 1 for OAI.CubicEisenstein.ramified_geometric_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:57:08.632369+00:00
-- url     : https://prove2.me/submissions/4f288a1a-8258-49b2-a0af-2bc819905867

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FrequencyCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
import Theorems.Thm_OAI_CubicEisenstein_norm_ramifiedRatio_lt_one

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
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (hs : 1<s.re) :
    (∑' n : ℕ,ramifiedRatio s^(n+1))=((3:ℂ)^(3*s-3)-1)⁻¹ := by
  have hn := norm_ramifiedRatio_lt_one s hs
  have hne : ramifiedRatio s ≠ 0 := by
    unfold ramifiedRatio
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (by norm_num)
  have hone : ramifiedRatio s ≠ 1 := by intro h; rw [h,norm_one] at hn; exact lt_irrefl 1 hn
  have hi : (3:ℂ)^(3*s-3)=(ramifiedRatio s)⁻¹ := by
    rw [ramifiedRatio,← Complex.cpow_neg]
    congr 1
    ring
  simp_rw [pow_succ]
  rw [tsum_mul_right,tsum_geometric_of_norm_lt_one hn,hi]
  field_simp
end OAI.CubicEisenstein
