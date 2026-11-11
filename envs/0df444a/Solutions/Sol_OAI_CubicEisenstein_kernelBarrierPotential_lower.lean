-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelBarrierPotential_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:18:36.450069+00:00
-- url     : https://prove2.me/submissions/8c40bb4f-8d02-473e-a67b-7f89d87cfb41

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_UnitRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientBarrierDefect_continuous
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientBarrierDefect_hasCompactSupport
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientBarrier_one_le


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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 1<a) (hab : a<b) :
    ∃K : Set KernelQuotient,IsCompact K ∧ ∃C : ℝ,0≤C ∧
      ∀q,1-C*(K.indicator (fun _ => (1:ℝ))) q≤kernelBarrierPotential a b q := by
  let D := kernelQuotientBarrierDefect a b
  let K := tsupport D
  have hK : IsCompact K := kernelQuotientBarrierDefect_hasCompactSupport a b ha hab
  obtain ⟨C,hC⟩ := (kernelQuotientBarrierDefect_hasCompactSupport a b ha hab).exists_bound_of_continuous
    (kernelQuotientBarrierDefect_continuous a b ha hab)
  refine ⟨K,hK,max C 0,le_max_right _ _,fun q => ?_⟩
  have hphi := kernelQuotientBarrier_one_le a b ha.le hab q
  have hpos : 0<kernelQuotientBarrier a b q := by linarith
  by_cases hq : q∈K
  · rw [Set.indicator_of_mem hq,mul_one,kernelBarrierPotential]
    have hD : -max C 0≤D q := by
      have hn : -‖D q‖≤D q := neg_abs_le (D q)
      exact (neg_le_neg ((hC q).trans (le_max_left C 0))).trans hn
    have hdiv : -max C 0≤D q/kernelQuotientBarrier a b q := by
      apply (le_div_iff₀ hpos).mpr
      have hm : -max C 0*kernelQuotientBarrier a b q≤-max C 0 := by
        nlinarith [mul_nonneg (le_max_right C 0) (sub_nonneg.mpr hphi)]
      exact hm.trans hD
    linarith
  · rw [Set.indicator_of_notMem hq,mul_zero,sub_zero,kernelBarrierPotential]
    have hz : D q=0 := image_eq_zero_of_notMem_tsupport hq
    change 1≤1+D q/kernelQuotientBarrier a b q
    rw [hz,zero_div,add_zero]
end OAI.CubicEisenstein
