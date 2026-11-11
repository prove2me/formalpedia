-- Prove2me | solution 1 for OAI.CubicEisenstein.weightedOutgoingConstant_cross_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:39:18.893532+00:00
-- url     : https://prove2.me/submissions/50e1a3c6-83b5-47e4-b899-0b8a55d5ddc9

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualFourierBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualFourierSeries
import Theorems.Thm_OAI_CubicEisenstein_compactHeightMellin_analyticAt
import Theorems.Thm_OAI_CubicEisenstein_kernelCuspHeightFourierFamily_zero_initial
import Theorems.Thm_OAI_CubicEisenstein_weightedOutgoingConstant_analyticAt
import Theorems.Thm_OAI_CubicEisenstein_baseOutgoingConstant_analyticAt
import Theorems.Thm_OAI_CubicEisenstein_cuspScatterHeightFactor_analyticAt
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicEisenstein_cusp_average_eq
import Theorems.Thm_OAI_CubicEisenstein_kernelCuspAverageFamily_eq_of_initial_overlap
import Theorems.Thm_OAI_CubicEisenstein_kernelEisensteinL2Correction_initial_overlap


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Filter MeasureTheory
open scoped BigOperators Classical Topology
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    Set.EqOn (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s)
      (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1))
      {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s) domain := by
    intro s hs
    exact (weightedOutgoingConstant_analyticAt a b ha ρ s hs.1 hs.2).mul
      (cuspScatterHeightFactor_analyticAt s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1)) domain := by
    intro s hs
    exact (baseOutgoingConstant_analyticAt s hs.1 hs.2).mul
      ((compactHeightMellin_analyticAt a b ha ρ _).comp_of_eq
        (analyticAt_id.neg.sub analyticAt_const) rfl)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s => weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s => baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1)) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    have hb : kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s=cuspConstantAverage s := by
      apply (kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num)
        s (by linarith [hs.1])
        (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)).trans
      exact hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1])
    rw [weightedOutgoingConstant,baseOutgoingConstant,
      kernelCuspHeightFourierFamily_zero_initial a b ha ρ s hs.1 hs.2,hb,
      cuspHeightConstantAverage,cuspConstantAverage]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent
end OAI.CubicEisenstein
