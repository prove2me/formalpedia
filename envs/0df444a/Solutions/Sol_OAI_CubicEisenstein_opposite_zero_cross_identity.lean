-- Prove2me | solution 1 for OAI.CubicEisenstein.opposite_zero_cross_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:56:54.067837+00:00
-- url     : https://prove2.me/submissions/a1548deb-bf0a-43b9-9b19-0438ca87ece6

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RationalTranslations
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspAverage
import Theorems.Thm_OAI_CubicEisenstein_opposite_zero_initial_cross
import Theorems.Thm_OAI_CubicEisenstein_baseOutgoingConstant_analyticAt
import Theorems.Thm_OAI_CubicEisenstein_translatedCuspFamily_analyticAt_nonreal


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
namespace OAI.CubicEisenstein
theorem _root_.solution :
    Set.EqOn (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s)
      {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s) domain := by
    intro s hs
    exact analyticAt_const.mul (translatedCuspFamily_analyticAt_nonreal 0 oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hright : AnalyticOnNhd ℂ
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) domain := by
    intro s hs
    have hp : AnalyticAt ℂ (fun z:ℂ=>(3:ℂ)^(3*z-3)-1) s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      exact Eventually.of_forall fun z=>
        ((((differentiableAt_const (3:ℂ)).mul differentiableAt_id).sub_const 3).const_cpow
          (Or.inl (by norm_num))).sub_const 1
    exact hp.mul (baseOutgoingConstant_analyticAt s hs.1 hs.2)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact opposite_zero_initial_cross s hs.1 hs.2
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent
end OAI.CubicEisenstein
