-- Prove2me | solution 1 for OAI.CubicEisenstein.cuspWhittakerHeightFactor_punctured_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:41:20.780202+00:00
-- url     : https://prove2.me/submissions/ec4b183a-ca11-4027-8145-38a0db28f798

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_WhittakerContinuation
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GaussFactorization
import Theorems.Thm_OAI_CubicEisenstein_cuspWhittakerHeightFactor_analyticAt
import Theorems.Thm_OAI_CubicEisenstein_cuspWhittakerHeightFactor_real_re_pos


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
open scoped Classical Topology
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h : ActualEisensteinCubic.O) (s : ℂ) (hs : 1<s.re) :
    ∀ᶠw : ℂ in 𝓝[≠] s,cuspWhittakerHeightFactor w h≠0 := by
  rcases (cuspWhittakerHeightFactor_analyticAt h s hs).eventually_eq_zero_or_eventually_ne_zero with hz|hne
  · have han : AnalyticOnNhd ℂ (fun w => cuspWhittakerHeightFactor w h) {w : ℂ | 1<w.re} :=
      fun w hw => cuspWhittakerHeightFactor_analyticAt h w hw
    have hcon : Convex ℝ {w : ℂ | 1<w.re} :=
      (convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap
    have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hcon.isPreconnected hs hz
    have hval : cuspWhittakerHeightFactor (5:ℂ) h=0 := heq (by norm_num)
    have hpos := cuspWhittakerHeightFactor_real_re_pos 5 (by norm_num) h
    norm_num only [Complex.ofReal_ofNat] at hpos
    rw [hval,Complex.zero_re] at hpos
    exact (lt_irrefl 0 hpos).elim
  · exact hne
end OAI.CubicEisenstein
