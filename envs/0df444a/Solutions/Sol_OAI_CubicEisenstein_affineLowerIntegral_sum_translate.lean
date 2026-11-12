-- Prove2me | solution 1 for OAI.CubicEisenstein.affineLowerIntegral_sum_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:03:39.310214+00:00
-- url     : https://prove2.me/submissions/1ece059a-5b27-44d7-ac7f-e139295e7d15

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedCuspPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_AffineCuspFourier
import Theorems.Thm_OAI_CubicEisenstein_affineLowerTerm_integrable
import Theorems.Thm_OAI_CubicEisenstein_affineLowerTerm_weighted_translate
import Theorems.Thm_OAI_CubicEisenstein_finite_index_period_unfold
import Theorems.Thm_OAI_CubicEisenstein_trace_mul_integrable


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
open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (h h1 q r a k x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re) :
    (∑'m:Eis,∫z in periodDomain,affineLowerTerm q r z v s a (a+3*(x+a*m))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        ∫z:ℂ,affineLowerTerm q r z v s a (a+3*x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have hint:=trace_mul_integrable (fun z=>affineLowerTerm q r z v s a (a+3*x))
    (affineLowerTerm_integrable q r v hv s hs a (a+3*x) ha hq) (ninthCuspFrequency h)
  rw [←finite_index_period_unfold q hq _ hint]
  apply tsum_congr
  intro m
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>affineLowerTerm_weighted_translate
    h h1 q r a k x m j n ha hprimary hq hr hh hk z v s)
end OAI.CubicEisenstein
