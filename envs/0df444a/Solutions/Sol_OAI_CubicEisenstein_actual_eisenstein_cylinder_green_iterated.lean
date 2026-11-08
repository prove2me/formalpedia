-- Prove2me | solution 1 for OAI.CubicEisenstein.actual_eisenstein_cylinder_green_iterated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:02:54.840496+00:00
-- url     : https://prove2.me/submissions/3220cf8d-cd63-4ec9-8311-4db0510a2888

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogarithmicTargets
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspIntegration
import Theorems.Thm_OAI_CubicEisenstein_actual_eisenstein_cylinder_green
import Theorems.Thm_OAI_CubicEisenstein_cuspBoxIntegral_eq_iterated_positive
import Theorems.Thm_OAI_CubicEisenstein_eisensteinHermitianDensity_continuousAt

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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
namespace OAI.CubicEisenstein
theorem _root_.solution (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    (s*(s-2)-star (t*(t-2)))*
      (∫v in a..b, ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        upperEisensteinField s (spatialTriple x y v)*star (upperEisensteinField t (spatialTriple x y v))/(v:ℂ)^3)=
      ∫y in (0:ℝ)..(3*Real.sqrt 3), ∫x in (0:ℝ)..3,
        greenBoundaryFlux s t (spatialTriple x y b)-greenBoundaryFlux s t (spatialTriple x y a) := by
  have h := actual_eisenstein_cylinder_green s t hs ht a b ha hab
  rw [cuspBoxIntegral_eq_iterated_positive _
    (eisensteinHermitianDensity_continuousAt s t hs ht) a b ha hab] at h
  exact h
end OAI.CubicEisenstein
