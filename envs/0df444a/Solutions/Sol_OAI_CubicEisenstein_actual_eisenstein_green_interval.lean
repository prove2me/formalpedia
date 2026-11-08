-- Prove2me | solution 1 for OAI.CubicEisenstein.actual_eisenstein_green_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:32:13.951023+00:00
-- url     : https://prove2.me/submissions/40883f4c-cdab-4e51-8d69-0609a3210497

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MiddleWindows
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GreenIntegrals
import Theorems.Thm_OAI_CubicEisenstein_green_identity_interval
import Theorems.Thm_OAI_CubicEisenstein_actual_axis_differentiable_at
import Theorems.Thm_OAI_CubicEisenstein_actual_axis_second_locallyIntegrable

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
open scoped BigOperators Classical SchwartzMap
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (j : Fin 3) (a b : ℝ)
    (hheight : ∀x∈Set.uIcc a b,0<(Function.update p j x) 2) :
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  apply green_identity_interval
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).2
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).2
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable s hs p j).integrableOn_compact_subset hheight isCompact_uIcc
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable t ht p j).integrableOn_compact_subset hheight isCompact_uIcc
end OAI.CubicEisenstein
