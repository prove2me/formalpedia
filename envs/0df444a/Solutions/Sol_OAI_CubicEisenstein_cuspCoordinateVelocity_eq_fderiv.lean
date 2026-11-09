-- Prove2me | solution 1 for OAI.CubicEisenstein.cuspCoordinateVelocity_eq_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:45:35.558088+00:00
-- url     : https://prove2.me/submissions/d897e187-7f92-484f-ad59-6bd5a18a31f1

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal ContDiff
namespace OAI.CubicEisenstein
theorem _root_.solution (F : CuspChartCoordinates → ℂ)
    (hF : Differentiable ℝ F) (q : CuspChartCoordinates) (j : Fin 3) :
    cuspCoordinateVelocity F q j=(q.2:ℂ)*fderiv ℝ F q (cuspCoordinateVector j) := by
  fin_cases j
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.1.1
      (((hasDerivAt_id q.1.1).prodMk (hasDerivAt_const q.1.1 q.1.2)).prodMk (hasDerivAt_const q.1.1 q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.1.2
      (((hasDerivAt_const q.1.2 q.1.1).prodMk (hasDerivAt_id q.1.2)).prodMk (hasDerivAt_const q.1.2 q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
  · have hd := (hF q).hasFDerivAt.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))
    exact congrArg (fun u : ℂ => (q.2:ℂ)*u) hd.deriv
end OAI.CubicEisenstein
