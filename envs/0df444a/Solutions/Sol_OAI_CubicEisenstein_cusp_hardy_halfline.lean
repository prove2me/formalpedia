-- Prove2me | solution 1 for OAI.CubicEisenstein.cusp_hardy_halfline
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:57:16.349721+00:00
-- url     : https://prove2.me/submissions/f196918d-da01-4017-9004-b26fafea452c

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Theorems.Thm_OAI_CubicEisenstein_cusp_hardy_interval

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
namespace OAI.CubicEisenstein
theorem _root_.solution (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a))
    (hM : IntegrableOn (fun t => ‖f t‖^2/t^3) (Set.Ioi a) volume)
    (hE : IntegrableOn (fun t => ‖deriv f t‖^2/t) (Set.Ioi a) volume) :
    (∫t in Set.Ioi a,‖f t‖^2/t^3)≤∫t in Set.Ioi a,‖deriv f t‖^2/t := by
  apply le_of_tendsto_of_tendsto
    (intervalIntegral_tendsto_integral_Ioi a hM tendsto_id)
    (intervalIntegral_tendsto_integral_Ioi a hE tendsto_id)
  filter_upwards [eventually_ge_atTop a] with b hab
  exact cusp_hardy_interval f a b ha hab hfa
    (fun t ht => hf t ht.1) (hdf.mono (fun t ht => ht.1))
end OAI.CubicEisenstein
