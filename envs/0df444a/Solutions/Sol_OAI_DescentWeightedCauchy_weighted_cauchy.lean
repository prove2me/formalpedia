-- Prove2me | solution 1 for OAI.DescentWeightedCauchy.weighted_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:48:24.243114+00:00
-- url     : https://prove2.me/submissions/162aecdd-34a1-4392-bf1e-f67bf9acc85a

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Theorems.Thm_OAI_DescentWeightedCauchy_weighted_cauchy_sq
import Theorems.Thm_OAI_AnalyticBridge_weighted_cauchy_sq


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
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
open scoped BigOperators Classical
open OAI.DescentWeightedCauchy
namespace OAI.DescentWeightedCauchy
theorem _root_.solution {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have h1 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have h2 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hs := weighted_cauchy_sq s w U V
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : (Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2)) ^ 2 =
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by rw [mul_pow, he1, he2]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hp ▸ hs)
end OAI.DescentWeightedCauchy
