-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.cauchy_large_scale_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:11:33.269239+00:00
-- url     : https://prove2.me/submissions/191c4692-09f8-4210-9cc9-43f5b92aa341

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion

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
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open OAI.EisensteinSchwartzPoisson
open ConcreteTraceCRT ActualEisensteinCubic
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (K q : ℝ) (hK : 1 ≤ K) (hq : 1 ≤ q) :
    K * ((1 + K * q) ^ 2)⁻¹ ≤ 4 * ((1 + q) ^ 2)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hqp : 0 < q := by linarith
  have h1 : K * (1 + q) ≤ 2 * (1 + K * q) := by nlinarith
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ K * (1 + q)) h1 2
  have h3 : K * (1 + q) ^ 2 ≤ K ^ 2 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (1 + q)]
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + K * q) ^ 2)
    (by positivity : 0 < (1 + q) ^ 2)).mpr
  nlinarith
end OAI.EisensteinSchwartzPoisson
