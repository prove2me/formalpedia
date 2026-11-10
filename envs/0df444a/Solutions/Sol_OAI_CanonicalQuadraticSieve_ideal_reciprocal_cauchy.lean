-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.ideal_reciprocal_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:51:23.648055+00:00
-- url     : https://prove2.me/submissions/ba760f0d-dbe5-48bf-8fa1-4ddc878a1671

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns

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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (v : Ideal O → ℂ) :
    ‖∑I∈S,v I‖^2≤(∑I∈S,1/(Ideal.absNorm I:ℝ))*
      (∑I∈S,(Ideal.absNorm I:ℝ)*‖v I‖^2) := by
  have hpos (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun I hI => by positivity) (fun I hI => by positivity)
  intro I hI
  exact le_of_eq (by field_simp [(hpos I hI).ne'])
end OAI.CanonicalQuadraticSieve
