-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.cutoff_middle_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:29:26.882767+00:00
-- url     : https://prove2.me/submissions/1253da60-aa9a-401c-91a0-8d2d93409373

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins

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
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M X T α : ℝ) (hM : 0<M) (hX : 0<X) (hT : 0<T) :
    T*Real.sqrt M*(T*X^2/M)^(α-1/2) =
      T^(α+1/2)*X^(2*α-1)*M^(1-α) := by
  rw [Real.div_rpow (by positivity : 0≤T*X^2) hM.le,
    Real.mul_rpow hT.le (sq_nonneg X),←Real.rpow_two,←Real.rpow_mul hX.le]
  have hx : 2*(α-1/2)=2*α-1 := by ring
  have hm : 1-α=1/2-(α-1/2) := by ring
  have ht : α+1/2=1+(α-1/2) := by ring
  have hmPow : M^(1-α)=M^(1/2:ℝ)/M^(α-1/2) := by
    calc
      _ = M^((1/2:ℝ)-(α-1/2)) := by rw [hm]
      _ = _ := Real.rpow_sub hM _ _
  have htPow : T^(α+1/2)=T*T^(α-1/2) := by
    calc
      _ = T^(1+(α-1/2)) := by rw [ht]
      _ = _ := by rw [Real.rpow_add hT,Real.rpow_one]
  rw [hx,hmPow,htPow,Real.sqrt_eq_rpow]
  ring
end OAI.CanonicalQuadraticSieve
