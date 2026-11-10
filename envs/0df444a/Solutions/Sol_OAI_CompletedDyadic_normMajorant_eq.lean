-- Prove2me | solution 1 for OAI.CompletedDyadic.normMajorant_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:54:18.700068+00:00
-- url     : https://prove2.me/submissions/b0dddcfb-7516-4a48-ab26-45e424e257ef

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators
open OAI.CompletedDyadic
namespace OAI.CompletedDyadic
theorem _root_.solution (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    normMajorant deltaLoss A K t r H U B =
      (K*(U*B))^deltaLoss*(Real.sqrt K+Real.sqrt U*Real.sqrt B)/
        (Real.sqrt B*r*Real.sqrt H*(1+t*r^3*B^3*U)^A) := by
  unfold normMajorant
  rw [Real.mul_rpow hK.le (mul_pos hU hB).le,Real.mul_rpow hU.le hB.le,
    Real.rpow_sub hB,Real.rpow_add hU,←Real.sqrt_eq_rpow B,←Real.sqrt_eq_rpow U]
  have hsB : Real.sqrt B≠0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  field_simp
end OAI.CompletedDyadic
