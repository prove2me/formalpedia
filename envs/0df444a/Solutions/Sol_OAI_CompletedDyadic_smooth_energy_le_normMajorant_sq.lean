-- Prove2me | solution 1 for OAI.CompletedDyadic.smooth_energy_le_normMajorant_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:57:19.457447+00:00
-- url     : https://prove2.me/submissions/2da849bd-863d-4e56-a86c-a29b4c749cfb

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
import Theorems.Thm_OAI_CompletedDyadic_normMajorant_eq

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
    (K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+t*r^3*B^3*U)^(2*A)
      ≤(normMajorant deltaLoss A K t r H U B)^2 := by
  rw [normMajorant_eq deltaLoss A K t r H U B hK ht hr hH hU hB,div_pow,mul_pow,
    mul_pow,mul_pow,mul_pow,Real.sq_sqrt hB.le,Real.sq_sqrt hH.le]
  have hc : 0≤(K*(U*B))^deltaLoss := by positivity
  have hden : 0<(B*r^2*H)*(1+t*r^3*B^3*U)^(2*A) := by positivity
  have hp (x : ℝ) (hx : 0≤x) (s : ℝ) : (x^s)^2=x^(2*s) := by
    rw [←Real.rpow_mul_natCast hx]
    congr 1
    ring
  rw [hp _ (mul_pos hK (mul_pos hU hB)).le,hp _ (by positivity)]
  rw [div_div]
  apply div_le_div_of_nonneg_right _ hden.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hcross : 0≤2*Real.sqrt K*(Real.sqrt U*Real.sqrt B) := by positivity
  nlinarith [Real.sq_sqrt hK.le,Real.sq_sqrt hU.le,Real.sq_sqrt hB.le,
    sq_nonneg (Real.sqrt K+Real.sqrt U*Real.sqrt B)]
end OAI.CompletedDyadic
