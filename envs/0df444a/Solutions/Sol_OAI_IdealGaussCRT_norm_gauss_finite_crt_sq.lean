-- Prove2me | solution 1 for OAI.IdealGaussCRT.norm_gauss_finite_crt_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:05:50.132504+00:00
-- url     : https://prove2.me/submissions/5ae25939-2c9a-4257-80ae-f3ba9d4bfdbc

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_gauss_transform_finite_crt
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftGauss_norm_gaussSum_eq_sqrt_card
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.IdealGaussCRT
namespace OAI.IdealGaussCRT
theorem _root_.solution {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1)
    (hψ : ∀ i, (coordinateAddChar R e ψ i).IsPrimitive) :
    ‖∑ x : T, (∏ i, χ i (e x i)) * ψ x‖ ^ 2 = (Fintype.card T : ℝ) := by
  classical
  have hbase := gauss_transform_finite_crt R e χ ψ hχ (1 : T)
  simp only [one_mul, map_one, Pi.one_apply, one_ne_zero, ↓reduceIte,
    inv_one, one_mul] at hbase
  rw [hbase, norm_prod, ← Finset.prod_pow]
  have hlocal (i : ι) : ‖gaussSum (χ i) (coordinateAddChar R e ψ i)‖ ^ 2 =
      (Fintype.card (R i) : ℝ) := by
    rw [ShortDraftGauss.norm_gaussSum_eq_sqrt_card (χ i)
      (coordinateAddChar R e ψ i) (hχ i) (hψ i), Real.sq_sqrt (by positivity)]
  simp_rw [hlocal]
  rw [Fintype.card_congr e.toEquiv, Fintype.card_pi, Nat.cast_prod]
end OAI.IdealGaussCRT
