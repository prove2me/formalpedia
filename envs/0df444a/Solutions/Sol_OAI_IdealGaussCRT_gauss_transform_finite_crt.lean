-- Prove2me | solution 1 for OAI.IdealGaussCRT.gauss_transform_finite_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:42.803354+00:00
-- url     : https://prove2.me/submissions/763941ff-01d1-4122-b49e-7e144052a6ab

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Theorems.Thm_OAI_IdealGaussCRT_addChar_finite_crt_factor
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftFiniteGaussFourier_product_gauss_transform
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
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
open OAI.IdealGaussCRT
namespace OAI.IdealGaussCRT
theorem _root_.solution {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      ∏ i, if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
  classical
  calc
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
        ∑ x : T, ∏ i, χ i (e x i) *
          coordinateAddChar R e ψ i (e h i * e x i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ (h * x)]
      simp only [map_mul, Pi.mul_apply, Finset.prod_mul_distrib]
    _ = ∑ x : ∀ i, R i, ∏ i, χ i (x i) *
          coordinateAddChar R e ψ i (e h i * x i) :=
      Equiv.sum_comp e.toEquiv (fun z : ∀ i, R i =>
        ∏ i, χ i (z i) * coordinateAddChar R e ψ i (e h i * z i))
    _ = _ := ShortDraftFiniteGaussFourier.product_gauss_transform
      R χ (coordinateAddChar R e ψ) hχ (e h)
end OAI.IdealGaussCRT
