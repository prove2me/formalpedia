-- Prove2me | solution 1 for OAI.IdealGaussCRT.gauss_transform_finite_ideal_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:02:59.919709+00:00
-- url     : https://prove2.me/submissions/c9970884-d8c3-44b8-aa65-d2d5344f5d8c

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_EisensteinLattice
import Theorems.Thm_OAI_IdealGaussCRT_gauss_transform_finite_crt

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
theorem _root_.solution {ι A : Type*} [Fintype ι] [CommRing A]
    (P : ι → Ideal A) (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, (P i).IsMaximal]
    [Fintype (A ⧸ ∏ i, P i)] [∀ i, Fintype (A ⧸ P i)]
    (χ : ∀ i, MulChar (A ⧸ P i) ℂ)
    (ψ : AddChar (A ⧸ ∏ i, P i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (h : A ⧸ ∏ i, P i) :
    (∑ x : A ⧸ ∏ i, P i, (∏ i, χ i (quotientProdEquivPi P hc x i)) * ψ (h * x)) =
      ∏ i, if quotientProdEquivPi P hc h i = 0 then 0 else
        (χ i (quotientProdEquivPi P hc h i))⁻¹ *
          gaussSum (χ i) (coordinateAddChar (fun i => A ⧸ P i)
            (quotientProdEquivPi P hc) ψ i) := by
  let (i : ι) : Field (A ⧸ P i) := Ideal.Quotient.field (P i)
  exact gauss_transform_finite_crt (fun i => A ⧸ P i)
    (quotientProdEquivPi P hc) χ ψ hχ h
end OAI.IdealGaussCRT
