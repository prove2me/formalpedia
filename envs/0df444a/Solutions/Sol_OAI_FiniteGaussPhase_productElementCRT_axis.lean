-- Prove2me | solution 1 for OAI.FiniteGaussPhase.productElementCRT_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:09:27.532515+00:00
-- url     : https://prove2.me/submissions/c770f2ec-c9d9-48eb-b6cc-599fd10e01e4

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_bezout_inverse_left
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk

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
open scoped BigOperators Classical
open OAI.FiniteGaussPhase
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.FiniteGaussPhase
theorem _root_.solution {ι : Type*} [Fintype ι]
    (p : ι → O) (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (u v : O) (hbez : u * p i + v * cofactor p i = 1) (x : O) :
    (productElementCRT p hcop).symm (Pi.single i (Ideal.Quotient.mk (Ideal.span {p i}) x)) =
      Ideal.Quotient.mk (Ideal.span {∏ k, p k}) (x * v * cofactor p i) := by
  apply (productElementCRT p hcop).injective
  rw [RingEquiv.apply_symm_apply]
  funext k
  rw [productElementCRT_mk]
  by_cases hk : k = i
  · subst k
    simp only [Pi.single_eq_same, map_mul]
    have hlocal := IdealGaussCRT.bezout_inverse_left hbez
    calc
      Ideal.Quotient.mk (Ideal.span {p i}) x =
          Ideal.Quotient.mk (Ideal.span {p i}) x *
            (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i) *
              Ideal.Quotient.mk (Ideal.span {p i}) v) := by rw [hlocal, mul_one]
      _ = _ := by ring
  · have hd : p k ∣ cofactor p i := Finset.dvd_prod_of_mem p (by simp [hk])
    have hz : Ideal.Quotient.mk (Ideal.span {p k}) (cofactor p i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    simp only [Pi.single_eq_of_ne hk, map_mul, hz, mul_zero]
end OAI.FiniteGaussPhase
