-- Prove2me | solution 1 for OAI.CompletedGauss.gaussTwo_eq_canonicalProductGauss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:24:37.910018+00:00
-- url     : https://prove2.me/submissions/b64acb4f-179b-4466-872a-e7467bc00c46

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_IdealMobius
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Theorems.Thm_OAI_CompletedGauss_product_primary
import Theorems.Thm_OAI_CompletedGauss_cubicRow_product_mk
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CompletedGauss_primaryGenerator_span
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk



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
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic
open ActualEisensteinCubic ConcreteTraceCRT
namespace OAI.CompletedGauss
theorem _root_.solution {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (hI : primaryGenerator (Ideal.span {∏ i, p i}) ≠ 0) :
    gaussTwo (Ideal.span {∏ i, p i}) hI =
      FiniteGaussPhase.canonicalProductGauss p hp hcop hgood (fun _ => 2) := by
  have hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hgen := primaryGenerator_span (∏ i, p i) hpall (product_primary p hprimary)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := finite_quotient_span hI
  let : Fintype (O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec (Ideal.span {∏ i, p i}) hI).1
  have hsum :
      (∑ x : O ⧸ Ideal.span {primaryGenerator (Ideal.span {∏ i, p i})},
        cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (primaryGenerator (Ideal.span {∏ i, p i})) hI x) =
      (∑ x : O ⧸ Ideal.span {∏ i, p i},
        (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
          (FiniteGaussPhase.productElementCRT p hcop x i)) *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
            (∏ i, p i) hpall x) := by
    apply Fintype.sum_equiv e.toEquiv
    intro x
    change cubicRow (Ideal.span {∏ i, p i}) hI (e x) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (primaryGenerator (Ideal.span {∏ i, p i})) hI x =
      (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 2)
        (FiniteGaussPhase.productElementCRT p hcop (e x) i)) *
        eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
          (∏ i, p i) hpall (e x)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [e, Ideal.quotEquivOfEq_mk, cubicRow_product_mk p hcop hgood hI,
      FiniteGaussPhase.productElementCRT_mk, eisTraceModChar, IdealGaussCRT.traceModChar_mk, hgen]
  change _ / _ = _ / _
  rw [hsum, hgen]
end OAI.CompletedGauss
