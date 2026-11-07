-- Prove2me | solution 1 for OAI.FiniteGaussPhase.normalizedProductTraceGauss_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:21:59.413195+00:00
-- url     : https://prove2.me/submissions/ce88b63d-29b2-4d36-b47d-633e56624020

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_FiniteGaussPhase_gauss_sum_product_element
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span


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
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    normalizedProductTraceGauss p hp hcop χ =
      ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i)) *
        ConcreteBreveE.normalizedTraceGauss (p i) (hp i) (χ i) := by
  let hpall : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hpall
  let : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  let (i : ι) : Finite (O ⧸ Ideal.span {p i}) := finite_quotient_span (hp i)
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have hn : (‖eisEmbedding (∏ i, p i)‖ : ℂ) = ∏ i, (‖eisEmbedding (p i)‖ : ℂ) := by
    rw [map_prod, norm_prod]
    norm_cast
  change (∑ x : O ⧸ Ideal.span {∏ i, p i},
    (∏ i, χ i (productElementCRT p hcop x i)) *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (∏ i, p i) hpall x) / (‖eisEmbedding (∏ i, p i)‖ : ℂ) = _
  rw [gauss_sum_product_element p hp hcop χ, hn, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change (_ * _) / _ = _ * (_ / _)
  ring
end OAI.FiniteGaussPhase
