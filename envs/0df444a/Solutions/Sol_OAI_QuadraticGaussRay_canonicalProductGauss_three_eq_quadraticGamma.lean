-- Prove2me | solution 1 for OAI.QuadraticGaussRay.canonicalProductGauss_three_eq_quadraticGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:23:34.192429+00:00
-- url     : https://prove2.me/submissions/d06737ea-2678-4418-acfb-a8dd6b8de376

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Theorems.Thm_OAI_IdealGaussCRT_quadratic_gauss_finite_crt_eq_square_sum
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_three_quadratic
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_GeneralPrimitiveTrace_eisTraceModChar_breveE_primitive
import Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_primitive


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
open OAI.QuadraticGaussRay
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
namespace OAI.QuadraticGaussRay
theorem _root_.solution
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticGammaO (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let e := productElementCRT p hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ Ideal.span {p i}) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) hchar
end OAI.QuadraticGaussRay
