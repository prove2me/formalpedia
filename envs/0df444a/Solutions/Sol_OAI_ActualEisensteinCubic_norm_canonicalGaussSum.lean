-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.norm_canonicalGaussSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:21:58.622527+00:00
-- url     : https://prove2.me/submissions/151fc86a-c174-42bb-87c6-b5d2be1264a3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Theorems.Thm_OAI_GeneralPrimitiveTrace_eisTraceModChar_breveE_primitive
import Theorems.Thm_OAI_IdealGaussCRT_coordinateAddChar_isPrimitive
import Theorems.Thm_OAI_IdealGaussCRT_norm_gauss_finite_crt_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_ne_one
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_primitive
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
open OAI.ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.ActualEisensteinCubic
theorem _root_.solution {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6) :
    ‖canonicalGaussSum P hcop hgood j‖ = ‖eisEmbedding (finitePrimeModulus P)‖ := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let χ : ∀ i, MulChar (O ⧸ P i) ℂ := fun i => canonicalSextic (P i) (hgood i) ^ j i
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0
  have hχ : ∀ i, χ i ≠ 1 := fun i =>
    canonicalSextic_pow_ne_one (P i) (hgood i) (hchar i) (hj0 i) (hj6 i)
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i)
    e χ ψ hχ (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun i => O ⧸ P i) e ψ hψ i)
  change ‖canonicalGaussSum P hcop hgood j‖ ^ 2 =
    (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq
end OAI.ActualEisensteinCubic
