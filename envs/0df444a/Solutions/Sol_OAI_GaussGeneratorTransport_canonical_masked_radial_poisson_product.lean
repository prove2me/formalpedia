-- Prove2me | solution 1 for OAI.GaussGeneratorTransport.canonical_masked_radial_poisson_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:05.191196+00:00
-- url     : https://prove2.me/submissions/790ee2f9-74d4-4611-83ce-9a835d674dae

import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_CubicJacobi
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_RamifiedSymbol
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_masked_radial_poisson_collected
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_GaussGeneratorTransport_finitePrimeModulus_norm_eq_product
import Theorems.Thm_OAI_GaussGeneratorTransport_gauss_weighted_finite_radial_sum_transport
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



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
open scoped BigOperators Classical SchwartzMap
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
namespace OAI.GaussGeneratorTransport
theorem _root_.solution
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z * finiteSexticRow (fun i => Ideal.span {p i}) hg j z *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    ((M : ℂ) * canonicalProductGauss p hp hcop hg j / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator R E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
          finiteSexticRow (fun i => Ideal.span {p i}) hg j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by
  have ht := canonical_masked_radial_poisson_collected R hinj S
    (fun i => Ideal.span {p i}) hcop hg hchar j hj0 hj6 W M hM
  dsimp only at ht
  rw [finitePrimeModulus_norm_eq_product p] at ht
  rw [ht]
  let a : Finset α → ℂ := fun E =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
      finiteSexticRow (fun i => Ideal.span {p i}) hg j (primeSubsetGenerator R E) /
      (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 : ℝ)
  let F : Finset α → ℝ → ℂ := fun E t => paperRadialFourier W
    (M * t / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  have hu := gauss_weighted_finite_radial_sum_transport p hp hcop hg j S.powerset a F
  change ((M : ℂ) * canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j /
      (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (∑ E ∈ S.powerset, a E * ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          F E (‖eisEmbedding h‖ ^ 2)) = _
  calc
    _ = ((M : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j *
        ∑ E ∈ S.powerset, a E * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [hu]; ring
end OAI.GaussGeneratorTransport
