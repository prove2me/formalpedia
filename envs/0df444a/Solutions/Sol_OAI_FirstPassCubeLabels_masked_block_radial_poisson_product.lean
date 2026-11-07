-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.masked_block_radial_poisson_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:48:06.16819+00:00
-- url     : https://prove2.me/submissions/24c62eb5-d7d6-44d4-99ff-8ad0480a6207

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (columnPrimeCoprime quadraticCrossPhase)
open FiniteGaussPhase (canonicalProductGauss)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z * blockRow p hg S e z *
      W (‖eisEmbedding z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) * canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) /
        (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * blockRow p hg S e d /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, star (blockRow p hg S e h) * paperRadialFourier W
            (lengthScale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2)) := by
  let Q := fun i : S => Ideal.span {p i.val}
  let q := fun i : S => p i.val
  let hQ := columnPrimeCoprime p hcop S
  let j := fun i : S => e i.val
  have h := canonical_masked_radial_poisson_collected (fun i => Ideal.span {p i}) hinj M
    Q hQ (fun i => hg i.val) (fun i => hc i.val) j
    (fun i => he i.val i.property) (fun i => he6 i.val i.property) W lengthScale hL
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding (∏ i ∈ S, p i)‖ := by
    rw [GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q, Finset.prod_coe_sort]
  dsimp only at h
  rw [hn] at h
  have hrow : finiteSexticRow Q (fun i => hg i.val) j = blockRow p hg S e := rfl
  rw [hrow] at h
  rw [h]
  let a := fun E : Finset ι =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * blockRow p hg S e d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)
  let F := fun E : Finset ι => fun t : ℝ =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    paperRadialFourier W (lengthScale * t / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2))
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset a F
  rw [hrow] at ht
  change ((lengthScale : ℂ) * canonicalNormalizedGauss Q hQ (fun i => hg i.val) j /
      (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) * _ = _
  calc
    _ = ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
        ∑ E ∈ M.powerset, a E * ∑' h : O, star (blockRow p hg S e h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [ht]; ring
end OAI.FirstPassCubeLabels
