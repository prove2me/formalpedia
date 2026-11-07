-- Prove2me | solution 1 for OAI.GaussGeneratorTransport.squarefreePairPoissonKernel_eq_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:29:43.771856+00:00
-- url     : https://prove2.me/submissions/47397074-b932-45dc-9263-609be00f2e52

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Theorems.Thm_OAI_GaussGeneratorTransport_gauss_weighted_finite_radial_sum_transport
import Theorems.Thm_OAI_GaussGeneratorTransport_finitePrimeModulus_norm_eq_product
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
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
open OAI.GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
namespace OAI.GaussGeneratorTransport
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) :
    squarefreePairPoissonKernel (fun i => Ideal.span {p i}) hinj hgood S T W scale =
      squarefreePairProductPoissonKernel p hp hinj hgood S T W scale := by
  let q : activeSupport S T → O := fun i => p i.val
  let Q := activePrimes (fun i => Ideal.span {p i}) S T
  let hQ := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  let hg : ∀ i : activeSupport S T, lambda ∉ Q i := fun i => hgood i.val
  let j := activeExponent S T
  let row := finiteSexticRow Q hg j
  let n := ∏ i, q i
  let a : Finset ι → ℂ := fun E =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * row d /
      (‖eisEmbedding d‖ ^ 2 : ℝ)
  let F : Finset ι → ℝ → ℂ := fun E t =>
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    paperRadialFourier W (scale * t / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))
  have hc : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    finitePrimeModulus_norm_eq_product q
  unfold squarefreePairPoissonKernel squarefreePairProductPoissonKernel
  dsimp only
  change ((scale : ℂ) * canonicalNormalizedGauss Q hQ hg j /
      (‖eisEmbedding (finitePrimeModulus Q)‖ : ℂ)) * _ = _
  rw [hc]
  change ((scale : ℂ) * canonicalNormalizedGauss Q hQ hg j / (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2)) =
    ((scale : ℂ) * canonicalProductGauss q (fun i => hp i.val) hQ hg j /
      (‖eisEmbedding n‖ : ℂ)) *
      (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2))
  have ht := gauss_weighted_finite_radial_sum_transport q (fun i => hp i.val)
    hQ hg j (S ∩ T).powerset a F
  calc
    _ = ((scale : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ hg j *
          (∑ E ∈ (S ∩ T).powerset, a E * ∑' h : O, star (row h) * F E (‖eisEmbedding h‖ ^ 2))) := by ring
    _ = _ := by rw [ht]; ring
end OAI.GaussGeneratorTransport
