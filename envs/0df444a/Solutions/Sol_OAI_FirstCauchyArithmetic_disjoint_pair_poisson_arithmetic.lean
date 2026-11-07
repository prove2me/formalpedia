-- Prove2me | solution 1 for OAI.FirstCauchyArithmetic.disjoint_pair_poisson_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:33:33.94951+00:00
-- url     : https://prove2.me/submissions/afa8f953-d5dc-4b63-898a-1aa73f3f45c0

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Theorems.Thm_OAI_ActualEisensteinCubic_activeExponent_lt_six
import Theorems.Thm_OAI_ActualEisensteinCubic_activeExponent_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_pair_activeSupport
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_GaussGeneratorTransport_canonical_radial_poisson_product
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
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.FirstCauchyArithmetic
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open MixedCrossSeparation GaussGeneratorTransport ConcretePrimeRowBridge EisensteinSchwartzPoisson
namespace OAI.FirstCauchyArithmetic
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (hd : Disjoint S T)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let n := ∏ i : activeSupport S T, p i.val
    (∑' z : O, (star (finiteSquarefreeRow P hg S z) * finiteSquarefreeRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
    ((scale : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      ∑' h : O, paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding n‖ ^ 2) *
        activeGaussRowFactor p hp hinj hg S T 1 h := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let q : activeSupport S T → O := fun i => p i.val
  let hq := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
  let G := canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val) (activeExponent S T)
  have hpz (z : O) : star (finiteSquarefreeRow P hg S z) * finiteSquarefreeRow P hg T z = row z := by
    rw [finiteSquarefreeRow_pair_activeSupport]
    simp [Finset.disjoint_iff_inter_eq_empty.mp hd, rowCoprimeMask, row]
  have hrow1 : row 1 = 1 := by simp [row, finiteSexticRow]
  have ht := canonical_radial_poisson_product q (fun i => hp i.val) hq (fun i => hg i.val)
    (fun i => hc i.val) (activeExponent S T) (activeExponent_ne_zero S T)
    (activeExponent_lt_six S T) W scale hscale
  have hseries : (∑' h : O,
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) *
        activeGaussRowFactor p hp hinj hg S T 1 h) =
      G * ∑' h : O, star (row h) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) := by
    calc
      _ = ∑' h : O, G * (star (row h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2)) := by
        apply tsum_congr
        intro h
        change _ * (G * (row 1 * star (row h))) = _
        rw [hrow1]
        ring
      _ = _ := tsum_mul_left
  rw [hseries]
  calc
    _ = ∑' z : O, row z * W (‖eisEmbedding z‖ ^ 2 / scale) := by
      apply tsum_congr
      intro z
      rw [hpz]
    _ = ((scale : ℂ) * G / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
        ∑' h : O, star (row h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) := ht
    _ = _ := by ring
end OAI.FirstCauchyArithmetic
