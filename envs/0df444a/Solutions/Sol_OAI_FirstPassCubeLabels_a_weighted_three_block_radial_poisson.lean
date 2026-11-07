-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.a_weighted_three_block_radial_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:18:16.661874+00:00
-- url     : https://prove2.me/submissions/12ac7aa6-d21a-4bb8-9fc3-a37220521085

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Theorems.Thm_OAI_FirstPassCubeLabels_masked_block_radial_poisson_product
import Theorems.Thm_OAI_FirstPassCubeLabels_threeGaussRowFactor_eq_transformedPair
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
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
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (M N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
    let e := threeBlockExponent N P v ε₁ ε₂
    star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
      (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z * blockRow p hg S e z *
        W (‖eisEmbedding z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, paperRadialFourier W
            (lengthScale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i ∈ S, p i)‖ ^ 2)) *
              cubeTransformedPair p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  dsimp only
  have he : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i ≠ 0 := by
    intro i hi
    by_cases hn : i ∈ N
    · simp [threeBlockExponent, hn]
    by_cases hp' : i ∈ P
    · simp [threeBlockExponent, hn, hp']
    · have hiC : i ∈ cubeActiveSupport B v ε₁ ε₂ := by simpa [hn, hp'] using hi
      simp only [threeBlockExponent, if_neg hn, if_neg hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  have he6 : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i < 6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hcop hg hc M _ _ he he6 W lengthScale hL]
  simp_rw [← threeGaussRowFactor_eq_transformedPair p hp hcop hg hc hpr N P B hNP hNB hPB]
  simp only [Finset.mul_sum, ← tsum_mul_left]
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro h
  unfold threeGaussRowFactor
  dsimp only
  ring
end OAI.FirstPassCubeLabels
