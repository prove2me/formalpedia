-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.gaussBlock_three_cube_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:47:32.552587+00:00
-- url     : https://prove2.me/submissions/7f55bd18-e740-4638-b3a6-f850a440cae6

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Theorems.Thm_OAI_FirstPassCubeLabels_blockCross_union_left
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_gaussBlock_congr
import Theorems.Thm_OAI_FirstPassCubeLabels_gaussBlock_union
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_MixedCrossSeparation_mixed_cross_eq_quadratic
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
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    gaussBlock p hp hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P * mixedCubeCross p hg N B v ε₁ ε₂ true *
        mixedCubeCross p hg P B v ε₁ ε₂ false := by
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hNC : Disjoint N C := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P C := hPB.mono_right (Finset.filter_subset _ _)
  have hNPC : Disjoint (N ∪ P) C := Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩
  have hN (i : ι) (hi : i ∈ N) : e i = 5 := by simp [e, threeBlockExponent, hi]
  have hP (i : ι) (hi : i ∈ P) : e i = 1 := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNP h hi
    simp [e, threeBlockExponent, hn, hi]
  have hC (i : ι) (hi : i ∈ C) : e i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNC h hi
    have hp' : i ∉ P := fun h => Finset.disjoint_left.mp hPC h hi
    simp [e, threeBlockExponent, hn, hp']
  have hcrossNP : blockCross p hg N P e = quadraticCrossPhase p hg N P := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hP k hk, pow_one]
    exact MixedCrossSeparation.mixed_cross_eq_quadratic p hg i k (hpr i) (hpr k)
  have hcrossNC : blockCross p hg N C e = mixedCubeCross p hg N B v ε₁ ε₂ true := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hC k hk]
    rfl
  have hcrossPC : blockCross p hg P C e = mixedCubeCross p hg P B v ε₁ ε₂ false := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hP i hi, hC k hk]
    rfl
  change gaussBlock p hp hg ((N ∪ P) ∪ C) e = _
  rw [gaussBlock_union p hp hg (N ∪ P) C hNPC, gaussBlock_union p hp hg N P hNP,
    blockCross_union_left p hg N P C hNP,
    gaussBlock_congr p hp hg N e (fun _ => 5) hN,
    gaussBlock_congr p hp hg P e (fun _ => 1) hP,
    gaussBlock_congr p hp hg C e _ hC, hcrossNP, hcrossNC, hcrossPC]
  ring
end OAI.FirstPassCubeLabels
