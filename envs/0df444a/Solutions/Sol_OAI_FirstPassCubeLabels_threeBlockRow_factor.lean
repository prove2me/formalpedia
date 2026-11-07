-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.threeBlockRow_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:51:37.286273+00:00
-- url     : https://prove2.me/submissions/8a1d4148-51b9-4549-bb6a-94271144b219

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Theorems.Thm_OAI_FirstPassCubeLabels_blockRow_union
import Theorems.Thm_OAI_FirstPassCubeLabels_blockRow_congr
import Theorems.Thm_OAI_FirstPassCubeLabels_blockRow_one
import Theorems.Thm_OAI_FirstPassCubeLabels_blockRow_five
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
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (u : O) :
    blockRow p hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) u =
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N u) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P u *
      blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
        (fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) u := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  have hN : ∀ i ∈ N, threeBlockExponent N P v ε₁ ε₂ i = 5 := by
    intro i hi; simp [threeBlockExponent, hi]
  have hP : ∀ i ∈ P, threeBlockExponent N P v ε₁ ε₂ i = 1 := by
    intro i hi
    simp [threeBlockExponent, hi, show i ∉ N from fun hn => Finset.disjoint_left.mp hNP hn hi]
  have hC : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, threeBlockExponent N P v ε₁ ε₂ i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    simp [threeBlockExponent,
      show i ∉ N from fun hn => Finset.disjoint_left.mp hNC hn hi,
      show i ∉ P from fun hp => Finset.disjoint_left.mp hPC hp hi]
  rw [blockRow_union p hg (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    blockRow_union p hg N P hNP, blockRow_congr p hg N _ _ hN,
    blockRow_congr p hg P _ _ hP, blockRow_congr p hg _ _ _ hC,
    blockRow_five, blockRow_one]
end OAI.FirstPassCubeLabels
