-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.a_weighted_three_cube_gauss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:54:53.075577+00:00
-- url     : https://prove2.me/submissions/1adfbfda-aa3e-43fe-9a40-f85a30f31458

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_UniformKernelBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Theorems.Thm_OAI_FirstPassCubeLabels_canonicalProductGauss_three_cube_partition
import Theorems.Thm_OAI_FirstPassCubeLabels_gaussBlock_eq_mobius_converted
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstCauchyArithmetic_star_supportMobius
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_false
import Theorems.Thm_OAI_MixedCrossSeparation_columnCoefficient_cancel_true
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
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) :
    star (MixedCrossSeparation.columnCoefficient p hp hcop hg N * C₁ N) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P * C₂ P) *
      canonicalProductGauss
        (fun i : ↥((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) => p i.val)
        (fun i => hp i.val) (columnPrimeCoprime p hcop _) (fun i => hg i.val)
        (fun i => threeBlockExponent N P v ε₁ ε₂ i.val) =
    (gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
      quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) *
      star (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
        FirstCauchyArithmetic.firstPassColumnMinus p hp hcop hg C₁ (crtLabel p B v ε₁ ε₂ true) N) *
      (FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
        FirstCauchyArithmetic.firstPassColumnPlus p hp hcop hg C₂ (crtLabel p B v ε₁ ε₂ false) P) := by
  rw [canonicalProductGauss_three_cube_partition p hp hcop hg hpr N P B hNP hNB hPB]
  have hconvN := gaussBlock_eq_mobius_converted p hp hcop hg hc hpr N true
  have hconvP := gaussBlock_eq_mobius_converted p hp hcop hg hc hpr P false
  simp only [Bool.false_eq_true, ↓reduceIte] at hconvN hconvP
  rw [hconvN, hconvP]
  have hn := MixedCrossSeparation.columnCoefficient_cancel_true p hp hcop hg hc hpr N
  have hp' := MixedCrossSeparation.columnCoefficient_cancel_false p hp hcop hg hc hpr P
  simp only [FirstCauchyArithmetic.firstPassColumnMinus, FirstCauchyArithmetic.firstPassColumnPlus,
    star_mul, star_star, FirstCauchyArithmetic.star_supportMobius]
  calc
    _ = (star (MixedCrossSeparation.columnCoefficient p hp hcop hg N) *
        MixedCrossSeparation.convertedColumnBlock p hp hg N true) *
      (MixedCrossSeparation.columnCoefficient p hp hcop hg P *
        MixedCrossSeparation.convertedColumnBlock p hp hg P false) *
      (star (C₁ N) * C₂ P *
        FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) N *
        FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) P *
        gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
          (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
        quadraticCrossPhase p hg N P *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
        star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (crtLabel p B v ε₁ ε₂ true)) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P (crtLabel p B v ε₁ ε₂ false)) := by ring
    _ = _ := by rw [hn, hp']; ring
end OAI.FirstPassCubeLabels
