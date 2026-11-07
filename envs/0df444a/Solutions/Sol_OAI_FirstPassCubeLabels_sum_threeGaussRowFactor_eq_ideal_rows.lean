-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.sum_threeGaussRowFactor_eq_ideal_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:04:22.970074+00:00
-- url     : https://prove2.me/submissions/9117c3f7-3ead-4e2b-8f34-bcd4e04f19d5

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Theorems.Thm_OAI_FirstPassCubeLabels_threeGaussRowFactor_eq_ray_columns
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstCauchyArithmetic_quadratic_phase_reindex_to_ideal_rows
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
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport firstPassColumnMinus firstPassColumnPlus)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (R B : Finset ι) (hRB : Disjoint R B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg R
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d) h := by
  let A := cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ C₁ d
  let C := cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ C₂ d
  have hsum :
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        quadraticCrossPhase p hg N P *
          star (supportMobius (fun i => Ideal.span {p i}) N * A N *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N h)) *
          (supportMobius (fun i => Ideal.span {p i}) P * C P *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg P h)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N hN
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hd : Disjoint N P
    · rw [if_pos hd, if_pos hd,
        threeGaussRowFactor_eq_ray_columns p hp hcop hg hc hpr N P B hd
          (hRB.mono_left (Finset.mem_powerset.mp hN))
          (hRB.mono_left (Finset.mem_powerset.mp hP))]
      dsimp only [A, C]
      ring
    · simp [hd]
  rw [hsum]
  congr 1
  exact FirstCauchyArithmetic.quadratic_phase_reindex_to_ideal_rows p hp hinj hg hc R A C h
end OAI.FirstPassCubeLabels
