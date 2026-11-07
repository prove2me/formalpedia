-- Prove2me | solution 1 for OAI.FirstCauchyArithmetic.finite_phase_coprime_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:33:22.081206+00:00
-- url     : https://prove2.me/submissions/d5f4be89-3450-4c9d-aced-478c26e4b517

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Theorems.Thm_OAI_FirstCauchyArithmetic_coprime_pair_sum_reindexed
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
open OAI.FirstCauchyArithmetic
open ActualEisensteinCubic CoprimeMobiusExtension
namespace OAI.FirstCauchyArithmetic
theorem _root_.solution
    {ι R : Type*} [DecidableEq ι] [Fintype R] [DecidableEq R]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι)
    (σ : Finset ι → R) (phase : R → R → ℂ) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then phase (σ S) (σ T) *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : R × R, phase r.1 r.2 *
      ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
        star (supportConjugateSum P hg (B \ D)
          (fun U => if σ (D ∪ U) = r.1 then C₁ (D ∪ U) else 0) h) *
        supportConjugateSum P hg (B \ D)
          (fun V => if σ (D ∪ V) = r.2 then C₂ (D ∪ V) else 0) h := by
  let Z (r : R × R) (S T : Finset ι) : ℂ :=
    if Disjoint S T then
      star (supportMobius P S * (if σ S = r.1 then C₁ S else 0) *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * (if σ T = r.2 then C₂ T else 0) *
        star (finiteSquarefreeRow P hg T h)) else 0
  have ht (S T : Finset ι) :
      (if Disjoint S T then phase (σ S) (σ T) *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
      ∑ r : R × R, phase r.1 r.2 * Z r S T := by
    by_cases hd : Disjoint S T
    · simp only [Z, if_pos hd, Fintype.sum_prod_type]
      simp only [ mul_zero, ite_mul, zero_mul, apply_ite, star_zero]
      simp
      ring
    · simp [Z, hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        ∑ r : R × R, phase r.1 r.2 * Z r S T := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => ht S T)
    _ = ∑ r : R × R, phase r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, Z r S T := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : R × R,
            ∑ T ∈ B.powerset, phase r.1 r.2 * Z r S T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      exact coprime_pair_sum_reindexed P hprime hinj hg B
        (fun S => if σ S = r.1 then C₁ S else 0)
        (fun T => if σ T = r.2 then C₂ T else 0) h
end OAI.FirstCauchyArithmetic
