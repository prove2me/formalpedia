-- Prove2me | solution 1 for OAI.FirstCauchyArithmetic.quadratic_phase_coprime_ray_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:32:49.489802+00:00
-- url     : https://prove2.me/submissions/5e413dab-d1e4-4b6e-a240-ea3d3c837499

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Theorems.Thm_OAI_RayFourExpansion_quadraticCrossPhase_character_expansion
import Theorems.Thm_OAI_FirstCauchyArithmetic_coprime_pair_sum_reindexed
import Theorems.Thm_OAI_FirstCauchyArithmetic_supportConjugateSum_ray_common
import Theorems.Thm_OAI_FirstCauchyArithmetic_supportConjugateSum_star_ray_common
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
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedCrossSeparation RayFourExpansion
namespace OAI.FirstCauchyArithmetic
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (supportConjugateSum P hg (B \ D)
          (fun U => star (supportRay p r.1 U) * C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D)
          (fun V => supportRay p r.2 V * C₂ (D ∪ V)) h := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  have hcop : Pairwise (Function.onFun IsCoprime P) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hinj.ne hik)
  have hprime (i : ι) : Prime (P i) :=
    Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
  let Z (r : RayCharacter × RayCharacter) (S T : Finset ι) : ℂ :=
    if Disjoint S T then
      star (supportMobius P S * (star (supportRay p r.1 S) * C₁ S) *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * (supportRay p r.2 T * C₂ T) *
        star (finiteSquarefreeRow P hg T h)) else 0
  have ht (S T : Finset ι) :
      (if Disjoint S T then quadraticCrossPhase p hg S T *
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
      ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 * Z r S T := by
    by_cases hd : Disjoint S T
    · rw [if_pos hd, quadraticCrossPhase_character_expansion p hp hcop hg hchar S T hd]
      simp only [Fintype.sum_prod_type, Z, if_pos hd, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [supportRay, star_mul, star_star]
      ring
    · simp [Z, hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 * Z r S T := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => ht S T)
    _ = ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, Z r S T := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : RayCharacter × RayCharacter,
            ∑ T ∈ B.powerset, crossCoeff r.1 r.2 * Z r S T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      change (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        if Disjoint S T then star (supportMobius P S *
          (star (supportRay p r.1 S) * C₁ S) * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * (supportRay p r.2 T * C₂ T) *
            star (finiteSquarefreeRow P hg T h)) else 0) = _
      rw [coprime_pair_sum_reindexed P hprime hinj hg B]
      apply Finset.sum_congr rfl
      intro D hD
      rw [supportConjugateSum_star_ray_common p hg B D C₁ r.1 h,
        supportConjugateSum_ray_common p hg B D C₂ r.2 h]
      simp only [star_mul, star_star]
      ring
end OAI.FirstCauchyArithmetic
