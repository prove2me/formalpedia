-- Prove2me | solution 1 for OAI.FirstCauchyArithmetic.coprime_pair_sum_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:26:22.430565+00:00
-- url     : https://prove2.me/submissions/32248aae-5777-4607-a16a-18b17bb9b810

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Theorems.Thm_OAI_FirstCauchyArithmetic_supportMobius_sq
import Theorems.Thm_OAI_FirstCauchyArithmetic_star_supportMobius
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_self_pair
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_product_moebius
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CoprimeMobiusExtension_double_sum_disjoint_reindexed
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


section
namespace OAI
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
namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase QuadraticGaussRay
open ActualEisensteinCoordinates MixedCrossSeparation
end RayFourExpansion
namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates GaussGeneratorTransport
end MixedCrossSeparation
namespace FirstCauchyArithmetic
section
open ActualEisensteinCubic CoprimeMobiusExtension
private theorem supportMobius_union {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (S T : Finset ι) (hd : Disjoint S T) :
    supportMobius P (S ∪ T) = supportMobius P S * supportMobius P T := by
  simp only [supportMobius, prime_product_moebius P hprime hinj,
    Finset.card_union_of_disjoint hd, pow_add]
private theorem finiteSquarefreeRow_union {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S T : Finset ι) (hd : Disjoint S T) (h : O) :
    finiteSquarefreeRow P hg (S ∪ T) h =
      finiteSquarefreeRow P hg S h * finiteSquarefreeRow P hg T h := by
  exact Finset.prod_union hd
end
section
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedCrossSeparation RayFourExpansion
end
open ActualEisensteinCubic ConcretePrimeRowBridge
end FirstCauchyArithmetic
end
end OAI
end

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
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then
        star (supportMobius P S * C₁ S * star (finiteSquarefreeRow P hg S h)) *
          (supportMobius P T * C₂ T * star (finiteSquarefreeRow P hg T h)) else 0) =
    ∑ D ∈ B.powerset, supportMobius P D * rowCoprimeMask P D h *
      star (supportConjugateSum P hg (B \ D) (fun U => C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D) (fun V => C₂ (D ∪ V)) h := by
  rw [double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  rw [← prime_product_moebius P hprime hinj D]
  change supportMobius P D * _ = _
  have ht (U V : Finset ι) (hU : U ∈ (B \ D).powerset) (hV : V ∈ (B \ D).powerset) :
      star (supportMobius P (D ∪ U) * C₁ (D ∪ U) *
        star (finiteSquarefreeRow P hg (D ∪ U) h)) *
      (supportMobius P (D ∪ V) * C₂ (D ∪ V) *
        star (finiteSquarefreeRow P hg (D ∪ V) h)) =
      rowCoprimeMask P D h *
        star (supportMobius P U * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg U h)) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by
    have hdU : Disjoint D U := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
    have hdV : Disjoint D V := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hV) disjoint_sdiff_self_right
    rw [supportMobius_union P hprime hinj D U hdU,
      supportMobius_union P hprime hinj D V hdV,
      finiteSquarefreeRow_union P hg D U hdU,
      finiteSquarefreeRow_union P hg D V hdV]
    simp only [star_mul, star_star, star_supportMobius]
    have hmu := supportMobius_sq P hprime hinj D
    have hrow := finiteSquarefreeRow_self_pair P hg D h
    calc
      _ = (supportMobius P D * supportMobius P D) *
          (star (finiteSquarefreeRow P hg D h) * finiteSquarefreeRow P hg D h) *
          (finiteSquarefreeRow P hg U h * star (C₁ (D ∪ U)) * supportMobius P U) *
          (supportMobius P V * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg V h)) := by ring
      _ = _ := by rw [hmu, hrow]; ring
  have heq : (∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset,
      star (supportMobius P (D ∪ U) * C₁ (D ∪ U) * star (finiteSquarefreeRow P hg (D ∪ U) h)) *
      (supportMobius P (D ∪ V) * C₂ (D ∪ V) * star (finiteSquarefreeRow P hg (D ∪ V) h))) =
    rowCoprimeMask P D h *
      star (supportConjugateSum P hg (B \ D) (fun U => C₁ (D ∪ U)) h) *
        supportConjugateSum P hg (B \ D) (fun V => C₂ (D ∪ V)) h := by
    simp only [supportConjugateSum, star_sum]
    rw [mul_assoc, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    simpa only [mul_assoc] using ht U V hU hV
  rw [heq]
  ring
end OAI.FirstCauchyArithmetic
