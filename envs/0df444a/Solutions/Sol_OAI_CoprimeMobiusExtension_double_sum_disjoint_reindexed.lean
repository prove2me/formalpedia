-- Prove2me | solution 1 for OAI.CoprimeMobiusExtension.double_sum_disjoint_reindexed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:07.705378+00:00
-- url     : https://prove2.me/submissions/529d98bb-38ab-4a8c-a09b-64a9e0a5e56a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
import Theorems.Thm_OAI_CoprimeMobiusExtension_double_sum_disjoint_expansion
import Theorems.Thm_OAI_CoprimeMobiusExtension_sum_supersets
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
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
open OAI.CoprimeMobiusExtension
namespace OAI.CoprimeMobiusExtension
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset, Z (D ∪ U) (D ∪ V) := by
  rw [double_sum_disjoint_expansion]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hDB := Finset.mem_powerset.mp hD
  calc
    _ = ∑ S ∈ B.powerset, if D ⊆ S then
          (∑ T ∈ B.powerset, if D ⊆ T then Z S T else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hh : D ⊆ S <;> simp [hh]
    _ = _ := by
      rw [sum_supersets B D hDB]
      apply Finset.sum_congr rfl
      intro U hU
      exact sum_supersets B D hDB (Z (D ∪ U))
end OAI.CoprimeMobiusExtension
