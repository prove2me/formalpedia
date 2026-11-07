-- Prove2me | solution 1 for OAI.CoprimeMobiusExtension.disjoint_indicator_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:14:29.550204+00:00
-- url     : https://prove2.me/submissions/afad97c2-d4b2-48e2-bc2d-2dbfe7ef5c81

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
import Theorems.Thm_OAI_CoprimeMobiusExtension_sum_subset_sign
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
    (B S T : Finset ι) (hS : S ⊆ B) (_hT : T ⊆ B) :
    (if Disjoint S T then (1 : ℂ) else 0) =
      ∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
  have hsub : (S ∩ T).powerset ⊆ B.powerset :=
    Finset.powerset_mono.mpr (Finset.inter_subset_left.trans hS)
  have heq : (∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) =
      ∑ D ∈ (S ∩ T).powerset, (-1 : ℂ) ^ D.card := by
    calc
      _ = ∑ D ∈ (S ∩ T).powerset,
            if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
        symm
        apply Finset.sum_subset hsub
        intro D hD hnot
        have hn : ¬(D ⊆ S ∧ D ⊆ T) := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hnot
        simp [hn]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro D hD
        have hh : D ⊆ S ∧ D ⊆ T := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hD
        simp [hh]
  rw [heq, sum_subset_sign]
  simp only [Finset.disjoint_iff_inter_eq_empty]
end OAI.CoprimeMobiusExtension
