-- Prove2me | solution 1 for OAI.DescentFiberCost.fixed_triple_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:15:41.824591+00:00
-- url     : https://prove2.me/submissions/e6c595e0-2ee0-4b53-8f31-9afec76b39f1

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MainTermDifference
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_InverseContour
import Theorems.Thm_OAI_DescentFiberCost_finite_ideal_count_real
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
open OAI.DescentFiberCost
open scoped BigOperators Classical
open ConcretePrimeRowBridge
namespace OAI.DescentFiberCost
theorem _root_.solution
    (s : Finset (Ideal O × Ideal O × Ideal O)) (B T W : ℝ)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hW : 1 ≤ W)
    (hpos : ∀ x ∈ s, x.1 ≠ ⊥ ∧ x.2.1 ≠ ⊥ ∧ x.2.2 ≠ ⊥)
    (hN : ∀ x ∈ s, (Ideal.absNorm x.1 : ℝ) ≤ B ∧
      (Ideal.absNorm x.2.1 : ℝ) ≤ T ∧ (Ideal.absNorm x.2.2 : ℝ) ≤ W) :
    (s.card : ℝ) ≤ 128 ^ 3 * B * T * W := by
  let a := s.image Prod.fst
  let b := s.image (fun x => x.2.1)
  let c := s.image (fun x => x.2.2)
  have hsub : s ⊆ a ×ˢ (b ×ˢ c) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩⟩
  have ha : (a.card : ℝ) ≤ 128 * B := by
    apply finite_ideal_count_real a B hB
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).1
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).1
  have hb : (b.card : ℝ) ≤ 128 * T := by
    apply finite_ideal_count_real b T hT
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).2.1
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).2.1
  have hc : (c.card : ℝ) ≤ 128 * W := by
    apply finite_ideal_count_real c W hW
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hpos x hx).2.2
    · intro I hI
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hI
      exact (hN x hx).2.2
  have hs : (s.card : ℝ) ≤ (a.card : ℝ) * ((b.card : ℝ) * c.card) := by
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_product] at hcard
    exact_mod_cast hcard
  apply hs.trans
  calc
    _ ≤ (128 * B) * ((128 * T) * (128 * W)) := by gcongr
    _ = _ := by ring
end OAI.DescentFiberCost
