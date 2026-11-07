-- Prove2me | solution 1 for OAI.MixedCrossSeparation.quadraticBlock_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:12:43.09519+00:00
-- url     : https://prove2.me/submissions/4e452571-a8fe-4a45-8b0b-5148d98cbaf0

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SquarePhaseFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_MixedConversion
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CrossSeparation
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
open OAI.MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates
namespace OAI.MixedCrossSeparation
theorem _root_.solution
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticBlock p hp hg (A ∪ B) = quadraticBlock p hp hg A *
      quadraticBlock p hp hg B * quadraticCrossPhase p hg A B := by
  let x := crossSymbol p hg
  let l := fun i => localGauss (p i) (hp i) (hg i) 3
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ (A ∪ B).erase i, x i k ^ 3) =
        (∏ k ∈ A.erase i, x i k ^ 3) * (∏ k ∈ B, x i k ^ 3) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : (A ∪ B).erase i = A.erase i ∪ B := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ (A ∪ B).erase i, x i k ^ 3) =
        (∏ k ∈ B.erase i, x i k ^ 3) * (∏ k ∈ A, x i k ^ 3) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : (A ∪ B).erase i = B.erase i ∪ A := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 3) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ 3) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ 3) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ 3) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  change (∏ i ∈ A ∪ B, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) = _
  rw [Finset.prod_union hd, hpA, hpB, Finset.prod_comm (s := B) (t := A)]
  unfold quadraticBlock quadraticCrossPhase
  simp only [Finset.prod_mul_distrib]
  dsimp only [x, l]
  ring
end OAI.MixedCrossSeparation
