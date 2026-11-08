-- Prove2me | solution 1 for OAI.SecondPassArithmetic.global_second_energy_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:30:34.042107+00:00
-- url     : https://prove2.me/submissions/18b33bb2-cd53-49bc-b959-5dfd8d2f58cc

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MaskedPrincipalBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_GlobalEncoding
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalNormalization
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondLabelUnit_spec
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_DescentWeightedCauchy_bounded_energy_pushforward
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecond_fiber_card
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.spatialTriple_one
attribute [local simp] OAI.CubicEisenstein.spatialTriple_two
attribute [local simp] OAI.CubicEisenstein.spatialTriple_zero
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.FirstPassCubeLabels.coreRayTwist_prod
attribute [local simp] OAI.FirstPassCubeLabels.twisted_core_product
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_apply
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_norm
attribute [local simp] OAI.JointLogSeparation.frequencyTwist_twice
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_apply
attribute [local simp] OAI.QuadraticInitialBound.annularSieveCutoff_zero
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newLabel
attribute [local simp] OAI.SecondPassArithmetic.secondSupportTuple_newRow
attribute [local simp] OAI.SecondPassIntegration.conjugateProfile_apply



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
open scoped BigOperators
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open ConcretePrimeRowBridge (idealGenerator)
attribute [local instance] OAI.SecondPassArithmetic._p2m_local_instance_e2c0b3c9fb_81
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Finset (GlobalSecondData ι)) (t : Finset (Ideal O × O))
      (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
      (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈t) →
      (∀ z∈t,z.1 ≠ ⊥) → (∀ z∈t,(Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x∈s,‖w x‖ ≤ B) →
      (∑ x∈s,‖w x‖ * ‖fixedChildRow p hp hcop hg F Ψ m H (globalSecondLabel p x)
        (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖^2) ≤
      B*C*(lengthScale*Ideal.absNorm q.1)^ε *
        ∑ u : Oˣ,∑ z∈t,‖idealChildRow p hp hcop hg F Ψ m H negative u z‖^2 := by
  obtain ⟨C,hC,hcard⟩ := globalSecond_fiber_card p hinj ε hε
  refine ⟨C,hC,?_⟩
  intro s t q w B lengthScale F Ψ m H negative hq hB hL hs hfixed hmap ht hnorm hw
  let f : GlobalSecondData ι → Oˣ × (Ideal O × O) := fun x =>
    (globalSecondLabelUnit p x,newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))
  let P : Oˣ × (Ideal O × O) → ℂ := fun z => idealChildRow p hp hcop hg F Ψ m H negative z.1 z.2
  have hm : ∀ x∈s,f x∈Finset.univ ×ˢ t := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,hmap x hx⟩
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward s (Finset.univ ×ˢ t) f w P B hm hw
  have he : (∑ x∈s,‖w x‖ * ‖fixedChildRow p hp hcop hg F Ψ m H (globalSecondLabel p x)
      (if negative then -newRow (globalSecondTuple p x) else newRow (globalSecondTuple p x))‖^2) =
      ∑ x∈s,‖w x‖ * ‖P (f x)‖^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [globalSecondLabelUnit_spec p x]
    rfl
  rw [he]
  apply hpush.trans
  calc
    _ ≤ ∑ z∈Finset.univ ×ˢ t,B*C*(lengthScale*Ideal.absNorm q.1)^ε * ‖P z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      have hzt := (Finset.mem_product.mp hz).2
      have hc := hcard (s.filter (fun x => f x=z)) q z.2.1 z.2.2
        (fun x hx => hs x (Finset.mem_filter.mp hx).1) (ht z.2 hzt) hq
        (fun x hx => hfixed x (Finset.mem_filter.mp hx).1)
        (fun x hx => congrArg (fun z : Oˣ × (Ideal O × O) => z.2.1) (Finset.mem_filter.mp hx).2)
        (fun x hx => congrArg (fun z : Oˣ × (Ideal O × O) => z.2.2) (Finset.mem_filter.mp hx).2)
      have hn : (Ideal.absNorm z.2.1 : ℝ)*Ideal.absNorm q.1 ≤ lengthScale*Ideal.absNorm q.1 :=
        mul_le_mul_of_nonneg_right (hnorm z.2 hzt) (by positivity)
      have hc' := hc.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hn hε.le) hC.le)
      have hfinal := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' hB) (sq_nonneg ‖P z‖)
      simpa only [mul_assoc] using hfinal
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_product]
end OAI.SecondPassArithmetic
