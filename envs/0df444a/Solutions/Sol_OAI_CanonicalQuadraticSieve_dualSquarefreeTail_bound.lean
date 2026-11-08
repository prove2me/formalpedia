-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.dualSquarefreeTail_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:04:36.157583+00:00
-- url     : https://prove2.me/submissions/1bd35e7e-ebe9-41a6-b57c-52a84e32ea45

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DyadicColumns
import Theorems.Thm_OAI_CanonicalQuadraticSieve_squarefreePart_norm_le
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealGenerator_norm_sq
import Theorems.Thm_OAI_CanonicalQuadraticSieve_quadraticRow_norm_le_one
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_lattice_summable_norm
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_lattice_tail
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
import Theorems.Thm_OAI_QuadraticInitialBound_quadraticRow_norm_le_one
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (I J : Ideal O) (W : 𝓢(ℝ, ℂ)) (t K : ℝ), 0 < t → 0 ≤ K →
        ‖dualSquarefreeTail I J W t K‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 t) ^ 2 * (1 + t * K) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro I J W t K ht hK
  let Q := {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)}
  have hgen : Function.Injective (fun lengthScale : Q => idealGenerator lengthScale.val) := by
    intro lengthScale R h
    apply Subtype.ext
    simpa only [span_idealGenerator] using congrArg (fun z : O => Ideal.span {z}) h
  have hlat := paperRadialFourier_lattice_summable_norm W t ht
  have hQ : Summable (fun lengthScale : Q => ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) := by
    have hs := hlat.comp_injective hgen
    simpa only [Function.comp_def, idealGenerator_norm_sq] using hs
  have hp (lengthScale : Q) :
      ‖unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖ ≤
        ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖ := by
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    unfold unrestrictedPairCharacter
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (quadraticRow_norm_le_one I _) (quadraticRow_norm_le_one J _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hnorm : Summable (fun lengthScale : Q =>
      ‖unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hQ
  let f : Q → {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2} := fun lengthScale =>
    ⟨idealGenerator lengthScale.val, by
      rw [idealGenerator_norm_sq]
      apply mul_le_mul_of_nonneg_left _ ht.le
      exact lengthScale.property.2.le.trans (Nat.cast_le.mpr (squarefreePart_norm_le lengthScale.val lengthScale.property.1))⟩
  have hf : Function.Injective f := by
    intro lengthScale R h
    apply hgen
    exact congrArg (fun z : {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2} => z.val) h
  have hi : (∑' lengthScale : Q, ‖paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))‖) ≤
      ∑' z : {z : O // t * K ≤ t * ‖eisEmbedding z‖ ^ 2},
        ‖paperRadialFourier W (t * ‖eisEmbedding z.val‖ ^ 2)‖ := by
    apply hQ.tsum_le_tsum_of_inj f hf (fun _ _ => norm_nonneg _) _ (hlat.subtype _)
    intro lengthScale
    simp only [f, idealGenerator_norm_sq]
    rfl
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_le_tsum hp hQ).trans (hi.trans (hb W t (t * K) ht (mul_nonneg ht.le hK))))
end OAI.CanonicalQuadraticSieve
