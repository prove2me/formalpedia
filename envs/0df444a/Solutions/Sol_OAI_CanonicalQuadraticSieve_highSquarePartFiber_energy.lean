-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.highSquarePartFiber_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:24:19.809659+00:00
-- url     : https://prove2.me/submissions/123ed140-6bf7-4bc9-9fb5-dc3f3ae6c978

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_RetainedDualBounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_highSquarePart_fiber_row_bounds
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_quadraticRow_primary_squarefree
import Theorems.Thm_OAI_CanonicalQuadraticSieve_energy_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_family_squared_norm_le
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_nonneg
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_one
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_two
import Theorems.Thm_OAI_CubicEisenstein_spatialTriple_zero
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_FiniteSieveOperator_energy_bound
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
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic QuadraticSquarefreeKernel CompletedGauss
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N K : ℝ) (A : Ideal O)
    (a : idealRange N → ℂ) :
    (∑ I ∈ highSquarePartFiber M K A,
      ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖^2) ≤
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N * ∑ J, ‖a J‖^2 := by
  let S := highSquarePartFiber M K A
  let b : idealRange N → ℂ := fun J => idealZeroMask J.val (primaryGenerator A) * a J
  let B : Matrix S (idealRange N) ℂ := fun I J =>
    quadraticRow J.val (primaryGenerator (squarefreePart I.val))
  have hinj : Function.Injective (fun I : S => squarefreePart I.val) := by
    intro I I' heq
    dsimp only at heq
    apply Subtype.ext
    have hI := (Finset.mem_filter.mp I.property).2
    have hI' := (Finset.mem_filter.mp I'.property).2
    calc
      I.val = A^2 * squarefreePart I.val := by
        simpa only [hI] using (squarePart_sq_mul_squarefreePart I.val).symm
      _ = A^2 * squarefreePart I'.val := by rw [heq]
      _ = I'.val := by simpa only [hI'] using squarePart_sq_mul_squarefreePart I'.val
  have hnorm : ‖FiniteSieveOperator.operator B‖^2 ≤
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N := by
    apply family_squared_norm_le (fun I : S => squarefreePart I.val)
      (fun J : idealRange N => J.val) hinj Subtype.val_injective
    · intro I
      exact highSquarePart_fiber_row_bounds M K A I.val
        (Finset.mem_filter.mp I.property).1 (Finset.mem_filter.mp I.property).2
    · intro J
      exact mem_idealRange.mp J.property
  have hrow (I : S) :
      (∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J) =
      ∑ J : idealRange N, B I J * b J := by
    apply Finset.sum_congr rfl
    intro J _
    have hI := (Finset.mem_filter.mp I.property).2
    have he : I.val = A^2 * squarefreePart I.val := by
      simpa only [hI] using (squarePart_sq_mul_squarefreePart I.val).symm
    rw [he, canonical_quadraticRow_primary_squarefree J.val
      (mem_idealRange.mp J.property).1]
    change _ = quadraticRow J.val (primaryGenerator (squarefreePart I.val)) *
      (idealZeroMask J.val (primaryGenerator A) * a J)
    ring
  have hb (J : idealRange N) : ‖b J‖^2 ≤ ‖a J‖^2 := by
    dsimp only [b]
    unfold idealZeroMask
    split_ifs <;> simp
  rw [← Finset.sum_coe_sort S]
  simp_rw [hrow]
  exact (FiniteSieveOperator.energy_bound B b).trans
    ((mul_le_mul_of_nonneg_right hnorm (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun J _ => hb J)
        (sieveNorm_nonneg _ _)))
end OAI.CanonicalQuadraticSieve
