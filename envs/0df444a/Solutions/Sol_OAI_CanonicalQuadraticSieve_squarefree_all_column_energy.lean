-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.squarefree_all_column_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:21:34.652653+00:00
-- url     : https://prove2.me/submissions/bac63c21-9acb-42a0-88dc-6bfc0c266a8e

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_quadraticRow_argument_mul
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_quadraticRow_star
import Theorems.Thm_OAI_CanonicalQuadraticSieve_energy_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_family_squared_norm_le
import Theorems.Thm_OAI_CanonicalQuadraticSieve_fixedBadPrimes_card
import Theorems.Thm_OAI_CanonicalQuadraticSieve_fixedBadPrimes_powerset_card
import Theorems.Thm_OAI_CanonicalQuadraticSieve_goodSquarefreePart_injective_on_sector
import Theorems.Thm_OAI_CanonicalQuadraticSieve_goodSquarefreePart_mem_idealRange
import Theorems.Thm_OAI_CanonicalQuadraticSieve_quadraticRow_norm_le_one
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sector_bad_good_product
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
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
import Theorems.Thm_OAI_FiniteSieveOperator_operator_conjTranspose_norm
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
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
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
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.append_first
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.first_append
attribute [local simp] OAI.SecondPassArithmetic.GlobalSecondData.source_append
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
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hinj : Function.Injective cols) (X K : ℝ)
    (hcols : ∀j,Squarefree (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤X) (a : n → ℂ) :
    (∑k : idealRange K,‖∑j,quadraticRow k.val (primaryGenerator (cols j))*a j‖^2)≤
      4*sieveNorm X K*∑j,‖a j‖^2 := by
  classical
  let sector (E : fixedBadPrimes.powerset) := {j : n // badPrimeSector (cols j)=E}
  have hsector (E : fixedBadPrimes.powerset) :
      (∑k : idealRange K,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2)≤
        sieveNorm X K*∑j : sector E,‖a j.val‖^2 := by
    let good : sector E → Ideal O := fun j => goodSquarefreePart (cols j.val)
    have hg : Function.Injective good := by
      intro i j hij
      apply Subtype.ext
      apply hinj
      exact goodSquarefreePart_injective_on_sector _ _ (hcols i.val).1 (hcols j.val).1
        (i.property.trans j.property.symm) hij
    have hgood (j : sector E) : Admissible (good j) ∧ (Ideal.absNorm (good j):ℝ)≤X :=
      mem_idealRange.mp (goodSquarefreePart_mem_idealRange _ (hcols j.val).1 X (hcols j.val).2)
    let B : Matrix (sector E) (idealRange K) ℂ := fun j k => quadraticRow k.val (primaryGenerator (good j))
    have hB := family_squared_norm_le good (fun k : idealRange K => k.val) hg Subtype.val_injective X K
      hgood (fun k => mem_idealRange.mp k.property)
    change ‖FiniteSieveOperator.operator B‖^2≤sieveNorm X K at hB
    have hBT : B.conjTranspose=(fun k j => quadraticRow k.val (primaryGenerator (good j))) := by
      ext k j
      exact canonical_quadraticRow_star _ (mem_idealRange.mp k.property).1 _
    have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun j : sector E => a j.val)
    rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
    have hrow (k : idealRange K) :
        (∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val)=
          quadraticRow k.val (primaryGenerator (sectorBadIdeal E))*
          ∑j : sector E,quadraticRow k.val (primaryGenerator (good j))*a j.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj := sector_bad_good_product (cols j.val) (hcols j.val).1 E j.property
      have hq : quadraticRow k.val (primaryGenerator (cols j.val))=
          quadraticRow k.val (primaryGenerator (sectorBadIdeal E))*quadraticRow k.val (primaryGenerator (good j)) := by
        conv_lhs => rw [←hj]
        rw [primaryGenerator_mul,canonical_quadraticRow_argument_mul _ (mem_idealRange.mp k.property).1]
      rw [hq]
      ring
    have hpoint (k : idealRange K) :
        ‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2≤
          ‖∑j : sector E,quadraticRow k.val (primaryGenerator (good j))*a j.val‖^2 := by
      rw [hrow,norm_mul]
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    exact (Finset.sum_le_sum (fun k _ => hpoint k)).trans
      (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))
  have hpoint (k : idealRange K) :
      ‖∑j,quadraticRow k.val (primaryGenerator (cols j))*a j‖^2≤
        4*∑E : fixedBadPrimes.powerset,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 := by
    rw [←Fintype.sum_fiberwise (fun j => badPrimeSector (cols j))]
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sum_le Finset.univ (fun E : fixedBadPrimes.powerset =>
        ∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val)) 2
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : fixedBadPrimes.powerset => (1:ℝ))
      (fun E : fixedBadPrimes.powerset => ‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖)
    have hcard : Fintype.card fixedBadPrimes.powerset=4 := by
      rw [Fintype.card_coe,fixedBadPrimes_powerset_card]
    apply hn.trans
    simpa [hcard,fixedBadPrimes_card] using hc
  calc
    _ ≤ ∑k : idealRange K,4*∑E : fixedBadPrimes.powerset,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = 4*∑E : fixedBadPrimes.powerset,∑k : idealRange K,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ 4*∑E : fixedBadPrimes.powerset,sieveNorm X K*∑j : sector E,‖a j.val‖^2 := by
      gcongr with E
      exact hsector E
    _ = _ := by
      have he : (∑E : fixedBadPrimes.powerset,∑j : sector E,‖a j.val‖^2)=∑j,‖a j‖^2 :=
        Fintype.sum_fiberwise (fun j => badPrimeSector (cols j)) (fun j => ‖a j‖^2)
      rw [←Finset.mul_sum,he]
      ring
end OAI.CanonicalQuadraticSieve
