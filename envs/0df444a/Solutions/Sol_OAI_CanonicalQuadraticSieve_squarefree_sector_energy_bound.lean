-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.squarefree_sector_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:26:20.788279+00:00
-- url     : https://prove2.me/submissions/e0dd97bc-cc8d-46d2-826f-2790c3d6f292

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ResidualSectors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UnrestrictedCharacters
import Theorems.Thm_OAI_CanonicalQuadraticSieve_unrestrictedPairCharacter_squarefree_bad_split
import Theorems.Thm_OAI_CanonicalQuadraticSieve_goodSquarefreePart_injective_on_sector
import Theorems.Thm_OAI_CanonicalQuadraticSieve_goodSquarefreePart_mem_idealRange
import Theorems.Thm_OAI_CanonicalQuadraticSieve_norm_sum_sq_eq_of_pair_gram
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_canonical_quadraticRow_star
import Theorems.Thm_OAI_CanonicalQuadraticSieve_energy_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_family_squared_norm_le
import Theorems.Thm_OAI_CanonicalQuadraticSieve_quadraticRow_norm_le_one
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_nonneg
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
open FiniteSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Squarefree (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (cols j) = columnRay (cols k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticRow (cols j) (idealGenerator (rows i)) * a j‖ ^ 2) ≤
      sieveNorm M N * ∑ j, ‖a j‖ ^ 2 := by
  let good := fun i => goodSquarefreePart (rows i)
  let d := idealGenerator (∏ P ∈ E.val, P)
  let b := fun j => a j * quadraticRow (cols j) d
  have hgood : Function.Injective good := by
    intro i k h
    apply hr
    exact goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
      ((hE i).trans (hE k).symm) h
  have hgoodrows (i : m) : Admissible (good i) ∧ (Ideal.absNorm (good i) : ℝ) ≤ M := by
    exact mem_idealRange.mp (goodSquarefreePart_mem_idealRange _ (hrows i).1 M (hrows i).2)
  have hnorm (i : m) :
      ‖∑ j, quadraticRow (cols j) (idealGenerator (rows i)) * a j‖ ^ 2 =
      ‖∑ j, quadraticRow (cols j) (primaryGenerator (good i)) * b j‖ ^ 2 := by
    apply norm_sum_sq_eq_of_pair_gram
    intro j k
    have hbad : badPrimeSupport (rows i) = E.val := congrArg Subtype.val (hE i)
    have hp := unrestrictedPairCharacter_squarefree_bad_split (cols j) (cols k) (rows i)
      (hcols j).1 (hcols k).1 (hray j k) (hrows i).1
    simp only [unrestrictedPairCharacter, hbad] at hp
    change quadraticRow (cols j) (idealGenerator (rows i)) * quadraticRow (cols k) (idealGenerator (rows i)) =
      (quadraticRow (cols j) d * quadraticRow (cols k) d) *
      (quadraticRow (cols j) (primaryGenerator (good i)) * quadraticRow (cols k) (primaryGenerator (good i))) at hp
    calc
      _ = (quadraticRow (cols j) (idealGenerator (rows i)) * quadraticRow (cols k) (idealGenerator (rows i))) *
          (star (a j) * a k) := by
            rw [star_mul, canonical_quadraticRow_star _ (hcols j).1]
            ring
      _ = _ := by
        rw [hp]
        simp only [b, star_mul, canonical_quadraticRow_star _ (hcols j).1]
        ring
  have hcoeff : (∑ j, ‖b j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    apply pow_le_pow_left₀ (norm_nonneg _)
    dsimp only [b]
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
  have hfamily := family_squared_norm_le good cols hgood hc M N hgoodrows hcols
  calc
    _ = ∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (good i)) * b j‖ ^ 2 :=
      Finset.sum_congr rfl (fun i _ => hnorm i)
    _ ≤ ‖operator (fun i j => quadraticRow (cols j) (primaryGenerator (good i)))‖ ^ 2 * ∑ j, ‖b j‖ ^ 2 :=
      FiniteSieveOperator.energy_bound _ b
    _ ≤ sieveNorm M N * ∑ j, ‖a j‖ ^ 2 :=
      mul_le_mul hfamily hcoeff (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sieveNorm_nonneg M N)
end OAI.CanonicalQuadraticSieve
