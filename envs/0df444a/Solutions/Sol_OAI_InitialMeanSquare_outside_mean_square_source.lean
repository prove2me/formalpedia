-- Prove2me | solution 1 for OAI.InitialMeanSquare.outside_mean_square_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:29:12.363372+00:00
-- url     : https://prove2.me/submissions/7703c25c-41db-435a-b2b5-65fc315b9234

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_OutsideIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poolPrimary_odd
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
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
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_InitialMeanSquare_mobiusRow_finite_source
import Theorems.Thm_OAI_InitialMeanSquare_outside_idealRowSum_initial_energy
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
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
attribute [local simp] OAI.InitialMeanSquare.initialLogProfile_apply
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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic
open FirstPassCubeLabels (normalizedColumn columnLog)
namespace OAI.InitialMeanSquare
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (W : ℝ → ℂ) (a b Z Y : ℝ)
    (ha : 0 < a) (hZ : 0 < Z) (hY : 0 < Y)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hD : b*Z ≤ D) (T : Finset O)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    (hT0 : ∀ z ∈ T, z ≠ 0)
    (K : Finset (primePool (outsideSquarefreeIdeals S D)) →
      Finset (primePool (outsideSquarefreeIdeals S D)) → Finset O) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p, poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid (normCharacter χ)
    (∑ z ∈ T, ‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z ≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y (fun C E => (K C E).erase 0)‖+
      (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K).re+
      ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => star (G V)) rowMajorant Y K‖-‖G ∅‖^2 := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀ i : primePool F, (Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p, poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  have he := mobiusRow_finite_source p hg hp hinj (poolPrimary_odd F hF) Finset.univ
    (normCharacter χ) 1 G Y hY T hT hT0 K
  calc
    _ = ∑ z ∈ T, ‖mobiusRow p hg Finset.univ (normCharacter χ) 1 G z‖^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      exact outside_idealRowSum_initial_energy χ S D hbad hSp W a b Z ha hZ hs hW hD z
    _ ≤ _ := he
end OAI.InitialMeanSquare
