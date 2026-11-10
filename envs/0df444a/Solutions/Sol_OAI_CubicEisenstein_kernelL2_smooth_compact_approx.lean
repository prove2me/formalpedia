-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelL2_smooth_compact_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:56:39.607981+00:00
-- url     : https://prove2.me/submissions/e6090845-5f93-4d10-b440-c280bd1196ed

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RowCaps
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelL2_continuous_compact_approx
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
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal NNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (f : KernelQuotientL2) (ε : ℝ) (hε : 0<ε) :
    ∃g : kernelSmoothTests,
      eLpNorm ((f : KernelQuotient→ℂ)-g.1) 2 (integralQuotientVolume globalKubotaKernel)≤
        ENNReal.ofReal ε := by
  obtain ⟨g,hgK,hfg,hgc,hgLp⟩ := kernelL2_continuous_compact_approx f
    (ENNReal.ofReal (ε/2)) (by positivity)
  let mass : ℝ≥0∞ := (integralQuotientVolume globalKubotaKernel Set.univ)^((2:ℝ≥0∞).toReal⁻¹)
  have hm : mass≠(∞:ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  let deltaLoss : ℝ := ε/(2*(mass.toReal+1))
  have hδ : 0<deltaLoss := div_pos hε (by positivity)
  obtain ⟨k,hkg,hksupp⟩ := hgc.exists_contMDiff_approx 𝓘(ℝ,SpatialCoordinates) ⊤
    (ε := fun _ => deltaLoss) continuous_const (fun _ => hδ)
  have hkK : HasCompactSupport (k : KernelQuotient→ℂ) :=
    HasCompactSupport.of_support_subset_isCompact hgK (hksupp.trans (subset_tsupport g))
  let kt : kernelSmoothTests := ⟨k,k.contMDiff,hkK⟩
  have hkgLp : eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel)≤
      ENNReal.ofReal (ε/2) := by
    have hb : ∀ᵐ q ∂integralQuotientVolume globalKubotaKernel,‖g q-k q‖≤deltaLoss :=
      Filter.Eventually.of_forall fun q => by
        simpa only [dist_eq_norm,norm_sub_rev] using (hkg q).le
    have hmul : mass.toReal*deltaLoss≤ε/2 := by
      have he : deltaLoss*(2*(mass.toReal+1))=ε := div_mul_cancel₀ _ (by positivity)
      have hp := ENNReal.toReal_nonneg (a := mass)
      nlinarith [mul_nonneg hp hδ.le]
    calc
      _ ≤ mass*ENNReal.ofReal deltaLoss := eLpNorm_le_of_ae_bound hb
      _ = ENNReal.ofReal (mass.toReal*deltaLoss) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hm]
      _ ≤ ENNReal.ofReal (ε/2) := ENNReal.ofReal_le_ofReal hmul
  refine ⟨kt,?_⟩
  have he : (f : KernelQuotient→ℂ)-kt.1=((f : KernelQuotient→ℂ)-g)+(g-(k : KernelQuotient→ℂ)) := by
    funext q
    change f q-k q=(f q-g q)+(g q-k q)
    ring
  rw [he]
  calc
    _ ≤ eLpNorm ((f : KernelQuotient→ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)+
        eLpNorm (g-(k : KernelQuotient→ℂ)) 2 (integralQuotientVolume globalKubotaKernel) :=
      eLpNorm_add_le ((Lp.aestronglyMeasurable f).sub hgc.aestronglyMeasurable)
        (hgc.sub k.contMDiff.continuous).aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add hfg hkgLp
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
end OAI.CubicEisenstein
