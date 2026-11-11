-- Prove2me | solution 1 for OAI.SixthPowerAverage.outside_totient_moebius_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:25:59.712661+00:00
-- url     : https://prove2.me/submissions/a16d4181-578c-4771-a9f0-d469c80dd3e0

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ThetaDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Theorems.Thm_OAI_SixthPowerAverage_exists_averaging_test
import Theorems.Thm_OAI_SixthPowerAverage_averagingRows_power_norm
import Theorems.Thm_OAI_SixthPowerAverage_average_tsum_cauchy
import Theorems.Thm_OAI_SixthPowerAverage_average_remainder_small_power
import Theorems.Thm_OAI_SixthPowerAverage_totient_sum_normalized_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CompletedHeight_completedT_normHeight_norm
import Theorems.Thm_OAI_CompletedHeight_shortCompletedSum_normHeight_norm
import Theorems.Thm_OAI_CubicEisenstein_finiteCubicMultiplier_coe
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_apply
import Theorems.Thm_OAI_CubicEisenstein_hyperbolicSpatialChart_source
import Theorems.Thm_OAI_CubicEisenstein_integralComplexMatrix_apply
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalLift_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelQuotientChart_symm
import Theorems.Thm_OAI_CubicEisenstein_kernelTruncatedWeight_apply
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
import Theorems.Thm_OAI_InitialMeanSquare_outside_mean_square_of_theta_models
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_apply
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_norm
import Theorems.Thm_OAI_JointLogSeparation_frequencyTwist_twice
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_apply
import Theorems.Thm_OAI_QuadraticInitialBound_annularSieveCutoff_zero
import Theorems.Thm_OAI_QuadraticInitialBound_pvControl_nonneg
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CanonicalCubeSeparation.cubeFrequencyFactor_norm
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_succ
attribute [local simp] OAI.CanonicalCubeSeparation.radiusIter_zero
attribute [local simp] OAI.CanonicalCubeSeparation.sourceLogProfile_apply
attribute [local simp] OAI.CanonicalRowCompletion.cubeIndex_apply
attribute [local simp] OAI.CompletedHeight.completedT_normHeight_norm
attribute [local simp] OAI.CompletedHeight.shortCompletedSum_normHeight_norm
attribute [local simp] OAI.CubicEisenstein.finiteCubicMultiplier_coe
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_apply
attribute [local simp] OAI.CubicEisenstein.hyperbolicSpatialChart_source
attribute [local simp] OAI.CubicEisenstein.integralComplexMatrix_apply
attribute [local simp] OAI.CubicEisenstein.kernelLocalLift_symm
attribute [local simp] OAI.CubicEisenstein.kernelQuotientChart_symm
attribute [local simp] OAI.CubicEisenstein.kernelTruncatedWeight_apply
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
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply



set_option autoImplicit false
open OAI
noncomputable section
open OAI.SixthPowerAverage
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
open InitialMeanSquare
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalRowCompletion
namespace OAI.SixthPowerAverage
theorem _root_.solution {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O))
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(D : ℕ) (Z : ℝ),1≤Z → b*Z≤D →
      ‖∑I∈outsideIdealsUpTo S D,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I‖≤
        C*Z^((23:ℝ)/24+ε) := by
  obtain ⟨V,hV,hVs,hV0,hVhat⟩:=exists_averaging_test
  obtain ⟨Cm,hCm,hm⟩:=outside_mean_square_of_theta_models χ S hbad hSp ρ q levelBound hρ hq hlevel hmodels
    W a b ha hs hW ((1:ℝ)/10) (2*ε) (by norm_num) (by positivity)
  simp only [show (1:ℝ)+1/10=11/10 by norm_num] at hm
  obtain ⟨Ce,hCe,he⟩:=average_remainder_small_power ε hε
  have hWc : HasCompactSupport W := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs
  let Ws : 𝓢(ℝ,ℂ):=hWc.toSchwartzMap hW
  let G : ℝ:=SchwartzMap.seminorm ℝ 0 0 Ws
  let B : ℝ:=max 1 b
  let Err : ℝ:=Ce*G*pvControl V*B^(1+ε)
  let Avg : ℝ:=Real.sqrt (768*Cm)
  let C : ℝ:=(Avg+Err)/‖paperRadialFourier V 0‖
  have hG : 0≤G:=apply_nonneg _ _
  have hB : 1≤B:=le_max_left _ _
  have hErr : 0≤Err:=mul_nonneg (mul_nonneg (mul_nonneg hCe.le hG) (pvControl_nonneg V)) (by positivity)
  have hAvg : 0<Avg:=Real.sqrt_pos.mpr (by positivity)
  have hhat : 0<‖paperRadialFourier V 0‖:=norm_pos_iff.mpr hVhat
  refine ⟨C,div_pos (by linarith) hhat,?_⟩
  intro D Z hZ hD
  have hZp : 0<Z:=by linarith
  let Y : ℝ:=Z^((11:ℝ)/60)
  have hY : 1≤Y:=Real.one_le_rpow hZ (by norm_num)
  have hYp : 0<Y:=by linarith
  let F:=outsideIdealsUpTo S D
  let A : ActualEisensteinCubic.O→ℂ:=idealRowSum F (outsideIdealsUpTo_ne_bot S D)
    (outside_good S D hbad) χ (fun n=>W (n/Z))
  have hYpow : Y^6=Z^((11:ℝ)/10) := by
    dsimp only [Y]
    rw [←Real.rpow_mul_natCast hZp.le]
    norm_num
  have hms : (∑z∈(averagingRows Y).image (fun b=>b^6),‖A z‖^2)≤
      Cm*Z*Z^((11:ℝ)/10)*Z^(2*ε) := by
    apply hm D Z hZ hD
    · intro z hz
      have hn:=(averagingRows_power_norm Y hY hz).2
      simpa only [hYpow,show (1:ℝ)+1/10=11/10 by norm_num] using hn
    · intro z hz
      exact (averagingRows_power_norm Y hY hz).1
  have havg2:= (average_tsum_cauchy V hV hVs hV0 Y hY A).trans
    (mul_le_mul_of_nonneg_left hms (by positivity : 0≤768*Y))
  have heq : 768*Y*(Cm*Z*Z^((11:ℝ)/10)*Z^(2*ε))=
      (Avg*Z^((137:ℝ)/120+ε))^2 := by
    dsimp only [Y,Avg]
    rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤768*Cm),←Real.rpow_mul_natCast hZp.le]
    calc
      _ = (768*Cm)*(Z^((11:ℝ)/60)*Z^(1:ℝ)*Z^((11:ℝ)/10)*Z^(2*ε)) := by rw [Real.rpow_one];ring
      _ = (768*Cm)*Z^((11:ℝ)/60+1+11/10+2*ε) := by
        rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
      _ = _ := by congr 2 ; ring
  rw [heq] at havg2
  have havg : ‖∑'z : ActualEisensteinCubic.O,V (‖eisEmbedding z‖^2/Y)*A (z^6)‖≤
      Avg*Z^((137:ℝ)/120+ε) := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp havg2
  have herr : ‖∑I∈F,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*
      maskedPrincipalRemainder (fun i : primePool F=>i.val) (idealSupport F I) V Y‖≤Err*Z^(1+ε) := by
    have hbZ : 1≤B*Z:=by nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hZ)]
    have hh:=he F (outsideIdealsUpTo_ne_bot S D) χ (fun n=>W (n/Z)) V Y (B*Z) G hYp hbZ hG
      (fun n=>Ws.norm_le_seminorm ℝ (n/Z)) (by
        intro I hI hn
        have hh:=(hs hn).2
        exact ((div_le_iff₀ hZp).mp hh).trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hZp.le))
    calc
      _≤Ce*G*pvControl V*(B*Z)^(1+ε):=hh
      _=Err*Z^(1+ε):=by rw [Real.mul_rpow (by linarith : 0≤B) hZp.le];dsimp only [Err];ring
  have hexponent : Z^(1+ε)≤Z^((137:ℝ)/120+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hmain:=totient_sum_normalized_bound F (outsideIdealsUpTo_ne_bot S D)
    (outside_good S D hbad) χ (fun n=>W (n/Z)) V Y hYp
  have hbound : Y*‖paperRadialFourier V 0‖*
      ‖∑I∈F,baseChangeWeight χ I*W ((Ideal.absNorm I:ℝ)/Z)*totientDensity I‖≤
      (Avg+Err)*Z^((137:ℝ)/120+ε) := by
    apply hmain.trans
    have := add_le_add havg (herr.trans (mul_le_mul_of_nonneg_left hexponent hErr))
    simpa only [add_mul] using this
  have hzexp : Z^((137:ℝ)/120+ε)=Y*Z^((23:ℝ)/24+ε) := by
    dsimp only [Y]
    rw [←Real.rpow_add hZp]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (mul_pos hYp hhat)).mp
  apply hbound.trans_eq
  rw [hzexp]
  dsimp only [C]
  field_simp [hhat.ne']
end OAI.SixthPowerAverage
