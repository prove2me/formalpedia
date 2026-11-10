-- Prove2me | solution 1 for OAI.CompletedGauss.short_completed_average_of_exact_reflection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T20:01:08.450163+00:00
-- url     : https://prove2.me/submissions/3a831c01-8f31-4eac-8ea7-cdaad61e73e8

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Theorems.Thm_OAI_CompletedGauss_completed_mean_square_of_exact_reflection
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CompletedGauss_mem_shortCubeRange
import Theorems.Thm_OAI_CompletedGauss_short_completed_normalized_small_power
import Theorems.Thm_OAI_CompletedGauss_short_cube_scales
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace OAI.CompletedGauss
theorem _root_.solution
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (ε ρ q levelBound : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^(1/1000:ℝ) → ∀G : Ideal O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      K*(Ideal.absNorm G:ℝ)≤X*F*Z^(-(1/40:ℝ)) →
    ∀rows : Finset (Ideal O),(∀I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) →
    ∀Ψ : idealRange F→Ideal O→O→*ℂ,(∀f I z,‖Ψ f I z‖≤1) → ∀lengthScale : ℂ,
      (∀f : idealRange F,∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        HasExactCompletedDyadicModels rays rows K (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound
          f.val (G*f.val) W (Ψ f) lengthScale) →
      (∑f : idealRange F,∑I∈rows,‖shortCompletedSum (Ψ f I) W X (Z^(1/1000:ℝ))‖^2)/F≤
        C*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε*K*Z^ε := by
  obtain ⟨Cr,hCr,hr⟩ := completed_mean_square_of_exact_reflection
    W a b ha hsupp hW ε ρ q levelBound hε hρ hq hlevel
  obtain ⟨Cs,hCs,hs⟩ := short_completed_normalized_small_power ε hε
  refine ⟨Cs*Cr,by positivity,?_⟩
  intro rays Z K X F hZ hK hF hFZ G hG hbad hmargin rows hrows Ψ hΨ lengthScale hmodels
  have hG1 : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  let A : ℝ := Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*(Ideal.absNorm G:ℝ)*F)^ε
  have hA : 0≤A := by dsimp [A]; positivity
  have hcompleted (f : idealRange F) (H : Ideal O) (hH : H∈shortCubeRange (Z^(1/1000:ℝ))) :
      (∑I : rows,‖completedT (Ψ f I.val) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X) := by
    have hf0 := (mem_idealRange.mp f.property).1.1
    have hfN := (mem_idealRange.mp f.property).2
    have hHN := (mem_shortCubeRange _ H).mp hH
    have hH1 : 1≤(Ideal.absNorm H:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hHN.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH0 : (Ideal.absNorm H:ℝ)≠0 := by linarith
    have hscale := short_cube_scales Z K (Ideal.absNorm G:ℝ) X F (Ideal.absNorm H:ℝ)
      hZ hK hG1 hF hFZ hH1 hHN.2.le hmargin
    have hb := hr rays K (X/(Ideal.absNorm H:ℝ)^3) hK hscale.1 rows f.val (G*f.val)
      (mul_ne_zero hG hf0) (fun P hP => dvd_trans (hbad P hP) (dvd_mul_right G f.val))
      hrows (Ψ f) lengthScale (hmodels f H hH)
    rw [Finset.sum_coe_sort (s := rows) (f := fun I : Ideal O => ‖completedT (Ψ f I) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)]
    apply hb.trans
    simp only [map_mul,Nat.cast_mul]
    have hpow : (K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε≤
        (K*(Ideal.absNorm G:ℝ)*F)^ε := by
      apply Real.rpow_le_rpow (by positivity) _ hε.le
      have hh := mul_le_mul_of_nonneg_left hfN (show 0≤K*(Ideal.absNorm G:ℝ) by positivity)
      nlinarith
    have hshape : K+K^2*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ))/(X/(Ideal.absNorm H:ℝ)^3)=
        K+K^2*(Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X := by
      field_simp

    rw [hshape]
    change Cr*(rays:ℝ)^2*‖lengthScale‖^2*(K*((Ideal.absNorm G:ℝ)*(Ideal.absNorm f.val:ℝ)))^ε*_≤A*_
    have hX0 : 0<X := by
      have hh := (le_div_iff₀ (show 0<(Ideal.absNorm H:ℝ)^3 by positivity)).mp hscale.1
      exact (show 0<(Ideal.absNorm H:ℝ)^3 by positivity).trans_le (by simpa only [one_mul] using hh)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  have hb := hs Z K (Ideal.absNorm G:ℝ) X F A hZ hK hG1 hF hFZ hA hmargin
    (fun f (I : rows) => Ψ f I.val) (fun f I z => hΨ f I.val z) W hcompleted
  have hsum (f : idealRange F) :
      (∑I : rows,‖shortCompletedSum (Ψ f I.val) W X (Z^(1/1000:ℝ))‖^2)=
      ∑I∈rows,‖shortCompletedSum (Ψ f I) W X (Z^(1/1000:ℝ))‖^2 :=
    Finset.sum_coe_sort (s := rows) (f := fun I : Ideal O => ‖shortCompletedSum (Ψ f I) W X (Z^(1/1000:ℝ))‖^2)
  simp_rw [hsum] at hb
  apply hb.trans_eq
  dsimp [A]
  ring
end OAI.CompletedGauss
