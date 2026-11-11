-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.hasInitialCanonicalDensityAtRadius_of_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:57:39.781685+00:00
-- url     : https://prove2.me/submissions/2e224bdc-b451-4818-ac12-5b56ff9ada9a

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_DensityTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_InitialDensity
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalCoefficientClass_IsBaseRayTwist_secondMinus
import Theorems.Thm_OAI_CanonicalCoefficientClass_IsBaseRayTwist_secondPlus
import Theorems.Thm_OAI_CanonicalCubeSeparation_cubeFrequencyFactor_norm
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_nonneg
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_succ
import Theorems.Thm_OAI_CanonicalCubeSeparation_radiusIter_zero
import Theorems.Thm_OAI_CanonicalCubeSeparation_sourceLogProfile_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_canonicalDescentPadding_budget
import Theorems.Thm_OAI_CanonicalRowCompletion_canonicalInitialThreshold
import Theorems.Thm_OAI_CanonicalRowCompletion_cubeIndex_apply
import Theorems.Thm_OAI_CanonicalRowCompletion_initialCanonicalState
import Theorems.Thm_OAI_CanonicalRowCompletion_outsideLogEnergy_small_power
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
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_conjugateMonoid_norm_le_one
import Theorems.Thm_OAI_InitialMeanSquare_initialElementaryConstant_nonneg
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_InitialMeanSquare_initial_density_elementary_squared_mass
import Theorems.Thm_OAI_InitialMeanSquare_initial_two_windows_bounded
import Theorems.Thm_OAI_InitialMeanSquare_normCharacter_norm_le_one
import Theorems.Thm_OAI_InitialMeanSquare_outsidePrime_injective
import Theorems.Thm_OAI_InitialMeanSquare_outsidePrime_odd
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
import Theorems.Thm_OAI_SecondPassArithmetic_secondRayMinus_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_secondRayPlus_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_OAI_SecondPassIntegration_densityChildEnergy_from_canonical_heights
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
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SecondPassIntegration hiding O
open InitialMeanSquare hiding O
open CanonicalCubeSeparation
open CanonicalCoefficientClass (IsBaseRayTwist)
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.CanonicalRowCompletion
theorem _root_.solution {q₀ : ℕ}
    (χ : DirichletCharacter ℂ q₀)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (ρ q levelBound : ℝ) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound)
    (hmodels : HasCanonicalThetaModels S (conjugateMonoid (normCharacter χ)) ρ q levelBound) :
    HasInitialCanonicalDensityAtRadius χ S hbad := by
  intro deltaLoss hδ P A hA
  let base:=conjugateMonoid (normCharacter χ)
  have hbase : ∀u,‖base u‖≤1:=conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  obtain ⟨d,henergy⟩:=outsideLogEnergy_small_power S hSp hbad base hbase
    ρ q levelBound hρ hq hlevel hmodels deltaLoss hδ A hA
  refine ⟨d,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂ hV₁ hV₂
  have hs₁ : ContDiff ℝ ∞ (orientedLogProfile true V₁):=Complex.conjCLE.contDiff.comp hVs₁
  have hb₁ : ∀s,orientedLogProfile true V₁ s≠0→|s|≤A := by
    intro s hs
    apply hV₁ s
    intro hz
    exact hs (by simp [orientedLogProfile,hz])
  obtain ⟨C₁,hC₁,he₁⟩:=henergy (orientedLogProfile true V₁) hs₁ hb₁
  obtain ⟨C₂,hC₂,he₂⟩:=henergy (orientedLogProfile false V₂) hVs₂ hV₂
  obtain ⟨A',Vmax,hA',hVmax,hbV₁,hbV₂,hsV₁,hsV₂⟩:=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z₀,hZ₀,hthreshold⟩:=canonicalInitialThreshold S
  let I₀:=∫t : ℝ,firstLogDensity 0 t
  have hI₀ : 0≤I₀:=integral_nonneg (fun t=>FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  let Ccan:=6*(C₁+C₂)*I₀^3
  let Cele:=initialElementaryConstant A' Vmax*I₀^3
  let C:=Ccan+Cele*Z₀^3+1
  have hCcan : 0≤Ccan:=by dsimp only [Ccan];positivity
  have hCele : 0≤Cele:=mul_nonneg (initialElementaryConstant_nonneg A' Vmax) (pow_nonneg hI₀ _)
  have hC : 0<C:=by dsimp only [C];positivity
  have hcanC : Ccan≤C:=by
    have hp : 0≤Cele*Z₀^3:=by positivity
    dsimp only [C]
    linarith
  have heleC : Cele*Z₀^3≤C:=by
    dsimp only [C]
    linarith
  let Cpool:=Real.exp (radiusIter A 3000)
  refine ⟨C,Cpool,max P 3,hC,Real.one_le_exp (radiusIter_nonneg A hA 3000),le_max_left _ _,?_⟩
  intro D Z X lengthScale K R ray T hZ hpool hX hL hK hXP hLP hKP hRP hmass hinv hT hout
  let p:=outsidePrime S D
  let hp:=outsidePrime_ne_zero S hbad D
  let hcop:=outsidePrime_coprime S hbad D
  let hg:=outsidePrime_good S hbad D
  let:=outsidePrime_maximal S hbad D
  let Ψ₁:=secondRayMinus base ray
  let Ψ₂:=secondRayPlus base ray
  let m:=primeSubsetGenerator (fun i=>Ideal.span {p i}) R
  let labels:=T.image Prod.fst
  have hmember : IsBaseRayTwist base base:=Or.inl rfl
  have hη : 0≤canonicalDescentPadding deltaLoss:=(canonicalDescentPadding_budget deltaLoss hδ).1.le
  have hstate₁ := initialCanonicalState S D hbad base Ψ₁ (hmember.secondMinus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hstate₂ := initialCanonicalState S D hbad base Ψ₂ (hmember.secondPlus ray)
    Z (canonicalDescentPadding deltaLoss) X lengthScale K hZ hη hX hL hK R T hmass hinv
    (fun z hz=>⟨(hT z hz).1,(hT z hz).2.1⟩) hout
  have hZδ : 1≤Z^deltaLoss:=Real.one_le_rpow hZ hδ.le
  have hD : Real.exp (radiusIter A 3000)*Z^3≤D :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ (le_max_right P 3)) (Real.exp_pos _).le).trans hpool
  have hlabels : ∀z∈T,z.1∈labels:=fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩
  have hrows : ∀z∈T,‖eisEmbedding z.2‖^2≤K:=fun z hz=>(hT z hz).2.2.2
  have hzero : ∀z∈T,z.2≠0:=fun z hz=>(hT z hz).2.2.1
  by_cases hlarge : Z₀≤Z
  · obtain ⟨hZgt,hZbig,hfixed⟩:=hthreshold Z hlarge
    have hleft (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₁ t) m labels (orientedLogProfile true V₁) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₁ D Z Ψ₁ m labels X lengthScale K t hstate₁ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₁ t) m labels
        (orientedLogProfile true V₁) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hright (t : ℝ) : canonicalLogEnergy p hp hcop hg Finset.univ
        (normHeightTwist Ψ₂ t) m labels (orientedLogProfile false V₂) X K≤
        ((C₁+C₂)*Z^deltaLoss)*(X*lengthScale)^2*(1+‖t‖)^(2*d) := by
      have hh:=he₂ D Z Ψ₂ m labels X lengthScale K t hstate₂ hZgt hZbig hfixed hD
      change canonicalLogEnergy p hp hcop hg Finset.univ (normHeightTwist Ψ₂ t) m labels
        (orientedLogProfile false V₂) X K≤_ at hh
      apply hh.trans
      rw [Real.norm_eq_abs]
      gcongr
      · linarith
      · linarith [abs_nonneg t]
      · omega
    have hd:=densityChildEnergy_from_canonical_heights p hp hcop hg Finset.univ Ψ₁ Ψ₂ m T labels
      V₁ V₂ X lengthScale K ((C₁+C₂)*Z^deltaLoss) d (by linarith) (by linarith) (by positivity)
      hlabels hrows hzero hleft hright
    change outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤_ at hd
    have hcan : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤Ccan*Z^deltaLoss*(X*lengthScale)^2 := by
      convert hd using 1 ; dsimp only [Ccan,I₀] ; ring
    exact hcan.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcanC (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _))
  · have hKcap : K≤Z₀^3:=hstate₁.row_le_global.trans
      (pow_le_pow_left₀ (by linarith) (le_of_not_ge hlarge) 3)
    have hΨ₁ : ∀u,‖Ψ₁ u‖≤1:=fun u=>(secondRayMinus_norm_le base ray u).trans (hbase u)
    have hΨ₂ : ∀u,‖Ψ₂ u‖≤1:=fun u=>(secondRayPlus_norm_le base ray u).trans (hbase u)
    have hd:=initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X lengthScale K A' Vmax d (by linarith) hL hK hA' hVmax hbV₁ hbV₂ hsV₁ hsV₂
      (fun z hz=>⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩)
    change outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X d≤Cele*K*(X*lengthScale)^2 at hd
    apply hd.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hKcap hCele).trans
      (heleC.trans (le_mul_of_one_le_right hC.le hZδ))
end OAI.CanonicalRowCompletion
