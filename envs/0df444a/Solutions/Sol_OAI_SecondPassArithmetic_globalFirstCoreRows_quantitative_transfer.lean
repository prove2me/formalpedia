-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstCoreRows_quantitative_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:27:30.914039+00:00
-- url     : https://prove2.me/submissions/271a2672-58d8-4180-86ab-be39349ebaf6

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstFiniteEnergy_eq_supported
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTailCost_parent_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
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
import Theorems.Thm_OAI_SecondPassArithmetic_firstCoreBaseProfile_apply
import Theorems.Thm_OAI_SecondPassArithmetic_firstCoreTwist_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstCoreRows_integrated_transfer
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstDiagonalCost_parent_bound
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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ),0≤C ∧ 0<Cd ∧ 0<Ct ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H U : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M≤U →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let activeFamily := s.filter (fun b => FirstPassCubeLabels.primeProductNorm p b.common≤U ∧
        FirstPassCubeLabels.primeProductNorm p b.firstCommon≤U)
      let source := globalFirstSupportedPool p pool activeFamily
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t) ≤
      (∫ t : ℝ,firstLogDensity 0 t)*
        (Cd*Γ*(ell*B^3*F)*(B*U)^ε +
          globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side +
          Ct*Γ*(ell*B^3*F)*(B*U)^ε*globalFirstTailFactor K ell B F U H N) := by
  have hbase : ∀t,firstCoreBaseProfile g V side t≠0 → |t|≤M := by
    intro t ht
    apply hgM t
    intro hz
    apply ht
    simp only [firstCoreBaseProfile_apply,hz,zero_mul]
  obtain ⟨windows,C,Ct0,hC,hCt0,hwc,hws,hwb,hrows⟩ :=
    globalFirstCoreRows_integrated_transfer ε hε g V M hM hgM side A J N
  obtain ⟨Cd,hCd,hdiag⟩ := globalFirstDiagonalCost_parent_bound ε hε
    (firstCoreBaseProfile g V side) rowMajorant M hbase
  obtain ⟨Ct1,hCt1,htail⟩ := globalFirstTailCost_parent_bound ε hε
  refine ⟨windows,C,Cd,Ct0*Ct1,hC,hCd,mul_pos hCt0 hCt1,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ K ell B F H U Ψ m χ r T
    hΓ hw hK hell hB hF hH hU hellU hs hΨ hb1 hb2 hT hT0
  dsimp only
  have hB0 : 0<B := by linarith
  let activeFamily := s.filter (fun b => FirstPassCubeLabels.primeProductNorm p b.common≤U ∧
    FirstPassCubeLabels.primeProductNorm p b.firstCommon≤U)
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  let Ψmode := firstCoreTwist side χ Ψ r
  have hsub (b : GlobalFirstData ι) (hb : b∈activeFamily) : b∈s := (Finset.mem_filter.mp hb).1
  have hΓw := fun b hb => hw b (hsub b hb)
  have hsa := fun b hb => hs b (hsub b hb)
  have hba1 := fun b hb => hb1 b (hsub b hb)
  have hba2 := fun b hb => hb2 b (hsub b hb)
  have hΨmode : ∀a,‖Ψmode a‖≤1 := fun a => (firstCoreTwist_norm_le side χ Ψ r a).trans (hΨ a)
  have hr := hrows p hp hcop hg hinj hc hpr pool activeFamily w Γ K ell B F H Ψ m χ r T
    hΓ hΓw hK hell hB0 hF hH hsa hΨ hba1 hba2
    (fun b hb => hT b (hsub b hb)) (fun b hb => hT0 b (hsub b hb))
  dsimp only at hr
  have hd := hdiag p hp hg hinj pool activeFamily w Ψmode m Γ K ell B F U side
    hΓ hK hell hB hF hU hellU hΨmode hΓw hsa hba1 hba2
  have ht := htail p hp hinj activeFamily w Γ K ell B F M U H N side
    hΓ hK hell hB hF hU hH hellU hΓw hsa
    (fun b hb => (Finset.mem_filter.mp hb).2.1) (fun b hb => (Finset.mem_filter.mp hb).2.2) hba1 hba2
  have heq :
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t)=
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*globalFirstFiniteEnergy p hg pool activeFamily weight Ψ m g V ell side χ r T t) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [globalFirstFiniteEnergy_eq_supported p hp hg pool s weight Ψ m g V ell M U hell hgM hellU side χ r T t]
  rw [heq]
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t))
  have ht' := mul_le_mul_of_nonneg_left ht hCt0.le
  have h := add_le_add (add_le_add hd (le_refl
    (globalChildBudget p hp hcop hg pool
      (globalFirstSupportedPool p pool activeFamily
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side)
      Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side))) ht'
  convert h using 1 ; dsimp [weight,Ψmode] ; ring
end OAI.SecondPassArithmetic
