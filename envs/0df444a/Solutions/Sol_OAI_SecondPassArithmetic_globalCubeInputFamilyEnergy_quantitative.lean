-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalCubeInputFamilyEnergy_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:31:32.83881+00:00
-- url     : https://prove2.me/submissions/f5a36e3a-268c-4449-a78c-52ad6b83db1e

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstCoreRows_quantitative_transfer
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
import Theorems.Thm_OAI_RayFourExpansion_crossCoeff_sum_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_append_first
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_first_append
import Theorems.Thm_OAI_SecondPassArithmetic_GlobalSecondData_source_append
import Theorems.Thm_OAI_SecondPassArithmetic_firstCoreUniformWeight_mass
import Theorems.Thm_OAI_SecondPassArithmetic_globalCubeInputFamilyEnergy_eq_integrated_rows
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstFamilyWeight_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstPooledRow_block
import Theorems.Thm_OAI_SecondPassArithmetic_mem_globalFirstFamilySet
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


section
namespace OAI
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
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
end InitialMeanSquare
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
end
private lemma two_finite_error_sum {α β : Type*} [Fintype α] [Fintype β]
    (a : α → ℝ) (b : β → ℝ) (E : ℝ) (c : α → β → ℝ) :
    (∑x,a x*∑y,(b y*E+c x y))=(∑x,a x)*(∑y,b y)*E+∑x,a x*∑y,c x y := by
  simp only [Finset.sum_add_distrib,Finset.sum_mul,mul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_mul]
  ring
end SecondPassArithmetic
end
end OAI
end

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
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀t,g t≠0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cd Ct : ℝ),0≤C ∧ 0<Cd ∧ 0<Ct ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0 → |t|≤M+6+1) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O ⧸ Ideal.span {p i})≠2) (_hpr : ∀i,lambda^2∣p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (w : GlobalCubeBlock ι → ℝ) (Γ K ell B F H U : ℝ)
      (Ψ : O →* ℂ) (m : O) (T : GlobalCubeBlock ι → Finset O),
      0≤Γ → (∀b∈blocks,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M≤U →
      (∀b∈blocks,GlobalCubeAdmissible b) → (∀a,‖Ψ a‖≤1) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀b∈blocks,∀z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side (b.withCommon ∅)) →
      (∀b∈blocks,∀z∈T b,z≠0) →
      (∑b∈blocks,w b*globalCubeCoefficient p K ell B F side b*
        globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side (2*(J+2)) (T b))≤
      globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ m windows C Cd Ct Γ ε K ell B F M H U A J N side := by
  obtain ⟨windows,C,Cd,Ct,hC,hCd,hCt,hwc,hws,hwb,hrow⟩ :=
    globalFirstCoreRows_quantitative_transfer ε hε g V M hM hgM side A J N
  refine ⟨windows,C,Cd,Ct,hC,hCd,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ m T
    hΓ hw hK hell hB hF hH hU hellU hs hΨ hb1 hb2 hT hT0
  have hB0 : 0<B := by linarith
  let family := globalFirstFamilySet pool blocks
  let activeFamily := family.filter (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let source := globalFirstSupportedPool p pool activeFamily
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  let child := fun (a : RayCharacter×RayCharacter) (r : FirstCoreIndex) =>
    (∫t : ℝ,firstLogDensity 0 t)*globalChildBudget p hp hcop hg pool source
      (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
      ε 0 0 K ell B F M H A J side
  let E0 := (∫t : ℝ,firstLogDensity 0 t)*Γ*(ell*B^3*F)*(B*U)^ε*(Cd+Ct*globalFirstTailFactor K ell B F U H N)
  have hI : 0≤∫t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hf0 : 0≤globalFirstTailFactor K ell B F U H N := by unfold globalFirstTailFactor; positivity
  have hE0 : 0≤E0 := by dsimp [E0]; positivity
  have hrow' (a : RayCharacter×RayCharacter) (r : FirstCoreIndex) :
      (∫t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool family
          (fun d => globalFirstFamilyWeight p hg w Ψ m side r d*globalFirstCoefficient p K ell B F side d)
          Ψ m g V ell side (if side then a.1 else a.2) r (fun d => T d.block) t)≤
      firstCoreUniformWeight r*E0+child a r := by
    have hΓr : 0≤Γ*firstCoreUniformWeight r := by unfold firstCoreUniformWeight; positivity
    have h := hrow p hp hcop hg hinj hc hpr pool family
      (globalFirstFamilyWeight p hg w Ψ m side r) (Γ*firstCoreUniformWeight r) K ell B F H U Ψ m
      (if side then a.1 else a.2) r (fun d => T d.block) hΓr
      (fun d hd => globalFirstFamilyWeight_bounds p hg blocks w Γ hw Ψ hΨ m side r pool d hd)
      hK hell hB hF hH hU hellU
      (fun d hd => hs d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1) hΨ
      (fun d hd => hb1 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
      (fun d hd => hb2 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
      (by intro d hd z hz; rw [globalFirstPooledRow_block]; exact hT d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1 z hz)
      (fun d hd => hT0 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1)
    dsimp only at h
    convert h using 1 ; dsimp [E0,child,source,activeFamily] ; ring
  rw [globalCubeInputFamilyEnergy_eq_integrated_rows]
  have hm : (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)*(∑r : FirstCoreIndex,firstCoreUniformWeight r)≤512*(512*32) := by
    have ha : (∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)≤512 := by
      simpa only [Fintype.sum_prod_type] using RayFourExpansion.crossCoeff_sum_norm_le
    exact mul_le_mul ha firstCoreUniformWeight_mass
      (Finset.sum_nonneg (fun r _ => by unfold firstCoreUniformWeight; positivity)) (by norm_num)
  calc
    _ ≤ ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,(firstCoreUniformWeight r*E0+child a r) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r _ => hrow' a r)) (norm_nonneg _))
    _ = ((∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖)*(∑r : FirstCoreIndex,firstCoreUniformWeight r))*E0+
        ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,child a r :=
      two_finite_error_sum _ _ _ _
    _ ≤ (512*(512*32))*E0+∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,child a r :=
      add_le_add (mul_le_mul_of_nonneg_right hm hE0) le_rfl
    _ = _ := by
      unfold globalFirstQuantitativeBudget globalFirstRayChildBudget
      dsimp [E0,child,source,activeFamily,family]
      ring
end OAI.SecondPassArithmetic
