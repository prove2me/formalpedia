-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstCoreRows_integrated_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:54:28.005206+00:00
-- url     : https://prove2.me/submissions/f7cf6cb2-44aa-4c5b-849c-aef38cdc3a05

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
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
import Theorems.Thm_OAI_FirstPassCubeLabels_coreRayTwist_prod
import Theorems.Thm_OAI_FirstPassCubeLabels_integral_pair_moment_bound
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
import Theorems.Thm_OAI_SecondPassArithmetic_firstCoreTwist_norm_le
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinFirstCoefficient_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_globalChildBudget_height
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstCoreRows_actual_transfer
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstDiagonalCost_nonneg
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstFiniteEnergy_integrable
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstSourceTail_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstSourceZero_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstTailCost_nonneg
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
open OAI.SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Ct : ℝ),0≤C ∧ 0<Ct ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let source := globalFirstSupportedPool p pool s
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t) ≤
      (∫ t : ℝ,firstLogDensity 0 t)*
        (globalFirstDiagonalCost p hg pool s (fun b => weight b) Ψmode m
            (firstCoreBaseProfile g V side) rowMajorant ell side (globalFirstPooledRow p K ell B F side) +
          globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side +
          Ct*globalFirstTailCost p s (fun b => weight b) K ell B F M H N side) := by
  obtain ⟨windows,C,hC,hwc,hws,hwb,hrows⟩ := globalFirstCoreRows_actual_transfer ε hε g V M hM hgM side A J
  obtain ⟨Ct,hCt,htail⟩ := globalFirstSourceTail_bound N g V rowMajorant side
  refine ⟨windows,C,Ct,hC,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ K ell B F H Ψ m χ r T hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
  dsimp only
  let source := globalFirstSupportedPool p pool s
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  let Ψmode := firstCoreTwist side χ Ψ r
  let d := globalFirstDiagonalCost p hg pool s (fun b => weight b) Ψmode m
    (firstCoreBaseProfile g V side) rowMajorant ell side (globalFirstPooledRow p K ell B F side)
  let c := globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side
  let q := Ct*globalFirstTailCost p s (fun b => weight b) K ell B F M H N side
  have hΨmode : ∀ a,‖Ψmode a‖≤1 := fun a => (firstCoreTwist_norm_le side χ Ψ r a).trans (hΨ a)
  have hweight (b : GlobalFirstData ι) (hb : b∈s) : 0≤weight b :=
    mul_nonneg (hw b hb).1 (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hd : 0≤d := globalFirstDiagonalCost_nonneg p hp hg pool s _ Ψmode m _ rowMajorant ell side _
  have hq : 0≤q := mul_nonneg hCt.le (globalFirstTailCost_nonneg p hp s _ K ell B F M H N side hK hell hB hF hH)
  have hpoint (t : ℝ) : globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t ≤
      1*(d+((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*c+q) := by
    have hrow := hrows p hp hcop hg hinj hc hpr pool s w Γ K ell B F H Ψ m χ r t T
      hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
    dsimp only at hrow
    have hsmall : globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t ≤
        ∑ b∈s,weight b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
          globalFirstCoreCorrection p g V ell side t b) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (hweight b hb)
    have hz := globalFirstSourceZero_bound p hp hg hinj pool s (fun b => weight b) Ψmode m
      g V rowMajorant K ell B F M H side t
    have ht := htail p hp hg hinj hc pool s (fun b => weight b) Ψmode m K ell B F M H t
      hΨmode hK hell hB hF hH hgM
    have hupper := add_le_add (add_le_add (le_refl
      (globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side)) hz) ht
    have hfinal := hsmall.trans (hrow.trans hupper)
    rw [globalChildBudget_height] at hfinal
    simpa only [d,c,q,one_mul,add_comm,add_left_comm,add_assoc] using hfinal
  have hint := FirstPassCubeLabels.integral_pair_moment_bound J
    (globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T)
    (globalFirstFiniteEnergy_integrable p hg pool s weight Ψ m g V ell side χ r T (2*(J+2)))
    1 d c q (by norm_num) hd hq hpoint
  simpa only [mul_one] using hint
end OAI.SecondPassArithmetic
