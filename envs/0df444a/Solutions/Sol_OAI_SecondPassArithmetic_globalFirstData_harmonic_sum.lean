-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstData_harmonic_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:17:08.224003+00:00
-- url     : https://prove2.me/submissions/7f6b3cbb-243a-4e28-b4ee-236200f4eaa0

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DivisorTargets
import Theorems.Thm_OAI_SecondPassArithmetic_cube_coordinates_inverse_active_sum
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstDivisorTarget_ne_zero
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirst_divisor_fiber_card
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstDivisorTarget_norm_bound
import Theorems.Thm_OAI_SecondPassArithmetic_primeSupport_inverse_sum
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
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_twisted_core_product
import Theorems.Thm_OAI_IdealDivisorBound_ideal_divisor_small_power
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
open OAI.SecondPassArithmetic
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
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (GlobalFirstData ι)) (B U : ℝ),
      1≤B → 1≤U → (∀b∈s,GlobalFirstAdmissible b) →
      (∀b∈s,primeProductNorm p b.common≤U) → (∀b∈s,primeProductNorm p b.firstCommon≤U) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∑b∈s,(1/primeProductNorm p b.common)*(1/primeProductNorm p b.firstCommon)*
        (1/‖eisEmbedding (∏i∈cubeActiveSupport b.cube.support
          (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))≤
        C*B^(1+ε)*(U*B^2)^ε*(128*Real.exp 1*(normLogBin U+1 : ℝ))^2 := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  obtain ⟨E,hE,hcube⟩ := cube_coordinates_inverse_active_sum ε hε
  refine ⟨D*E,mul_pos hD hE,?_⟩
  intro ι _ p hp _ hinj s B U hB hU hs hC ht hb1 hb2
  let Q := s.image globalFirstCountKey
  let cubes := s.image GlobalFirstData.cube
  let commons := s.image GlobalFirstData.common
  let firsts := s.image GlobalFirstData.firstCommon
  let weight := fun q : CubeCoordinates ι × Finset ι × Finset ι =>
    (1/primeProductNorm p q.2.1)*(1/primeProductNorm p q.2.2)*
      (1/‖eisEmbedding (∏i∈cubeActiveSupport q.1.support
        (fun i => q.1.leftExponent i+q.1.rightExponent i) q.1.leftBit q.1.rightBit,p i)‖)
  have hw (q : CubeCoordinates ι × Finset ι × Finset ι) : 0≤weight q := by
    have h1 := (FirstPassCubeLabels.primeProductNorm_pos p hp q.2.1).le
    have h2 := (FirstPassCubeLabels.primeProductNorm_pos p hp q.2.2).le
    dsimp [weight]
    positivity
  have hfiber (q : CubeCoordinates ι × Finset ι × Finset ι) (hq : q∈Q) :
      ((s.filter (fun b => globalFirstCountKey b=q)).card : ℝ)≤D*(U*B^2)^ε := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    have hc : ((s.filter (fun d => globalFirstCountKey d=globalFirstCountKey b)).card : ℝ)≤
        ((idealDivisors (globalFirstDivisorTarget p (globalFirstCountKey b))).card : ℝ) := by
      exact_mod_cast globalFirst_divisor_fiber_card p hinj (s.filter (fun d => globalFirstCountKey d=globalFirstCountKey b))
        (globalFirstCountKey b) (fun d hd => hs d (Finset.mem_filter.mp hd).1) (fun d hd => (Finset.mem_filter.mp hd).2)
    apply hc.trans ((hdiv _ (globalFirstDivisorTarget_ne_zero p _)).trans _)
    apply mul_le_mul_of_nonneg_left _ hD.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (globalFirstDivisorTarget_norm_bound p hp b B U (by linarith) (by linarith) (hC b hb) (hb1 b hb) (hb2 b hb)) hε.le
  have hsub : Q⊆cubes.product (commons.product firsts) := by
    intro q hq
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hb,Finset.mem_image_of_mem _ hb⟩⟩
  have he : (∑b∈s,weight (globalFirstCountKey b))=
      ∑q∈Q,((s.filter (fun b => globalFirstCountKey b=q)).card : ℝ)*weight q := by
    calc
      _ = ∑q∈Q,∑b∈s.filter (fun b => globalFirstCountKey b=q),weight (globalFirstCountKey b) :=
        (Finset.sum_fiberwise_of_maps_to (fun b hb => Finset.mem_image_of_mem globalFirstCountKey hb) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        have h := Finset.sum_congr rfl (fun b (hb : b∈s.filter (fun b => globalFirstCountKey b=q)) =>
          show weight (globalFirstCountKey b)=weight q by rw [(Finset.mem_filter.mp hb).2])
        rw [h]
        simp
  have hcube' := hcube p hp hinj cubes B hB (by
      intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact (hs b hb).1)
    (by intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact hb1 b hb)
    (by intro x hx; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx; exact hb2 b hb)
  have hC' := primeSupport_inverse_sum p hinj commons U (by
    intro C hCmem; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hCmem; exact hC b hb)
  have ht' := primeSupport_inverse_sum p hinj firsts U (by
    intro T hT; obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hT; exact ht b hb)
  have hC0 : 0≤∑C∈commons,1/primeProductNorm p C :=
    Finset.sum_nonneg (fun C _ => one_div_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp C).le)
  have ht0 : 0≤∑T∈firsts,1/primeProductNorm p T :=
    Finset.sum_nonneg (fun T _ => one_div_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp T).le)
  change (∑b∈s,weight (globalFirstCountKey b))≤_
  rw [he]
  calc
    _ ≤ ∑q∈Q,(D*(U*B^2)^ε)*weight q := Finset.sum_le_sum (fun q hq => mul_le_mul_of_nonneg_right (hfiber q hq) (hw q))
    _ = (D*(U*B^2)^ε)*∑q∈Q,weight q := (Finset.mul_sum _ _ _).symm
    _ ≤ (D*(U*B^2)^ε)*∑q∈cubes.product (commons.product firsts),weight q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hw q)) (by positivity)
    _ = (D*(U*B^2)^ε)*
        ((∑x∈cubes,1/‖eisEmbedding (∏i∈cubeActiveSupport x.support
          (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖)*
          (∑C∈commons,1/primeProductNorm p C)*(∑T∈firsts,1/primeProductNorm p T)) := by
      congr 1
      simp only [Finset.product_eq_sprod,Finset.sum_product,weight]
      simp_rw [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro C hCmem
      ring
    _ ≤ (D*(U*B^2)^ε)*((E*B^(1+ε))*(128*Real.exp 1*(normLogBin U+1 : ℝ))*(128*Real.exp 1*(normLogBin U+1 : ℝ))) := by
      gcongr
    _ = _ := by ring
end OAI.SecondPassArithmetic
