-- Prove2me | solution 1 for OAI.SecondPassArithmetic.cube_coordinates_parity_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:14:09.877035+00:00
-- url     : https://prove2.me/submissions/eec4c2e0-60a2-40d2-a9f4-37ca82f6cc97

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothTests
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DivisorTargets
import Theorems.Thm_OAI_SecondPassArithmetic_parity_ideal_pair_count
import Theorems.Thm_OAI_SecondPassArithmetic_cubeParityKey_norm_product
import Theorems.Thm_OAI_SecondPassArithmetic_cubeParityKey_active_bound
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
import Theorems.Thm_OAI_SecondPassArithmetic_cubeParityKey_fiber_card
import Theorems.Thm_OAI_SecondPassArithmetic_cubeParityKey_ne_zero
import Theorems.Thm_OAI_SecondPassArithmetic_descent_normLogBin_small_power
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
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (s : Finset (CubeCoordinates ι)) (B H : ℝ),
      1≤B → 0≤H → (∀ x∈s,x.Admissible) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.leftExponent)‖^2≤B) →
      (∀ x∈s,‖eisEmbedding (primeProduct p x.support x.rightExponent)‖^2≤B) →
      (∀ x∈s,‖eisEmbedding (∏ i∈cubeActiveSupport x.support
        (fun i => x.leftExponent i+x.rightExponent i) x.leftBit x.rightBit,p i)‖≤H) →
      (s.card : ℝ)≤C*B^(1+ε)*H := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/12) (by positivity)
  let C := D^3*(16384*Real.exp 1)*(1+1/(ε/4))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ι _ p hp _ hinj s B H hB hH hs hb1 hb2 ha
  have hB0 : 0<B := by linarith
  have hprod (x : CubeCoordinates ι) (hx : x∈s) :
      (Ideal.absNorm (cubeParityKey p x).2 : ℝ)^2*Ideal.absNorm (cubeParityKey p x).1≤B^2 := by
    rw [cubeParityKey_norm_product]
    simpa only [pow_two] using mul_le_mul (hb1 x hx) (hb2 x hx) (sq_nonneg _) hB0.le
  let Q := s.image (cubeParityKey p)
  have hQ (q : Ideal O × Ideal O) (hq : q∈Q) :
      q.1≠0 ∧ q.2≠0 ∧ (Ideal.absNorm q.2 : ℝ)^2*Ideal.absNorm q.1≤B^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(cubeParityKey_ne_zero p hp x).1,(cubeParityKey_ne_zero p hp x).2,hprod x hx⟩
  have hQactive (q : Ideal O × Ideal O) (hq : q∈Q) : (Ideal.absNorm q.1 : ℝ)≤H^2 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact cubeParityKey_active_bound p hp x H (ha x hx)
  have hfiber (q : Ideal O × Ideal O) (hq : q∈Q) :
      ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤D^3*B^(ε/2) := by
    have hq0 := hQ q hq
    have hqprod0 : q.2^2*q.1≠0 := mul_ne_zero (pow_ne_zero _ hq0.2.1) hq0.1
    have hc : ((s.filter (fun x => cubeParityKey p x=q)).card : ℝ)≤
        ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := by
      exact_mod_cast cubeParityKey_fiber_card p hp hinj (s.filter (fun x => cubeParityKey p x=q)) q
        hq0.1 hq0.2.1 (fun x hx => hs x (Finset.mem_filter.mp hx).1)
        (fun x hx => (Finset.mem_filter.mp hx).2)
    have hn : (Ideal.absNorm (q.2^2*q.1) : ℝ)≤B^2 := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hq0.2.2
    calc
      _ ≤ ((idealDivisors (q.2^2*q.1)).card : ℝ)^3 := hc
      _ ≤ (D*(Ideal.absNorm (q.2^2*q.1) : ℝ)^(ε/12))^3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ hqprod0) 3
      _ ≤ (D*(B^2)^(ε/12))^3 := by gcongr
      _ = D^3*B^(ε/2) := by
        rw [mul_pow]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul (sq_nonneg B),
          ←Real.rpow_natCast,←Real.rpow_mul hB0.le]
        congr 1
        ring
  have hqcard := parity_ideal_pair_count Q B H hB0 hH hQ hQactive
  have hlog := descent_normLogBin_small_power (ε/4) (by positivity) (B^2) (one_le_pow₀ hB)
  have hlog' : (normLogBin (B^2)+1 : ℝ)≤(1+1/(ε/4))*B^(ε/2) := by
    convert hlog using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hB0.le]
    congr 2
    ring
  have hsum : (s.card : ℝ)=∑q∈Q,((s.filter (fun x => cubeParityKey p x=q)).card : ℝ) := by
    calc
      _ = ∑_x∈s,(1 : ℝ) := by simp
      _ = ∑q∈Q,∑_x∈s.filter (fun x => cubeParityKey p x=q),(1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem (cubeParityKey p) hx) _).symm
      _ = _ := by simp
  rw [hsum]
  calc
    _ ≤ ∑_q∈Q,D^3*B^(ε/2) := Finset.sum_le_sum hfiber
    _ = (Q.card : ℝ)*(D^3*B^(ε/2)) := by simp
    _ ≤ (16384*Real.exp 1*B*H*(normLogBin (B^2)+1 : ℝ))*(D^3*B^(ε/2)) := by gcongr
    _ ≤ (16384*Real.exp 1*B*H*((1+1/(ε/4))*B^(ε/2)))*(D^3*B^(ε/2)) := by gcongr
    _ = C*B^(1+ε)*H := by
      rw [Real.rpow_add hB0,Real.rpow_one]
      have he : B^(ε/2)*B^(ε/2)=B^ε := by rw [←Real.rpow_add hB0]; congr 1; ring
      dsimp [C]
      calc
        _ = D^3*(16384*Real.exp 1)*(1+1/(ε/4))*B*(B^(ε/2)*B^(ε/2))*H := by ring
        _ = _ := by rw [he]; ring
end OAI.SecondPassArithmetic
