-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.bounded_nonzero_quadratic_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:30:52.449458+00:00
-- url     : https://prove2.me/submissions/0448d57e-ab3c-41f7-8a36-c24c98f80aed

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnSquareFiber_nonzero_card
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnSquareFiber_all_energy
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnSquareParts_nonzero_bounds
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CanonicalQuadraticSieve_columnDyadicLength_small_power
import Theorems.Thm_OAI_CanonicalQuadraticSieve_finite_inverse_norm_sum
import Theorems.Thm_OAI_CanonicalQuadraticSieve_ideal_reciprocal_cauchy
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_sharp
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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K X lengthScale : ℝ,
      1≤K → 1≤X → 0≤lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖≤lengthScale) →
      (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤
        C*(K*X)^ε*(K+X)*X*lengthScale^2 := by
  intro ε hε
  let deltaLoss := ε/3
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := 256*(2+1/(deltaLoss*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨512*C*D^2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image squarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0<K := by linarith
  have hX0 : 0<X := by linarith
  have hP0 : 0<K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_nonzero_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0≤R := by dsimp [R]; positivity
  have hRL : R≤D*X^deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    nlinarith
  let F : ℝ := 512*C*(K*X)^deltaLoss*(K+X)*X*lengthScale^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : idealRange K,‖∑I∈columnSquareFiber S A,
        quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0<(Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ)^2
    have hY : 1≤Y := hp.2.2.2
    have hYX : Y≤X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K≤C*(K*X)^deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K≤K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0≤Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖^2)≤128*Y*lengthScale^2 := by
      calc
        _ ≤ ∑_I∈columnSquareFiber S A,lengthScale^2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (columnSquareFiber_nonzero_card S X hS A hY) (sq_nonneg _)
    have he := columnSquareFiber_all_energy S X K hS A a
    calc
      _ ≤ (Ideal.absNorm A:ℝ)*(4*sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖^2)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ ≤ (Ideal.absNorm A:ℝ)*((4*C*(K*X)^deltaLoss*(K+X))*(128*Y*lengthScale^2)) := by
        have h4 := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4)
        have hh := mul_le_mul h4 hea (by positivity) (by positivity)
        have hw := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) (Ideal.absNorm A))
        convert hw using 1 <;> first | rfl | ring
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne'] ; ring
  have hsplit (k : idealRange K) :
      (∑I∈S,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarePart hI) _).symm
  have hcauchy (k : idealRange K) :
      ‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2≤
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F*R^2 := by
    calc
      _ ≤ ∑k : idealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : idealRange K,‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _ ≤ R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R^2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X)^deltaLoss*(X^deltaLoss)^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^deltaLoss*((K*X)^deltaLoss)^2 := by gcongr
      _ = (K*X)^ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _ ≤ F*(D*X^deltaLoss)^2 := by gcongr
    _ = (512*C*D^2)*((K*X)^deltaLoss*(X^deltaLoss)^2)*(K+X)*X*lengthScale^2 := by dsimp [F]; ring
    _ ≤ _ := by gcongr
end OAI.CanonicalQuadraticSieve
