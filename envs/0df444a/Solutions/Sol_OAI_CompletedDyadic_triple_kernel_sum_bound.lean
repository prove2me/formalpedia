-- Prove2me | solution 1 for OAI.CompletedDyadic.triple_kernel_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:02:33.875428+00:00
-- url     : https://prove2.me/submissions/ce40a2e6-7e31-4ac0-b0da-b6c8f7760689

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
import Theorems.Thm_OAI_CompletedDyadic_weighted_scale_identity
import Theorems.Thm_OAI_CompletedDyadic_double_kernel_sum_bound
import Theorems.Thm_OAI_CompletedDyadic_ramifiedScale_pos
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CompletedDyadic_kernelTerm_nonneg
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
open scoped BigOperators
open OAI.CompletedDyadic
namespace OAI.CompletedDyadic
theorem _root_.solution (s A β ρ q : ℝ)
    (hs : 0<s) (hsA : s<A) (hβ : β<3*s) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      (∀m b : ℕ,Summable (kernelTerm
        (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A)) ∧
      (∀m : ℕ,Summable (fun b : ℕ => ((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u)) ∧
      Summable (fun m : ℕ => (ramifiedScale ρ q m)⁻¹*
        ∑'b : ℕ,((2:ℝ)^b)^β*
          ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u) ∧
      (∑'m : ℕ,(ramifiedScale ρ q m)⁻¹*
        ∑'b : ℕ,((2:ℝ)^b)^β*
          ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u)
        ≤C*t^(-s) := by
  obtain ⟨Cb,hCb,hb⟩ := double_kernel_sum_bound s A β hs hsA hβ
  let v : ℝ := q^(-1-3*s)
  have hv : v<1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hq0 : 0<q := by linarith
  have hv0 : 0≤v := by dsimp [v]; positivity
  let B : ℝ := Cb*ρ^(-1-3*s)
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B/(1-v),by positivity,?_⟩
  intro t ht
  have hm (m : ℕ) := hb (t*(ramifiedScale ρ q m)^3) (by
    have := ramifiedScale_pos ρ q hρ hq0 m
    positivity)
  have hn (m : ℕ) : 0≤(ramifiedScale ρ q m)⁻¹*
      ∑'b : ℕ,((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u := by
    apply mul_nonneg (le_of_lt (inv_pos.mpr (ramifiedScale_pos ρ q hρ hq0 m)))
    apply tsum_nonneg
    intro b
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (kernelTerm_nonneg _ s A (by
      have := ramifiedScale_pos ρ q hρ hq0 m
      positivity))
  have hbound (m : ℕ) : (ramifiedScale ρ q m)⁻¹*
      ∑'b : ℕ,((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u
      ≤(B*t^(-s))*v^m := by
    have hr := ramifiedScale_pos ρ q hρ hq0 m
    calc
      _ ≤ (ramifiedScale ρ q m)⁻¹*(Cb*(t*(ramifiedScale ρ q m)^3)^(-s)) :=
        mul_le_mul_of_nonneg_left (hm m).2.2 (by positivity)
      _ = Cb*((ramifiedScale ρ q m)^(-1:ℝ)*(t*(ramifiedScale ρ q m)^3)^(-s)) := by
        rw [Real.rpow_neg_one]; ring
      _ = Cb*(t^(-s)*(ramifiedScale ρ q m)^(-1-3*s)) := by
        rw [weighted_scale_identity _ t (-1) s hr ht]
      _ = _ := by
        rw [ramifiedScale,Real.mul_rpow hρ.le (pow_nonneg hq0.le _),
          ←Real.rpow_natCast_mul hq0.le,
          mul_comm (m:ℝ) (-1-3*s),Real.rpow_mul_natCast hq0.le]
        dsimp [B,v]
        ring
  have hg := (summable_geometric_of_lt_one hv0 hv).mul_left (B*t^(-s))
  have hf := hg.of_nonneg_of_le hn hbound
  refine ⟨fun m b => (hm m).1 b,fun m => (hm m).2.1,hf,?_⟩
  have hfinal := hf.tsum_le_tsum hbound hg
  rw [tsum_mul_left,tsum_geometric_of_lt_one hv0 hv] at hfinal
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hfinal
end OAI.CompletedDyadic
