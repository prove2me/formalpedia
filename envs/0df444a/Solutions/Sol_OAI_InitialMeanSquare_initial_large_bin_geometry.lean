-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_large_bin_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:11:56.92262+00:00
-- url     : https://prove2.me/submissions/3791eb50-33c5-430d-8dea-83917435a108

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_RetainedDensity
import Theorems.Thm_OAI_InitialMeanSquare_initialLogColumn_le
import Theorems.Thm_OAI_InitialMeanSquare_initialLogLabel_cap
import Theorems.Thm_OAI_InitialMeanSquare_initial_radial_invariant
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
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_InitialMeanSquare_initialErrorRowBound_ge_one
import Theorems.Thm_OAI_InitialMeanSquare_initialLogProfile_apply
import Theorems.Thm_OAI_InitialMeanSquare_initial_actual_bin_polynomial_caps
import Theorems.Thm_OAI_InitialMeanSquare_initial_bin_row_scale_le
import Theorems.Thm_OAI_InitialMeanSquare_initial_log_mass
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
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newLabel
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportTuple_newRow
import Theorems.Thm_OAI_SecondPassIntegration_conjugateProfile_apply
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
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
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply



set_option autoImplicit false
open OAI
noncomputable section
open OAI.InitialMeanSquare
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
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)
namespace OAI.InitialMeanSquare
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z σ θ deltaLoss c : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hc : 1 ≤ c)
    (hR : R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)))
    (hj : j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b))
      (initialErrorRowBound a b Z (Z^(1+σ))))
    (hσ : 0 ≤ σ) (hmargin : deltaLoss+θ ≤ σ-(1 : ℝ)/20)
    (hlarge : Real.exp 2 ≤ Z ∧ c*Real.exp (initialErrorWindow a b) ≤ Z ∧
      initialPolynomialCap a b*Real.exp 2 ≤ Z ∧
      (Real.exp (initialErrorWindow a b))^2*Real.exp 2 ≤ Z ∧ c ≤ Z^deltaLoss)
    (hrad : initialRadial Z (Z^(1+σ)) (primeProductNorm p R) j ≤ Z^θ) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let lengthScale := initialLogLabel j
    let K := secondLogK j*Real.exp 2
    X ≤ Z^20 ∧ lengthScale ≤ Z^20 ∧ K ≤ Z^20 ∧ c*primeProductNorm p R ≤ Z^20 ∧
      X*lengthScale ≤ Z^2 ∧ K*(c*primeProductNorm p R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) := by
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hB := primeProductNorm_ge_one p hp R
  have hBp := zero_lt_one.trans_le hB
  have hU : 1 ≤ Z*Real.exp (initialErrorWindow a b) := one_le_mul_of_one_le_of_one_le hZ
    (Real.one_le_exp (by unfold initialErrorWindow; positivity))
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
  have hBcap := (Finset.mem_filter.mp hR).2
  have hKcap := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
  have hKbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
    (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
  have hL := initialLogLabel_cap _ _ hU j hj
  have hp20 (n : ℕ) (hn : n ≤ 20) : Z^n ≤ Z^20 := pow_le_pow_right₀ hZ hn
  have hinv := initial_radial_invariant Z (primeProductNorm p R) c σ θ deltaLoss
    ((1 : ℝ)/20) j hZ hBp (zero_le_one.trans hc) hlarge.2.2.2.2 hmargin hrad
  rw [show -((1 : ℝ)/20)=(-1 : ℝ)/20 by ring] at hinv
  refine ⟨?_,?_,?_,?_,?_,hinv⟩
  · exact (initialLogColumn_le Z _ j hZ0.le hB).trans (by simpa using hp20 1 (by decide))
  · apply hL.trans
    calc
      _ = ((Real.exp (initialErrorWindow a b))^2*Real.exp 2)*Z^2 := by ring
      _ ≤ Z*Z^2 := mul_le_mul_of_nonneg_right hlarge.2.2.2.1 (sq_nonneg Z)
      _ ≤ Z^20 := by simpa [pow_succ,mul_comm] using hp20 3 (by decide)
  · calc
      _ ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
        mul_le_mul_of_nonneg_right (hKbin.trans hKcap) (Real.exp_pos _).le
      _ = (initialPolynomialCap a b*Real.exp 2)*Z^17 := by ring
      _ ≤ Z*Z^17 := mul_le_mul_of_nonneg_right hlarge.2.2.1 (pow_nonneg hZ0.le _)
      _ ≤ Z^20 := by simpa [pow_succ,mul_comm] using hp20 18 (by decide)
  · calc
      _ ≤ c*(Z*Real.exp (initialErrorWindow a b)) := mul_le_mul_of_nonneg_left hBcap (zero_le_one.trans hc)
      _ = (c*Real.exp (initialErrorWindow a b))*Z := by ring
      _ ≤ Z*Z := mul_le_mul_of_nonneg_right hlarge.2.1 hZ0.le
      _ ≤ Z^20 := by simpa [pow_two] using hp20 2 (by decide)
  · rw [initial_log_mass Z (primeProductNorm p R) hBp.ne' j]
    calc
      _ ≤ Z*Real.exp 2 := mul_le_mul_of_nonneg_right (div_le_self hZ0.le hB) (Real.exp_pos _).le
      _ ≤ Z^2 := by simpa [pow_two] using mul_le_mul_of_nonneg_left hlarge.1 hZ0.le
end OAI.InitialMeanSquare
