-- Prove2me | solution 1 for Malliavin.indicator_brownianCylinder_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:52.916716+00:00
-- url     : https://prove2.me/submissions/5eb5507a-ae47-4ec8-b6c5-4231793191b8

import Definitions.Def_Malliavin_PastCylinderDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Theorems.Thm_Malliavin_dense_gaussianPolynomialSpan
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IsWienerGenerated_measurable
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule


section
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
section GaussianPolynomial
variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
  (μ : Measure E) [IsGaussian μ]
end GaussianPolynomial
section BrownianPolynomial
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    [IsGaussian P] in
private theorem stepSum_brownianDualCoefficients (I : Finset ℝ≥0)
    (K : StrongDual ℝ (I → ℝ)) (w : W) :
    stepSum B (brownianDualCoefficients I K) w = K (fun i ↦ B i w) := by
  classical
  rw [show K (fun i ↦ B i w) =
      K (∑ i : I, B i w • (Pi.single i (1 : ℝ) : I → ℝ)) by
    congr 1
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_ite_eq]]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  simp only [stepSum, brownianDualCoefficients, Finsupp.sum_embDomain]
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ zero_mul _)]
  apply Finset.sum_congr rfl
  intro i _hi
  change K (Pi.single i 1) * B i w = B i w * K (Pi.single i 1)
  ring
end BrownianPolynomial
end Malliavin
end
end

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B)
    {s : Set W} (hs : s ∈ brownianCylinderEvents B) :
    indicatorConstLp 2 (measurableSet_brownianCylinderEvents hgen hs)
        (measure_ne_top P s) (1 : ℝ) ∈
      (brownianPolynomialSpan hB).topologicalClosure := by
  rcases hs with ⟨C, hC, rfl⟩
  rcases (mem_measurableCylinders C).mp hC with ⟨I, A, hA, rfl⟩
  let L : W → (I → ℝ) := fun w i ↦ B i w
  have hL : Measurable L := by
    apply measurable_pi_lambda
    intro i
    exact hgen.measurable i
  let ν : Measure (I → ℝ) := P.map L
  let _ : IsGaussian ν := by
    dsimp only [ν, L]
    exact (hB.isGaussianProcess.hasGaussianLaw I).isGaussian_map
  let hmp : MeasurePreserving L P ν := hL.measurePreserving P
  let Y : Lp ℝ 2 ν :=
    indicatorConstLp 2 hA (measure_ne_top ν A) (1 : ℝ)
  have hset : brownianProcess B ⁻¹' cylinder I A = L ⁻¹' A := by
    ext w
    simp only [Set.mem_preimage, mem_cylinder, Finset.restrict_def,
      brownianProcess, L]
  change indicatorConstLp 2
      (measurableSet_brownianCylinderEvents hgen
        ⟨cylinder I A, hC, rfl⟩)
      (measure_ne_top P (brownianProcess B ⁻¹' cylinder I A)) (1 : ℝ) ∈
    closure (brownianPolynomialSpan hB : Set (RandomL2 P))
  refine Metric.mem_closure_iff.mpr fun ε hε ↦ ?_
  have hY : Y ∈ closure (gaussianPolynomialSpan ν : Set (Lp ℝ 2 ν)) :=
    dense_gaussianPolynomialSpan ν Y
  rcases Metric.mem_closure_iff.mp hY ε hε with ⟨Z, hZ, hdist⟩
  let pull : Lp ℝ 2 ν →ₗ[ℝ] RandomL2 P :=
    Lp.compMeasurePreservingₗ ℝ L hmp
  have hpull (K : StrongDual ℝ (I → ℝ)) (n : ℕ) :
      pull (gaussianLinearPowerLp ν K n) =
        brownianStepPowerLp hB (brownianDualCoefficients I K) n := by
    unfold pull gaussianLinearPowerLp brownianStepPowerLp
    change Lp.compMeasurePreserving L hmp
        ((memLp_two_dual_pow ν K n).toLp fun x ↦ K x ^ n) = _
    rw [Lp.toLp_compMeasurePreserving]
    apply MemLp.toLp_congr
    filter_upwards with w
    simp only [Function.comp_apply, stepSum_brownianDualCoefficients]
    rfl
  have hpull_mem {Z : Lp ℝ 2 ν} (hZ : Z ∈ gaussianPolynomialSpan ν) :
      pull Z ∈ brownianPolynomialSpan hB := by
    induction hZ using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨⟨K, n⟩, rfl⟩ := hz
        rw [hpull K n]
        exact Submodule.subset_span
          ⟨(brownianDualCoefficients I K, n), rfl⟩
    | zero => exact (brownianPolynomialSpan hB).zero_mem
    | add x y _hx _hy hx hy =>
        rw [map_add]
        exact (brownianPolynomialSpan hB).add_mem hx hy
    | smul c x _hx hx =>
        rw [map_smul]
        exact (brownianPolynomialSpan hB).smul_mem c hx
  refine ⟨pull Z, hpull_mem hZ, ?_⟩
  have hI : indicatorConstLp 2
      (measurableSet_brownianCylinderEvents hgen
        ⟨cylinder I A, hC, rfl⟩)
      (measure_ne_top P (brownianProcess B ⁻¹' cylinder I A)) (1 : ℝ) =
      Lp.compMeasurePreserving L hmp Y := by
    rw [Lp.indicatorConstLp_compMeasurePreserving]
    congr 1
  rw [hI]
  change dist (Lp.compMeasurePreserving L hmp Y)
      (Lp.compMeasurePreserving L hmp Z) < ε
  rw [(Lp.isometry_compMeasurePreserving hmp).dist_eq]
  exact hdist
end Malliavin
