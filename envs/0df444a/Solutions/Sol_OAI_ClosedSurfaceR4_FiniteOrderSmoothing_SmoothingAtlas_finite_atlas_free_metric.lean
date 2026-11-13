-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_free_metric
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:43:21.82846+00:00
-- url     : https://prove2.me/submissions/539764d6-5234-4f20-b6c1-b9360a1bfedf

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_atlas_zeroPhase

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalFrame
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.NormalFrame

lemma unitPerp_unit {X Y B : Vec} (hD : gramDet X Y ≠ 0) (hB : B ≠ 0)
    (hX : X ⬝ᵥ B = 0) (hY : Y ⬝ᵥ B = 0) : unitPerp X Y B ⬝ᵥ unitPerp X Y B = 1 := by
  have hp := perp_sq_pos hD hB hX hY
  have hs : Real.sqrt (perpProduct X Y B ⬝ᵥ perpProduct X Y B) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have he := Real.sq_sqrt hp.le
  simp only [unitPerp, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  nlinarith [he]

end ClosedSurfaceR4.NormalFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

lemma phase_add (θ ψ : ℝ) : phase (θ + ψ) = phase θ * phase ψ := by
  simp only [phase, ofReal_add, add_mul, Complex.exp_add]

lemma phase_conj (θ : ℝ) : star (phase θ) = phase (-θ) := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, ofReal_neg]
  congr 1
  ring

lemma phase_sub (θ ψ : ℝ) : phase (θ - ψ) = phase θ * star (phase ψ) := by
  rw [phase_conj, ← phase_add, sub_eq_add_neg]

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma real_product (a b : ℂ) : a.re * b.re = ((a * star b).re + (a * b).re) / 2 := by
  simp only [Complex.star_def, mul_re, conj_re, conj_im]
  ring

lemma mode_product (θ ψ : ℝ) (a b : ℂ) :
    (phase θ * a).re * (phase ψ * b).re =
      ((phase (θ - ψ) * (a * star b)).re + (phase (θ + ψ) * (a * b)).re) / 2 := by
  rw [real_product, phase_sub, phase_add]
  simp only [Complex.star_def, map_mul]
  congr 2 <;> congr 1 <;> ring



theorem realMode_dot {n : ℕ} (θ ψ : ℝ) (A B : CVec n) :
    realMode θ A ⬝ᵥ realMode ψ B =
      ((phase (θ - ψ) * (A ⬝ᵥ conjugate B)).re +
        (phase (θ + ψ) * (A ⬝ᵥ B)).re) / 2 := by
  unfold realMode realPart dotProduct conjugate
  simp only [Pi.smul_apply, smul_eq_mul, mode_product, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]




theorem realMode_self_phase {n : ℕ} (θ : ℝ) (A B : CVec n) :
    realMode θ A ⬝ᵥ realMode θ B =
      (A ⬝ᵥ conjugate B).re / 2 + (phase (2 * θ) * (A ⬝ᵥ B)).re / 2 := by
  rw [realMode_dot, sub_self, phase_zero, one_mul]
  have h : θ + θ = 2 * θ := by ring
  rw [h, add_div]



lemma phase_comp_hasFDerivAt {φ : Base → ℝ} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (τ : ℝ) :
    HasFDerivAt (fun q => phase (φ q / τ))
      (phase (φ p / τ) • ((I / (τ : ℂ)) • (Complex.ofRealCLM.comp (fderiv ℝ φ p)))) p := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp p hφ.hasFDerivAt).const_mul
    (I / (τ : ℂ))).cexp
  have he (q : Base) : phase (φ q / τ) = Complex.exp (I / (τ : ℂ) * (φ q : ℂ)) := by
    simp only [phase, ofReal_div]
    congr 1
    ring
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, he] using h

lemma derivative_displacement {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v : Base) :
    fderiv ℝ (displacement τ φ Z) p v =
      realMode (φ p / τ) (derivativeAmplitude τ φ Z v p) := by
  have hc := ((phase_comp_hasFDerivAt hφ τ).fun_smul hZ.hasFDerivAt)
  have hr := (realPartCLM n).hasFDerivAt.comp p hc
  simp only [Function.comp_def] at hr
  rw [show displacement τ φ Z = fun q => realPartCLM n (phase (φ q / τ) • Z q) from rfl,
    hr.fderiv]
  ext i
  simp only [realPartCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    Complex.reCLM_apply, ContinuousLinearMap.proj_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    Complex.ofRealCLM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    realMode, realPart, derivativeAmplitude]
  congr 1
  ring




theorem finite_phase_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) (A B : ι → CVec n) :
    (∑ i, realMode (θ i) (A i)) ⬝ᵥ (∑ i, realMode (θ i) (B i)) =
      (∑ i, zeroPair (A i) (B i)) + (∑ i, doublePair (θ i) (A i) (B i)) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, crossPair (θ i) (θ j) (A i) (B j) := by
  simp only [sum_dotProduct, dotProduct_sum]
  have hi (i : ι) :
      ∑ j, realMode (θ i) (A i) ⬝ᵥ realMode (θ j) (B j) =
        zeroPair (A i) (B i) + doublePair (θ i) (A i) (B i) +
          ∑ j ∈ Finset.univ.erase i, crossPair (θ i) (θ j) (A i) (B j) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i), realMode_self_phase]
    simp only [realMode_dot, crossPair, zeroPair, doublePair]
    ring
  rw [Finset.sum_comm]
  simp only [hi, Finset.sum_add_distrib]

lemma differentiableAt_displacement {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) :
    DifferentiableAt ℝ (displacement τ φ Z) p :=
  ((realPartCLM n).hasFDerivAt.comp p
    ((phase_comp_hasFDerivAt hφ τ).fun_smul hZ.hasFDerivAt)).differentiableAt



theorem quadraticMetric_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) {φ : ι → Base → ℝ} {Z : ι → Base → CVec n} {p : Base}
    (hφ : ∀ i, DifferentiableAt ℝ (φ i) p) (hZ : ∀ i, DifferentiableAt ℝ (Z i) p)
    (v w : Base) :
    quadraticMetric (sumDisplacement τ φ Z) v w p = meanMetric τ φ Z v w p +
      (∑ i, doublePair (φ i p / τ) (derivativeAmplitude τ (φ i) (Z i) v p)
        (derivativeAmplitude τ (φ i) (Z i) w p)) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        crossPair (φ i p / τ) (φ j p / τ) (derivativeAmplitude τ (φ i) (Z i) v p)
          (derivativeAmplitude τ (φ j) (Z j) w p) := by
  have hd (v : Base) : fderiv ℝ (sumDisplacement τ φ Z) p v =
      ∑ i, realMode (φ i p / τ) (derivativeAmplitude τ (φ i) (Z i) v p) := by
    unfold sumDisplacement
    rw [fderiv_fun_sum (fun i _ => differentiableAt_displacement (hφ i) (hZ i) τ)]
    simp only [sum_apply, derivative_displacement (hφ _) (hZ _)]
  rw [quadraticMetric, hd v, hd w, finite_phase_expansion]
  rfl


lemma leadingAmplitude_zeroPair {n : ℕ} (δ b ξ ζ : ℝ) (N : RVec n)
    (hN : N ⬝ᵥ N = 1) :
    zeroPair (leadingAmplitude δ b ξ N) (leadingAmplitude δ b ζ N) =
      δ ^ 2 * b ^ 2 * ξ * ζ := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold zeroPair dotProduct conjugate leadingAmplitude
  simp only [Complex.star_def, map_mul, conj_I, conj_ofReal, Complex.re_sum,
    mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, mul_zero,
    zero_sub, sub_zero, zero_add, one_mul, neg_re, neg_im, neg_zero]
  have he (j : Fin n) :
      -(Real.sqrt 2 * δ * b * ξ * N j * -(Real.sqrt 2 * δ * b * ζ * N j)) =
        (2 * δ ^ 2 * b ^ 2 * ξ * ζ) * (N j * N j) := by
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) * δ ^ 2 * b ^ 2 * ξ * ζ * (N j * N j) := by ring
      _ = _ := by rw [hs]
  simp only [neg_one_mul, he, ← Finset.mul_sum]
  change 2 * δ ^ 2 * b ^ 2 * ξ * ζ * (N ⬝ᵥ N) / 2 = _
  rw [hN]
  ring

end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GradientBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma gradientAmplitude_eq {n : ℕ} (τ : ℝ) (Z : Field n) (v : Base) (p : Base) :
    gradientAmplitude τ Z v p =
      ClosedSurfaceR4.QuadraticMean.derivativeAmplitude τ Prod.fst Z v p := by
  simp [gradientAmplitude, ClosedSurfaceR4.QuadraticMean.derivativeAmplitude,
    coordDeriv, fderiv_fst]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_RealModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma freeNormal_unit {F : RField 4} {U : Set Base} (h : RealModeDomain F U)
    {p : Base} (hp : p ∈ U) : freeNormal F p ⬝ᵥ freeNormal F p = 1 := by
  have hn := realNormalPart_perp (coordDeriv dx F p) (coordDeriv dy F p)
    (coordDeriv dy (coordDeriv dy F) p) (h.determinant p hp)
  exact NormalFrame.unitPerp_unit (h.determinant p hp) (h.good p hp) hn.1 hn.2

lemma leadingDerivative_freeSeed {τ : ℝ} (hτ : τ ≠ 0) (δ : ℝ) (b : Base → ℝ)
    (F : RField 4) (v p : Base) :
    leadingDerivative τ (freeSeed δ τ b F) v p =
      ClosedSurfaceR4.QuadraticMean.leadingAmplitude δ (b p) v.1 (freeNormal F p) := by
  ext i
  have htc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  simp only [leadingDerivative, freeSeed, Pi.smul_apply, smul_eq_mul, complexify_apply,
    ClosedSurfaceR4.QuadraticMean.leadingAmplitude, Complex.ofReal_mul]
  field_simp



theorem freeSeed_zeroPair {F : RField 4} {U : Set Base} (h : RealModeDomain F U)
    {τ : ℝ} (hτ : τ ≠ 0) (δ : ℝ) (b : Base → ℝ) (v w : Base) {p : Base} (hp : p ∈ U) :
    ClosedSurfaceR4.QuadraticMean.zeroPair (leadingDerivative τ (freeSeed δ τ b F) v p)
      (leadingDerivative τ (freeSeed δ τ b F) w p) = δ ^ 2 * b p ^ 2 * v.1 * w.1 := by
  rw [leadingDerivative_freeSeed hτ, leadingDerivative_freeSeed hτ]
  exact ClosedSurfaceR4.QuadraticMean.leadingAmplitude_zeroPair _ _ _ _ _ (freeNormal_unit h hp)



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CrossModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.QuadraticMean (zeroPair derivativeAmplitude conjugate displacement
  doublePair crossPair realMode sumDisplacement quadraticMetric quadraticMetric_expansion
  differentiableAt_displacement)
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)


lemma displacement_doubleTensor {n : ℕ} (τ : ℝ) (φ : Base → ℝ)
    (Z : SmallModes.Field n) (p : Base) (i : Fin 3) :
    displacement τ (fun q => 2 * φ q) (phaseDoubleTensor τ φ Z) p i =
      doublePair (φ p / τ) (derivativeAmplitude τ φ Z (firstDirection i) p)
        (derivativeAmplitude τ φ Z (secondDirection i) p) := by
  simp only [displacement, realMode, QuadraticMean.realPart, phaseDoubleTensor, Pi.smul_apply, smul_eq_mul,
    ← mul_div_assoc, Complex.div_ofNat_re, doublePair]

lemma displacement_crossTensor {n : ℕ} (τ : ℝ) (φ ψ : Base → ℝ)
    (Z W : SmallModes.Field n) (p : Base) (i : Fin 3) :
    displacement τ (fun q => φ q - ψ q) (phaseMinusTensor τ φ ψ Z W) p i +
      displacement τ (fun q => φ q + ψ q) (phasePlusTensor τ φ ψ Z W) p i =
      crossPair (φ p / τ) (ψ p / τ) (derivativeAmplitude τ φ Z (firstDirection i) p)
        (derivativeAmplitude τ ψ W (secondDirection i) p) := by
  simp only [displacement, realMode, QuadraticMean.realPart, phaseMinusTensor, phasePlusTensor,
    Pi.smul_apply, smul_eq_mul, sub_div, add_div,
    ← mul_div_assoc, Complex.div_ofNat_re, crossPair]



lemma realMetric_sumDisplacement {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : ι → Base → ℝ} {Z : ι → SmallModes.Field n} {p : Base}
    (hφ : ∀ i, DifferentiableAt ℝ (φ i) p) (hZ : ∀ i, DifferentiableAt ℝ (Z i) p) (τ : ℝ) :
    realMetricTensor (sumDisplacement τ φ Z) p = zeroPhaseSum τ φ Z p +
      nonzeroPhaseSum τ φ Z p := by
  ext k
  rw [realMetricTensor_apply]
  change quadraticMetric (sumDisplacement τ φ Z) (firstDirection k) (secondDirection k) p = _
  rw [quadraticMetric_expansion τ hφ hZ]
  simp only [zeroPhaseSum, nonzeroPhaseSum, phaseZeroTensor, QuadraticMean.meanMetric, Pi.add_apply, Finset.sum_apply,
    displacement_doubleTensor, displacement_crossTensor]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanBilinearity
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

lemma zeroPair_add_left {n : ℕ} (A B C : CVec n) :
    zeroPair (A + B) C = zeroPair A C + zeroPair B C := by
  simp [zeroPair, add_dotProduct, add_div]

lemma zeroPair_add_right {n : ℕ} (A B C : CVec n) :
    zeroPair A (B + C) = zeroPair A B + zeroPair A C := by
  have hc : conjugate (B + C) = conjugate B + conjugate C := by
    ext i; simp [conjugate]
  simp [zeroPair, hc, dotProduct_add, add_div]

lemma zeroPair_smul_left {n : ℕ} (a : ℝ) (A B : CVec n) :
    zeroPair (a • A) B = a * zeroPair A B := by
  simp [zeroPair, smul_dotProduct, mul_div_assoc]

lemma zeroPair_smul_right {n : ℕ} (a : ℝ) (A B : CVec n) :
    zeroPair A (a • B) = a * zeroPair A B := by
  have hc : conjugate (a • B) = a • conjugate B := by
    ext i; simp [conjugate]
  simp [zeroPair, hc, dotProduct_smul, mul_div_assoc]

lemma zeroPair_comm {n : ℕ} (A B : CVec n) : zeroPair A B = zeroPair B A := by
  unfold zeroPair dotProduct conjugate
  simp only [Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

end ClosedSurfaceR4.QuadraticMean

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean
open ClosedSurfaceR4.QuadraticMean (zeroPair derivativeAmplitude zeroPair_add_left
  zeroPair_add_right zeroPair_smul_left zeroPair_smul_right zeroPair_comm)

lemma gradientAmplitude_base_decomposition {n : ℕ} (τ : ℝ) (Z : Field n) (v p : Base) :
    gradientAmplitude τ Z v p = v.1 • gradientAmplitude τ Z dx p +
      v.2 • gradientAmplitude τ Z dy p := by
  unfold gradientAmplitude
  have hd : coordDeriv v Z p = v.1 • coordDeriv dx Z p + v.2 • coordDeriv dy Z p := by
    unfold coordDeriv
    conv_lhs => rw [base_decomposition v]
    simp only [map_add, map_smul]
  rw [hd]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, dx, dy, Complex.ofReal_one, Complex.ofReal_zero,
    mul_one, mul_zero, zero_smul, add_zero, smul_add, smul_eq_mul, Complex.real_smul]
  ring

lemma evaluate_phaseZeroTensor {n : ℕ} (τ : ℝ) (Z : Field n) (p v w : Base) :
    evaluate (phaseZeroTensor τ Prod.fst Z p) v w =
      zeroPair (gradientAmplitude τ Z v p) (gradientAmplitude τ Z w p) := by
  rw [gradientAmplitude_base_decomposition τ Z v p, gradientAmplitude_base_decomposition τ Z w p]
  simp only [zeroPair_add_left, zeroPair_add_right, zeroPair_smul_left, zeroPair_smul_right]
  unfold evaluate phaseZeroTensor
  simp only [← gradientAmplitude_eq, firstDirection, secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [zeroPair_comm (gradientAmplitude τ Z dy p) (gradientAmplitude τ Z dx p)]
  ring

lemma derivativeAmplitude_coordinate {n : ℕ} {Z : Field n} {χ : Base → Base} {p : Base}
    (hZ : DifferentiableAt ℝ Z (χ p)) (hχ : DifferentiableAt ℝ χ p) (τ : ℝ) (v : Base) :
    derivativeAmplitude τ (fun p => (χ p).1) (Z ∘ χ) v p =
      gradientAmplitude τ Z (fderiv ℝ χ p v) (χ p) := by
  have hfst : DifferentiableAt ℝ (Prod.fst : Base → ℝ) (χ p) := differentiableAt_fst
  change derivativeAmplitude τ (Prod.fst ∘ χ) (Z ∘ χ) v p = _
  simp only [derivativeAmplitude, gradientAmplitude, coordDeriv,
    fderiv_comp p hZ hχ, fderiv_comp p hfst hχ, fderiv_fst,
    ContinuousLinearMap.comp_apply]
  rfl

lemma phaseZeroTensor_coordinate {n : ℕ} {Z : Field n} {χ : Base → Base} {p : Base}
    (hZ : DifferentiableAt ℝ Z (χ p)) (hχ : DifferentiableAt ℝ χ p) (τ : ℝ) :
    phaseZeroTensor τ (fun p => (χ p).1) (Z ∘ χ) p =
      pullbackField χ p (phaseZeroTensor τ Prod.fst Z (χ p)) := by
  ext i
  change zeroPair (derivativeAmplitude τ (fun p => (χ p).1) (Z ∘ χ) (firstDirection i) p)
    (derivativeAmplitude τ (fun p => (χ p).1) (Z ∘ χ) (secondDirection i) p) =
    evaluate (phaseZeroTensor τ Prod.fst Z (χ p))
      (fderiv ℝ χ p (firstDirection i)) (fderiv ℝ χ p (secondDirection i))
  rw [derivativeAmplitude_coordinate hZ hχ, derivativeAmplitude_coordinate hZ hχ,
    evaluate_phaseZeroTensor]




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_FreeAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.RootMean
open ClosedSurfaceR4.WeightedEstimates Set
open ClosedSurfaceR4.QuadraticMean (derivativeAmplitude zeroPair)


lemma phaseZeroTensor_zero {n : ℕ} (τ : ℝ) (φ : Base → ℝ) (p : Base) :
    phaseZeroTensor τ φ (fun _ => (0 : Ambient n)) p = 0 := by
  ext i
  simp [phaseZeroTensor, derivativeAmplitude, zeroPair]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedNormalSeed
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported normal seeds and the exact leading quadratic metric. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm )

lemma corrected_seed_mean (δ : ℝ) {τ : ℝ} (hτ : τ ≠ 0) {F : RField 4} {U : Set Base}
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (b : SupportedField (F := ℝ) K)
    (T : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Ambient 4) K)
    (v w p : Base) (hp : p ∈ U) :
    let V := supportedFreeSeed δ τ hF h K hKU b
    QuadraticMean.zeroPair (gradientAmplitude τ (T V) v p) (gradientAmplitude τ (T V) w p) =
      δ ^ 2 * b p ^ 2 * v.1 * w.1 + seedMeanError τ T V V v w p := by
  dsimp only
  have hh := freeSeed_zeroPair h hτ δ b v w hp
  change QuadraticMean.zeroPair (leadingDerivative τ (supportedFreeSeed δ τ hF h K hKU b) v p)
      (leadingDerivative τ (supportedFreeSeed δ τ hF h K hKU b) w p) = _ at hh
  rw [seedMeanError, hh]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedPerturbedMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.chartPush_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization of the actual corrected metric mean by the seed amplitude. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates
open JetPolynomial (SupportedField supportedWeightedSeminorm)

variable {F : RField 4} {U : Set Base}

lemma perturbed_seed_mean_identity (δ τ : ℝ) (hδ : δ ≠ 0) (hτ : τ ≠ 0)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient 4) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (b : SupportedField (F := ℝ) K) (v w p : Base) (hp : p ∈ U) :
    let V := supportedFreeSeed δ τ hF h K hKU b
    let T := perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) K hKU R q
    QuadraticMean.zeroPair (gradientAmplitude τ (T V) v p) (gradientAmplitude τ (T V) w p) =
      δ ^ 2 * (b p ^ 2 * v.1 * w.1 + normalizedPerturbedMean δ τ hF h K hKU R q b v w p) := by
  dsimp only
  rw [corrected_seed_mean δ hτ hF h K hKU b _ v w p hp, normalizedPerturbedMean]
  field_simp [hδ]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedZeroMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual zero phase of a transported free amplitude. The metric
part transforms as a covariant tensor through the phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes
open QuadraticMean (derivativeAmplitude)

lemma phaseZeroTensor_congr {n : ℕ} {φ ψ : Base → ℝ} {Z W : Field n} {p : Base}
    (hφ : φ =ᶠ[nhds p] ψ) (hZ : Z =ᶠ[nhds p] W) (τ : ℝ) :
    phaseZeroTensor τ φ Z p = phaseZeroTensor τ ψ W p := by
  unfold phaseZeroTensor derivativeAmplitude
  rw [Filter.EventuallyEq.fderiv_eq hφ, Filter.EventuallyEq.fderiv_eq hZ, hZ.eq_of_nhds]

lemma phaseZeroTensor_chart {n : ℕ}
    (e : OpenPartialHomeomorph Base Base) (he : ContDiffOn ℝ ∞ e e.source)
    (K : Compacts Base) (hK : (K : Set Base) ⊆ e.source)
    {φ : Base → ℝ} (hφ : ∀ x ∈ e.source, (e x).1 = φ x) (τ : ℝ)
    (Z : JetPolynomial.SupportedField (F := Ambient n) (JetPolynomial.chartSupport e K hK))
    {p : Base} (hp : p ∈ e.source) :
    phaseZeroTensor τ φ (JetPolynomial.chartPull e he K hK Z) p =
      PhaseMean.pullbackField e p (phaseZeroTensor τ Prod.fst Z (e p)) := by
  have hphase : φ =ᶠ[nhds p] (fun x => (e x).1) := by
    filter_upwards [e.open_source.mem_nhds hp] with x hx using (hφ x hx).symm
  have hseed : (JetPolynomial.chartPull e he K hK Z : Field n) =ᶠ[nhds p] Z ∘ e := by
    filter_upwards [e.open_source.mem_nhds hp] with x hx
    exact Set.indicator_of_mem hx _
  rw [phaseZeroTensor_congr hphase hseed τ]
  exact phaseZeroTensor_coordinate (Z.contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)
    ((he.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) τ

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes
open SmallModes (gradientAmplitude)
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

lemma freeSeed_zeroPhase {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) {y : SmallModes.Base} (hy : y ∈ c.e.target) :
    phaseZeroTensor τ Prod.fst (c.freeSeed δ q b) y =
      δ ^ 2 • (c.leadingInChart b y + c.metricMeanInChart δ q b y) := by
  funext k
  simp only [phaseZeroTensor, ← SmallModes.gradientAmplitude_eq, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  exact perturbed_seed_mean_identity δ τ hδ hτ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) c.operator q b
    (firstDirection k) (secondDirection k) y hy

lemma originalFreeSeed_zeroPhase {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) {x : SmallModes.Base} (hx : x ∈ c.e.source) :
    phaseZeroTensor τ (coordinatePhase φ) (coordinateAmplitude (c.originalFreeSeed δ q b)) x =
      δ ^ 2 • (pullbackField c.e x (c.leadingInChart b (c.e x)) +
        pullbackField c.e x (c.metricMeanInChart δ q b (c.e x))) := by
  have he : coordinateAmplitude (c.originalFreeSeed δ q b) =
      (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b) : SmallModes.Field 4) := by
    funext y
    change (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b))
      (planeCoordinateIsometry (planeCoordinateIsometry.symm y)) = _
    rw [planeCoordinateIsometry.apply_symm_apply]
  rw [he, phaseZeroTensor_chart c.e c.smoothForward (modeSupport K) c.supportChart c.phase τ _ hx,
    c.freeSeed_zeroPhase hδ hτ q b (c.e.map_source hx), map_smul, map_add]

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMetricMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global supported metric mean fields for the actual charted free seed. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

lemma metricMeanField_apply (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact)
    (x : SmallModes.Base) :
    c.metricMeanField δ q b x = c.e.source.indicator
      (fun x => pullbackField c.e x (c.metricMeanInChart δ q b (c.e x))) x := rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SupportedQuadraticFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual supported targets for the doubled and mixed quadratic phases.
Mixed labels retain the intersection of the original amplitude supports. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean

lemma coordinateAmplitude_tsupport {K : Compacts Base}
    (H : SupportedField (F := Fin 4 → ℂ) K) :
    tsupport (coordinateAmplitude H) ⊆ (modeSupport K : Set SmallModes.Base) :=
  (pushSupported planeCoordinateIsometry K H).tsupport_subset

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedCombinedMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The combined mean of the actual transported free amplitude, with the
polynomial evaluated in the original coordinates and the metric transformed
as a two-tensor. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

lemma metric_zero_phase_identity {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    phaseZeroTensor τ (coordinatePhase φ) (coordinateAmplitude (c.originalFreeSeed δ q b)) x =
      δ ^ 2 • (c.leadingField b x + c.metricMeanField δ q b x) := by
  by_cases hx : x ∈ c.e.source
  · rw [c.originalFreeSeed_zeroPhase hδ hτ q b hx]
    simp only [leadingField, realTensorChartPull_apply, metricMeanField_apply, Set.indicator_of_mem hx]
    rfl
  · have hn : x ∉ tsupport (coordinateAmplitude (c.originalFreeSeed δ q b)) :=
      fun hs => hx (c.supportChart (coordinateAmplitude_tsupport (c.originalFreeSeed δ q b) hs))
    have hz := RealModes.phaseZeroTensor_congr (φ := coordinatePhase φ) (ψ := coordinatePhase φ)
      Filter.EventuallyEq.rfl (notMem_tsupport_iff_eventuallyEq.mp hn) τ
    rw [hz]
    change phaseZeroTensor τ (coordinatePhase φ) (fun _ => (0 : SmallModes.Ambient 4)) x = _
    rw [RealModes.phaseZeroTensor_zero]
    simp only [leadingField, realTensorChartPull_apply, metricMeanField_apply,
      Set.indicator_of_notMem hx, zero_add, smul_zero]

theorem combined_zero_phase_identity {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    phaseZeroTensor τ (coordinatePhase φ) (coordinateAmplitude (c.originalFreeSeed δ q b)) x +
      (fun k => quadraticMeanCoefficient (P k) ε G φ (c.originalFreeSeed δ q b) τ 0
        (planeCoordinateIsometry.symm x)) =
      δ ^ 2 • (c.leadingField b x + c.combinedMeanField δ q b x) := by
  rw [c.metric_zero_phase_identity hδ hτ q b x]
  funext k
  change δ ^ 2 * (_ + _) + _ = δ ^ 2 * (_ + (_ +
    normalizedPolynomialMean (P k) δ ε G φ (c.originalFreeSeed δ q b) τ 0 (planeCoordinateIsometry.symm x)))
  unfold normalizedPolynomialMean
  field_simp [hδ]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed geometric and jet bounds for the actual mean map of one phase. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference)

lemma zero_phase_identity (hρ : 0 < ρ) {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (A : SmallModes.Base → Tensor) (x : SmallModes.Base) :
    phaseZeroTensor τ (coordinatePhase φ) (coordinateAmplitude (d.freeAmplitude hρ δ q A)) x +
      (fun k => quadraticMeanCoefficient (P k) ε G φ (d.freeAmplitude hρ δ q A) τ 0
        (planeCoordinateIsometry.symm x)) =
      δ ^ 2 • (d.leading hρ A x + d.mean hρ δ q A x) :=
  c.combined_zero_phase_identity hδ hτ q (d.amplitude hρ A) x

end ChartedMeanData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual charted free amplitudes and their zero-phase tensors. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanData (c i) r ρ R reference)

theorem charted_family_zero_phase_identity (hρ : 0 < ρ) {δ : ℝ}
    (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) (A : SmallModes.Base → Tensor) :
    combinedQuadraticMean P ε G φ (fun i => (d i).freeAmplitude hρ δ q A) τ 0 =
      δ ^ 2 • (chartedFamilyLeading d hρ A + chartedFamilyMean d hρ δ q A) := by
  funext x k
  simp only [combinedQuadraticMean, zeroPhaseSum, coordinateQuadraticMean, Pi.add_apply,
    Finset.sum_apply]
  change (∑ i, phaseZeroTensor τ (coordinatePhase (φ i))
      (coordinateAmplitude ((d i).freeAmplitude hρ δ q A)) x k) +
      (∑ i, quadraticMeanCoefficient (P k) ε G (φ i) ((d i).freeAmplitude hρ δ q A) τ 0
        (planeCoordinateIsometry.symm x)) = _
  rw [← Finset.sum_add_distrib]
  simp_rw [show ∀ i, phaseZeroTensor τ (coordinatePhase (φ i))
      (coordinateAmplitude ((d i).freeAmplitude hρ δ q A)) x k +
      quadraticMeanCoefficient (P k) ε G (φ i) ((d i).freeAmplitude hρ δ q A) τ 0
        (planeCoordinateIsometry.symm x) =
      δ ^ 2 * ((d i).leading hρ A x k + (d i).mean hρ δ q A x k) from
    fun i => congrFun ((d i).zero_phase_identity hρ hδ hτ q A x) k]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul,
    Pi.add_apply, chartedFamilyLeading, chartedFamilyMean, Finset.sum_apply, mul_add]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalOscillatoryModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global phase/amplitude representatives of the actual supported oscillations. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

lemma realMode_contDiff {n : ℕ} (τ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => realMode (p.1/τ) p.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) =>
    realPartCLM n (QuadraticMean.phase (p.1/τ) • p.2))
  apply (realPartCLM n).contDiff.comp
  apply ContDiff.smul (f := fun p : ℝ × (Fin n → ℂ) => QuadraticMean.phase (p.1/τ))
    (g := fun p : ℝ × (Fin n → ℂ) => p.2)
  · have ha : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => ((p.1/τ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.div_const τ)
    exact Complex.contDiff_exp.comp (ha.mul contDiff_const)
  · exact contDiff_snd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfaceMode_smooth {n : ℕ} (τ : ℝ) {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) :
    ContMDiff planeModel 𝓘(ℝ,Fin n → ℝ) ∞ (surfaceMode τ φ Z) :=
  (realMode_contDiff τ).contMDiff.comp (hφ.prodMk_space hZ)

variable [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_mode_on_support {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin n → ℂ) {x : JetPolynomial.Base}
    (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.vectorChartRead i (surfaceMode τ φ Z) x =
      realMode (A.vectorChartRead i φ x/τ) (A.vectorChartRead i Z x) := by
  rw [A.vectorChartRead_on_support i _ hx,A.vectorChartRead_on_support i _ hx,
    A.vectorChartRead_on_support i _ hx]
  rfl

lemma vectorChartRead_mode_jets {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) (m : ℕ)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    iteratedFDeriv ℝ m (A.vectorChartRead i (surfaceMode τ φ Z)) x =
      iteratedFDeriv ℝ m (fun y =>
        realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)) x := by
  apply iteratedFDeriv_eq_on_tsupport (A.chartWeight_smooth i).continuous
    isOpen_univ (subset_univ _) (A.vectorChartRead_smooth i (surfaceMode_smooth τ hφ hZ)).contDiffOn
    ((realMode_contDiff τ).comp ((A.vectorChartRead_smooth i hφ).prodMk
      (A.vectorChartRead_smooth i hZ))).contDiffOn
    (fun y hy => A.vectorChartRead_mode_on_support i τ φ Z (A.chartWeight_tsupport i ▸ hy)) m
  rwa [A.chartWeight_tsupport]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalModeDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual chart differentials of global oscillatory modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_mode_fderiv {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    fderiv ℝ (A.vectorChartRead i (surfaceMode τ φ Z)) x =
      fderiv ℝ (fun y => realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)) x := by
  ext v : 1
  have hh := congrArg (fun T => T (fun _ : Fin 1 => v)) (A.vectorChartRead_mode_jets i τ hφ hZ 1 hx)
  simpa only [iteratedFDeriv_one_apply] using hh

lemma vectorPlaneRead_mode_fderiv {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z)
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    fderiv ℝ (A.vectorPlaneRead i (surfaceMode τ φ Z)) x =
      fderiv ℝ (QuadraticMean.displacement τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z)) x := by
  obtain ⟨y,hy,rfl⟩ := hx
  let f := fun y => realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)
  have hf : ContDiff ℝ ∞ f := (realMode_contDiff τ).comp
    ((A.vectorChartRead_smooth i hφ).prodMk (A.vectorChartRead_smooth i hZ))
  change fderiv ℝ (A.vectorChartRead i (surfaceMode τ φ Z) ∘ planeCoordinateIsometry.symm) _ =
    fderiv ℝ (f ∘ planeCoordinateIsometry.symm) _
  rw [fderiv_comp _ ((A.vectorChartRead_smooth i (surfaceMode_smooth τ hφ hZ)).differentiable
      (by simp) _) (planeCoordinateIsometry.symm.differentiableAt),
    fderiv_comp _ (hf.differentiable (by simp) _) (planeCoordinateIsometry.symm.differentiableAt),
    LinearIsometryEquiv.symm_apply_apply,A.vectorChartRead_mode_fderiv i τ hφ hZ hy]

omit [CompactSpace M] in
lemma vectorPlaneRead_clm {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (i : A.centers)
    (L : V →L[ℝ] W) (F : M → V) :
    A.vectorPlaneRead i (L ∘ F) = L ∘ A.vectorPlaneRead i F := by
  funext x
  change localize (i : M) (A.outer i) (L ∘ F) (planeCoordinateIsometry.symm x) =
    L (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm x))
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [localize,hx,map_smul]

omit [CompactSpace M] in
lemma vectorPlaneRead_sum {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] (i : A.centers) (F : ι → M → V) :
    A.vectorPlaneRead i (∑ j, F j) = ∑ j, A.vectorPlaneRead i (F j) := by
  funext x
  simpa only [vectorPlaneRead,vectorChartRead,Function.comp_apply,Finset.sum_apply] using
    congrFun (localize_sum Finset.univ (i : M) (A.outer i) F) (planeCoordinateIsometry.symm x)

lemma vectorPlaneRead_modes_fderiv {ι : Type*} [Fintype ι] (i : A.centers) (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    fderiv ℝ (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      fderiv ℝ (QuadraticMean.sumDisplacement τ
        (fun j => A.vectorPlaneRead i (φ j)) (fun j => A.vectorPlaneRead i (Z j))) x := by
  classical
  rw [A.vectorPlaneRead_sum]
  change fderiv ℝ (∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j))) x =
    fderiv ℝ (fun y => ∑ j, QuadraticMean.displacement τ (A.vectorPlaneRead i (φ j))
      (A.vectorPlaneRead i (Z j)) y) x
  have he : (∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j))) =
      fun y => ∑ j, A.vectorPlaneRead i (surfaceMode τ (φ j) (Z j)) y := by
    funext y
    exact Finset.sum_apply _ _ _
  have hloc (j : ι) : DifferentiableAt ℝ (QuadraticMean.displacement τ
      (A.vectorPlaneRead i (φ j)) (A.vectorPlaneRead i (Z j))) x :=
    ((realMode_contDiff τ).comp ((A.vectorPlaneRead_smooth i (hφ j)).prodMk
      (A.vectorPlaneRead_smooth i (hZ j)))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  rw [he,fderiv_fun_sum (fun j _ =>
    (A.vectorPlaneRead_smooth i (surfaceMode_smooth τ (hφ j) (hZ j))).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x),
    fderiv_fun_sum (fun j _ => hloc j)]
  apply Finset.sum_congr rfl
  intro j _
  exact A.vectorPlaneRead_mode_fderiv i τ (hφ j) (hZ j) hx

lemma vectorPlaneRead_modes_metric {ι : Type*} [Fintype ι] [DecidableEq ι] (i : A.centers) (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    RealModes.realMetricTensor (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      RealModes.zeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
        (fun j => A.vectorPlaneRead i (Z j)) x +
      RealModes.nonzeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
        (fun j => A.vectorPlaneRead i (Z j)) x := by
  classical
  have hd := A.vectorPlaneRead_modes_fderiv i τ φ Z hφ hZ hx
  have he : RealModes.realMetricTensor (A.vectorPlaneRead i (∑ j, surfaceMode τ (φ j) (Z j))) x =
      RealModes.realMetricTensor (QuadraticMean.sumDisplacement τ
        (fun j => A.vectorPlaneRead i (φ j)) (fun j => A.vectorPlaneRead i (Z j))) x := by
    ext k
    simp only [RealModes.realMetricTensor_apply, RealModes.realMetric,SmallModes.coordDeriv,hd]
  rw [he]
  exact RealModes.realMetric_sumDisplacement
    (fun j => (A.vectorPlaneRead_smooth i (hφ j)).differentiable (by simp) x)
    (fun j => (A.vectorPlaneRead_smooth i (hZ j)).differentiable (by simp) x) τ

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalQuadraticModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global quadratic phase expansion, retaining all cross-chart interactions. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.globalModeMetricDualAdd
local instance globalModeMetricFiberNormed_r320114_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance globalModeMetricFiberSpace_r320114_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance globalModeMetricDualSmul_r320114_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance globalModeMetricSectionNormed_r320114_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalModeMetricSectionSpace_r320114_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem global_modes_metric {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    inducedTensor (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.zeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x) +
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.nonzeroPhaseSum τ (fun j => A.vectorPlaneRead i (φ j))
          (fun j => A.vectorPlaneRead i (Z j)) x) := by
  classical
  let U : M → RealModes.RVec 4 := ∑ j, surfaceMode τ (φ j) (Z j)
  have hU : ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞ U := by
    have hh := ContMDiff.sum (t := Finset.univ) (fun j _ => surfaceMode_smooth τ (hφ j) (hZ j))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [U,Finset.sum_apply]
  have he (i : A.centers) :
      spaceCoordinates ∘ A.vectorPlaneRead i (spaceCoordinates.symm ∘ U) = A.vectorPlaneRead i U := by
    have hr : A.vectorPlaneRead i (spaceCoordinates.symm ∘ U) =
        spaceCoordinates.symm ∘ A.vectorPlaneRead i U :=
      A.vectorPlaneRead_clm i spaceCoordinates.symm.toContinuousLinearMap U
    rw [hr]
    funext x
    exact spaceCoordinates.apply_symm_apply _
  rw [← A.metric_from_chart_reads (spaceCoordinates.symm.contDiff.contMDiff.comp hU)]
  simp_rw [he]
  rw [← A.tensorPlaneRestore_add]
  congr 1
  funext i x
  by_cases hw : A.planeWeight i x = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.add_apply,zero_add]
  · have hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
      (A.supportedPlaneWeight i).tsupport_subset (subset_tsupport (A.planeWeight i) hw)
    rw [A.vectorPlaneRead_modes_metric i τ φ Z hφ hZ hx,smul_add]
    rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteAtlasFreeMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global free-mode identities for an arbitrary finite family in
each fixed atlas chart. This accommodates the variable number of grid cells. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberSpace
local instance finiteAtlasFreeDualSmul_r320114_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberNormed
local instance finiteAtlasFreeSectionNormed_r320114_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteAtlasFreeSectionSpace_r320114_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasIndexDecidable
theorem finite_atlas_free_metric_oai
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u) =
      δ^2 • A.tensorPlaneRestore (fun i =>
        chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
        chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) +
      A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.nonzeroPhaseSum τ
        (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
        (fun a : Σ i, ι i => A.vectorPlaneRead k
          (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x) := by
  classical
  have hphase (a : Σ i, ι i) : ContMDiff planeModel 𝓘(ℝ) ∞
      (A.finiteGlobalPhase (φ := φ) a.1 a.2) :=
    restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1) (c a.1 a.2).smoothPhase
  have hamp (a : Σ i, ι i) : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞
      (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2) :=
    restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
      ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff
  have hm := A.global_modes_metric τ
    (fun a : Σ i, ι i => A.finiteGlobalPhase (φ := φ) a.1 a.2)
    (fun a : Σ i, ι i => A.finiteGlobalAmplitude d hρ δ q u a.1 a.2) hphase hamp
  rw [A.finite_atlas_zeroPhase d hρ δ q u hK] at hm
  have hlocal (i : A.centers) : RealModes.zeroPhaseSum τ
      (fun j => coordinatePhase (φ i j))
      (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))) =
      δ^2 • (chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
        chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) := by
    have hz : combinedQuadraticMean (P i) 0 (G i) (φ i)
        (fun j => (d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)) τ 0 =
        RealModes.zeroPhaseSum τ (fun j => coordinatePhase (φ i j))
          (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u))) := by
      ext x k
      simp [combinedQuadraticMean,coordinateQuadraticMean,quadraticMeanCoefficient,conjugated]
    rw [← hz]
    exact charted_family_zero_phase_identity (d i) hρ hδ hτ q (A.tensorPlaneRead i u)
  have he : (fun i => RealModes.zeroPhaseSum τ (fun j => coordinatePhase (φ i j))
      (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)))) =
      δ^2 • (fun i => chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
        chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) := funext hlocal
  rw [he,A.tensorPlaneRestore_smul] at hm
  exact hm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_free_metric_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_free_metric_oai.{u_1, u_2}
