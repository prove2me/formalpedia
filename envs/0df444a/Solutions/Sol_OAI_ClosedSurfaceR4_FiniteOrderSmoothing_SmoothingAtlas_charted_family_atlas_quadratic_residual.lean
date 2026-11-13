-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:13.070625+00:00
-- url     : https://prove2.me/submissions/513c90c6-de2c-4ae4-9dd3-f3a026132ade

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

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticMean
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


lemma phaseLinear_apply (ξ x : SmallModes.Base) : phaseLinear ξ x = ξ.1*x.1+ξ.2*x.2 := rfl

end ClosedSurfaceR4

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff square-root trial amplitudes on the actual transported support.
These use the original tensor field and the inverse of its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

lemma trialAmplitude_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiffOn ℝ ∞ A c.e.source) (hball : InTrialBall c.e.source reference r A)
    (y : SmallModes.Base) :
    c.trialAmplitude ψ Q h hρ A y = phaseAmplitude ψ (coefficient Q c.e.symm A) y := by
  classical
  simp only [trialAmplitude, dite_eq_left (show ContDiffOn ℝ ∞ A c.e.source ∧
    InTrialBall c.e.source reference r A from ⟨hA,hball⟩)]
  rfl

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedLeadingTensor
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading tensors of the actual charted amplitudes are the prescribed
cutoff squares times phase-covector squares. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

lemma chartLeadingTensor_apply (b : SmallModes.Base → ℝ) (e : SmallModes.Base → SmallModes.Base)
    (x : SmallModes.Base) (k : Fin 3) :
    chartLeadingTensor b e x k = b (e x) ^ 2 *
      (fderiv ℝ e x (firstDirection k)).1 * (fderiv ℝ e x (secondDirection k)).1 := by
  change evaluate (fun i => b (e x) ^ 2 * (firstDirection i).1 * (secondDirection i).1)
    (fderiv ℝ e x (firstDirection k)) (fderiv ℝ e x (secondDirection k)) = _
  simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

lemma phase_derivative {x : SmallModes.Base} (hx : x ∈ c.e.source) (v : SmallModes.Base) :
    (fderiv ℝ c.e x v).1 = fderiv ℝ (coordinatePhase φ) x v := by
  have he : (fun y => (c.e y).1) =ᶠ[nhds x] coordinatePhase φ := by
    filter_upwards [c.e.open_source.mem_nhds hx] with y hy using c.phase y hy
  have hd := (c.smoothForward.contDiffAt (c.e.open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [← he.fderiv_eq, fderiv.fst hd]
  rfl

lemma leadingField_apply (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    c.leadingField b x = c.e.source.indicator (fun y k => b (c.e y) ^ 2 *
      fderiv ℝ (coordinatePhase φ) y (firstDirection k) *
      fderiv ℝ (coordinatePhase φ) y (secondDirection k)) x := by
  by_cases hx : x ∈ c.e.source
  · simp only [leadingField, realTensorChartPull_apply, Set.indicator_of_mem hx]
    change chartLeadingTensor b c.e x = _
    ext k
    rw [chartLeadingTensor_apply, c.phase_derivative hx, c.phase_derivative hx]
  · simp only [leadingField, realTensorChartPull_apply, Set.indicator_of_notMem hx]

end PolynomialSolveData

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference)

lemma leading_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) (x : SmallModes.Base) :
    d.leading hρ A x = c.e.source.indicator (fun y k => d.cutoff (c.e y) ^ 2 *
      d.form (c.e y) (A y) * fderiv ℝ (coordinatePhase φ) y (firstDirection k) *
      fderiv ℝ (coordinatePhase φ) y (secondDirection k)) x := by
  change c.leadingField (d.amplitude hρ A) x = _
  rw [c.leadingField_apply]
  by_cases hx : x ∈ c.e.source
  · simp only [Set.indicator_of_mem hx]
    have ha := c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hA.contDiffOn
      (fun y _ => hball y (Set.mem_univ y)) (c.e x)
    have hpos := coefficient_trial_range d.localBounds.invInto d.localBounds.margin
      (fun y _ => hball y (Set.mem_univ y)) (c.e.map_source hx)
    have hn : 0 ≤ coefficient d.form c.e.symm A (c.e x) := hρ.le.trans hpos.1
    have hn' : 0 ≤ d.form (c.e x) (A x) := by
      simpa only [coefficient, c.e.left_inv hx] using hn
    ext k
    change c.trialAmplitude d.cutoff d.form d.localBounds hρ A (c.e x) ^ 2 * _ * _ = _
    rw [ha]
    simp only [phaseAmplitude, mul_pow, coefficient, c.e.left_inv hx, Real.sq_sqrt hn']
  · simp only [Set.indicator_of_notMem hx]

end ChartedMeanData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedPartitionLeading
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported phase family has leading tensor equal to the cutoff square
 times its input tensor. This is the local identity used by the global atlas. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean PhaseGeometry

lemma covectorSquare_directions (ξ : SmallModes.Base) (k : Fin 3) :
    covectorSquare ξ k = phaseLinear ξ (firstDirection k) * phaseLinear ξ (secondDirection k) := by
  fin_cases k <;> simp [covectorSquare, firstDirection, secondDirection, phaseLinear_apply,
    SmallModes.dx, SmallModes.dy] <;> ring

theorem charted_cutoff_leading {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (χ : SmallModes.Base → ℝ) (Q : Tensor →L[ℝ] ℝ) (ξ : SmallModes.Base) (w : ℝ)
    (hw : w ≠ 0) (hphase : coordinatePhase φ = phaseLinear (w • ξ))
    (hcutoff : ∀ x ∈ c.e.source, d.cutoff (c.e x) = χ x / w)
    (hform : ∀ x ∈ c.e.source, d.form (c.e x) = Q)
    (hsupport : tsupport χ ⊆ c.e.source) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) (x : SmallModes.Base) :
    d.leading hρ A x = (χ x)^2 • (Q (A x) • covectorSquare ξ) := by
  rw [d.leading_apply hρ hA hball]
  by_cases hx : x ∈ c.e.source
  · rw [Set.indicator_of_mem hx]
    have hd (v : SmallModes.Base) : fderiv ℝ (coordinatePhase φ) x v = w * phaseLinear ξ v := by
      rw [hphase, (phaseLinear (w • ξ)).fderiv]
      simp only [phaseLinear_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    ext k
    simp only [hcutoff x hx, hform x hx, hd, Pi.smul_apply, smul_eq_mul,
      covectorSquare_directions]
    field_simp [hw]
  · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupport h))
    simp only [Set.indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

theorem charted_partition_leading {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Fin 3 → Base → ℝ}
    {K : Fin 3 → Compacts Base} {s : ℝ≥0}
    {c : ∀ j, PolynomialSolveData P ε G hG (φ j) (K j) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ j, ChartedMeanData (c j) r ρ R reference) (hρ : 0 < ρ)
    (χ : SmallModes.Base → ℝ) (Q : PhaseBasis) (w : Fin 3 → ℝ)
    (hw : ∀ j, w j ≠ 0) (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (w j • Q.ξ j))
    (hcutoff : ∀ j x, x ∈ (c j).e.source → (d j).cutoff ((c j).e x) = χ x / w j)
    (hform : ∀ j x, x ∈ (c j).e.source → (d j).form ((c j).e x) = Q.Q j)
    (hsupport : ∀ j, tsupport χ ⊆ (c j).e.source) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) :
    chartedFamilyLeading d hρ A = fun x => (χ x)^2 • A x := by
  funext x
  change (∑ j : Fin 3, (d j).leading hρ A x) = _
  simp_rw [charted_cutoff_leading _ hρ χ _ _ _ (hw _) (hphase _) (hcutoff _) (hform _)
    (hsupport _) hA hball]
  rw [← Finset.smul_sum, Q.decomposition]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three independent coordinates of a symmetric surface tensor, with
an explicit continuous linear reconstruction into the full tensor fiber. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberNormed
local instance coordinateFiberSpace_r89573b_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberToThree_apply (B : TensorFiber) (k : Fin 3) :
    fiberToThree B k = B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k)) := rfl

lemma plane_basis_expansion (v : Plane) :
    v = (planeCoordinates v).1 • planeCoordinates.symm SmallModes.dx +
      (planeCoordinates v).2 • planeCoordinates.symm SmallModes.dy := by
  apply planeCoordinates.injective
  simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  exact RealModes.base_decomposition (planeCoordinates v)

lemma fiberFromThree_toThree (B : TensorFiber) (hB : ∀ v w, B v w = B w v) :
    fiberFromThree (fiberToThree B) = B := by
  ext v w
  rw [fiberFromThree_apply]
  have hcross := hB (planeCoordinates.symm SmallModes.dy) (planeCoordinates.symm SmallModes.dx)
  conv_rhs => rw [plane_basis_expansion v, plane_basis_expansion w]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  simp only [evaluate, fiberToThree_apply]
  simp only [firstDirection, secondDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]
  dsimp
  rw [hcross]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothingSymmetry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor coordinate maps commute with transposition. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r89573b_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r89573b_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualSmul
variable (A : SmoothingAtlas M)

lemma tensorComponent_flip (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    A.bundleComponent A.tensorTriv i (fun p => tensorTranspose (u p)) p =
      (A.bundleComponent A.tensorTriv i u p).flip := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  have hs : p ∈ (trivializationAt ℝ (fun _ : M => ℝ) (i : M)).baseSet := mem_univ p
  unfold bundleComponent
  rw [(A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp),
    (A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp)]
  unfold tensorTriv
  simp only [hom_trivializationAt_apply]
  ext v w
  simp only [ContinuousLinearMap.flip_apply]
  rw [inCoordinates_apply_eq₂ ht ht hs, inCoordinates_apply_eq₂ ht ht hs]
  rfl

lemma tensorLocalize_flip (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p) :
    A.bundleLocalize A.tensorTriv i (fun p => tensorTranspose (u p)) =
      fun x => (A.bundleLocalize A.tensorTriv i u x).flip := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · unfold bundleLocalize localize
    rw [indicator_of_mem hx, indicator_of_mem hx,
      A.tensorComponent_flip i u ((chart (i : M)).map_target hx)]
    ext v w
    rfl
  · simp only [bundleLocalize, localize, indicator_of_notMem hx]
    rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPhaseDecomposition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite phase-basis decomposition on global symmetric tensor sections.
The atlas partition restores the tensor exactly, including chart overlaps. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance phaseFiberNormed_r89573b_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_r89573b_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_r89573b_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_r89573b_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_r89573b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_r89573b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorEncode_symmetric {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ∀ p v w, u p v w = u p w v) :
    ∀ x i v w, A.tensorEncode u x i v w = A.tensorEncode u x i w v := by
  have ht : (fun p => tensorTranspose (u p)) = u := by
    funext p
    ext v w
    exact (hu p w v)
  intro x i v w
  have hh := A.tensorLocalize_flip i u
  rw [ht] at hh
  exact congrArg (fun b : TensorFiber => b v w) (congrFun hh x)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberSpace
local instance chartReadSectionNormed_r89573b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r89573b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorChartRead_on_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorChartRead i u (chart (i : M) p) = fiberToThree (A.bundleComponent A.tensorTriv i u p) := by
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp]
  simp only [one_pow, one_smul]

lemma tensorEncode_read (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    fiberToThree (A.tensorEncode u (chart (i : M) p) i) =
      (A.weight i p)^2 • A.tensorChartRead i u (chart (i : M) p) := by
  change fiberToThree (localize (i : M) (A.weight i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ hp, map_smul]
  by_cases hz : A.weight i p = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_smul]
  · rw [A.tensorChartRead_on_weight i u (subset_tsupport _ hz)]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r89573b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorPlaneReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction from the three independent tensor coordinates. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean
open JetPolynomial (Base planeCoordinateIsometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.reconstructionDualAdd
local instance reconstructionFiberNormed_r89573b_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance reconstructionFiberSpace_r89573b_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance reconstructionDualSmul_r89573b_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance reconstructionSectionNormed_r89573b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance reconstructionSectionSpace_r89573b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_encode (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ∀ p v w, u p v w = u p w v) : A.tensorPlaneRestore (A.tensorPlaneEncode u) = u := by
  have he : (fun x i => fiberFromThree (A.tensorPlaneEncode u i (planeCoordinateIsometry x))) =
      A.tensorEncode u := by
    funext x i
    simp only [tensorPlaneEncode, LinearIsometryEquiv.symm_apply_apply]
    exact fiberFromThree_toThree _ (A.tensorEncode_symmetric hu x i)
  change A.tensorDecode (fun x i => fiberFromThree (A.tensorPlaneEncode u i (planeCoordinateIsometry x))) = u
  rw [he, A.tensorDecode_encode]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneWeight
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual chart cutoff whose square converts an unweighted tensor
reading into its atlas coordinate component. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates
open JetPolynomial (Base planeCoordinateIsometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance weightPlaneFiberNormed_r89573b_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance weightPlaneFiberSpace_r89573b_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance weightPlaneDualAdd_r89573b_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance weightPlaneDualSmul_r89573b_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance weightPlaneSectionNormed_r89573b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance weightPlaneSectionSpace_r89573b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneEncode_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    (y : SmallModes.Base) :
    A.tensorPlaneEncode u i y = (A.planeWeight i y)^2 • A.tensorPlaneRead i u y := by
  let x := planeCoordinateIsometry.symm y
  change fiberToThree (A.tensorEncode u x i) = (A.chartWeight i x)^2 • A.tensorChartRead i u x
  by_cases hx : x ∈ (chart (i : M)).target
  · have hp := (chart (i : M)).map_target hx
    have hh := A.tensorEncode_read i u hp
    rw [(chart (i : M)).right_inv hx] at hh
    simpa only [chartWeight, indicator_of_mem hx] using hh
  · simp only [tensorEncode, bundleLocalize, localize, indicator_of_notMem hx, map_zero,
      chartWeight, zero_pow (by decide : 2 ≠ 0), zero_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAdjustedMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual original-coordinate quadratic mean after finite substitution.
The threshold in this statement still concerns fixed scale data. -/
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

lemma chartedFamilyMean_smooth (hρ : 0 < ρ) (δ : ℝ) (q : ℕ)
    (A : SmallModes.Base → Tensor) : ContDiff ℝ ∞ (chartedFamilyMean d hρ δ q A) :=
  ContDiff.sum (fun i _ => ((c i).combinedMeanField δ q ((d i).amplitude hρ A)).contDiff)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasMeanIdentity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual quadratic zero-phase terms of the charted free oscillations
restore to the input global tensor plus the global nonlinear mean. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartedAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartedAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartedAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartedAtlasFiberSpace
local instance chartedAtlasSectionNormed_r89573b_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartedAtlasSectionSpace_r89573b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem charted_atlas_mean_identity
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {G : A.centers → Base → JetPolynomial.Space}
    {hG : ∀ i, ContDiff ℝ ∞ (G i)} {φ : A.centers → Fin 3 → Base → ℝ}
    {K : A.centers → Fin 3 → TopologicalSpace.Compacts Base}
    {c : ∀ i j, PolynomialSolveData (P i) ε (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ} {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase : ∀ i j, coordinatePhase (φ i j) = phaseLinear (w i j • (Q i).ξ j))
    (hcutoff : ∀ i j x, x ∈ (c i j).e.source →
      (d i j).cutoff ((c i j).e x) = A.planeWeight i x / w i j)
    (hform : ∀ i j x, x ∈ (c i j).e.source → (d i j).form ((c i j).e x) = (Q i).Q j)
    (hsupport : ∀ i j, tsupport (A.planeWeight i) ⊆ (c i j).e.source)
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ p v v', u p v v' = u p v' v)
    (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) :
    A.tensorPlaneRestore (fun i => combinedQuadraticMean (P i) ε (G i) (φ i)
      (fun j => (d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)) τ 0) =
        δ^2 • (u + A.atlasMean (fun i => chartedFamilyMean (n := n i) (ι := Fin 3) (P := P i) (ε := ε) (τ := τ) (s := s) (G := G i) (hG := hG i) (φ := φ i) (K := K i) (c := c i) (r := r i) (ρ := ρ) (R := R) (reference := reference i) (d i) hρ δ q) u) := by
  have hleading (i : A.centers) :
      chartedFamilyLeading (n := n i) (ι := Fin 3) (P := P i) (ε := ε) (τ := τ) (s := s) (G := G i) (hG := hG i) (φ := φ i) (K := K i) (c := c i) (r := r i) (ρ := ρ) (R := R) (reference := reference i) (d i) hρ (A.tensorPlaneRead i u) = A.tensorPlaneEncode u i := by
    rw [charted_partition_leading (d i) hρ (A.planeWeight i) (Q i) (w i)
      (hw i) (hphase i) (hcutoff i) (hform i) (hsupport i)
      (A.tensorPlaneRead_smooth i hu) (hball i)]
    funext x
    exact (A.tensorPlaneEncode_weight i u x).symm
  have he : (fun i => combinedQuadraticMean (P i) ε (G i) (φ i)
      (fun j => (d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)) τ 0) =
      δ^2 • (A.tensorPlaneEncode u +
        (fun i => chartedFamilyMean (n := n i) (ι := Fin 3) (P := P i) (ε := ε) (τ := τ) (s := s) (G := G i) (hG := hG i) (φ := φ i) (K := K i) (c := c i) (r := r i) (ρ := ρ) (R := R) (reference := reference i) (d i) hρ δ q (A.tensorPlaneRead i u))) := by
    funext i
    rw [charted_family_zero_phase_identity (d i) hρ hδ hτ q, hleading i]
    rfl
  rw [he, A.tensorPlaneRestore_smul, A.tensorPlaneRestore_add, A.tensorPlaneRestore_encode u hsym]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedMeanFamilyData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite charted phase family with its actual solvers and amplitudes,
packaged for assembling different coordinate patches on one surface. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanFamilyData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ} {s : ℝ≥0}
  {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

lemma mean_smooth (d : ChartedMeanFamilyData P ε τ s r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (f : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (d.mean hρ δ q f) := chartedFamilyMean_smooth d.data hρ δ q f

end ChartedMeanFamilyData

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasQuadraticResidual
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero-phase residual of the actual charted free family. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasSectionNormed
local instance quadraticAtlasSectionSpace_r89573b_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_const_smul
    {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ}
    (hb : A.TensorWeightedBound s m C u) (a : ℝ) :
    A.TensorWeightedBound s m (|a| * C) (a • u) := by
  intro i
  have hb' := (hb i).const_smul uniqueDiffOn_univ
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu).contDiffOn a
  change _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (|a| * C) (A.bundleLocalize A.tensorTriv i (a • u))
  rw [A.bundleLocalize_smul]
  exact hb'

theorem charted_family_atlas_mean_identity
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase : ∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hcutoff : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j)
    (hform : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j)
    (hsupport : ∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source)
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ x v v', u x v v' = u x v' v)
    (hball : ∀ i, InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) :
    A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) =
      δ^2 • (u + A.atlasMean (fun i => (d i).mean hρ δ q) u) :=
  A.charted_atlas_mean_identity (fun i => (d i).data) hρ Q w hw hphase hcutoff hform hsupport
    u hu hsym hball hδ hτ q

theorem charted_family_atlas_quadratic_residual_oai
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase : ∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hcutoff : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j)
    (hform : ∀ i j x, x ∈ ((d i).solver j).e.source →
      ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j)
    (hsupport : ∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source)
    (u H : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (H x)))
    (hsym : ∀ x v v', u x v v' = u x v' v)
    (hball : ∀ i, InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ C : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hτ : τ ≠ 0)
    (q : ℕ)
    (hb : A.TensorWeightedBound s m C
      (u + A.atlasMean (fun i => (d i).mean hρ δ q) u - H)) :
    A.TensorWeightedBound s m (δ^2*C)
      (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) := by
  have hm : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.atlasMean (fun i => (d i).mean hρ δ q) u x)) :=
    A.tensorPlaneRestore_smooth (fun i => (d i).mean_smooth hρ δ q _)
  have hr := (hu.add_section hm).sub_section hH
  rw [A.charted_family_atlas_mean_identity d hρ Q w hw hphase hcutoff hform hsupport
    u hu hsym hball hδ hτ q, ← smul_sub]
  have hh := A.tensorWeightedBound_const_smul hr hb (δ^2)
  rw [abs_of_nonneg (sq_nonneg δ)] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.charted_family_atlas_quadratic_residual_oai.{u_1}
