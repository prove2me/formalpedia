-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:50.234875+00:00
-- url     : https://prove2.me/submissions/f1c9adb9-9293-4a3d-9796-db24b0a838ad

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
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



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)

end ClosedSurfaceR4.WeightedEstimates

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingConvolution
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothing operators from the finite-moment kernels. They are
linear on locally integrable inputs, smooth their outputs, and fix constants. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

lemma kernel_smooth (r : ℕ) : ContDiff ℝ ∞ (kernel r) :=
  (Classical.choose_spec (exists_smoothing_kernel r)).1

lemma kernel_compact (r : ℕ) : HasCompactSupport (kernel r) :=
  (Classical.choose_spec (exists_smoothing_kernel r)).2.1

lemma mass_dilate (K : Base → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x, dilate K s x) = ∫ x, K x := by
  simpa only [monomial, degree, Finset.sum_const_zero, pow_zero,
    Finset.prod_const_one, one_mul] using moment_dilate K (fun _ => 0) hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma smooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (smooth r s f) :=
  (compact_dilate (kernel_compact r) hs.ne').contDiff_convolution_left (lsmul ℝ ℝ)
    (smooth_dilate (kernel_smooth r) s) hf

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingNormBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale-independent zeroth-order bounds for the constructed smoothing
operator, including the signed finite-moment kernels. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

lemma norm_dilate (K : Base → ℝ) (s : ℝ) (x : Base) :
    ‖dilate K s x‖ = dilate (fun y => ‖K y‖) s x := by
  simp only [dilate, norm_mul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (sq_nonneg s)]

lemma norm_mass_dilate (K : Base → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x, ‖dilate K s x‖) = ∫ x, ‖K x‖ := by
  simp_rw [norm_dilate]
  exact mass_dilate (fun x => ‖K x‖) hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Signed moment cancellation does not cost a power of the smoothing scale:
the operator bound is the fixed L1 norm of the chosen kernel. -/
lemma smooth_norm_le (r : ℕ) {s C : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : ∀ x, ‖f x‖ ≤ C) (x : Base) :
    ‖smooth r s f x‖ ≤ (∫ y, ‖kernel r y‖) * C := by
  have hk := compact_dilate (kernel_compact r) hs.ne'
  have hcont := (smooth_dilate (kernel_smooth r) s).continuous
  have hi := (hcont.integrable_of_hasCompactSupport (μ := volume) hk).norm.mul_const C
  change ‖∫ y, dilate (kernel r) s y • f (x - y)‖ ≤ _
  calc
    _ ≤ ∫ y, ‖dilate (kernel r) s y‖ * C :=
      norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun y => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hf (x - y)) (norm_nonneg _))
    _ = (∫ y, ‖kernel r y‖) * C := by rw [integral_mul_const, norm_mass_dilate _ hs]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingDerivatives
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differentiation of the constructed smoothing operator on localized
smooth inputs. This moves derivatives onto the input without scale loss. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fderiv_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (x : Base) :
    fderiv ℝ (smooth r s f) x = smooth r s (fderiv ℝ f) x := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := lsmul ℝ ℝ
  have hk : LocallyIntegrable (dilate (kernel r) s) volume :=
    (((smooth_dilate (kernel_smooth r) s).continuous).integrable_of_hasCompactSupport
      (compact_dilate (kernel_compact r) hs.ne')).locallyIntegrable
  have h := hfc.hasFDerivAt_convolution_right L hk (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) x
  have heq : ((dilate (kernel r) s) ⋆[L.precompR Base, volume] fderiv ℝ f) x =
      smooth r s (fderiv ℝ f) x := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by ext v; rfl)
  exact h.fderiv.trans heq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConvolutionDerivativeBounds
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the compact kernel gives derivative gains without using
uncontrolled derivatives of the input. -/
noncomputable section
open scoped ContDiff Convolution

universe u v w
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

variable {E : Type u} {F : Type v} {H : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- All derivatives may be placed on the compactly supported kernel. -/
theorem convolution_iterated_norm_le (L : E →L[ℝ] F →L[ℝ] H) (n : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {g : Base → F} (hg : Continuous g) {C : ℝ} (hb : ∀ x, ‖g x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ n (f ⋆[L, volume] g) x‖ ≤
      ‖L‖ * (∫ y, ‖iteratedFDeriv ℝ n f y‖) * C := by
  have hC : 0 ≤ C := (norm_nonneg (g 0)).trans (hb 0)
  induction n generalizing E H with
  | zero =>
    simp only [norm_iteratedFDeriv_zero]
    have hi := (hf.continuous.integrable_of_hasCompactSupport (μ := volume) hfc).norm
    change ‖∫ y, L (f y) (g (x - y))‖ ≤ _
    calc
      _ ≤ ∫ y, ‖L‖ * ‖f y‖ * C := by
        apply norm_integral_le_of_norm_le ((hi.const_mul ‖L‖).mul_const C)
        exact Filter.Eventually.of_forall fun y =>
          (L.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_left (hb (x - y))
            (mul_nonneg (norm_nonneg L) (norm_nonneg (f y))))
      _ = _ := by rw [integral_mul_const, integral_const_mul]
  | succ n ih =>
    rw [← norm_iteratedFDeriv_fderiv]
    have heq : fderiv ℝ (f ⋆[L, volume] g) =
        (fderiv ℝ f ⋆[L.precompL Base, volume] g) := by
      funext y
      exact (hfc.hasFDerivAt_convolution_left L (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hg.locallyIntegrable y).fderiv
    rw [heq]
    have h := ih (L.precompL Base) (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hfc.fderiv ℝ)
    simp_rw [norm_iteratedFDeriv_fderiv] at h
    apply h.trans
    gcongr
    exact L.norm_precompL_le Base

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingGain
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale-exact derivative gains for convolution by the constructed kernels. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

lemma norm_iterated_dilate {K : Base → ℝ} (hK : ContDiff ℝ ∞ K)
    {s : ℝ} (hs : 0 < s) (n : ℕ) (x : Base) :
    ‖iteratedFDeriv ℝ n (dilate K s) x‖ =
      (s ^ 2)⁻¹ * (s ^ n)⁻¹ * ‖iteratedFDeriv ℝ n K (s⁻¹ • x)‖ := by
  have heq : dilate K s = (s ^ 2)⁻¹ • (fun y : Base => K (s⁻¹ • y)) := rfl
  have hc : ContDiff ℝ (n : ℕ∞ω) (fun y : Base => K (s⁻¹ • y)) :=
    (hK.comp (contDiff_id.const_smul s⁻¹)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [heq, iteratedFDeriv_const_smul_apply (f := fun y : Base => K (s⁻¹ • y)) hc.contDiffAt]
  rw [congrFun (iteratedFDeriv_comp_const_smul s⁻¹ (hK.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))) x]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_pow,
    abs_of_pos hs, inv_pow]
  ring

lemma integral_norm_iterated_dilate {K : Base → ℝ} (hK : ContDiff ℝ ∞ K)
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (∫ x, ‖iteratedFDeriv ℝ n (dilate K s) x‖) =
      (s ^ n)⁻¹ * ∫ x, ‖iteratedFDeriv ℝ n K x‖ := by
  have hdim : Module.finrank ℝ Base = 2 := by simp [Base]
  simp_rw [norm_iterated_dilate hK hs]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x => ‖iteratedFDeriv ℝ n K x‖) hs.le, hdim, smul_eq_mul]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An arbitrarily high output derivative is bounded by the zeroth input
norm and the corresponding fixed kernel derivative mass. -/
theorem smooth_derivative_gain (r n : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ n (smooth r s f) x‖ ≤
      (s ^ n)⁻¹ * (∫ y, ‖iteratedFDeriv ℝ n (kernel r) y‖) * C := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hb 0)
  have h := convolution_iterated_norm_le (lsmul ℝ ℝ)
    n (smooth_dilate (kernel_smooth r) s) (compact_dilate (kernel_compact r) hs.ne') hf hb x
  change ‖iteratedFDeriv ℝ n (smooth r s f) x‖ ≤ _ at h
  apply h.trans
  rw [integral_norm_iterated_dilate (kernel_smooth r) hs]
  calc
    _ ≤ 1 * ((s ^ n)⁻¹ * ∫ y, ‖iteratedFDeriv ℝ n (kernel r) y‖) * C := by
      gcongr
      exact opNorm_lsmul_le
    _ = _ := by rw [one_mul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingResidual
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterated smoothing residuals give arbitrary finite approximation order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_compact (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hfc : HasCompactSupport f) : HasCompactSupport (smooth r s f) :=
  (compact_dilate (kernel_compact r) hs.ne').convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfc

lemma residual_smooth {s : ℝ} (hs : 0 < s) (n : ℕ) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (residual s n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.sub (smooth_smooth 0 hs ih.continuous.locallyIntegrable)

lemma residual_compact {s : ℝ} (hs : 0 < s) (n : ℕ) {f : Base → E}
    (hfc : HasCompactSupport f) : HasCompactSupport (residual s n f) := by
  induction n with
  | zero => exact hfc
  | succ n ih => exact ih.sub (smooth_compact 0 hs ih)

/-- Differentiation commutes with every finite residual. -/
lemma fderiv_residual {s : ℝ} (hs : 0 < s) (n : ℕ) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    fderiv ℝ (residual s n f) = residual s n (fderiv ℝ f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    have hr := residual_smooth hs n hf
    change fderiv ℝ (residual s n f - smooth 0 s (residual s n f)) x = _
    rw [fderiv_sub (hr.differentiable (by simp) x)
      ((smooth_smooth 0 hs hr.continuous.locallyIntegrable).differentiable (by simp) x)]
    rw [fderiv_smooth 0 hs hr (residual_compact hs n hfc), ih]
    rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingResidualOperator
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds in unchanged derivative norms for repeated residual operators. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The residual operator is bounded in the original norm, independently of
its smoothing scale. -/
theorem residual_bounded {s C : ℝ} (hs : 0 < s) (n : ℕ)
    {f : Base → E} (hb : ∀ x, ‖f x‖ ≤ C) (x : Base) :
    ‖residual s n f x‖ ≤ (1 + ∫ y, ‖kernel 0 y‖) ^ n * C := by
  induction n generalizing x with
  | zero => simpa only [residual, pow_zero, one_mul] using hb x
  | succ n ih =>
    change ‖residual s n f x - smooth 0 s (residual s n f) x‖ ≤ _
    calc
      _ ≤ ‖residual s n f x‖ + ‖smooth 0 s (residual s n f) x‖ := norm_sub_le _ _
      _ ≤ (1 + ∫ y, ‖kernel 0 y‖) ^ n * C +
          (∫ y, ‖kernel 0 y‖) * ((1 + ∫ y, ‖kernel 0 y‖) ^ n * C) :=
        add_le_add (ih x) (smooth_norm_le 0 hs ih x)
      _ = _ := by rw [pow_succ]; ring

/-- Repeated residuals are bounded in every original derivative norm. -/
theorem iterated_residual_bounded {s C : ℝ} (hs : 0 < s) (n m : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ m (residual s n f) x‖ ≤
      (1 + ∫ y, ‖kernel 0 y‖) ^ n * C := by
  induction m generalizing E with
  | zero =>
    simp only [norm_iteratedFDeriv_zero] at hb ⊢
    exact residual_bounded hs n hb x
  | succ m ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_residual hs n hf hfc]
    apply ih (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hfc.fderiv ℝ)
    intro y
    rw [norm_iteratedFDeriv_fderiv]
    exact hb y

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteOrderSmoother
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete smoother of any prescribed finite approximation order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma finiteSmooth_eq (n : ℕ) (s : ℝ) (f : Base → E) :
    finiteSmooth n s f = f - residual s n f := by
  induction n with
  | zero => simp [finiteSmooth, residual]
  | succ n ih =>
    unfold finiteSmooth at ih ⊢
    rw [Finset.sum_range_succ, ih]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, residual]
    abel

lemma finiteSmooth_smooth (n : ℕ) {s : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (finiteSmooth n s f) := by
  rw [finiteSmooth_eq]
  exact hf.sub (residual_smooth hs n hf)

lemma fderiv_finiteSmooth (n : ℕ) {s : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    fderiv ℝ (finiteSmooth n s f) = finiteSmooth n s (fderiv ℝ f) := by
  rw [finiteSmooth_eq, finiteSmooth_eq]
  funext x
  rw [fderiv_sub (hf.differentiable (by simp) x)
    ((residual_smooth hs n hf).differentiable (by simp) x),
    fderiv_residual hs n hf hfc]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSmootherBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds and derivative gain for the same finite-order smoother. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every original derivative norm remains bounded independently of scale. -/
theorem finiteSmooth_bounded (n m : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ m (finiteSmooth n s f) x‖ ≤
      (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ n) * C := by
  rw [finiteSmooth_eq, iteratedFDeriv_sub_apply
    ((hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)
    (((residual_smooth hs n hf).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m (residual s n f) x‖ := norm_sub_le _ _
    _ ≤ C + (1 + ∫ y, ‖kernel 0 y‖) ^ n * C :=
      add_le_add (hb x) (iterated_residual_bounded hs n m hf hfc hb x)
    _ = _ := by ring

lemma gainConstant_nonneg (n m : ℕ) : 0 ≤ gainConstant n m := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (pow_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) _)

/-- A gain of `m` derivatives uses just the zeroth input norm. -/
theorem finiteSmooth_gain (n m : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hb : ∀ x, ‖f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ m (finiteSmooth n s f) x‖ ≤
      (s ^ m)⁻¹ * gainConstant n m * C := by
  unfold finiteSmooth
  rw [iteratedFDeriv_sum_apply (fun i _ =>
    ((smooth_smooth 0 hs (residual_smooth hs i hf).continuous.locallyIntegrable).of_le
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt)]
  calc
    _ ≤ ∑ i ∈ Finset.range n, ‖iteratedFDeriv ℝ m (smooth 0 s (residual s i f)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, (s ^ m)⁻¹ *
        ((∫ y, ‖iteratedFDeriv ℝ m (kernel 0) y‖) *
          (1 + ∫ y, ‖kernel 0 y‖) ^ i) * C := by
      apply Finset.sum_le_sum
      intro i _
      have h := smooth_derivative_gain 0 m hs (residual_smooth hs i hf).continuous
        (fun y => residual_bounded hs i hb y) x
      convert h using 1
      all_goals try with_reducible_and_instances rfl
      ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]; rfl

/-- Additional output derivatives cost the smoothing scale, while the
original `q` input derivatives commute through the same operator. -/
theorem finiteSmooth_gain_from_derivatives (n q m : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ q f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ (q + m) (finiteSmooth n s f) x‖ ≤
      (s ^ m)⁻¹ * gainConstant n m * C := by
  induction q generalizing E with
  | zero =>
    rw [Nat.zero_add]
    simp only [norm_iteratedFDeriv_zero] at hb
    exact finiteSmooth_gain n m hs hf hb x
  | succ q ih =>
    rw [show q + 1 + m = (q + m) + 1 by omega, ← norm_iteratedFDeriv_fderiv,
      fderiv_finiteSmooth n hs hf hfc]
    apply ih (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hfc.fderiv ℝ)
    intro y
    rw [norm_iteratedFDeriv_fderiv]
    exact hb y

end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

/-- Each overlap transports a global weighted bound with fixed constants. -/
theorem pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m C h →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m (D * C)
        (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.localize_restore]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
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

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

/-- Restoring finitely many coordinate functions is bounded in every fixed
weighted atlas norm, uniformly in the input and the scale. -/
theorem restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, WeightedEstimates.WeightedBound Set.univ s m C (h i)) →
      A.WeightedBound s m (D * C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.pair_weighted_bound (V := V) i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j) (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [localize_sum]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSmootherWeighted
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted bounds for finite-order smoothing in the chart norms used by
the correction iteration. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory WeightedEstimates
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothing at one scale remains bounded in the original weighted norm
at any other positive scale. -/
theorem finiteSmooth_weighted_bounded (n m : ℕ) {s t C : ℝ}
    (hs : 0 < s) (ht : 0 < t) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : WeightedBound Set.univ t m C f) :
    WeightedBound Set.univ t m ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ n) * C)
      (finiteSmooth n s f) := by
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  have h := finiteSmooth_bounded n j hs hf hfc (C := C / t ^ j)
    (fun y => by simpa only [iteratedFDerivWithin_univ] using hb.deriv_le ht hj (Set.mem_univ y)) x
  calc
    _ ≤ t ^ j * ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ n) * (C / t ^ j)) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg ht.le _)
    _ = _ := by field_simp

lemma weightedGainConstant_nonneg (n m : ℕ) : 0 ≤ weightedGainConstant n m :=
  Finset.sum_nonneg (fun j _ => gainConstant_nonneg n j)

/-- Every weighted output derivative is controlled by the zeroth input
norm; higher input derivatives do not enter the constant. -/
theorem finiteSmooth_weighted_gain (n m : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hb : ∀ x, ‖f x‖ ≤ C) :
    WeightedBound Set.univ s m (weightedGainConstant n m * C) (finiteSmooth n s f) := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hb 0)
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  have h := finiteSmooth_gain n j hs hf hb x
  have hsum : gainConstant n j ≤ weightedGainConstant n m :=
    Finset.single_le_sum (fun i _ => gainConstant_nonneg n i) (Finset.mem_range.mpr (by omega))
  calc
    _ ≤ s ^ j * ((s ^ j)⁻¹ * gainConstant n j * C) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg hs.le _)
    _ = gainConstant n j * C := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum hC

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalBundleSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundedness, gain and finite-input tails for bundle smoothing. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle MeasureTheory
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContMDiffVectorBundle ∞ F E planeModel]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

/-- No derivative above the stated input order occurs in either bound. -/
theorem bundle_smoothing_bounds (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ (u : ∀ x, E x) (s t C : ℝ), 0 < s → 0 < t → t ≤ 1 → 0 ≤ C →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
          (fun x => TotalSpace.mk' F x (u x)) → A.BundleWeightedBound e t m C u →
        A.BundleWeightedBound e t m (D * (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C)
          (A.bundleSmooth e r s u)) ∧
      (∀ (u : ∀ x, E x) (s t C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
          (fun x => TotalSpace.mk' F x (u x)) → A.BundleWeightedBound e t 0 C u →
        A.BundleWeightedBound e s m (D * weightedGainConstant r m * C)
          (A.bundleSmooth e r s u)) := by
  obtain ⟨D, hD, hd⟩ := A.bundle_restoration_bound e hdomain m
  refine ⟨D, hD, ?_, ?_⟩
  · intro u s t C hs ht ht1 hC hu hb
    have hnon : 0 ≤ (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C := by positivity
    have h := hd (fun i => finiteSmooth r s (A.bundleLocalize e i u)) t
      ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C) ht ht1 hnon
      (fun i => finiteSmooth_smooth r hs (A.bundleLocalize_smooth e hdomain i hu))
      (fun i => finiteSmooth_weighted_bounded r m hs ht
        (A.bundleLocalize_smooth e hdomain i hu)
        (localize_compact (i : M) (A.weight_support i) _) (hb i))
    rw [show A.bundleSmooth e r s u = (fun x => ∑ i : A.centers,
      A.bundleRestore e i (finiteSmooth r s (A.bundleLocalize e i u)) x) from rfl]
    simpa only [mul_assoc] using h
  · intro u s t C hs hs1 hC hu hb
    have h := hd (fun i => finiteSmooth r s (A.bundleLocalize e i u)) s
      (weightedGainConstant r m * C) hs hs1
      (mul_nonneg (weightedGainConstant_nonneg r m) hC)
      (fun i => finiteSmooth_smooth r hs (A.bundleLocalize_smooth e hdomain i hu))
      (fun i => finiteSmooth_weighted_gain r m hs
        (A.bundleLocalize_smooth e hdomain i hu) (fun x => (hb i).norm_le (mem_univ x)))
    rw [show A.bundleSmooth e r s u = (fun x => ∑ i : A.centers,
      A.bundleRestore e i (finiteSmooth r s (A.bundleLocalize e i u)) x) from rfl]
    simpa only [mul_assoc] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

/-- An unweighted prefix of any lower order is controlled by a shifted bound. -/
lemma ShiftedBound.prefix {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {j : ℕ} (hj : j ≤ q + m) :
    WeightedBound Set.univ 1 j (C / s ^ (j - q)) f := by
  intro i hi x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  apply (h.deriv_le hs (hi.trans hj) x).trans
  exact div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le_sub_right hi q))

/-- No derivative in the unweighted prefix incurs a smoothing-scale loss. -/
theorem finiteSmooth_shifted_gain (r q m : ℕ) {s C : ℝ} (hs : 0 < s)
    (hC : 0 ≤ C) {f : Base → V} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hb : WeightedBound Set.univ 1 q C f) :
    ShiftedBound q m s
      (((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * C)
      (finiteSmooth r s f) := by
  intro j hj x
  by_cases hjq : j ≤ q
  · have hi : ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ C := fun y => by
      simpa only [one_pow, one_mul, iteratedFDerivWithin_univ] using hb j hjq y (Set.mem_univ y)
    have h := finiteSmooth_bounded r j hs hf hc hi x
    rw [Nat.sub_eq_zero_of_le hjq, pow_zero, one_mul]
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (weightedGainConstant_nonneg r m)) hC
  · have hi : ∀ y, ‖iteratedFDeriv ℝ q f y‖ ≤ C := fun y => by
      simpa only [one_pow, one_mul, iteratedFDerivWithin_univ] using hb q le_rfl y (Set.mem_univ y)
    have h := finiteSmooth_gain_from_derivatives r q (j - q) hs hf hc hi x
    rw [Nat.add_sub_of_le (by omega : q ≤ j)] at h
    have hsum : gainConstant r (j - q) ≤ weightedGainConstant r m :=
      Finset.single_le_sum (fun i _ => gainConstant_nonneg r i) (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ s ^ (j - q) * ((s ^ (j - q))⁻¹ * gainConstant r (j - q) * C) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hs.le _)
      _ = gainConstant r (j - q) * C := by field_simp
      _ ≤ (((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * C) := by
        apply mul_le_mul_of_nonneg_right _ hC
        exact hsum.trans (le_add_of_nonneg_left (by positivity))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalShiftedSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas smoothing with an unweighted derivative prefix. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold MeasureTheory
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Fixed smooth chart transitions preserve the unweighted prefix. -/
theorem restoration_shifted_bound (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, FiniteOrderSmoothing.ShiftedBound q m s C (h i)) →
      A.ShiftedBound q m s (D * C)
        (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hd using fun j : ℕ => A.restoration_bound (V := V) j
  refine ⟨∑ j ∈ Finset.range (q + m + 1), D j,
    Finset.sum_nonneg (fun j _ => hD j), ?_⟩
  intro h s C hs hs1 hC hh hb i j hj x
  have he : 0 < s ^ (j - q) := pow_pos hs _
  have ho := hd j h 1 (C / s ^ (j - q)) zero_lt_one le_rfl
    (div_nonneg hC he.le) hh (fun k => (hb k).prefix hs hs1 hC hj)
  have hi := ho i j le_rfl x (mem_univ x)
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ] at hi
  calc
    _ ≤ s ^ (j - q) * (D j * (C / s ^ (j - q))) :=
      mul_le_mul_of_nonneg_left hi he.le
    _ = D j * C := by field_simp
    _ ≤ (∑ k ∈ Finset.range (q + m + 1), D k) * C :=
      mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC

/-- Global gain of arbitrary higher derivatives uses only the fixed prefix. -/
theorem smoothing_shifted_gain (r q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ, V) ∞ f →
      A.ShiftedBound q 0 1 C f → A.ShiftedBound q m s
        (D * ((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * C)
        (A.smooth r s f) := by
  obtain ⟨D, hD, hd⟩ := A.restoration_shifted_bound (V := V) q m
  refine ⟨D, hD, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hg := weightedGainConstant_nonneg r m
  have h := hd (fun i => finiteSmooth r s (localize (i : M) (A.weight i) f)) s
    (((1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) + weightedGainConstant r m) * C)
    hs hs1 (by positivity)
    (fun i => finiteSmooth_smooth r hs
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))
    (fun i => finiteSmooth_shifted_gain r q m hs hC
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
      (localize_compact (i : M) (A.weight_support i) f)
      (by simpa using (hb i).prefix zero_lt_one le_rfl hC (j := q) (by omega)))
  simpa only [smooth, mul_assoc] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanIteration
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth of the actual finite mean iteration and of the
finite value budget appearing in its explicit smallness threshold. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.nonneg {f : ℝ → ℝ} (hf : HasPolynomialBound f)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ f x := by
  obtain ⟨_,_,_,h⟩ := hf
  exact (h x hx).1

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothing
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing on the actual covariant two-tensor bundle of the surface. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle MeasureTheory
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelSpace
local instance tensorModelComplete_r01bf32_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelSpace
local instance tensorModelComplete_r01bf32_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

theorem tensor_smoothing_bounds (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ (u : ∀ p : M, CovariantTwoTensor p) (s t C : ℝ),
        0 < s → 0 < t → t ≤ 1 → 0 ≤ C →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun p => TotalSpace.mk' TensorFiber p (u p)) → A.TensorWeightedBound t m C u →
        A.TensorWeightedBound t m
          (D * (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C) (A.tensorSmooth r s u)) ∧
      (∀ (u : ∀ p : M, CovariantTwoTensor p) (s t C : ℝ),
        0 < s → s ≤ 1 → 0 ≤ C →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun p => TotalSpace.mk' TensorFiber p (u p)) → A.TensorWeightedBound t 0 C u →
        A.TensorWeightedBound s m (D * weightedGainConstant r m * C) (A.tensorSmooth r s u)) :=
  A.bundle_smoothing_bounds (F := TensorFiber) (E := CovariantTwoTensor (M := M))
    A.tensorTriv A.tensorTriv_domain r m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialSmoothingProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for smoothed inputs with a polynomial finite input budget. -/
noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileFiberSpace
local instance polySmoothingProfileDualAdd_r01bf32_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileFiberNormed
local instance polySmoothingProfileSectionNormed_r01bf32_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polySmoothingProfileSectionSpace_r01bf32_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_smoothing_input_profiles_oai (r : ℕ) (B : ℝ → ℝ) (hB : HasPolynomialBound B) :
    ∃ P C : ℕ → ℝ → ℝ,
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (C m)) ∧
      (∀ m x, 1 ≤ x → 1 ≤ C m x) ∧
    ∀ x : ℝ, 1 ≤ x →
      ∀ (G : M → Space) (H : ∀ y : M, CovariantTwoTensor y) (t s : ℝ),
      0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (H y)) →
      A.InputBound t r (B x) G H →
      (∀ m, A.ShiftedBound 2 m s (P m x) (A.smooth r s G)) ∧
      (∀ m, A.TensorWeightedBound s m (C m x) (A.tensorSmooth r s H)) := by
  classical
  choose DG hDG hg using fun m => A.smoothing_shifted_gain (V := Space) r 2 m
  choose DH hDH hh using fun m => A.tensor_smoothing_bounds r m
  let U := fun m => DG m*((1+(1+∫ y, ‖kernel 0 y‖)^r)+weightedGainConstant r m)
  let V := fun m => DH m*weightedGainConstant r m
  have hker : 0 ≤ ∫ y, ‖kernel 0 y‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hU (m : ℕ) : 0 ≤ U m := by
    have hd := hDG m
    have hg := weightedGainConstant_nonneg r m
    dsimp [U] <;> positivity
  have hV (m : ℕ) : 0 ≤ V m := mul_nonneg (hDH m) (weightedGainConstant_nonneg r m)
  let P := fun m x => U m*B x
  let C := fun m x => 1+V m*B x
  refine ⟨P,C,fun m => (polynomialBound_const (hU m)).mul hB,
    fun m => (polynomialBound_const zero_le_one).add ((polynomialBound_const (hV m)).mul hB),?_,?_⟩
  · intro m x hx
    have hh := mul_nonneg (hV m) (hB.nonneg hx)
    dsimp [C] <;> linarith
  · intro x hx G H t s _ht _ht1 hs hs1 hG hH hinput
    have hb := hB.nonneg hx
    have hprefix : A.ShiftedBound 2 0 1 (B x) G := by
      intro i j hj y
      have hj2 : j ≤ 2 := by omega
      have hjr : j ≤ 2+r := by omega
      simpa only [Nat.sub_eq_zero_of_le hj2,pow_zero,one_mul] using hinput.1 i j hjr y
    refine ⟨fun m => hg m G s (B x) hs hs1 hb hG hprefix,?_⟩
    intro m i
    have hzero : A.TensorWeightedBound t 0 (B x) H :=
      fun k => (hinput.2 k).mono_order (Nat.zero_le r)
    apply (((hh m).2 H s t (B x) hs hs1 hb hH hzero) i).mono_const
    change V m*B x ≤ 1+V m*B x
    linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles_oai.{u_1}
