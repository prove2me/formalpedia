-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_actual_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:46.437206+00:00
-- url     : https://prove2.me/submissions/3a8fc563-ead1-4352-90f6-db08b23c7619

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_anchored_smoothed_increment
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_smoothed_normalized_metric_step_bound

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
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

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)


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

lemma WeightedBound.neg {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun x => -f x) := by
  simpa using hb.const_smul hU hf (-1)

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

lemma kernel_mass (r : ℕ) : (∫ x, kernel r x) = 1 :=
  (Classical.choose_spec (exists_smoothing_kernel r)).2.2.1

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingFirstMoment
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-moment control of the error of the actual convolution operator. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

lemma firstMoment_nonneg (K : Base → ℝ) : 0 ≤ firstMoment K :=
  integral_nonneg fun _x => mul_nonneg (norm_nonneg _) (norm_nonneg _)

lemma firstMoment_dilate (K : Base → ℝ) {s : ℝ} (hs : 0 < s) :
    firstMoment (dilate K s) = s * firstMoment K := by
  have hdim : Module.finrank ℝ Base = 2 := by simp [Base]
  have hn (x : Base) : ‖x‖ = s * ‖s⁻¹ • x‖ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hs]
    field_simp
  have heq : (fun x => ‖dilate K s x‖ * ‖x‖) =
      fun x => (s / s ^ 2) * ((fun y => ‖K y‖ * ‖y‖) (s⁻¹ • x)) := by
    funext x
    rw [hn x, norm_dilate]
    unfold dilate
    ring
  unfold firstMoment
  rw [heq, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖K x‖ * ‖x‖) hs.le]
  rw [hdim, smul_eq_mul]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The smoothing error loses one derivative and gains one power of its scale. -/
theorem smooth_sub_norm_le (r : ℕ) {s C : ℝ} (hs : 0 < s)
    {f : Base → E} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ C) (x : Base) :
    ‖f x - smooth r s f x‖ ≤ s * firstMoment (kernel r) * C := by
  let K := dilate (kernel r) s
  have hk : HasCompactSupport K := compact_dilate (kernel_compact r) hs.ne'
  have hkc : Continuous K := (smooth_dilate (kernel_smooth r) s).continuous
  have hi₁ : Integrable (fun y => K y • f x) := by
    exact ((hkc.smul continuous_const).integrable_of_hasCompactSupport
      (hk.smul_right (f' := fun _ => f x)))
  have hi₂ : Integrable (fun y => K y • f (x - y)) := by
    exact ((hkc.smul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (hk.smul_right (f' := fun y => f (x - y))))
  have heq : f x - smooth r s f x = ∫ y, K y • (f x - f (x - y)) := by
    simp_rw [smul_sub]
    rw [integral_sub hi₁ hi₂, integral_smul_const]
    change f x - smooth r s f x = (∫ y, dilate (kernel r) s y) • f x - smooth r s f x
    rw [mass_dilate _ hs, kernel_mass, one_smul]
  have him : Integrable (fun y => ‖K y‖ * ‖y‖ * C) := by
    exact ((hkc.norm.mul continuous_norm).integrable_of_hasCompactSupport
      (hk.norm.mul_right (f' := fun y => ‖y‖))).mul_const C
  rw [heq]
  calc
    _ ≤ ∫ y, ‖K y‖ * ‖y‖ * C := by
      apply norm_integral_le_of_norm_le him
      exact Filter.Eventually.of_forall fun y => by
        rw [norm_smul]
        have h := Convex.norm_image_sub_le_of_norm_fderiv_le
          (s := Set.univ) (fun z _ => hf.differentiable (by simp) z)
          (fun z _ => hb z) convex_univ (Set.mem_univ (x - y)) (Set.mem_univ x)
        have hd : ‖f x - f (x - y)‖ ≤ C * ‖y‖ := by
          simpa only [sub_sub_cancel] using h
        nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg (K y))]
    _ = firstMoment K * C := by rw [integral_mul_const]; rfl
    _ = s * firstMoment (kernel r) * C := by rw [firstMoment_dilate _ hs]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingResidualBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary finite approximation order from a finite input derivative bound. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Applying the smoothing residual `n` times gains `s^n`, using just the
`n`-th derivative of the original input. -/
theorem residual_norm_le {s C : ℝ} (hs : 0 < s) (n : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : Base) :
    ‖residual s n f x‖ ≤ (s * firstMoment (kernel 0)) ^ n * C := by
  induction n generalizing E x with
  | zero => simpa only [residual, pow_zero, one_mul, norm_iteratedFDeriv_zero] using hb x
  | succ n ih =>
    have hb' : ∀ y, ‖fderiv ℝ (residual s n f) y‖ ≤
        (s * firstMoment (kernel 0)) ^ n * C := by
      intro y
      rw [fderiv_residual hs n hf hfc]
      apply ih (hf.fderiv_right (m := ∞) (by simp)) (hfc.fderiv ℝ) (x := y)
      intro z
      rw [norm_iteratedFDeriv_fderiv]
      exact hb z
    have h := smooth_sub_norm_le 0 hs (residual_smooth hs n hf) hb' x
    change ‖residual s n f x - smooth 0 s (residual s n f) x‖ ≤ _
    apply h.trans_eq
    rw [pow_succ]
    ring

/-- The same finite-order approximation estimate in each higher derivative. -/
theorem iterated_residual_norm_le {s C : ℝ} (hs : 0 < s) (n m : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ (n + m) f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ m (residual s n f) x‖ ≤
      (s * firstMoment (kernel 0)) ^ n * C := by
  induction m generalizing E with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact residual_norm_le hs n hf hfc (by simpa only [Nat.add_zero] using hb) x
  | succ m ih =>
    rw [← norm_iteratedFDeriv_fderiv, fderiv_residual hs n hf hfc]
    apply ih (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hfc.fderiv ℝ)
    intro y
    rw [norm_iteratedFDeriv_fderiv]
    rw [Nat.add_assoc]
    exact hb y

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

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSmootherApproximation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-order smoother approximates using only the displayed finite
number of input derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma residual_add_orders (s : ℝ) (n m : ℕ) (f : Base → E) :
    residual s (n + m) f = residual s n (residual s m f) := by
  induction n with
  | zero => simp only [Nat.zero_add, residual]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [residual, ih]

lemma error_finiteSmooth (n : ℕ) (s : ℝ) (f : Base → E) :
    f - finiteSmooth n s f = residual s n f := by
  rw [finiteSmooth_eq]
  abel

lemma approximationConstant_nonneg (r j : ℕ) : 0 ≤ approximationConstant r j :=
  mul_nonneg
    (pow_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) _)
    (pow_nonneg (firstMoment_nonneg _) _)

variable [CompleteSpace E]

/-- The `q+j`-th error derivative gains `s^(r-j)`, using input derivatives
only through `q+r`. Constants do not depend on the input or the scale. -/
theorem finiteSmooth_approximation (r q j : ℕ) (hj : j ≤ r)
    {s C : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ∀ x, ‖iteratedFDeriv ℝ (q + r) f x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ (q + j) (f - finiteSmooth r s f) x‖ ≤
      approximationConstant r j * s ^ (r - j) * C := by
  rw [error_finiteSmooth]
  have heq : residual s r f = residual s j (residual s (r - j) f) := by
    rw [← residual_add_orders, Nat.add_sub_of_le hj]
  rw [heq]
  have hb' : ∀ y, ‖iteratedFDeriv ℝ (q + j) (residual s (r - j) f) y‖ ≤
      (s * firstMoment (kernel 0)) ^ (r - j) * C := by
    intro y
    apply iterated_residual_norm_le hs (r - j) (q + j) hf hfc
    intro z
    rw [show r - j + (q + j) = q + r by omega]
    exact hb z
  have h := iterated_residual_bounded hs j (q + j)
    (residual_smooth hs (r - j) hf) (residual_compact hs (r - j) hfc) hb' x
  apply h.trans_eq
  unfold approximationConstant
  rw [mul_pow]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

omit [IsManifold planeModel ∞ M] in
lemma restore_sub (p : M) (χ : M → ℝ) (h k : Base → V) :
    restore p χ (h - k) = restore p χ h - restore p χ k := by
  funext x
  by_cases hx : x ∈ (chart p).source <;>
    simp [restore, hx, smul_sub]

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

variable [CompactSpace M]

lemma smooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (A.smooth r s f) := by
  have heq : A.smooth r s f = fun x => ∑ i : A.centers,
      restore (i : M) (A.outer i) (finiteSmooth r s (localize (i : M) (A.weight i) f)) x := by
    funext x
    simp only [smooth, Finset.sum_apply]
  rw [heq]
  apply ContMDiff.sum
  intro i _
  exact restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (finiteSmooth_smooth r hs (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

omit [CompactSpace M] in
/-- Global smoothing error is exactly the sum of the localized residuals.
This identity is the link for transporting the coordinate tail estimates. -/
lemma sub_smooth_eq_error (r : ℕ) (s : ℝ) (f : M → V) :
    f - A.smooth r s f = A.error r s f := by
  conv_lhs => lhs; rw [← A.sum_restore_localize f]
  unfold smooth error
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← restore_sub, error_finiteSmooth]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_smul (p : M) (ψ : M → ℝ) (a : ℝ) (f : M → V) :
    localize p ψ (a • f) = a • localize p ψ f := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_smul, mul_comm]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual finite-atlas smoothing operator on smooth vector-bundle sections. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
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

variable [CompactSpace M]

/-- Smoothing produces a smooth section of the original bundle. -/
theorem bundleSmooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {u : ∀ x, E x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (u x))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
      (fun x => TotalSpace.mk' F x (A.bundleSmooth e r s u x)) := by
  apply ContMDiff.sum_section
  intro i _
  exact A.bundleRestore_smooth e hdomain i
    (finiteSmooth_smooth r hs (A.bundleLocalize_smooth e hdomain i hu))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BundleSmoothingIdentity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction and error identities for bundle smoothing. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

lemma bundleRestore_sub (i : A.centers) (f g : Base → F) (x : M) :
    A.bundleRestore e i (f - g) x = A.bundleRestore e i f x - A.bundleRestore e i g x := by
  simp only [bundleRestore, Pi.sub_apply, map_sub, smul_sub]

variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

/-- The smoothing tail is exactly the finite restoration of coordinate tails. -/
theorem bundle_smoothing_error (r : ℕ) (s : ℝ) (u : ∀ x, E x) (x : M) :
    u x - A.bundleSmooth e r s u x =
      ∑ i : A.centers, A.bundleRestore e i (residual s r (A.bundleLocalize e i u)) x := by
  rw [← A.bundle_sum_restore_localize e hdomain u x]
  unfold bundleSmooth
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← A.bundleRestore_sub, ← error_finiteSmooth]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTailBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-input smoothing-tail estimate at every output order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory WeightedEstimates
open JetPolynomial (Base)

lemma approximationConstant_le_tail {r j : ℕ} (hj : j ≤ r) :
    approximationConstant r j ≤ tailConstant r := by
  have h : approximationConstant r j ≤
      ∑ i ∈ Finset.range (r + 1), approximationConstant r i :=
    Finset.single_le_sum (fun i _ => approximationConstant_nonneg r i)
      (Finset.mem_range.mpr (by omega))
  exact h.trans (le_add_of_nonneg_right (pow_nonneg
    (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) r))

lemma residualConstant_le_tail (r : ℕ) :
    (1 + ∫ y, ‖kernel 0 y‖) ^ r ≤ tailConstant r :=
  le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => approximationConstant_nonneg r i)

lemma tailConstant_nonneg (r : ℕ) : 0 ≤ tailConstant r :=
  (approximationConstant_nonneg r 0).trans (approximationConstant_le_tail (Nat.zero_le r))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Only the finite order `r` is used in the approximation term; uncontrolled
higher input derivatives enter linearly, multiplied by `(τ/t)^r`. -/
theorem weighted_smoothing_tail (r m : ℕ) {s t τ B C : ℝ}
    (hτ : 0 < τ) (hτs : τ ≤ s) (hst : s ≤ t)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hBr : WeightedBound Set.univ t r B f)
    (hCm : WeightedBound Set.univ t m C f) :
    WeightedBound Set.univ τ m
      (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
      (f - finiteSmooth r s f) := by
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτt : τ ≤ t := hτs.trans hst
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hBr.norm_le (Set.mem_univ 0))
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hCm.norm_le (Set.mem_univ 0))
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hjr : j ≤ r
  · have hbr : ∀ y, ‖iteratedFDeriv ℝ r f y‖ ≤ B / t ^ r := fun y => by
      simpa only [iteratedFDerivWithin_univ] using hBr.deriv_le ht le_rfl (Set.mem_univ y)
    have h := finiteSmooth_approximation r 0 j hjr hs hf hfc
      (fun y => by rw [Nat.zero_add]; exact hbr y) x
    rw [Nat.zero_add] at h
    have hp : τ ^ j * s ^ (r - j) ≤ s ^ r := by
      calc
        _ ≤ s ^ j * s ^ (r - j) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hτ.le hτs j) (pow_nonneg hs.le _)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjr]
    calc
      _ ≤ τ ^ j * (approximationConstant r j * s ^ (r - j) * (B / t ^ r)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hτ.le _)
      _ = (approximationConstant r j * B / t ^ r) * (τ ^ j * s ^ (r - j)) := by ring
      _ ≤ (approximationConstant r j * B / t ^ r) * s ^ r :=
        mul_le_mul_of_nonneg_left hp (div_nonneg
          (mul_nonneg (approximationConstant_nonneg _ _) hB) (pow_nonneg ht.le _))
      _ = approximationConstant r j * (B * (s / t) ^ r) := by rw [div_pow]; ring
      _ ≤ tailConstant r * (B * (s / t) ^ r) :=
        mul_le_mul_of_nonneg_right (approximationConstant_le_tail hjr)
          (mul_nonneg hB (pow_nonneg (div_nonneg hs.le ht.le) _))
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hC (pow_nonneg (div_nonneg hτ.le ht.le) _)))
        (tailConstant_nonneg r)
  · have hrj : r ≤ j := by omega
    have hbc : ∀ y, ‖iteratedFDeriv ℝ j f y‖ ≤ C / t ^ j := fun y => by
      simpa only [iteratedFDerivWithin_univ] using hCm.deriv_le ht hj (Set.mem_univ y)
    have h := iterated_residual_bounded hs r j hf hfc hbc x
    rw [error_finiteSmooth]
    have hp : (τ / t) ^ j ≤ (τ / t) ^ r :=
      pow_le_pow_of_le_one (div_nonneg hτ.le ht.le) ((div_le_one ht).mpr hτt) hrj
    calc
      _ ≤ τ ^ j * ((1 + ∫ y, ‖kernel 0 y‖) ^ r * (C / t ^ j)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hτ.le _)
      _ = (1 + ∫ y, ‖kernel 0 y‖) ^ r * C * (τ / t) ^ j := by rw [div_pow]; ring
      _ ≤ (1 + ∫ y, ‖kernel 0 y‖) ^ r * C * (τ / t) ^ r :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg
          (pow_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => norm_nonneg _)) _) hC)
      _ ≤ tailConstant r * (C * (τ / t) ^ r) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (residualConstant_le_tail r)
          (mul_nonneg hC (pow_nonneg (div_nonneg hτ.le ht.le) _))
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg hB (pow_nonneg (div_nonneg hs.le ht.le) _)))
        (tailConstant_nonneg r)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
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

variable [CompleteSpace V]

/-- A finite shifted input order suffices for the approximation term. Higher
input derivatives occur linearly, with the two-scale decaying factor. -/
theorem shifted_smoothing_tail (r q m : ℕ) {s t τ B C : ℝ}
    (hτ : 0 < τ) (hτs : τ ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1)
    (hB : 0 ≤ B) (hC : 0 ≤ C) {f : Base → V}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hBr : ShiftedBound q r t B f) (hCm : ShiftedBound q m t C f) :
    ShiftedBound q m τ
      (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
      (f - finiteSmooth r s f) := by
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτt : τ ≤ t := hτs.trans hst
  have hprefix := hBr.prefix ht ht1 hB (j := q + r) le_rfl
  intro j hj x
  by_cases hjr : j - q ≤ r
  · have hbr : ∀ y, ‖iteratedFDeriv ℝ (min j q + r) f y‖ ≤ B / t ^ r := fun y => by
      have h := hprefix.deriv_le (by norm_num) (show min j q + r ≤ q + r by omega)
        (Set.mem_univ y)
      simpa only [one_pow, div_one, iteratedFDerivWithin_univ, Nat.add_sub_cancel_left] using h
    have h := finiteSmooth_approximation r (min j q) (j - q) hjr hs hf hfc hbr x
    rw [show min j q + (j - q) = j by omega] at h
    have hp : τ ^ (j - q) * s ^ (r - (j - q)) ≤ s ^ r := by
      calc
        _ ≤ s ^ (j - q) * s ^ (r - (j - q)) := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hτ.le hτs _) (pow_nonneg hs.le _)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hjr]
    calc
      _ ≤ τ ^ (j - q) * (approximationConstant r (j - q) *
          s ^ (r - (j - q)) * (B / t ^ r)) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hτ.le _)
      _ = (approximationConstant r (j - q) * B / t ^ r) *
          (τ ^ (j - q) * s ^ (r - (j - q))) := by ring
      _ ≤ (approximationConstant r (j - q) * B / t ^ r) * s ^ r :=
        mul_le_mul_of_nonneg_left hp (div_nonneg
          (mul_nonneg (approximationConstant_nonneg _ _) hB) (pow_nonneg ht.le _))
      _ = approximationConstant r (j - q) * (B * (s / t) ^ r) := by rw [div_pow]; ring
      _ ≤ tailConstant r * (B * (s / t) ^ r) :=
        mul_le_mul_of_nonneg_right (approximationConstant_le_tail hjr) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (tailConstant_nonneg r)
  · have hbc := fun y => hCm.deriv_le ht hj y
    have h := iterated_residual_bounded hs r j hf hfc hbc x
    rw [error_finiteSmooth]
    have hp : (τ / t) ^ (j - q) ≤ (τ / t) ^ r :=
      pow_le_pow_of_le_one (by positivity) ((div_le_one ht).mpr hτt) (by omega)
    calc
      _ ≤ τ ^ (j - q) * ((1 + ∫ y, ‖kernel 0 y‖) ^ r * (C / t ^ (j - q))) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hτ.le _)
      _ = (1 + ∫ y, ‖kernel 0 y‖) ^ r * C * (τ / t) ^ (j - q) := by rw [div_pow]; ring
      _ ≤ (1 + ∫ y, ‖kernel 0 y‖) ^ r * C * (τ / t) ^ r :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ tailConstant r * (C * (τ / t) ^ r) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (residualConstant_le_tail r) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity))
        (tailConstant_nonneg r)

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

variable [CompleteSpace V]

/-- The actual global smoothing error obeys the shifted two-scale estimate. -/
theorem smoothing_shifted_tail (r q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : M → V) (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel 𝓘(ℝ, V) ∞ f →
      A.ShiftedBound q r t B f → A.ShiftedBound q m t C f →
      A.ShiftedBound q m τ
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (f - A.smooth r s f) := by
  obtain ⟨D, hD, hd⟩ := A.restoration_shifted_bound (V := V) q m
  refine ⟨D, hD, ?_⟩
  intro f s t τ B C hτ hτs hst ht1 hB hC hf hb hc
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτ1 : τ ≤ 1 := hτs.trans (hst.trans ht1)
  have hsize : 0 ≤ tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r) :=
    mul_nonneg (tailConstant_nonneg r) (by positivity)
  have h := hd (fun i => residual s r (localize (i : M) (A.weight i) f)) τ
    (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r)) hτ hτ1 hsize
    (fun i => residual_smooth hs r
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf))
    (fun i => by
      rw [← error_finiteSmooth]
      exact shifted_smoothing_tail r q m hτ hτs hst ht1 hB hC
        (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
        (localize_compact (i : M) (A.weight_support i) f) (hb i) (hc i))
  rw [A.sub_smooth_eq_error]
  simpa only [error, mul_assoc] using h

end SmoothingAtlas
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

variable [CompleteSpace F]

/-- The high input norm remains linear after all bundle transition maps. -/
theorem bundle_smoothing_tail (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ x, E x) (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, F)) ∞
        (fun x => TotalSpace.mk' F x (u x)) →
      A.BundleWeightedBound e t r B u → A.BundleWeightedBound e t m C u →
      A.BundleWeightedBound e τ m
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (fun x => u x - A.bundleSmooth e r s u x) := by
  obtain ⟨D, hD, hd⟩ := A.bundle_restoration_bound e hdomain m
  refine ⟨D, hD, ?_⟩
  intro u s t τ B C hτ hτs hst ht1 hB hC hu hb hc
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hτ1 : τ ≤ 1 := hτs.trans (hst.trans ht1)
  have hsize : 0 ≤ tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r) :=
    mul_nonneg (tailConstant_nonneg r) (by positivity)
  have h := hd (fun i => residual s r (A.bundleLocalize e i u)) τ
    (tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r)) hτ hτ1 hsize
    (fun i => residual_smooth hs r (A.bundleLocalize_smooth e hdomain i hu))
    (fun i => by
      rw [← error_finiteSmooth]
      exact weighted_smoothing_tail r m hτ hτs hst
        (A.bundleLocalize_smooth e hdomain i hu)
        (localize_compact (i : M) (A.weight_support i) _) (hb i) (hc i))
  have heq : (fun x => u x - A.bundleSmooth e r s u x) =
      fun x => ∑ i : A.centers, A.bundleRestore e i
        (residual s r (A.bundleLocalize e i u)) x :=
    funext (A.bundle_smoothing_error e hdomain r s u)
  rw [heq]
  simpa only [mul_assoc] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothing
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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
local instance tensorModelComplete : CompleteSpace TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDualSmul
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorModelSpace
theorem tensorSmooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s)
    {u : ∀ p : M, CovariantTwoTensor p}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.tensorSmooth r s u p)) :=
  A.bundleSmooth_smooth (F := TensorFiber) (E := CovariantTwoTensor (M := M)) A.tensorTriv A.tensorTriv_domain r hs hu

theorem tensor_smoothing_tail (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ p : M, CovariantTwoTensor p) (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      A.TensorWeightedBound t r B u → A.TensorWeightedBound t m C u →
      A.TensorWeightedBound τ m
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (fun p => u p - A.tensorSmooth r s u p) :=
  A.bundle_smoothing_tail (F := TensorFiber) (E := CovariantTwoTensor (M := M)) A.tensorTriv A.tensorTriv_domain r m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoupledSmoothing
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The joint map/tensor input bound and its actual two-scale smoothing tail. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coupledModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coupledModelSpace
local instance coupledModelComplete_r430729_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coupledModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coupledModelSpace
local instance coupledModelComplete_r430729_2 : CompleteSpace TensorFiber := inferInstance
variable (A : SmoothingAtlas M)

/-- The two smoothing errors obey the finite-input estimate together, with
only linear dependence on the possibly large higher input norm. -/
theorem coupled_smoothing_tail (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : M → Space) (H : ∀ p : M, CovariantTwoTensor p)
      (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (H p)) →
      A.InputBound t r B G H → A.InputBound t m C G H →
      A.InputBound τ m
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (G - A.smooth r s G) (fun p => H p - A.tensorSmooth r s H p) := by
  obtain ⟨DG, hDG, hG⟩ := A.smoothing_shifted_tail (V := Space) r 2 m
  obtain ⟨DH, hDH, hH⟩ := A.tensor_smoothing_tail r m
  refine ⟨DG + DH, add_nonneg hDG hDH, ?_⟩
  intro G H s t τ B C hτ hτs hst ht1 hB hC hGs hHs hbr hcm
  have hs : 0 < s := hτ.trans_le hτs
  have ht : 0 < t := hs.trans_le hst
  have hsize : 0 ≤ B * (s / t) ^ r + C * (τ / t) ^ r := by positivity
  have hg := hG G s t τ B C hτ hτs hst ht1 hB hC hGs hbr.1 hcm.1
  have hh := hH H s t τ B C hτ hτs hst ht1 hB hC hHs hbr.2 hcm.2
  constructor
  · intro i j hj x
    exact (hg i j hj x).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hDH) (tailConstant_nonneg r)) hsize)
  · intro i
    exact (hh i).mono_const (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hDG) (tailConstant_nonneg r)) hsize)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothedInputCloseness
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed low input bound controls the map's C2 smoothing error and
the encoded tensor smoothing error with the same positive scale power. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputClosenessFiberSpace
local instance inputClosenessDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputClosenessDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputClosenessFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputClosenessFiberSpace
local instance inputClosenessSectionNormed_r430729_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputClosenessSectionSpace_r430729_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem smoothed_input_closeness (r : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : M → Space) (H : ∀ x : M, CovariantTwoTensor x) (B t s : ℝ),
        0 ≤ B → 0 < s → s ≤ t → t ≤ 1 →
        ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (H x)) →
        A.InputBound t r B G H →
        A.WeightedBound 1 2 (D*B*(s/t)^r) (G - A.smooth r s G) ∧
        ∀ x, ‖A.tensorEncode H x - A.tensorEncode (A.tensorSmooth r s H) x‖ ≤ D*B*(s/t)^r := by
  obtain ⟨D,hD,htail⟩ := A.coupled_smoothing_tail r 0
  refine ⟨2*D*tailConstant r,mul_nonneg (mul_nonneg (by norm_num) hD) (tailConstant_nonneg r),?_⟩
  intro G H B t s hB hs hst ht1 hG hH hinput
  have ht : 0 < t := hs.trans_le hst
  have hzero : A.InputBound t 0 B G H := by
    constructor
    · intro i j hj x
      exact hinput.1 i j (by omega) x
    · exact fun i => (hinput.2 i).mono_order (Nat.zero_le r)
  have hb := htail G H s t s B B hs le_rfl hst ht1 hB hB hG hH hinput hzero
  have he : D * tailConstant r * (B * (s/t)^r + B * (s/t)^r) =
      (2*D*tailConstant r)*B*(s/t)^r := by ring
  rw [he] at hb
  have hC : 0 ≤ (2*D*tailConstant r)*B*(s/t)^r :=
    mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hD) (tailConstant_nonneg r)) hB)
      (pow_nonneg (div_nonneg hs.le ht.le) r)
  constructor
  · intro i j hj x _hx
    have hh := hb.1 i j (by omega) x
    simpa only [Nat.sub_eq_zero_of_le hj,pow_zero,one_pow,one_mul,
      iteratedFDerivWithin_univ] using hh
  · have hdiff := hH.sub_section (A.tensorSmooth_smooth r hs hH)
    have henc := A.tensorEncode_bound hdiff hs hC hb.2
    intro x
    have hh := henc.norm_le (mem_univ x)
    simpa only [A.tensorEncode_sub,Pi.sub_apply] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothedInputAdmissibility
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-norm bootstrap assumptions imply the actual smoothed inputs
remain inside the fixed map and tensor neighborhoods. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.admissibilityFiberSpace
local instance admissibilityDualAdd_r430729_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.admissibilityDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.admissibilityFiberNormed
local instance admissibilitySectionNormed_r430729_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance admissibilitySectionSpace_r430729_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem smoothed_input_admissibility (r : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (g : SmoothMetric M) (F G : M → Space) (H : ∀ x : M, CovariantTwoTensor x)
        (ρ a b B t s α K : ℝ),
        0 < ρ → 0 < a → 0 ≤ B → 0 < s → s ≤ t → t ≤ 1 →
        ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (H x)) →
        A.InputBound t r B G H → A.WeightedBound 1 2 b (G-F) → b ≤ ρ/4 →
        (∀ x, ‖A.tensorEncode H x - A.tensorEncode g.inner x‖ ≤ a/8) →
        D*B*(s/t)^r ≤ min (ρ/4) (a/8) →
        0 ≤ α → (∀ x, ‖A.tensorEncode g.inner x‖ ≤ K) → α*K ≤ a/8 →
        A.WeightedBound 1 2 (ρ/2) (A.smooth r s G-F) ∧
        ∀ x, ‖A.tensorEncode (A.tensorSmooth r s H - α • g.inner) x -
          A.tensorEncode g.inner x‖ ≤ a/2 := by
  obtain ⟨D,hD,htail⟩ := A.smoothed_input_closeness r
  refine ⟨D,hD,?_⟩
  intro g F G H ρ a b B t s α K _hρ ha hB hs hst ht1 hF hG hH hinput
    hnear hb hHnear hsmall hα hK hαK
  obtain ⟨hmap,htensor⟩ := htail G H B t s hB hs hst ht1 hG hH hinput
  have hsmooth := A.smooth_smooth r hs hG
  have hmapneg : A.WeightedBound 1 2 (D*B*(s/t)^r) (A.smooth r s G-G) := by
    have he : A.smooth r s G-G = (-1 : ℝ) • (G-A.smooth r s G) := by
      funext p
      simp only [Pi.sub_apply,Pi.smul_apply,neg_one_smul]
      abel
    rw [he]
    intro i
    rw [localize_smul]
    rw [neg_one_smul]
    have hnegative := (hmap i).neg uniqueDiffOn_univ
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
        (hG.sub hsmooth)).contDiffOn
    convert hnegative using 1
    all_goals try with_reducible_and_instances rfl
  have hsum := A.weightedBound_add (hsmooth.sub hG) (hG.sub hF)
    (show (0 : ℝ) ≤ 1 by norm_num) hmapneg hnear
  change A.WeightedBound 1 2 (D*B*(s/t)^r+b)
    ((A.smooth r s G-G)+(G-F)) at hsum
  have he : (A.smooth r s G-G) + (G-F) = A.smooth r s G-F := by abel
  rw [he] at hsum
  refine ⟨fun i => (hsum i).mono_const (by
    have hsmall' := hsmall.trans (min_le_left _ _)
    linarith),?_⟩
  intro x
  have htail' : ‖A.tensorEncode (A.tensorSmooth r s H) x - A.tensorEncode H x‖ ≤ a/8 := by
    rw [norm_sub_rev]
    exact (htensor x).trans (hsmall.trans (min_le_right _ _))
  have hscalar : ‖α • A.tensorEncode g.inner x‖ ≤ a/8 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hα]
    exact (mul_le_mul_of_nonneg_left (hK x) hα).trans hαK
  rw [A.tensorEncode_sub,A.tensorEncode_smul]
  change ‖(A.tensorEncode (A.tensorSmooth r s H) x - α • A.tensorEncode g.inner x) -
    A.tensorEncode g.inner x‖ ≤ _
  calc
    _ = ‖(A.tensorEncode (A.tensorSmooth r s H) x - A.tensorEncode H x) +
        (A.tensorEncode H x - A.tensorEncode g.inner x) - α • A.tensorEncode g.inner x‖ := by
      congr 1
      abel
    _ ≤ (‖A.tensorEncode (A.tensorSmooth r s H) x - A.tensorEncode H x‖ +
        ‖A.tensorEncode H x - A.tensorEncode g.inner x‖) + ‖α • A.tensorEncode g.inner x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (a/8+a/8)+a/8 := add_le_add (add_le_add htail' (hHnear x)) hscalar
    _ ≤ a/2 := by linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AnchoredActualStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual normalized correction steps with an explicit fast-map neighborhood. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry MetricGoodPhaseData
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredActualFiberNormed
local instance anchoredActualFiberSpace_r430729_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance anchoredActualDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.anchoredActualFiberNormed
local instance anchoredActualFiberSpace_r430729_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance anchoredActualDualSmul_r430729_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance anchoredActualSectionNormed_r430729_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredActualSectionSpace_r430729_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem anchored_actual_step_oai (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D K : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧ 0 ≤ K ∧
    ∀ r : ℕ, ∃ T : ℝ, 0 ≤ T ∧
    ∀ (q : ℕ) (Budget : ℝ → ℝ), HasPolynomialBound Budget →
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, ∃ Dm Em : ℕ → ℝ, 1 ≤ E ∧
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (Q m)) ∧
      (∀ m, 0 ≤ Dm m) ∧ (∀ m, 0 ≤ Em m) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
    ∀ δ δ' t s τ : ℝ, 0 < δ → 0 < δ' → δ' ≤ δ →
      0 < t → t ≤ 1 → 0 < s → s ≤ t → 0 < τ → τ ≤ s → δ ≤ τ →
      τ/s ≤ min 1 ((a-a/2)/(2*(E*(z⁻¹)^e))) →
      A.InputBound t r (Budget z⁻¹) G (normalizedTensorDefect g.inner δ G) →
      A.WeightedBound 1 2 ((z^4/D)/4) (G-F) →
      (∀ x, ‖A.tensorEncode (normalizedTensorDefect g.inner δ G) x-A.tensorEncode g.inner x‖ ≤ a/8) →
      T*(Budget z⁻¹)*(s/t)^r ≤ min ((z^4/D)/4) (a/8) → (δ'/δ)^2*K ≤ a/8 →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
        ∀ m C, 0 ≤ C → A.InputBound t m C G (normalizedTensorDefect g.inner δ G) →
          A.TensorWeightedBound τ m
            (normalizedStepBound r q (Budget z⁻¹) (Dm m) (Em m) (P (m+1) z⁻¹) (Q m z⁻¹) C δ δ' τ s t)
            (normalizedTensorDefect g.inner δ' (G+U)-g.inner) := by
  classical
  obtain ⟨z₀,a,D,hz₀,hz₀1,ha,hD,hall⟩ := A.anchored_smoothed_increment g houter R c B b hc hB hb
  obtain ⟨K,hK,hKb⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain 0 g.contMDiff
  have hKn (x : JetPolynomial.Base) : ‖A.tensorEncode g.inner x‖ ≤ K :=
    (A.tensorEncode_bound g.contMDiff zero_lt_one hK hKb).norm_le (mem_univ x)
  refine ⟨z₀,a,D,K,hz₀,hz₀1,ha,hD,hK,?_⟩
  intro r
  obtain ⟨T,hT,hadmissible⟩ := A.smoothed_input_admissibility r
  refine ⟨T,hT,?_⟩
  intro q Budget hBudget
  obtain ⟨e,E,P,Q,hE,hP,hQ,hbuild⟩ := hall r q Budget hBudget
  choose Dm Em hDm hEm hmetric using fun m => A.smoothed_normalized_metric_step_bound r m
  refine ⟨e,E,P,Q,Dm,Em,hE,hP,hQ,hDm,hEm,?_⟩
  intro z hz hzsmall F hF hFb hFm G hG δ δ' t s τ hδ hδ' hδ'δ ht ht1 hs hst hτ hτs hδτ
    hsmall hinput hnear hHnear htail hratio
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  let H := normalizedTensorDefect g.inner δ G
  have hH := A.normalizedTensorDefect_smooth g.contMDiff δ hG
  have hsym : ∀ y v w, H y v w = H y w v := by
    intro y v w
    change (δ^2)⁻¹*(g.inner y v w-inducedTensor G y v w) =
      (δ^2)⁻¹*(g.inner y w v-inducedTensor G y w v)
    rw [g.symm y v w,inducedTensor_symmetric G y v w]
  have hρ : 0 < z^4/D := div_pos (pow_pos hz 4) (zero_lt_one.trans_le hD)
  have had := hadmissible g F G H (z^4/D) a ((z^4/D)/4) (Budget z⁻¹) t s ((δ'/δ)^2) K
    hρ ha (hBudget.nonneg hx) hs hst ht1 hF hG hH hinput hnear le_rfl hHnear htail
    (sq_nonneg _) hKn hratio
  have hsnear : A.WeightedBound 1 2 (z^4/D) (A.smooth r s G-F) :=
    fun i => (had.1 i).mono_const (by linarith)
  obtain ⟨U,hU,hUB,hUE⟩ := hbuild z hz hzsmall F hF hFb hFm G H hG hH hsym t s ht ht1 hs
    (hst.trans ht1) hinput hsnear δ δ' τ hδ hδ'.le hδ'δ hτ hτs hδτ hsmall had.2
  refine ⟨U,hU,hUB,?_⟩
  intro m C hC hCm
  exact hmetric m g.inner g.contMDiff G U hG hU δ δ' τ s t (Budget z⁻¹) C
    (P (m+1) z⁻¹*(δ*τ)) (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
    hδ.ne' hδ'.ne' hτ hτs hst ht1 (hBudget.nonneg hx) hC
    (mul_nonneg ((hP _).nonneg hx) (mul_nonneg hδ.le hτ.le)) hinput hCm (hUB (m+1)) (hUE m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_actual_step_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_actual_step_oai.{u_1}
