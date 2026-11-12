-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:12:47.712774+00:00
-- url     : https://prove2.me/submissions/b9a2d35a-d667-4df0-9d6b-d66d5f606b7a

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI008

section
-- module Solutions.OAIQ249_SI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
open scoped ContDiff in
/-- Backport (Mathlib d13f23b), with Mathlib's own proof: the iterated derivatives up to order `m` of a
smooth compactly supported function are uniformly bounded (Falconer all dimensions, oaiq-088: 3 modules;
OAIHecke carried its own copy). -/
theorem _root_.HasCompactSupport.exists_bound_iteratedFDeriv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} (hf : HasCompactSupport f) (hf' : ContDiff 𝕜 ∞ f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ i ≤ m, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C := by
  have key i : ∃ C, ∀ y, ‖_root_.iteratedFDeriv 𝕜 i f y‖ ≤ C :=
    (hf'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hf.iteratedFDeriv i)
  choose A hA using key
  refine ⟨max 0 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ A), le_max_left _ _, fun i hi y ↦ ?_⟩
  grw [hA i y, ← le_max_right]
  exact Finset.le_sup' A (by grind)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionDirections
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two affine charts for the tangent directions of a surface, and the
kernel criterion for a linear projection along a graph direction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma tangentRay_ne_zero (b : Bool) (t : ℝ) : tangentRay b t ≠ 0 := by
  cases b <;> intro h
  · have hh := congrFun h 0
    norm_num [tangentRay] at hh
  · have hh := congrFun h 1
    norm_num [tangentRay] at hh

lemma tangentRay_smooth (b : Bool) : ContDiff ℝ ∞ (tangentRay b) := by
  cases b <;> apply contDiff_pi.mpr <;> intro i <;> fin_cases i <;>
    first | exact contDiff_id | exact contDiff_const

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartGermImmersion
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Immersion of a smooth coordinate representative is equivalent to
immersion of the represented surface map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma chart_germ_immersion_iff (p : M) {q : M} (hq : q ∈ (chart p).source)
    {g : M → ProjectionTarget 3} {G : Base → ProjectionTarget 3}
    (hG : ContDiff ℝ ∞ G) (he : g =ᶠ[𝓝 q] G ∘ chart p) :
    Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g q) ↔
      Function.Injective (fderiv ℝ G (chart p q)) := by
  have hGc : ContMDiff 𝓘(ℝ,Base) 𝓘(ℝ,ProjectionTarget 3) ∞ G := hG.contMDiff
  rw [he.mfderiv_eq,mfderiv_comp q (hGc.mdifferentiable (by simp)).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt hq),mfderiv_eq_fderiv]
  change Function.Injective (fderiv ℝ G (chart p q) ∘
    mfderiv planeModel 𝓘(ℝ,Base) (chart p) q) ↔ _
  constructor
  · intro hi
    exact hi.of_comp_right ((chart_mdifferentiable p).mfderiv_surjective hq)
  · intro hi
    exact hi.comp ((chart_mdifferentiable p).mfderiv_injective hq)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionSlopeDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative of a graph-direction coordinate. At a projection kernel
its derivative is exactly the projected derivative divided by the height. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma tangentRay_hasDerivAt (b : Bool) (t : ℝ) :
    HasDerivAt (tangentRay b) (tangentRayVelocity b) t := by
  apply hasDerivAt_pi.mpr
  intro i
  cases b <;> fin_cases i <;>
    first | exact hasDerivAt_id t | exact hasDerivAt_const t _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceDirectionJet
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-direction map of an actual three-dimensional surface,
and its relation to the unweighted projection jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceDirection_smooth {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) : ContDiff ℝ ∞ (surfaceDirection f b) := by
  exact ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp contDiff_fst).clm_apply
    ((tangentRay_smooth b).comp contDiff_snd)

lemma surfaceDirection_hasFDerivAt {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (z : Base × ℝ) :
    HasFDerivAt (surfaceDirection f b) (surfaceDirectionLinearization f b z) z := by
  exact ((((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z.1).hasFDerivAt.comp z
    hasFDerivAt_fst).clm_apply
      ((tangentRay_hasDerivAt b z.2).hasFDerivAt.comp z hasFDerivAt_snd))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FlatSecondJetBounds
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale bounds for a remainder with vanishing value and first derivative.
The second derivative bound tends to zero for a flat second jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma flat_first_derivative_bound {R : Base → ProjectionTarget 3}
    (hR : ContDiff ℝ ∞ R) (hD0 : fderiv ℝ R 0 = 0)
    {r M : ℝ} (hr : 0 ≤ r)
    (hb : ∀ x ∈ Metric.closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M)
    {x : Base} (hx : x ∈ Metric.closedBall (0 : Base) r) :
    ‖fderiv ℝ R x‖ ≤ M*‖x‖ := by
  have hd : ∀ y ∈ Metric.closedBall (0 : Base) r, DifferentiableAt ℝ (fderiv ℝ R) y :=
    fun y _ => (hR.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
  have h := (convex_closedBall (0 : Base) r).norm_image_sub_le_of_norm_fderiv_le
    hd hb (Metric.mem_closedBall_self hr) hx
  simpa only [hD0,sub_zero] using h

lemma flat_value_bound {R : Base → ProjectionTarget 3}
    (hR : ContDiff ℝ ∞ R) (h0 : R 0 = 0) (hD0 : fderiv ℝ R 0 = 0)
    {r M : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Metric.closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M)
    {x : Base} (hx : x ∈ Metric.closedBall (0 : Base) r) :
    ‖R x‖ ≤ M*r*‖x‖ := by
  have hD : ∀ y ∈ Metric.closedBall (0 : Base) r, ‖fderiv ℝ R y‖ ≤ M*r := by
    intro y hy
    apply (flat_first_derivative_bound hR hD0 hr hb hy).trans
    exact mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy) hM
  have h := (convex_closedBall (0 : Base) r).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hR.differentiable (by simp) y) hD (Metric.mem_closedBall_self hr) hx
  simpa only [h0,sub_zero] using h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_FlatJetWeightedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A flat remainder has a scale-weighted second-order bound controlled
only by its second derivative on the coordinate ball. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem flat_remainder_weighted_bound {R : Base → ProjectionTarget 3}
    (hR : ContDiff ℝ ∞ R) (h0 : R 0 = 0) (hD0 : fderiv ℝ R 0 = 0)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ x ∈ Metric.closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M) :
    WeightedEstimates.WeightedBound (Metric.ball (0 : Base) r) r 2 (M*r^2) R := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j isOpen_ball hx]
  have hx' : x ∈ Metric.closedBall (0 : Base) r := Metric.ball_subset_closedBall hx
  have hxr : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx'
  interval_cases j
  · rw [pow_zero,one_mul,norm_iteratedFDeriv_zero]
    apply (flat_value_bound hR h0 hD0 hr.le hM hb hx').trans
    calc
      M*r*‖x‖ ≤ M*r*r := mul_le_mul_of_nonneg_left hxr (mul_nonneg hM hr.le)
      _ = M*r^2 := by ring
  · rw [pow_one,norm_iteratedFDeriv_one]
    have hd := flat_first_derivative_bound hR hD0 hr.le hb hx'
    calc
      r*‖fderiv ℝ R x‖ ≤ r*(M*‖x‖) := mul_le_mul_of_nonneg_left hd hr.le
      _ = M*r*‖x‖ := by ring
      _ ≤ M*r*r := mul_le_mul_of_nonneg_left hxr (mul_nonneg hM hr.le)
      _ = M*r^2 := by ring
  · rw [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one]
    exact (mul_le_mul_of_nonneg_left (hb x hx') (sq_nonneg r)).trans_eq (mul_comm _ _)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ShrinkingJetCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed cutoffs rescaled into smaller coordinate balls, with derivative
bounds measured at their actual radius. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma shrinkingJetCutoff_smooth (r : ℝ) : ContDiff ℝ ∞ (shrinkingJetCutoff r) :=
  flatJetCutoff.contDiff.comp (contDiff_id.const_smul r⁻¹)

lemma shrinkingJetCutoff_germ (r : ℝ) : shrinkingJetCutoff r =ᶠ[𝓝 (0 : Base)] 1 := by
  have hc0 : Continuous (fun x : Base => r⁻¹ • x) := by fun_prop
  have hc : Tendsto (fun x : Base => r⁻¹ • x) (𝓝 0) (𝓝 0) := by
    simpa only [smul_zero] using hc0.continuousAt.tendsto (x := (0 : Base))
  exact flatJetCutoff.eventuallyEq_one.comp_tendsto hc

lemma shrinkingJetCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (shrinkingJetCutoff r) ⊆ closedBall (0 : Base) (r/2) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  have hn' : r/2 < ‖x‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hn
  have hd : flatJetCutoff.rOut ≤ dist (r⁻¹ • x) 0 := by
    change (1/2 : ℝ) ≤ dist (r⁻¹ • x) 0
    rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
    change (1/2 : ℝ) ≤ r⁻¹*‖x‖
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hr).mpr
    linarith
  exact hx (flatJetCutoff.zero_of_le_dist hd)

theorem shrinkingJetCutoff_weighted_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      WeightedEstimates.WeightedBound (ball (0 : Base) r) r 2 C (shrinkingJetCutoff r) := by
  obtain ⟨C,hC,hb⟩ := flatJetCutoff.hasCompactSupport.exists_bound_iteratedFDeriv
    (𝕜 := ℝ) flatJetCutoff.contDiff 2
  refine ⟨C,hC,?_⟩
  intro r hr j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j isOpen_ball hx]
  change r^j*‖iteratedFDeriv ℝ j (fun y : Base => flatJetCutoff (r⁻¹ • y)) x‖ ≤ C
  have hjc : ContDiff ℝ j (flatJetCutoff : Base → ℝ) := flatJetCutoff.contDiff
  rw [congrFun (iteratedFDeriv_comp_const_smul r⁻¹ hjc) x,norm_smul]
  simp only [Real.norm_eq_abs,abs_pow,abs_inv,abs_of_pos hr,inv_pow]
  rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero j (ne_of_gt hr)),one_mul]
  exact hb j hj _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CutoffFlatJetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A shrinking cutoff applied to a flat remainder has a second-order
bound independent of the cutoff radius. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem cutoff_flat_jet_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (R : Base → ProjectionTarget 3), ContDiff ℝ ∞ R → R 0 = 0 →
      fderiv ℝ R 0 = 0 → ∀ r M : ℝ, 0 < r → r ≤ 1 → 0 ≤ M →
      (∀ x ∈ closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M) →
      ∀ j ≤ 2, ∀ x : Base,
        ‖iteratedFDeriv ℝ j (fun y => shrinkingJetCutoff r y • R y) x‖ ≤ C*M := by
  obtain ⟨C,hC,hcut⟩ := shrinkingJetCutoff_weighted_bound
  refine ⟨4*C,by positivity,?_⟩
  intro R hR h0 hD0 r M hr hr1 hM hb j hj x
  let Q : Base → ProjectionTarget 3 := fun y => shrinkingJetCutoff r y • R y
  have hQ : ContDiff ℝ ∞ Q := (shrinkingJetCutoff_smooth r).smul hR
  have hsupp : tsupport Q ⊆ closedBall (0 : Base) (r/2) :=
    (tsupport_smul_subset_left _ _).trans (shrinkingJetCutoff_tsupport hr)
  by_cases hx : x ∈ ball (0 : Base) r
  · have hRbound := flat_remainder_weighted_bound hR h0 hD0 hr hM hb
    have hprod := (hcut r hr).smul_real isOpen_ball.uniqueDiffOn hr.le hC
      (mul_nonneg hM (sq_nonneg r)) (shrinkingJetCutoff_smooth r).contDiffOn
      hR.contDiffOn hRbound
    have h := hprod j hj x hx
    rw [iteratedFDerivWithin_of_isOpen j isOpen_ball hx] at h
    have hpow : r^2 ≤ r^j := pow_le_pow_of_le_one hr.le hr1 hj
    apply (mul_le_mul_iff_right₀ (pow_pos hr j)).mp
    calc
      _ ≤ (2:ℝ)^2*C*(M*r^2) := h
      _ = (4*C*M)*r^2 := by ring
      _ ≤ (4*C*M)*r^j := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  · have hnot : x ∉ tsupport Q := by
      intro hm
      have hsmall := hsupp hm
      apply hx
      rw [mem_ball,dist_zero_right]
      have hnorm : ‖x‖ ≤ r/2 := by simpa only [mem_closedBall,dist_zero_right] using hsmall
      linarith
    have he := ((notMem_tsupport_iff_eventuallyEq.mp hnot).iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ j Q x‖ ≤ _
    rw [he]
    simpa only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero] using mul_nonneg (by positivity : 0 ≤ 4*C) hM

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceQuadraticTaylor
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual second Taylor polynomial of a smooth surface map at the
coordinate origin, including exact vanishing jets of its remainder. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceQuadratic_smooth (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) :
    ContDiff ℝ ∞ (surfaceQuadratic B) :=
  (B.contDiff.clm_apply contDiff_id).const_smul _

lemma surfaceQuadratic_hasFDerivAt (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3)
    (hB : ∀ v w, B v w = B w v) (x : Base) :
    HasFDerivAt (surfaceQuadratic B) (B x) x := by
  have hd := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)).const_smul (1/2 : ℝ)
  change HasFDerivAt (surfaceQuadratic B) _ x at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  change B x v = (1/2 : ℝ) • (B x v+B v x)
  rw [hB v x]
  module

lemma surfaceTaylorTwo_smooth (f : Base → ProjectionTarget 3) :
    ContDiff ℝ ∞ (surfaceTaylorTwo f) :=
  (contDiff_const.add (fderiv ℝ f 0).contDiff).add (surfaceQuadratic_smooth _)

lemma surfaceTaylorTwo_fderiv {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (x : Base) :
    fderiv ℝ (surfaceTaylorTwo f) x = fderiv ℝ f 0+fderiv ℝ (fderiv ℝ f) 0 x := by
  have hB : ∀ v w, fderiv ℝ (fderiv ℝ f) 0 v w = fderiv ℝ (fderiv ℝ f) 0 w v :=
    fun v w => hf.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) v w
  have hd := ((fderiv ℝ f 0).hasFDerivAt.const_add (f 0)).add
    (surfaceQuadratic_hasFDerivAt _ hB x)
  exact hd.fderiv

lemma surfaceTaylorTwo_second {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (x : Base) :
    fderiv ℝ (fderiv ℝ (surfaceTaylorTwo f)) x = fderiv ℝ (fderiv ℝ f) 0 := by
  have he : fderiv ℝ (surfaceTaylorTwo f) =
      fun y => fderiv ℝ f 0+fderiv ℝ (fderiv ℝ f) 0 y := funext (surfaceTaylorTwo_fderiv hf)
  rw [he]
  exact ((fderiv ℝ (fderiv ℝ f) 0).hasFDerivAt.const_add (fderiv ℝ f 0)).fderiv

lemma surfaceTaylorTwo_remainder_jets {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) :
    (f-surfaceTaylorTwo f) 0 = 0 ∧ fderiv ℝ (f-surfaceTaylorTwo f) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (f-surfaceTaylorTwo f)) 0 = 0 := by
  have hT := surfaceTaylorTwo_smooth f
  have hfirst : fderiv ℝ (f-surfaceTaylorTwo f) =
      fderiv ℝ f-fderiv ℝ (surfaceTaylorTwo f) := by
    funext x
    exact fderiv_sub (hf.differentiable (by simp) x) (hT.differentiable (by simp) x)
  refine ⟨?_,?_,?_⟩
  · simp [surfaceTaylorTwo,surfaceQuadratic]
  · rw [hfirst]
    simp [surfaceTaylorTwo_fderiv hf]
  · rw [hfirst,fderiv_sub
      ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) 0)
      ((hT.fderiv_right (m := ∞) (by simp)).differentiable (by simp) 0),
      surfaceTaylorTwo_second hf,sub_self]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalQuadraticReplacement
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth surface map can be made equal to its actual quadratic jet
near the origin by an arbitrarily small supported C2 change. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.firstJetNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.firstJetSpace
local instance secondJetNormed_r7b12c0_1 : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) := inferInstance
local instance secondJetSpace_r7b12c0_1 : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) := inferInstance
theorem exists_local_quadratic_replacement {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ g : Base → ProjectionTarget 3, ContDiff ℝ ∞ g ∧
      g =ᶠ[𝓝 (0 : Base)] surfaceTaylorTwo f ∧
      (∀ x, ρ ≤ ‖x‖ → g x = f x) ∧
      tsupport (g-f) ⊆ closedBall (0 : Base) (ρ/2) ∧
      ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (g-f) x‖ ≤ ε := by
  obtain ⟨C,hC,hbound⟩ := cutoff_flat_jet_bound
  let R := f-surfaceTaylorTwo f
  have hR : ContDiff ℝ ∞ R := hf.sub (surfaceTaylorTwo_smooth f)
  obtain ⟨h0,hD0,hD20⟩ := surfaceTaylorTwo_remainder_jets hf
  let M := ε/(C+1)
  have hM : 0 < M := by dsimp [M] <;> positivity
  have hCM : C*M ≤ ε := by
    dsimp [M]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hc : ContinuousAt (fderiv ℝ (fderiv ℝ R)) 0 :=
    ((hR.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
  have hevent : ∀ᶠ x in 𝓝 (0 : Base), ‖fderiv ℝ (fderiv ℝ R) x‖ < M := by
    change fderiv ℝ (fderiv ℝ R) 0 = 0 at hD20
    have hn : ‖fderiv ℝ (fderiv ℝ R) 0‖ < M := by simpa only [hD20,norm_zero] using hM
    exact hc.norm.eventually (isOpen_Iio.mem_nhds hn)
  obtain ⟨η,hη,hηbound⟩ := Metric.eventually_nhds_iff.mp hevent
  let r := min ρ (min 1 (η/2))
  have hr : 0 < r := lt_min hρ (lt_min zero_lt_one (half_pos hη))
  have hrρ : r ≤ ρ := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrη : r < η := by
    have h := (min_le_right ρ (min 1 (η/2))).trans (min_le_right 1 (η/2))
    linarith
  have hsecond : ∀ x ∈ closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M := by
    intro x hx
    exact (hηbound ((mem_closedBall.mp hx).trans_lt hrη)).le
  let Q : Base → ProjectionTarget 3 := fun x => shrinkingJetCutoff r x • R x
  have hQ : ContDiff ℝ ∞ Q := (shrinkingJetCutoff_smooth r).smul hR
  have hqbound := hbound R hR h0 hD0 r M hr hr1 hM.le hsecond
  let g := f-Q
  refine ⟨g,hf.sub hQ,?_,?_,?_,?_⟩
  · filter_upwards [shrinkingJetCutoff_germ r] with x hx
    change f x-shrinkingJetCutoff r x • (f x-surfaceTaylorTwo f x) = surfaceTaylorTwo f x
    rw [hx]
    change f x-(1 : ℝ) • (f x-surfaceTaylorTwo f x) = surfaceTaylorTwo f x
    rw [one_smul]
    abel
  · intro x hx
    have hnot : x ∉ tsupport (shrinkingJetCutoff r) := by
      intro hs
      have hm := shrinkingJetCutoff_tsupport hr hs
      have hl : ‖x‖ ≤ r/2 := by simpa only [mem_closedBall,dist_zero_right] using hm
      linarith
    change f x-shrinkingJetCutoff r x • R x = f x
    rw [image_eq_zero_of_notMem_tsupport hnot,zero_smul,sub_zero]
  · have he : g-f = -Q := by
      funext y
      change (f y-Q y)-f y = -Q y
      abel
    rw [he,tsupport_neg]
    exact ((tsupport_smul_subset_left _ _).trans (shrinkingJetCutoff_tsupport hr)).trans
      (closedBall_subset_closedBall (div_le_div_of_nonneg_right hrρ (by norm_num)))
  · intro j hj x
    have he : g-f = -Q := by
      funext y
      change (f y-Q y)-f y = -Q y
      abel
    rw [he,iteratedFDeriv_neg_apply,norm_neg]
    exact (hqbound j hj x).trans hCM

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceC2Difference
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Converting the global second-order norm estimate into the two actual
derivative estimates used by the crosscap direction map. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surface_second_derivative_sub {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Base) :
    fderiv ℝ (fderiv ℝ (g-f)) x =
      fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ f) x := by
  have he : fderiv ℝ (g-f) = fderiv ℝ g-fderiv ℝ f := by
    funext y
    exact fderiv_sub (hg.differentiable (by simp) y) (hf.differentiable (by simp) y)
  rw [he]
  exact fderiv_sub ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)

lemma surface_C2_difference {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {ε : ℝ}
    (hbound : ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (g-f) x‖ ≤ ε) (x : Base) :
    ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ f) x‖ ≤ ε := by
  constructor
  · have h := hbound 1 (by decide) x
    rwa [norm_iteratedFDeriv_one,fderiv_sub (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)
      (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)] at h
  · have h := hbound 2 (by decide) x
    rwa [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one,
      surface_second_derivative_sub hf hg] at h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapLinearStability
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform local injectivity estimate for a nondegenerate direction map.
It will allow the quadratic jet to replace the original map near a crosscap. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

local instance instContinuousSMulRealProdBase_r7b12c0_1 : ContinuousSMul ℝ (Base × ℝ) := Prod.continuousSMul
lemma near_equiv_derivative_injOn (L : (Base × ℝ) ≃L[ℝ] ProjectionTarget 3)
    {g : Base × ℝ → ProjectionTarget 3} {S : Set (Base × ℝ)}
    (hg : ∀ x ∈ S, DifferentiableAt ℝ g x) (hS : Convex ℝ S)
    {c : ℝ} (_hc : 0 ≤ c) (hsmall : ‖L.symm.toContinuousLinearMap‖*c < 1)
    (hbound : ∀ x ∈ S, ‖fderiv ℝ g x-L.toContinuousLinearMap‖ ≤ c) :
    S.InjOn g := by
  intro x hx y hy heq
  have hd : ∀ z ∈ S, DifferentiableAt ℝ (fun z => g z-L z) z :=
    fun z hz => (hg z hz).sub L.differentiableAt
  have hb : ∀ z ∈ S, ‖fderiv ℝ (fun z => g z-L z) z‖ ≤ c := by
    intro z hz
    rw [fderiv_fun_sub (hg z hz) L.differentiableAt,L.fderiv]
    exact hbound z hz
  have herr := hS.norm_image_sub_le_of_norm_fderiv_le hd hb hx hy
  have hL : ‖L (y-x)‖ ≤ c*‖y-x‖ := by
    have he : (g y-L y)-(g x-L x) = -L (y-x) := by
      rw [← heq,map_sub]
      abel
    rw [he,norm_neg] at herr
    exact herr
  have hback : ‖y-x‖ ≤ ‖L.symm.toContinuousLinearMap‖*‖L (y-x)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe,L.symm_apply_apply] using
      L.symm.toContinuousLinearMap.le_opNorm (L (y-x))
  have hn : ‖y-x‖ = 0 := by
    have hh := hback.trans (mul_le_mul_of_nonneg_left hL (norm_nonneg _))
    nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem local_linearization_stability_on
    {f : Base × ℝ → ProjectionTarget 3} (hf : ContDiff ℝ ∞ f) (z : Base × ℝ)
    (hreg : Function.Bijective (fderiv ℝ f z)) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧
      ∀ S : Set (Base × ℝ), Convex ℝ S → S ⊆ Metric.ball z r →
      ∀ g : Base × ℝ → ProjectionTarget 3, ContDiff ℝ ∞ g →
        (∀ x ∈ S, ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ ε) → S.InjOn g := by
  let L := ContinuousLinearEquiv.ofBijective (fderiv ℝ f z)
    (LinearMap.ker_eq_bot.mpr hreg.1) (LinearMap.range_eq_top.mpr hreg.2)
  let c := (2*(‖L.symm.toContinuousLinearMap‖+1))⁻¹
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hsmall : ‖L.symm.toContinuousLinearMap‖*c < 1 := by
    dsimp [c]
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith [norm_nonneg L.symm.toContinuousLinearMap]
  have hcont : ContinuousAt (fderiv ℝ f) z := (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
  have hevent : ∀ᶠ x in 𝓝 z, ‖fderiv ℝ f x-fderiv ℝ f z‖ < c/2 := by
    simpa only [Metric.mem_ball,dist_eq_norm] using
      hcont.eventually (Metric.ball_mem_nhds _ (half_pos hc))
  obtain ⟨r,hr,hclose⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r,c/2,hr,half_pos hc,?_⟩
  intro S hS hsub g hg hnear
  apply near_equiv_derivative_injOn L
    (fun x _ => hg.differentiable (by simp) x) hS hc.le hsmall
  intro x hx
  have hx' : dist x z < r := hsub hx
  change ‖fderiv ℝ g x-fderiv ℝ f z‖ ≤ c
  calc
    _ ≤ ‖fderiv ℝ g x-fderiv ℝ f x‖+‖fderiv ℝ f x-fderiv ℝ f z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ c/2+c/2 := add_le_add (hnear x hx) (hclose hx').le
    _ = c := by ring


end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceDirectionEstimates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second-jet control of the actual surface controls the first derivative
of its direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceDirectionLinearization_sub_apply (f g : Base → ProjectionTarget 3)
    (b : Bool) (z w : Base × ℝ) :
    (surfaceDirectionLinearization g b z-surfaceDirectionLinearization f b z) w =
      w.2 • ((fderiv ℝ g z.1-fderiv ℝ f z.1) (tangentRayVelocity b)) +
      (fderiv ℝ (fderiv ℝ g) z.1-fderiv ℝ (fderiv ℝ f) z.1) w.1 (tangentRay b z.2) := by
  change (fderiv ℝ g z.1 (w.2 • tangentRayVelocity b) +
    fderiv ℝ (fderiv ℝ g) z.1 w.1 (tangentRay b z.2)) -
      (fderiv ℝ f z.1 (w.2 • tangentRayVelocity b) +
        fderiv ℝ (fderiv ℝ f) z.1 w.1 (tangentRay b z.2)) = _
  simp only [sub_apply,smul_sub,map_smul]
  abel

lemma norm_surfaceJet_operator
    (A : Base →L[ℝ] ProjectionTarget 3)
    (B : Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) (u v : Base)
    (L : Base × ℝ →L[ℝ] ProjectionTarget 3)
    (hL : ∀ w : Base × ℝ, L w = w.2 • A v+B w.1 u) :
    ‖L‖ ≤ ‖A‖*‖v‖+‖B‖*‖u‖ := by
  apply L.opNorm_le_bound (by positivity)
  intro w
  rw [hL]
  have hb : ‖B w.1 u‖ ≤ ‖B‖*‖w.1‖*‖u‖ := by
    calc
      _ ≤ ‖B w.1‖*‖u‖ := (B w.1).le_opNorm _
      _ ≤ (‖B‖*‖w.1‖)*‖u‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
  calc
    _ ≤ ‖w.2 • A v‖+‖B w.1 u‖ := norm_add_le _ _
    _ ≤ ‖w.2‖*(‖A‖*‖v‖)+‖B‖*‖w.1‖*‖u‖ := by
      rw [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)) hb
    _ ≤ ‖w‖*(‖A‖*‖v‖)+‖B‖*‖w‖*‖u‖ := by
      gcongr
      · exact norm_snd_le w
      · exact norm_fst_le w
    _ = _ := by ring

lemma norm_surfaceDirection_fderiv_sub {f g : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (b : Bool) (z : Base × ℝ) :
    ‖fderiv ℝ (surfaceDirection g b) z-fderiv ℝ (surfaceDirection f b) z‖ ≤
      ‖fderiv ℝ g z.1-fderiv ℝ f z.1‖*‖tangentRayVelocity b‖ +
      ‖fderiv ℝ (fderiv ℝ g) z.1-fderiv ℝ (fderiv ℝ f) z.1‖*‖tangentRay b z.2‖ := by
  have hdg := (surfaceDirection_hasFDerivAt hg b z).fderiv
  have hdf := (surfaceDirection_hasFDerivAt hf b z).fderiv
  rw [hdg,hdf]
  exact norm_surfaceJet_operator _ _ _ _ _
    (surfaceDirectionLinearization_sub_apply f g b z)

lemma tangentRay_norm_le (b : Bool) (t : ℝ) : ‖tangentRay b t‖ ≤ |t|+1 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  cases b <;> fin_cases i <;> simp [tangentRay]

lemma tangentRayVelocity_norm (b : Bool) : ‖tangentRayVelocity b‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    cases b <;> fin_cases i <;> simp [tangentRayVelocity]
  · cases b
    · simpa [tangentRayVelocity] using
        (norm_le_pi_norm (tangentRayVelocity false) (1 : Fin 2))
    · simpa [tangentRayVelocity] using
        (norm_le_pi_norm (tangentRayVelocity true) (0 : Fin 2))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapJetStability
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nondegenerate crosscap direction remains the only zero in a fixed
neighborhood after a sufficiently small second-jet change fixing its first jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem crosscap_jet_stability {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (z : Base × ℝ)
    (hzero : surfaceDirection f b z = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) z)) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ g : Base → ProjectionTarget 3, ContDiff ℝ ∞ g →
        fderiv ℝ g z.1 = fderiv ℝ f z.1 →
        (∀ x ∈ Metric.ball z.1 r,
          ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ δ ∧
          ‖fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ f) x‖ ≤ δ) →
        ∀ w ∈ Metric.ball z r, surfaceDirection g b w = 0 ↔ w = z := by
  obtain ⟨r₀,ε,hr₀,hε,hstable⟩ :=
    local_linearization_stability_on (surfaceDirection_smooth hf b) z hreg
  let r := min r₀ 1
  let δ := ε/(|z.2|+3)
  have hr : 0 < r := lt_min hr₀ zero_lt_one
  have hδ : 0 < δ := by dsimp [δ] <;> positivity
  refine ⟨r,δ,hr,hδ,?_⟩
  intro g hg hfix hnear
  have hzeroG : surfaceDirection g b z = 0 := by
    simpa only [surfaceDirection,hfix] using hzero
  have hclose : ∀ w ∈ Metric.ball z r,
      ‖fderiv ℝ (surfaceDirection g b) w-fderiv ℝ (surfaceDirection f b) w‖ ≤ ε := by
    intro w hw
    have hw' : ‖w-z‖ < r := by simpa only [Metric.mem_ball,dist_eq_norm] using hw
    have hwbase : w.1 ∈ Metric.ball z.1 r := by
      rw [Metric.mem_ball,dist_eq_norm]
      exact (norm_fst_le (w-z)).trans_lt hw'
    have hθ : |w.2| ≤ |z.2|+1 := by
      have hd : |w.2-z.2| ≤ 1 := by
        have hh := (norm_snd_le (w-z)).trans hw'.le
        change |w.2-z.2| ≤ r at hh
        exact hh.trans (min_le_right _ _)
      calc
        _ ≤ |w.2-z.2|+|z.2| := by simpa using abs_add_le (w.2-z.2) z.2
        _ ≤ |z.2|+1 := by linarith
    obtain ⟨h₁,h₂⟩ := hnear w.1 hwbase
    calc
      _ ≤ ‖fderiv ℝ g w.1-fderiv ℝ f w.1‖*‖tangentRayVelocity b‖ +
          ‖fderiv ℝ (fderiv ℝ g) w.1-fderiv ℝ (fderiv ℝ f) w.1‖*‖tangentRay b w.2‖ :=
        norm_surfaceDirection_fderiv_sub hf hg b w
      _ ≤ δ*1+δ*(|z.2|+2) := by
        rw [tangentRayVelocity_norm]
        gcongr
        exact (tangentRay_norm_le b w.2).trans (by linarith)
      _ = ε := by dsimp [δ]; field_simp <;> ring
  have hinj : (Metric.ball z r).InjOn (surfaceDirection g b) := by
    exact hstable _ (convex_ball z r) (Metric.ball_subset_ball (min_le_left _ _))
      _ (surfaceDirection_smooth hg b) hclose
  intro w hw
  constructor
  · intro h
    exact hinj hw (Metric.mem_ball_self hr) (h.trans hzeroG.symm)
  · rintro rfl
    exact hzeroG

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapKernelCapture
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A kernel near a crosscap is captured in the same affine direction
chart, with an explicit bound on its direction parameter. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma tangentRay_sub (b : Bool) (s t : ℝ) :
    tangentRay b s-tangentRay b t = (s-t) • tangentRayVelocity b := by
  cases b <;> ext i <;> fin_cases i <;> simp [tangentRay,tangentRayVelocity]

lemma exists_fixed_tangentRay_kernel (L : Base →L[ℝ] ProjectionTarget 3)
    (b : Bool) (hL : ¬ Function.Injective L) (hv : L (tangentRayVelocity b) ≠ 0) :
    ∃ t : ℝ, L (tangentRay b t) = 0 := by
  change ¬ (∀ u v : Base, L u = L v → u = v) at hL
  push Not at hL
  obtain ⟨u,v,he,hne⟩ := hL
  have hn : u-v ≠ 0 := sub_ne_zero.mpr hne
  have hz : L (u-v) = 0 := by rw [map_sub,he,sub_self]
  let w := u-v
  have hw : w ≠ 0 := hn
  change L w = 0 at hz
  cases b
  · have h0 : w 0 ≠ 0 := by
      intro h0
      have hew : w = w 1 • tangentRayVelocity false := by
        ext i
        fin_cases i <;> simp [tangentRayVelocity,h0]
      rw [hew,map_smul] at hz
      have h1 := (smul_eq_zero.mp hz).resolve_right hv
      apply hw
      ext i
      fin_cases i <;> simp [h0,h1]
    refine ⟨w 1/w 0,?_⟩
    have hew : w = w 0 • tangentRay false (w 1/w 0) := by
      ext i
      fin_cases i
      · simp [tangentRay]
      · change w 1 = w 0*(w 1/w 0)
        field_simp
    rw [hew,map_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left h0
  · have h1 : w 1 ≠ 0 := by
      intro h1
      have hew : w = w 0 • tangentRayVelocity true := by
        ext i
        fin_cases i <;> simp [tangentRayVelocity,h1]
      rw [hew,map_smul] at hz
      have h0 := (smul_eq_zero.mp hz).resolve_right hv
      apply hw
      ext i
      fin_cases i <;> simp [h0,h1]
    refine ⟨w 0/w 1,?_⟩
    have hew : w = w 1 • tangentRay true (w 0/w 1) := by
      ext i
      fin_cases i
      · change w 0 = w 1*(w 0/w 1)
        field_simp
      · simp [tangentRay]
    rw [hew,map_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left h1

lemma exists_near_tangentRay_kernel (L : Base →L[ℝ] ProjectionTarget 3)
    (b : Bool) (t₀ η : ℝ) (hL : ¬ Function.Injective L)
    (hv : L (tangentRayVelocity b) ≠ 0)
    (hsmall : ‖L (tangentRay b t₀)‖ < η*‖L (tangentRayVelocity b)‖) :
    ∃ t : ℝ, |t-t₀| < η ∧ L (tangentRay b t) = 0 := by
  obtain ⟨t,ht⟩ := exists_fixed_tangentRay_kernel L b hL hv
  refine ⟨t,?_,ht⟩
  have he : L (tangentRay b t₀) = (t₀-t) • L (tangentRayVelocity b) := by
    calc
      _ = L (tangentRay b t₀)-L (tangentRay b t) := by rw [ht,sub_zero]
      _ = L (tangentRay b t₀-tangentRay b t) := (map_sub L _ _).symm
      _ = _ := by rw [tangentRay_sub,map_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_sub_comm] at hsmall
  exact (mul_lt_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp hsmall

theorem kernel_capture_near (L : Base →L[ℝ] ProjectionTarget 3)
    (b : Bool) (t₀ : ℝ) (hzero : L (tangentRay b t₀) = 0)
    (hv : L (tangentRayVelocity b) ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : Base →L[ℝ] ProjectionTarget 3,
      ‖H-L‖ < δ → ¬ Function.Injective H →
      ∃ t : ℝ, |t-t₀| < η ∧ H (tangentRay b t) = 0 := by
  let U := {H : Base →L[ℝ] ProjectionTarget 3 |
    ‖H (tangentRay b t₀)‖ < η*‖H (tangentRayVelocity b)‖}
  have hU : IsOpen U := isOpen_lt
    (ContinuousLinearMap.apply ℝ (ProjectionTarget 3) (tangentRay b t₀)).continuous.norm
    (continuous_const.mul
      (ContinuousLinearMap.apply ℝ (ProjectionTarget 3) (tangentRayVelocity b)).continuous.norm)
  have hL : L ∈ U := by
    change ‖L (tangentRay b t₀)‖ < η*‖L (tangentRayVelocity b)‖
    rw [hzero,norm_zero]
    exact mul_pos hη (norm_pos_iff.mpr hv)
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hL)
  refine ⟨δ,hδ,?_⟩
  intro H hnear hH
  have hHU : H ∈ U := hδU (by simpa only [mem_ball,dist_eq_norm] using hnear)
  have hHv : H (tangentRayVelocity b) ≠ 0 := by
    intro hn
    change ‖H (tangentRay b t₀)‖ < η*‖H (tangentRayVelocity b)‖ at hHU
    rw [hn,norm_zero,mul_zero] at hHU
    exact (not_lt_of_ge (norm_nonneg _)) hHU
  exact exists_near_tangentRay_kernel H b t₀ η hH hHv hHU

lemma crosscap_transverse_derivative_ne_zero {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (z : Base × ℝ)
    (hreg : Function.Injective (fderiv ℝ (surfaceDirection f b) z)) :
    fderiv ℝ f z.1 (tangentRayVelocity b) ≠ 0 := by
  intro hn
  rw [(surfaceDirection_hasFDerivAt hf b z).fderiv] at hreg
  have hval : surfaceDirectionLinearization f b z ((0 : Base),1) = 0 := by
    change fderiv ℝ f z.1 ((1:ℝ) • tangentRayVelocity b)+
      fderiv ℝ (fderiv ℝ f) z.1 0 (tangentRay b z.2) = 0
    simp [hn]
  have he := hreg (hval.trans (map_zero _).symm)
  have hh := congrArg Prod.snd he
  exact one_ne_zero hh

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticCrosscapPreparation
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacing an actual nondegenerate crosscap by its quadratic jet on a
smaller neighborhood, while creating no further singularities. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem quadratic_crosscap_preparation {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (t₀ : ℝ)
    (hzero : surfaceDirection f b (0,t₀) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (0,t₀)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (r : ℝ) (g : Base → ProjectionTarget 3), 0 < r ∧ r ≤ ρ ∧
      ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 (0 : Base)] surfaceTaylorTwo f ∧
      (∀ x, r ≤ ‖x‖ → g x = f x) ∧
      tsupport (g-f) ⊆ closedBall (0 : Base) (r/2) ∧
      ∀ x ∈ ball (0 : Base) r, (¬ Function.Injective (fderiv ℝ g x) ↔ x = 0) := by
  obtain ⟨r₀,δ₀,hr₀,hδ₀,hstable⟩ := crosscap_jet_stability hf b (0,t₀) hzero hreg
  have hv := crosscap_transverse_derivative_ne_zero hf b (0,t₀) hreg.1
  obtain ⟨δ₁,hδ₁,hcapture⟩ := kernel_capture_near (fderiv ℝ f 0) b t₀ hzero hv (half_pos hr₀)
  have hc : ContinuousAt (fderiv ℝ f) 0 := (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt
  have hevent : ∀ᶠ x in 𝓝 (0 : Base), ‖fderiv ℝ f x-fderiv ℝ f 0‖ < δ₁/2 := by
    simpa only [mem_ball,dist_eq_norm] using hc.eventually (ball_mem_nhds _ (half_pos hδ₁))
  obtain ⟨η,hη,hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let r := min ρ (min η (r₀/2))
  have hr : 0 < r := lt_min hρ (lt_min hη (half_pos hr₀))
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₀ : r ≤ r₀/2 := (min_le_right _ _).trans (min_le_right _ _)
  let ε := min δ₀ (δ₁/4)
  have hε : 0 < ε := lt_min hδ₀ (by positivity)
  obtain ⟨g,hg,hgerm,houtside,hsupport,hC2⟩ := exists_local_quadratic_replacement hf hε hr
  have hfix : fderiv ℝ g 0 = fderiv ℝ f 0 := by
    rw [hgerm.fderiv_eq,surfaceTaylorTwo_fderiv hf]
    simp
  have hest := surface_C2_difference hf hg hC2
  have hnear' : ∀ x ∈ ball (0 : Base) r₀,
      ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ δ₀ ∧
      ‖fderiv ℝ (fderiv ℝ g) x-fderiv ℝ (fderiv ℝ f) x‖ ≤ δ₀ := by
    intro x _
    exact ⟨(hest x).1.trans (min_le_left _ _),(hest x).2.trans (min_le_left _ _)⟩
  have hisolated := hstable g hg hfix hnear'
  refine ⟨r,g,hr,min_le_left _ _,hg,hgerm,houtside,hsupport,?_⟩
  intro x hx
  constructor
  · intro hbad
    have hxη : dist x 0 < η := (mem_ball.mp hx).trans_le hrη
    have hclose : ‖fderiv ℝ g x-fderiv ℝ f 0‖ < δ₁ := by
      calc
        _ ≤ ‖fderiv ℝ g x-fderiv ℝ f x‖+‖fderiv ℝ f x-fderiv ℝ f 0‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < ε+δ₁/2 := add_lt_add_of_le_of_lt (hest x).1 (hnear hxη)
        _ < δ₁ := by have he := min_le_right δ₀ (δ₁/4); dsimp [ε] <;> linarith
    obtain ⟨t,ht,hker⟩ := hcapture (fderiv ℝ g x) hclose hbad
    have hball : (x,t) ∈ ball ((0 : Base),t₀) r₀ := by
      rw [mem_ball,dist_eq_norm,Prod.norm_def]
      apply max_lt
      · have hn : ‖x‖ < r₀/2 := by simpa only [dist_zero_right] using (mem_ball.mp hx).trans_le hrr₀
        simp only [Prod.fst_sub,sub_zero]
        linarith
      · change |t-t₀| < r₀
        linarith
    exact congrArg Prod.fst ((hisolated (x,t) hball).mp hker)
  · rintro rfl hI
    have hz : fderiv ℝ g 0 (tangentRay b t₀) = fderiv ℝ g 0 0 := by
      rw [hfix,map_zero]
      exact hzero
    exact tangentRay_ne_zero b t₀ (hI hz)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CenteredCrosscapPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local polynomial preparation centered at the actual chart
coordinate of a singular point. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceDirection_translated (f : Base → ProjectionTarget 3) (a : Base)
    (b : Bool) (z : Base × ℝ) :
    surfaceDirection (translatedSurface f a) b z = surfaceDirection f b (z+(a,0)) := by
  unfold surfaceDirection translatedSurface
  rw [fderiv_comp_add_right]
  simp only [Prod.fst_add,Prod.snd_add,add_zero]

lemma surfaceDirection_translated_fderiv (f : Base → ProjectionTarget 3) (a : Base)
    (b : Bool) (z : Base × ℝ) :
    fderiv ℝ (surfaceDirection (translatedSurface f a) b) z =
      fderiv ℝ (surfaceDirection f b) (z+(a,0)) := by
  have he : surfaceDirection (translatedSurface f a) b =
      fun w => surfaceDirection f b (w+(a,0)) := funext (surfaceDirection_translated f a b)
  rw [he,fderiv_comp_add_right]

theorem centered_quadratic_crosscap_preparation {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (a : Base) (t₀ : ℝ)
    (hzero : surfaceDirection f b (a,t₀) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t₀)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (r : ℝ) (g : Base → ProjectionTarget 3), 0 < r ∧ r ≤ ρ ∧
      ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] centeredSurfaceTaylor f a ∧
      (∀ x, r ≤ ‖x-a‖ → g x = f x) ∧
      tsupport (g-f) ⊆ closedBall a (r/2) ∧
      ∀ x ∈ ball a r, (¬ Function.Injective (fderiv ℝ g x) ↔ x = a) := by
  have htrans : ContDiff ℝ ∞ (translatedSurface f a) := hf.comp (contDiff_id.add contDiff_const)
  have hzero' : surfaceDirection (translatedSurface f a) b (0,t₀) = 0 := by
    simpa only [surfaceDirection_translated,Prod.mk_add_mk,zero_add,add_zero] using hzero
  have hreg' : Function.Bijective (fderiv ℝ (surfaceDirection (translatedSurface f a) b) (0,t₀)) := by
    simpa only [surfaceDirection_translated_fderiv,Prod.mk_add_mk,zero_add,add_zero] using hreg
  obtain ⟨r,g,hr,hrρ,hg,he,hout,hsupp,hlocal⟩ :=
    quadratic_crosscap_preparation htrans b t₀ hzero' hreg' hρ
  refine ⟨r,(fun x => g (x-a)),hr,hrρ,hg.comp (contDiff_id.sub contDiff_const),?_,?_,?_,?_⟩
  · have ht : Tendsto (fun x : Base => x-a) (𝓝 a) (𝓝 0) := by
        have hc : Continuous (fun x : Base => x-a) := by fun_prop
        simpa only [sub_self] using hc.tendsto a
    exact he.comp_tendsto ht
  · intro x hx
    have h := hout (x-a) hx
    simpa only [translatedSurface,sub_add_cancel] using h
  · apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    have hnot : x-a ∉ tsupport (g-translatedSurface f a) := by
      intro hm
      apply hn
      simpa only [mem_closedBall,dist_eq_norm,sub_zero] using hsupp hm
    have hz := image_eq_zero_of_notMem_tsupport hnot
    change g (x-a)-translatedSurface f a (x-a) = 0 at hz
    have hx' : g (x-a)-f x ≠ 0 := hx
    exact hx' (by simpa only [translatedSurface,sub_add_cancel] using hz)
  · intro x hx
    rw [fderiv_comp_sub]
    have h := hlocal (x-a) (by simpa only [mem_ball,dist_eq_norm,sub_zero] using hx)
    exact h.trans sub_eq_zero

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CenteredTaylorJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered Taylor preparation retains the complete second jet, hence
also the actual regular zero of the derivative-direction map. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma centeredSurfaceTaylor_smooth (f : Base → ProjectionTarget 3) (a : Base) :
    ContDiff ℝ ∞ (centeredSurfaceTaylor f a) :=
  (surfaceTaylorTwo_smooth _).comp (contDiff_id.sub contDiff_const)

lemma centeredSurfaceTaylor_fderiv {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a x : Base) :
    fderiv ℝ (centeredSurfaceTaylor f a) x =
      fderiv ℝ f a + fderiv ℝ (fderiv ℝ f) a (x-a) := by
  have htrans : ContDiff ℝ ∞ (translatedSurface f a) := hf.comp (contDiff_id.add contDiff_const)
  change fderiv ℝ (fun y => surfaceTaylorTwo (translatedSurface f a) (y-a)) x = _
  rw [fderiv_comp_sub,surfaceTaylorTwo_fderiv htrans]
  have hfirst : fderiv ℝ (translatedSurface f a) = fun y => fderiv ℝ f (y+a) := by
    funext y
    exact fderiv_comp_add_right a
  rw [hfirst,fderiv_comp_add_right]
  simp only [zero_add]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapKernelLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit coordinates for the kernel line of a regular crosscap. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma kernel_eq_tangentRay_line (L : Base →L[ℝ] ProjectionTarget 3)
    (b : Bool) (t : ℝ) (hz : L (tangentRay b t) = 0)
    (hv : L (tangentRayVelocity b) ≠ 0) (x : Base) :
    L x = 0 ↔ x = tangentRayCoefficient b x • tangentRay b t := by
  constructor
  · intro hx
    have h := congrArg L (tangentRay_decomposition b t x)
    simp only [hx,map_add,map_smul,hz,smul_zero,add_zero] at h
    have ht : tangentTransverseCoefficient b t x = 0 :=
      (smul_eq_zero.mp h.symm).resolve_right hv
    simpa only [ht,zero_smul,zero_add] using tangentRay_decomposition b t x
  · intro hx
    rw [hx,map_smul,hz,smul_zero]

lemma crosscap_kernel_line {f : Base → ProjectionTarget 3} (hf : ContDiff ℝ ∞ f)
    (b : Bool) (z : Base × ℝ) (hz : surfaceDirection f b z = 0)
    (hreg : Function.Injective (fderiv ℝ (surfaceDirection f b) z)) (x : Base) :
    fderiv ℝ f z.1 x = 0 ↔ x = tangentRayCoefficient b x • tangentRay b z.2 :=
  kernel_eq_tangentRay_line _ b z.2 hz (crosscap_transverse_derivative_ne_zero hf b z hreg) x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticDoublePoints
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Double points of a quadratic crosscap have a singular midpoint. In a
neighborhood with one singular point their two preimages are reflections
through that point. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceTaylorTwo_midpoint_identity {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (x y : Base) :
    fderiv ℝ (surfaceTaylorTwo f) ((1/2 : ℝ) • (x+y)) (x-y) =
      surfaceTaylorTwo f x-surfaceTaylorTwo f y := by
  have hB : ∀ v w, fderiv ℝ (fderiv ℝ f) 0 v w = fderiv ℝ (fderiv ℝ f) 0 w v :=
    fun v w => hf.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) v w
  rw [surfaceTaylorTwo_fderiv hf]
  simp only [surfaceTaylorTwo,surfaceQuadratic,add_apply,
    map_smul,map_add,map_sub,smul_apply]
  rw [hB y x]
  module

lemma centeredSurfaceTaylor_midpoint_identity {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a x y : Base) :
    fderiv ℝ (centeredSurfaceTaylor f a) ((1/2 : ℝ) • (x+y)) (x-y) =
      centeredSurfaceTaylor f a x-centeredSurfaceTaylor f a y := by
  have ht : ContDiff ℝ ∞ (translatedSurface f a) := hf.comp (contDiff_id.add contDiff_const)
  change fderiv ℝ (fun z => surfaceTaylorTwo (translatedSurface f a) (z-a)) _ _ = _
  rw [fderiv_comp_sub]
  have hm : (1/2 : ℝ) • (x+y)-a = (1/2 : ℝ) • ((x-a)+(y-a)) := by module
  have hd : x-y = (x-a)-(y-a) := by abel
  rw [hm,hd,surfaceTaylorTwo_midpoint_identity ht]
  rfl

lemma centeredSurfaceTaylor_double_midpoint_singular {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a x y : Base) (hne : x ≠ y)
    (heq : centeredSurfaceTaylor f a x = centeredSurfaceTaylor f a y) :
    ¬ Function.Injective (fderiv ℝ (centeredSurfaceTaylor f a) ((1/2 : ℝ) • (x+y))) := by
  intro hinj
  have hz : fderiv ℝ (centeredSurfaceTaylor f a) ((1/2 : ℝ) • (x+y)) (x-y) =
      fderiv ℝ (centeredSurfaceTaylor f a) ((1/2 : ℝ) • (x+y)) 0 := by
    rw [centeredSurfaceTaylor_midpoint_identity hf,heq,sub_self,map_zero]
  exact hne (sub_eq_zero.mp (hinj hz))

theorem centeredSurfaceTaylor_double_reflection {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) {r : ℝ}
    (hsing : ∀ z ∈ ball a r,
      ¬ Function.Injective (fderiv ℝ (centeredSurfaceTaylor f a) z) → z = a)
    {x y : Base} (hx : x ∈ ball a r) (hy : y ∈ ball a r) (hne : x ≠ y)
    (heq : centeredSurfaceTaylor f a x = centeredSurfaceTaylor f a y) :
    y = (2 : ℝ) • a-x := by
  have hm : (1/2 : ℝ) • (x+y) ∈ ball a r := by
    have h := (convex_ball a r) hx hy (by norm_num : 0 ≤ (1/2 : ℝ))
      (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ)+(1/2) = 1)
    simpa only [smul_add] using h
  have he := hsing _ hm (centeredSurfaceTaylor_double_midpoint_singular hf a x y hne heq)
  have hsum : x+y = (2 : ℝ) • a := by
    have hh := congrArg (fun v : Base => (2 : ℝ) • v) he
    simpa only [smul_smul,show (2 : ℝ)*(1/2) = 1 by norm_num,one_smul] using hh
  calc
    y = (x+y)-x := by abel
    _ = (2 : ℝ) • a-x := by rw [hsum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticCrosscapIsolation
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prepared quadratic model has a single singularity in a fixed
neighborhood. Its two local sheets meet exactly along the kernel line. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem centeredSurfaceTaylor_isolated_crosscap {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r,
      (¬ Function.Injective (fderiv ℝ (centeredSurfaceTaylor f a) x) ↔ x = a) := by
  obtain ⟨r,g,hr,_hr1,_hg,he,_hout,_hsupp,hiso⟩ :=
    centered_quadratic_crosscap_preparation hf b a t hz hreg zero_lt_one
  obtain ⟨s,hs,hsg⟩ := Metric.eventually_nhds_iff.mp he.eventuallyEq_nhds
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro x hx
  have hxr : x ∈ ball a r := ball_subset_ball (min_le_left _ _) hx
  have hxs : dist x a < s := (mem_ball.mp hx).trans_le (min_le_right _ _)
  rw [← (hsg hxs).fderiv_eq]
  exact hiso x hxr

lemma centeredSurfaceTaylor_reflected_difference {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a v : Base) :
    centeredSurfaceTaylor f a (a+v)-centeredSurfaceTaylor f a (a-v) =
      (2 : ℝ) • fderiv ℝ f a v := by
  have h := centeredSurfaceTaylor_midpoint_identity hf a (a+v) (a-v)
  have hm : (1/2 : ℝ) • ((a+v)+(a-v)) = a := by module
  have hd : (a+v)-(a-v) = (2 : ℝ) • v := by module
  rw [hm,hd,centeredSurfaceTaylor_fderiv hf] at h
  simpa only [sub_self,map_zero,add_zero,map_smul] using h.symm

lemma centeredSurfaceTaylor_reflected_eq_iff {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a v : Base) :
    centeredSurfaceTaylor f a (a+v) = centeredSurfaceTaylor f a (a-v) ↔
      fderiv ℝ f a v = 0 := by
  rw [← sub_eq_zero,centeredSurfaceTaylor_reflected_difference hf]
  exact smul_eq_zero.trans (or_iff_right (by norm_num : (2 : ℝ) ≠ 0))

theorem quadratic_crosscap_double_points {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r, ∀ y ∈ ball a r, x ≠ y →
      (centeredSurfaceTaylor f a x = centeredSurfaceTaylor f a y ↔
        ∃ s : ℝ, s ≠ 0 ∧ x = a+s • tangentRay b t ∧ y = a-s • tangentRay b t) := by
  obtain ⟨r,hr,hiso⟩ := centeredSurfaceTaylor_isolated_crosscap hf a b t hz hreg
  refine ⟨r,hr,?_⟩
  intro x hx y hy hne
  constructor
  · intro hxy
    have hreflect := centeredSurfaceTaylor_double_reflection hf a
      (fun z hz h => (hiso z hz).mp h) hx hy hne hxy
    have hy' : y = a-(x-a) := by rw [hreflect]; module
    have hx' : x = a+(x-a) := by abel
    have hker : fderiv ℝ f a (x-a) = 0 := by
      apply (centeredSurfaceTaylor_reflected_eq_iff hf a (x-a)).mp
      simpa only [← hx',← hy'] using hxy
    have hline := (crosscap_kernel_line hf b (a,t) hz hreg.1 (x-a)).mp hker
    let s := tangentRayCoefficient b (x-a)
    have hxline : x = a+s • tangentRay b t := by
      change x = a+tangentRayCoefficient b (x-a) • tangentRay b t
      rw [← hline]
      abel
    have hyline : y = a-s • tangentRay b t := by rw [hy',hline]
    refine ⟨s,?_,hxline,hyline⟩
    intro hs
    apply hne
    rw [hxline,hyline,hs,zero_smul,add_zero,sub_zero]
  · rintro ⟨s,_hs,rfl,rfl⟩
    apply (centeredSurfaceTaylor_reflected_eq_iff hf a _).mpr
    rw [map_smul]
    change s • surfaceDirection f b (a,t) = 0
    rw [hz,smul_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticDoubleTransverse
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from its endpoint the double curve of a quadratic crosscap is
transverse: the difference map on the two source sheets is a submersion. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma quadraticDoubleDifference_fderiv (f : Base → ProjectionTarget 3)
    (a : Base) (z : Base × Base) (v : Base × Base) :
    fderiv ℝ (quadraticDoubleDifference f a) z v =
      fderiv ℝ (centeredSurfaceTaylor f a) z.1 v.1-
        fderiv ℝ (centeredSurfaceTaylor f a) z.2 v.2 := by
  have hQ := (centeredSurfaceTaylor_smooth f a).differentiable (by simp)
  exact congrArg (fun L : (Base × Base) →L[ℝ] ProjectionTarget 3 => L v)
    (((hQ z.1).hasFDerivAt.comp z hasFDerivAt_fst).sub
      ((hQ z.2).hasFDerivAt.comp z hasFDerivAt_snd)).fderiv

lemma quadraticDoubleDifference_at_kernel {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a w : Base) (s : ℝ) (u v : Base) :
    fderiv ℝ (quadraticDoubleDifference f a) (a+s • w,a-s • w) (u,v) =
      fderiv ℝ f a (u-v)+fderiv ℝ (fderiv ℝ f) a w (s • (u+v)) := by
  rw [quadraticDoubleDifference_fderiv,centeredSurfaceTaylor_fderiv hf,
    centeredSurfaceTaylor_fderiv hf]
  simp only [add_sub_cancel_left,sub_sub_cancel_left,
    map_smul,map_neg,add_apply,smul_apply,neg_apply,map_sub,map_add]
  module

theorem quadratic_crosscap_double_transverse {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hreg : Function.Surjective (fderiv ℝ (surfaceDirection f b) (a,t)))
    {s : ℝ} (hs : s ≠ 0) :
    Function.Surjective (fderiv ℝ (quadraticDoubleDifference f a)
      (a+s • tangentRay b t,a-s • tangentRay b t)) := by
  intro y
  obtain ⟨z,hz⟩ := hreg y
  let A : Base := z.2 • tangentRayVelocity b
  let C : Base := s⁻¹ • z.1
  let u := (1/2 : ℝ) • (A+C)
  let v := (1/2 : ℝ) • (C-A)
  have hd : u-v = A := by dsimp [u,v]; module
  have ha : s • (u+v) = z.1 := by
    have huv : u+v = C := by dsimp [u,v]; module
    rw [huv]
    dsimp [C]
    rw [smul_smul,mul_inv_cancel₀ hs,one_smul]
  refine ⟨(u,v),?_⟩
  rw [quadraticDoubleDifference_at_kernel hf,hd,ha]
  rw [(surfaceDirection_hasFDerivAt hf b (a,t)).fderiv] at hz
  have hsym : fderiv ℝ (fderiv ℝ f) a (tangentRay b t) z.1 =
      fderiv ℝ (fderiv ℝ f) a z.1 (tangentRay b t) :=
    hf.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _ _
  rw [hsym]
  exact hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CleanSurfacePairs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular pairs which additionally have no coincidence involving the
prescribed finite singular set form an open, stable condition. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma mem_cleanSurfacePairs {f : M → ProjectionTarget 3} {S : Set M} {z : M × M} :
    z ∈ cleanSurfacePairs f S ↔
      (f z.1 = f z.2 → z.1 ∉ S ∧ z.2 ∉ S ∧ Function.Surjective (surfacePairDerivative f z.1 z.2)) := by
  constructor
  · rintro ⟨hr,ha⟩ he
    exact ⟨(ha.resolve_left (not_not.mpr he)).1,(ha.resolve_left (not_not.mpr he)).2,
      hr.resolve_left (not_not.mpr he)⟩
  · intro h
    by_cases he : f z.1 = f z.2
    · have hh := h he
      exact ⟨Or.inr hh.2.2,Or.inr ⟨hh.1,hh.2.1⟩⟩
    · exact ⟨Or.inl he,Or.inl he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapFiberIsolation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prepared quadratic crosscap is isolated in the fiber of its own image. -/
noncomputable section
open Set Filter Manifold Topology Metric
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem quadratic_crosscap_isolated_fiber {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection φ b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (a,t))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r,
      centeredSurfaceTaylor φ a x = centeredSurfaceTaylor φ a a → x = a := by
  obtain ⟨r,hr,hiso⟩ := centeredSurfaceTaylor_isolated_crosscap hφ a b t hz hreg
  refine ⟨r,hr,?_⟩
  intro x hx heq
  by_contra hne
  have he := centeredSurfaceTaylor_double_reflection hφ a
    (fun z hz h => (hiso z hz).mp h) hx (mem_ball_self hr) hne heq
  apply hne
  calc
    x = (2 : ℝ) • a-((2 : ℝ) • a-x) := by module
    _ = (2 : ℝ) • a-a := by rw [← he]
    _ = a := by module

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem chart_isolated_fiber {f : M → ProjectionTarget 3} (p q : M)
    (hq : p ∈ (chart q).source) {F : Base → ProjectionTarget 3}
    (he : f =ᶠ[𝓝 p] F ∘ chart q)
    {r : ℝ} (hr : 0 < r)
    (hiso : ∀ x ∈ ball (chart q p) r, F x = F (chart q p) → x = chart q p) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, f x = f p → x = p := by
  have hbase : f p = F (chart q p) := he.self_of_nhds
  have hball := ((chart q).continuousAt hq).preimage_mem_nhds
    (ball_mem_nhds (chart q p) hr)
  have hlocal : {x | f x = f p → x = p} ∈ 𝓝 p := by
    filter_upwards [he,hball,(chart q).open_source.mem_nhds hq] with x hx hxball hxsrc
    intro hfx
    apply (chart q).injOn hxsrc hq
    apply hiso _ hxball
    exact hx.symm.trans (hfx.trans hbase)
  obtain ⟨U,hU,hopen,hp⟩ := _root_.mem_nhds_iff.mp hlocal
  exact ⟨U,hopen,hp,fun x hx => hU hx⟩

theorem prepared_crosscap_isolated_fiber {f : M → ProjectionTarget 3} (p q : M)
    (hq : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, f x = f p → x = p := by
  obtain ⟨r,hr,hiso⟩ := quadratic_crosscap_isolated_fiber hφ (chart q p) b t hz hreg
  exact chart_isolated_fiber p q hq he hr hiso

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceQuadraticDoubleChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local double curve is realized in the original surface chart,
including the exact singular point and actual image equalities. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_quadratic_crosscap_chart (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ r : ℝ, 0 < r ∧ closedBall (chart q p) r ⊆ (chart q).target ∧
      (∀ y ∈ ball (chart q p) r,
        F ((chart q).symm y) = centeredSurfaceTaylor φ (chart q p) y) ∧
      (∀ y ∈ ball (chart q p) r,
        (¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F ((chart q).symm y))
          ↔ y = chart q p)) ∧
      (∀ x ∈ ball (chart q p) r, ∀ y ∈ ball (chart q p) r, x ≠ y →
        (F ((chart q).symm x) = F ((chart q).symm y) ↔
          ∃ s : ℝ, s ≠ 0 ∧ x = chart q p+s • tangentRay b t ∧
            y = chart q p-s • tangentRay b t)) := by
  let a := chart q p
  let Q := centeredSurfaceTaylor φ a
  have haT : a ∈ (chart q).target := (chart q).map_source hp
  have ht : Tendsto (chart q).symm (𝓝 a) (𝓝 p) := by
    have hc := (chart q).symm.continuousAt haT
    simpa only [a,(chart q).left_inv hp] using hc.tendsto
  have hfml : ∀ᶠ y in 𝓝 a, y ∈ (chart q).target ∧ F ((chart q).symm y) = Q y := by
    filter_upwards [he.comp_tendsto ht,(chart q).open_target.mem_nhds haT] with y hy hyT
    exact ⟨hyT,by simpa only [Function.comp_apply,(chart q).right_inv hyT] using hy⟩
  obtain ⟨s,hs,hsub⟩ := nhds_basis_closedBall.mem_iff.mp hfml
  obtain ⟨r₀,hr₀,hiso⟩ := centeredSurfaceTaylor_isolated_crosscap hφ a b t hz hreg
  obtain ⟨r₁,hr₁,hdouble⟩ := quadratic_crosscap_double_points hφ a b t hz hreg
  let r := min s (min r₀ r₁)
  have hr : 0 < r := lt_min hs (lt_min hr₀ hr₁)
  have hrs : r ≤ s := min_le_left _ _
  have hrr₀ : r ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₁ : r ≤ r₁ := (min_le_right _ _).trans (min_le_right _ _)
  have hformula (y : Base) (hy : y ∈ ball a r) : F ((chart q).symm y) = Q y :=
    (hsub (closedBall_subset_closedBall hrs (ball_subset_closedBall hy))).2
  refine ⟨r,hr,fun y hy => (hsub (closedBall_subset_closedBall hrs hy)).1,hformula,?_,?_⟩
  · intro y hy
    have hyT := (hsub (closedBall_subset_closedBall hrs (ball_subset_closedBall hy))).1
    have hsource := (chart q).map_target hyT
    have hmodel : F =ᶠ[𝓝 ((chart q).symm y)] Q ∘ chart q := by
      have ho := (chart q).isOpen_inter_preimage (isOpen_ball : IsOpen (ball a r))
      have hm : (chart q).symm y ∈ (chart q).source ∩ (chart q) ⁻¹' ball a r := by
        exact ⟨hsource,by simpa only [mem_preimage,(chart q).right_inv hyT] using hy⟩
      filter_upwards [ho.mem_nhds hm] with z hz'
      have hh := hformula (chart q z) hz'.2
      simpa only [Function.comp_apply,(chart q).left_inv hz'.1] using hh
    have hi := chart_germ_immersion_iff q hsource (centeredSurfaceTaylor_smooth φ a) hmodel
    rw [(chart q).right_inv hyT] at hi
    exact hi.not.trans (hiso y (ball_subset_ball hrr₀ hy))
  · intro x hx y hy hne
    rw [hformula x hx,hformula y hy]
    exact hdouble x (ball_subset_ball hrr₁ hx) y (ball_subset_ball hrr₁ hy) hne

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceCrosscapTransverseNeighborhood
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All distinct coincident points in a sufficiently small prepared
crosscap neighborhood have transverse image tangent planes. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem crosscap_transverse_neighborhood (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, ∀ y ∈ U, x ≠ y → (x,y) ∈ regularSurfacePairs F := by
  obtain ⟨r,hr,hrT,hform,_,hdouble⟩ := surface_quadratic_crosscap_chart F p q hp hφ he b t hz hreg
  let U := (chart q).source ∩ (chart q) ⁻¹' ball (chart q p) r
  have hU : IsOpen U := (chart q).isOpen_inter_preimage isOpen_ball
  have hformula : EqOn F ((centeredSurfaceTaylor φ (chart q p)) ∘ chart q) U := by
    intro x hx
    have h := hform (chart q x) hx.2
    simpa only [Function.comp_apply,(chart q).left_inv hx.1] using h
  refine ⟨U,hU,⟨hp,mem_ball_self hr⟩,?_⟩
  intro x hx y hy hxy
  by_cases hne : F x ≠ F y
  · exact Or.inl hne
  right
  have heq : F x = F y := not_not.mp hne
  have hcne : chart q x ≠ chart q y := fun h => hxy ((chart q).injOn hx.1 hy.1 h)
  have hc : F ((chart q).symm (chart q x)) = F ((chart q).symm (chart q y)) := by
    simpa only [(chart q).left_inv hx.1,(chart q).left_inv hy.1] using heq
  obtain ⟨s,hs,hxs,hys⟩ := (hdouble (chart q x) hx.2 (chart q y) hy.2 hcne).mp hc
  apply (surface_pair_coordinate_regular_iff q q hx.1 hy.1
    (centeredSurfaceTaylor_smooth φ (chart q p)) (centeredSurfaceTaylor_smooth φ (chart q p))
    (hformula.eventuallyEq_of_mem (hU.mem_nhds hx))
    (hformula.eventuallyEq_of_mem (hU.mem_nhds hy))).mpr
  change Function.Surjective (fderiv ℝ (quadraticDoubleDifference φ (chart q p)) _)
  rw [hxs,hys]
  exact quadratic_crosscap_double_transverse hφ (chart q p) b t hreg.surjective hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_PreparedCrosscapNeighborhoods
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint compact frozen neighborhoods inside the actual quadratic
crosscap charts. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_crosscap_neighborhoods
    {f : M → ProjectionTarget 3}
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
    ∃ A : S → Set M, (∀ i, IsCompact (A i) ∧ i.val ∈ interior (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ regularSurfacePairs f := by
  classical
  dsimp only
  let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  obtain ⟨V,hV,hd⟩ := hfin.t2_separation
  have hex (p : S) : ∃ A : Set M, IsCompact A ∧ p.val ∈ interior A ∧ A ⊆ V p.val ∧
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y → (x,y) ∈ regularSurfacePairs f := by
    obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hreg⟩ := hrep p p.property
    obtain ⟨W,hW,hpW,hgood⟩ := crosscap_transverse_neighborhood f p q hpq hφ he b t hz hreg
    obtain ⟨A,hA,hpA,hsub⟩ := exists_compact_subset ((hV p.val).2.inter hW) ⟨(hV p.val).1,hpW⟩
    exact ⟨A,hA,hpA,fun _ hx => (hsub hx).1,
      fun x hx y hy hxy => hgood x (hsub hx).2 y (hsub hy).2 hxy⟩
  choose A hA hpA hAV hgood using hex
  refine ⟨A,fun p => ⟨hA p,hpA p⟩,?_,hgood⟩
  intro p q hpq
  exact (hd p.property q.property (fun h => hpq (Subtype.ext h))).mono (hAV p) (hAV q)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CleanCrosscapNeighborhoods
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen crosscap neighborhoods may be chosen so their internal double
pairs are transverse and involve no singular point. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_clean_crosscap_neighborhoods_oai
    {f : M → ProjectionTarget 3}
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
    ∃ A : S → Set M, (∀ i, IsCompact (A i) ∧ i.val ∈ interior (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, x ≠ y → (x,y) ∈ cleanSurfacePairs f S := by
  classical
  dsimp only
  let S := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  obtain ⟨A,hA,hdis,hreg⟩ := prepared_crosscap_neighborhoods hfin hrep
  have hex (i : S) : ∃ B : Set M, IsCompact B ∧ i.val ∈ interior B ∧ B ⊆ A i ∧
      ∀ x ∈ B, f x = f i.val → x = i.val := by
    obtain ⟨q,φ,b,t,hpq,hφ,he,hz,hR⟩ := hrep i.val i.property
    obtain ⟨U,hU,hiU,hiso⟩ := prepared_crosscap_isolated_fiber i.val q hpq hφ he b t hz hR
    obtain ⟨B,hB,hiB,hBU⟩ := exists_compact_subset (isOpen_interior.inter hU) ⟨(hA i).2,hiU⟩
    exact ⟨B,hB,hiB,fun x hx => interior_subset (hBU hx).1,
      fun x hx => hiso x (hBU hx).2⟩
  choose B hB hiB hBA hIso using hex
  have honly (i : S) (x : M) (hx : x ∈ B i) (hxS : x ∈ S) : x = i.val := by
    by_contra hne
    let j : S := ⟨x,hxS⟩
    have hij : i ≠ j := fun h => hne (congrArg Subtype.val h).symm
    exact (Set.disjoint_left.mp (hdis hij)) (hBA i hx) (interior_subset (hA j).2)
  refine ⟨B,fun i => ⟨hB i,hiB i⟩,?_,?_⟩
  · intro i j hij
    exact (hdis hij).mono (hBA i) (hBA j)
  · intro i x hx y hy hxy
    apply mem_cleanSurfacePairs.mpr
    intro heq
    refine ⟨?_,?_,(hreg i x (hBA i hx) y (hBA i hy) hxy).resolve_left (not_not.mpr heq)⟩
    · intro hxS
      have hxi := honly i x hx hxS
      have hyi : y = i.val := hIso i y hy (heq.symm.trans (congrArg f hxi))
      exact hxy (hxi.trans hyi.symm)
    · intro hyS
      have hyi := honly i y hy hyS
      have hxi : x = i.val := hIso i x hx (heq.trans (congrArg f hyi))
      exact hxy (hxi.trans hyi.symm)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_clean_crosscap_neighborhoods_oai.{u_1}
