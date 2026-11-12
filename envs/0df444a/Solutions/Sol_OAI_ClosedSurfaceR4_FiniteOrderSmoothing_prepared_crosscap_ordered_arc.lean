-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_crosscap_ordered_arc
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:12:49.150461+00:00
-- url     : https://prove2.me/submissions/0cac49cb-f785-4be3-a6bd-d0be8df56ccb

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
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
/-- Mathlib d13f23b's `SimpleGraph.ncard_neighborSet`: the neighbour set's `Set.ncard` is the degree. -/
theorem _root_.SimpleGraph.ncard_neighborSet {V : Type*} (G : SimpleGraph V) (v : V)
    [Fintype (G.neighborSet v)] : (G.neighborSet v).ncard = G.degree v := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree]
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

local instance instContinuousSMulRealProdBase_r4e4185_1 : ContinuousSMul ℝ (Base × ℝ) := Prod.continuousSMul
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
local instance secondJetNormed_r4e4185_1 : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) := inferInstance
local instance secondJetSpace_r4e4185_1 : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) := inferInstance
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_EmbeddingNeighborhoodChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedding whose image contains a neighborhood supplies a local
inverse chart on that neighborhood. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem embedding_neighborhood_chart (f : X → Y) (hf : IsEmbedding f) (p : X)
    {V : Set Y} (hV : IsOpen V) (hpV : f p ∈ V) (hsub : V ⊆ range f) :
    ∃ c : OpenPartialHomeomorph Y X, f p ∈ c.source ∧ c (f p) = p := by
  let : Nonempty X := ⟨p⟩
  let a := hf.toPartialHomeomorph f
  have hback (y : Y) (hy : y ∈ V) : f (a.symm y) = y :=
    hf.toPartialHomeomorph_right_inv f (hsub hy)
  let e : OpenPartialHomeomorph X Y := {
    toFun := f
    invFun := a.symm
    source := f ⁻¹' V
    target := V
    map_source' := fun _ hx => hx
    map_target' := by
      intro y hy
      change f (a.symm y) ∈ V
      rwa [hback y hy]
    left_inv' := fun x _ => hf.toPartialHomeomorph_left_inv f
    right_inv' := hback
    continuousOn_toFun := hf.continuous.continuousOn
    continuousOn_invFun := by
      apply a.continuousOn_symm.mono
      intro y hy
      change y ∈ f '' univ
      simpa only [image_univ] using hsub hy
    open_source := hV.preimage hf.continuous
    open_target := hV }
  exact ⟨e.symm,hpV,hf.toPartialHomeomorph_left_inv f⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_HalfIntervalChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Near its left endpoint, a closed nontrivial interval has the same
local topology as the nonnegative real half-line. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem half_interval_chart {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : OpenPartialHomeomorph (Icc (0:ℝ) δ) (Ici (0:ℝ)),
      (⟨0,le_rfl,hδ.le⟩ : Icc (0:ℝ) δ) ∈ c.source ∧
      c ⟨0,le_rfl,hδ.le⟩ = ⟨0,by simp⟩ := by
  let e := (OpenPartialHomeomorph.refl ℝ).restrOpen (Iio δ) isOpen_Iio
  have hsource : (0:ℝ) ∈ e.source := ⟨mem_univ _,hδ⟩
  obtain ⟨c,hc,_,_,hf,_⟩ := matched_subset_chart e (Icc (0:ℝ) δ) (Ici (0:ℝ)) 0 hsource
    ⟨le_rfl,hδ.le⟩ (by
      intro x hx
      change (0 ≤ x ∧ x ≤ δ) ↔ 0 ≤ x
      exact ⟨And.left,fun h => ⟨h,hx.2.le⟩⟩)
  refine ⟨c,hc,?_⟩
  apply Subtype.ext
  exact hf _ hc

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IntervalNoInteriorExtremum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An injective continuous real function on an interval has no interior
minimum or maximum. This excludes identifying the two local branches of
a curve vertex with a single endpoint of an embedded interval. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem injective_interval_no_minimum {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b)) (hi : InjOn f (Ioo a b))
    (hm : ∀ y ∈ Ioo a b, f x ≤ f y) : False := by
  rcases hf.strictMonoOn_of_injOn_Ioo (hx.1.trans hx.2) hi with hmono | hanti
  · let y := (a+x)/2
    have hy : y ∈ Ioo a b := by constructor <;> dsimp [y] <;> linarith [hx.1,hx.2]
    have hyx : y < x := by dsimp [y] <;> linarith [hx.1]
    exact (not_lt_of_ge (hm y hy)) (hmono hy hx hyx)
  · let y := (x+b)/2
    have hy : y ∈ Ioo a b := by constructor <;> dsimp [y] <;> linarith [hx.1,hx.2]
    have hxy : x < y := by dsimp [y] <;> linarith [hx.2]
    exact (not_lt_of_ge (hm y hy)) (hanti hx hy hxy)

theorem injective_interval_no_maximum {f : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b)) (hi : InjOn f (Ioo a b))
    (hm : ∀ y ∈ Ioo a b, f y ≤ f x) : False := by
  apply injective_interval_no_minimum (f := -f) hx hf.neg
  · intro y hy z hz he
    exact hi hy hz (neg_injective he)
  · intro y hy
    exact neg_le_neg (hm y hy)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LineChartEndpointObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An endpoint of an embedded compact interval cannot contain a
neighborhood of a point with a real-line chart. -/
noncomputable section
open Set Filter Metric Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem line_chart_not_interval_endpoint
    (d : OpenPartialHomeomorph X ℝ) {a b : ℝ}
    (c : OpenPartialHomeomorph X (Icc a b)) {p : X}
    (hd : p ∈ d.source) (hc : p ∈ c.source)
    (hend : (c p:ℝ) = a ∨ (c p:ℝ) = b) : False := by
  let t₀ := d p
  let U := d.target ∩ d.symm ⁻¹' c.source
  have hU : IsOpen U := d.isOpen_inter_preimage_symm c.open_source
  have hpU : t₀ ∈ U := by
    exact ⟨d.map_source hd,by change d.symm (d p) ∈ c.source; rwa [d.left_inv hd]⟩
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  let J := Ioo (t₀-r) (t₀+r)
  have hJU : J ⊆ U := by
    intro t ht
    apply hsub
    rw [mem_ball,Real.dist_eq,abs_lt]
    constructor <;> dsimp [J] at ht <;> linarith [ht.1,ht.2]
  let f : ℝ → ℝ := fun t => (c (d.symm t):ℝ)
  have hf : ContinuousOn f J :=
    continuous_subtype_val.continuousOn.comp
      (c.continuousOn.comp (d.continuousOn_symm.mono (fun t ht => (hJU ht).1))
        (fun t ht => (hJU ht).2)) (fun _ _ => mem_univ _)
  have hi : InjOn f J := by
    intro t ht u hu he
    apply d.symm.injOn (hJU ht).1 (hJU hu).1
    apply c.injOn (hJU ht).2 (hJU hu).2
    exact Subtype.ext he
  have ht₀ : t₀ ∈ J := by
    change t₀-r < t₀ ∧ t₀ < t₀+r
    constructor <;> linarith
  have hfp : f t₀ = (c p:ℝ) := by dsimp [f,t₀]; rw [d.left_inv hd]
  rcases hend with hend | hend
  · apply injective_interval_no_minimum ht₀ hf hi
    intro t _
    rw [hfp,hend]
    exact (c (d.symm t)).property.1
  · apply injective_interval_no_maximum ht₀ hf hi
    intro t _
    rw [hfp,hend]
    exact (c (d.symm t)).property.2

theorem compact_arc_endpoint_not_interior
    (d : OpenPartialHomeomorph X ℝ) {a b : ℝ} (hab : a ≤ b)
    (γ : Icc a b → X) (hγ : IsEmbedding γ) {p : X} (hp : p ∈ d.source)
    (hend : p = γ ⟨a,le_rfl,hab⟩ ∨ p = γ ⟨b,hab,le_rfl⟩) :
    p ∉ interior (range γ) := by
  intro hpin
  rcases hend with hend | hend
  · obtain ⟨c,hc,hcp⟩ := embedding_neighborhood_chart γ hγ ⟨a,le_rfl,hab⟩
      isOpen_interior (hend ▸ hpin) interior_subset
    apply line_chart_not_interval_endpoint d c hp (hend.symm ▸ hc)
    left
    rw [hend,hcp]
  · obtain ⟨c,hc,hcp⟩ := embedding_neighborhood_chart γ hγ ⟨b,hab,le_rfl⟩
      isOpen_interior (hend ▸ hpin) interior_subset
    apply line_chart_not_interval_endpoint d c hp (hend.symm ▸ hc)
    right
    rw [hend,hcp]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ClosedArcHalfChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded half-arc containing a relative neighborhood provides
an actual half-line chart of the ambient subspace. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem closed_arc_half_chart {K : Set X} {δ : ℝ} (hδ : 0 < δ)
    (γ : Icc (0:ℝ) δ → X) (hγ : IsEmbedding γ)
    (hmem : ∀ t, γ t ∈ K) {V : Set X} (hV : IsOpen V)
    (hpV : γ ⟨0,le_rfl,hδ.le⟩ ∈ V) (hsub : K ∩ V ⊆ range γ) :
    ∃ c : OpenPartialHomeomorph K (Ici (0:ℝ)),
      (⟨γ ⟨0,le_rfl,hδ.le⟩,hmem _⟩ : K) ∈ c.source ∧
      c ⟨γ ⟨0,le_rfl,hδ.le⟩,hmem _⟩ = ⟨0,by simp⟩ := by
  let g : Icc (0:ℝ) δ → K := K.codRestrict γ hmem
  have hg : IsEmbedding g := hγ.codRestrict K hmem
  let W : Set K := (↑) ⁻¹' V
  have hW : IsOpen W := hV.preimage continuous_subtype_val
  have hWsub : W ⊆ range g := by
    intro z hz
    obtain ⟨t,ht⟩ := hsub ⟨z.property,hz⟩
    exact ⟨t,Subtype.ext ht⟩
  obtain ⟨a,ha,ha0⟩ := embedding_neighborhood_chart g hg ⟨0,le_rfl,hδ.le⟩ hW hpV hWsub
  obtain ⟨b,hb,hb0⟩ := half_interval_chart hδ
  refine ⟨a.trans b,?_,?_⟩
  · change g ⟨0,le_rfl,hδ.le⟩ ∈ a.source ∧ a (g ⟨0,le_rfl,hδ.le⟩) ∈ b.source
    exact ⟨ha,by rw [ha0]; exact hb⟩
  · change b (a (g ⟨0,le_rfl,hδ.le⟩)) = _
    rw [ha0,hb0]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ImmersionLocalInjectivity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular point of a smooth surface map has a neighborhood on which
the map is injective. Only the two-to-three-dimensional case is needed. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma euclidean_surface_local_injective {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base) (hp : Function.Injective (fderiv ℝ f p)) :
    ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧ U.InjOn f := by
  obtain ⟨L,hL⟩ := (fderiv ℝ f p).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hp)
  let R := L.toContinuousLinearMap
  let g : Base → Base := R ∘ f
  have hg : ContDiff ℝ ∞ g := R.contDiff.comp hf
  have hcomp : R.comp (fderiv ℝ f p) = ContinuousLinearMap.id ℝ Base := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hL v
  have hd : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ Base).toContinuousLinearMap p := by
    have h := R.hasFDerivAt.comp p (hf.differentiable (by simp) p).hasFDerivAt
    rw [hcomp] at h
    exact h
  let e := hg.contDiffAt.toOpenPartialHomeomorph g hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  refine ⟨e.source,e.open_source,hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),?_⟩
  intro x hx y hy hxy
  exact e.injOn hx hy (congrArg R hxy)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_immersion_local_injective {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) (p : M)
    (hp : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U.InjOn f := by
  let a := chart p p
  have hps : p ∈ (chart p).source := by simpa only [chart_source] using mem_chart_source Plane p
  have haT : a ∈ (chart p).target := (chart p).map_source hps
  have hlocal : ContDiffOn ℝ ∞ (f ∘ (chart p).symm) (chart p).target :=
    (hf.comp_contMDiffOn (chart_symm_smooth p)).contDiffOn
  obtain ⟨W,hW,haW,_hWT,φ,hφ,hmatch⟩ :=
    CollarVelocity.compact_smooth_extension (isCompact_singleton : IsCompact ({a} : Set Base))
      (chart p).open_target (by simpa using haT) hlocal
  have hpmodel : f =ᶠ[𝓝 p] φ ∘ chart p := by
    have ho := (chart p).isOpen_inter_preimage hW
    have haW' : chart p p ∈ W := haW (by rfl)
    filter_upwards [ho.mem_nhds ⟨hps,haW'⟩] with x hx
    have hm := (hmatch hx.2).symm
    change f ((chart p).symm (chart p x)) = φ (chart p x) at hm
    simpa only [Function.comp_apply,(chart p).left_inv hx.1] using hm
  have hi : Function.Injective (fderiv ℝ φ a) :=
    (chart_germ_immersion_iff p hps hφ hpmodel).mp hp
  obtain ⟨O,hO,haO,hφI⟩ := euclidean_surface_local_injective hφ a hi
  let U := (chart p).source ∩ (chart p) ⁻¹' (O ∩ W)
  refine ⟨U,(chart p).isOpen_inter_preimage (hO.inter hW),⟨hps,haO,haW (by rfl)⟩,?_⟩
  intro x hx y hy hxy
  have hxφ : f x = φ (chart p x) := by
    have hh := hmatch hx.2.2
    simpa only [Function.comp_apply,(chart p).left_inv hx.1] using hh.symm
  have hyφ : f y = φ (chart p y) := by
    have hh := hmatch hy.2.2
    simpa only [Function.comp_apply,(chart p).left_inv hy.1] using hh.symm
  apply (chart p).injOn hx.1 hy.1
  apply hφI hx.2.1 hy.2.1
  exact hxφ.symm.trans (hxy.trans hyφ)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactDoublePairs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compactification of the double-pair locus can meet the diagonal
only at singular points. Removing open crosscap neighborhoods leaves a
compact set of genuine distinct double pairs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma doublePairs_closure_diagonal_singular {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) (p : M)
    (hp : (p,p) ∈ closure (surfaceDoublePairs f)) :
    ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) := by
  intro hreg
  obtain ⟨U,hU,hpU,hI⟩ := surface_immersion_local_injective hf p hreg
  obtain ⟨z,hzU,hzD⟩ := (_root_.mem_closure_iff.mp hp) (U ×ˢ U) (hU.prod hU) ⟨hpU,hpU⟩
  exact hzD.1 (hI hzU.1 hzU.2 hzD.2)

omit [ChartedSpace Plane M] [IsManifold planeModel ∞ M] in
lemma doublePairs_closure_equal {f : M → ProjectionTarget 3}
    (hf : Continuous f) : closure (surfaceDoublePairs f) ⊆ {z | f z.1 = f z.2} :=
  closure_minimal (fun _ hz => hz.2)
    (isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_UnorderedSurfacePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Hausdorff space of unordered pairs. The quotient identifies only
interchanging the two source points of a double pair. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma unorderedPair_eq {M : Type*} {x y : M × M} :
    unorderedPair x = unorderedPair y ↔ x = y ∨ x = y.swap := @Quotient.eq'' (M × M) (surfacePairSetoid M) x y

lemma unorderedPair_swap {M : Type*} (x : M × M) : unorderedPair x.swap = unorderedPair x :=
  unorderedPair_eq.mpr (Or.inr rfl)

lemma unorderedPair_preimage_image {M : Type*} (U : Set (M × M)) :
    unorderedPair ⁻¹' (unorderedPair '' U) = U ∪ Prod.swap ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨y,hy,hxy⟩
    rcases unorderedPair_eq.mp hxy with h | h
    · exact Or.inl (h ▸ hy)
    · apply Or.inr
      change x.swap ∈ U
      rwa [h] at hy
  · rintro (hx | hx)
    · exact ⟨x,hx,rfl⟩
    · exact ⟨x.swap,hx,unorderedPair_swap x⟩

lemma unorderedPair_continuous {M : Type*} [TopologicalSpace M] :
    Continuous (unorderedPair : M × M → UnorderedSurfacePairs M) := continuous_quotient_mk'

lemma unorderedPair_isOpenMap {M : Type*} [TopologicalSpace M] :
    IsOpenMap (unorderedPair : M × M → UnorderedSurfacePairs M) := by
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (unorderedPair ⁻¹' (unorderedPair '' U))
  rw [unorderedPair_preimage_image]
  exact hU.union (hU.preimage continuous_swap)

lemma unorderedPair_isOpenQuotientMap {M : Type*} [TopologicalSpace M] :
    IsOpenQuotientMap (unorderedPair : M × M → UnorderedSurfacePairs M) :=
  .of_isOpenMap_isQuotientMap unorderedPair_isOpenMap isQuotientMap_quotient_mk'

instance unorderedSurfacePairs_t2 {M : Type*} [TopologicalSpace M] [T2Space M] :
    T2Space (UnorderedSurfacePairs M) := by
  apply (t2Space_iff_of_isOpenQuotientMap unorderedPair_isOpenQuotientMap).mpr
  have he : {z : (M × M) × (M × M) | unorderedPair z.1 = unorderedPair z.2} =
      {z | z.1 = z.2} ∪ {z | z.1 = z.2.swap} := by
    ext z
    exact unorderedPair_eq
  rw [he]
  exact (isClosed_eq continuous_fst continuous_snd).union
    (isClosed_eq continuous_fst (continuous_swap.comp continuous_snd))

lemma unorderedPair_injOn_product {M : Type*} {U V : Set M} (hd : Disjoint U V) :
    (U ×ˢ V).InjOn (unorderedPair : M × M → UnorderedSurfacePairs M) := by
  intro x hx y hy he
  rcases unorderedPair_eq.mp he with he | he
  · exact he
  · exfalso
    have hfst : x.1 = y.2 := congrArg Prod.fst he
    exact Set.disjoint_left.mp hd hx.1 (hfst ▸ hy.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnorderedLinePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two sides of a line become a half-line after forgetting their
ordering. This is the endpoint coordinate for a prepared crosscap. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma unorderedLinePair_eq_iff (a w : Base) (hw : w ≠ 0) (s t : ℝ) :
    unorderedLinePair a w s = unorderedLinePair a w t ↔ s = t ∨ s = -t := by
  constructor
  · intro h
    rcases unorderedPair_eq.mp h with h | h
    · apply Or.inl
      have he := congrArg Prod.fst h
      have hs : (s-t) • w = 0 := by
        rw [sub_smul,sub_eq_zero]
        exact add_left_cancel he
      exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hw)
    · apply Or.inr
      have he := congrArg Prod.fst h
      have hs : (s+t) • w = 0 := by
        calc
          _ = (a+s • w)-(a-t • w) := by module
          _ = 0 := sub_eq_zero.mpr he
      exact eq_neg_iff_add_eq_zero.mpr ((smul_eq_zero.mp hs).resolve_right hw)
  · rintro (rfl | rfl)
    · rfl
    · apply unorderedPair_eq.mpr
      right
      apply Prod.ext <;> simp only [Prod.swap_prod_mk,neg_smul,sub_eq_add_neg,neg_neg]

lemma unorderedLinePair_injOn_nonneg (a w : Base) (hw : w ≠ 0) :
    (Ici (0 : ℝ)).InjOn (unorderedLinePair a w) := by
  intro s hs t ht he
  rcases (unorderedLinePair_eq_iff a w hw s t).mp he with h | h
  · exact h
  · change 0 ≤ s at hs
    change 0 ≤ t at ht
    have : s = 0 ∧ t = 0 := by constructor <;> linarith
    exact this.1.trans this.2.symm

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapDiagonalClosure
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prepared crosscap is an actual endpoint of the compactified
unordered double curve: distinct double pairs approach its diagonal. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem crosscap_diagonal_mem_closure (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    (p,p) ∈ closure (surfaceDoublePairs F) := by
  obtain ⟨r,hr,hball,hformula,_hsing,_hdouble⟩ :=
    surface_quadratic_crosscap_chart F p q hp hφ he b t hz hreg
  let a := chart q p
  let w := tangentRay b t
  have haT : a ∈ (chart q).target := (chart q).map_source hp
  have hs := (chart q).symm.continuousAt haT
  have hplus : Tendsto (fun s : ℝ => a+s • w) (𝓝 0) (𝓝 a) := by
    have hc : ContinuousAt (fun s : ℝ => a+s • w) 0 := by fun_prop
    simpa only [zero_smul,add_zero] using hc.tendsto
  have hminus : Tendsto (fun s : ℝ => a-s • w) (𝓝 0) (𝓝 a) := by
    have hc : ContinuousAt (fun s : ℝ => a-s • w) 0 := by fun_prop
    simpa only [zero_smul,sub_zero] using hc.tendsto
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), a+s • w ∈ ball a r ∧ a-s • w ∈ ball a r :=
    (hplus.eventually (ball_mem_nhds a hr)).and (hminus.eventually (ball_mem_nhds a hr))
  obtain ⟨δ,hδ,hδnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let σ : ℝ → M × M := fun s => ((chart q).symm (a+s • w),(chart q).symm (a-s • w))
  have hlim : Tendsto σ (𝓝 0) (𝓝 (p,p)) := by
    have h1 := hs.tendsto.comp hplus
    have h2 := hs.tendsto.comp hminus
    have h1' : Tendsto (fun s : ℝ => (chart q).symm (a+s • w)) (𝓝 0) (𝓝 p) := by
      simpa only [Function.comp_def,a,(chart q).left_inv hp] using h1
    have h2' : Tendsto (fun s : ℝ => (chart q).symm (a-s • w)) (𝓝 0) (𝓝 p) := by
      simpa only [Function.comp_def,a,(chart q).left_inv hp] using h2
    exact h1'.prodMk_nhds h2'
  have hσ0 : σ 0 = (p,p) := by simp [σ,a,(chart q).left_inv hp]
  have hσ : ContinuousAt σ 0 := by rw [ContinuousAt,hσ0]; exact hlim
  have h0 : (0 : ℝ) ∈ closure (Ioo 0 δ) := by
    rw [closure_Ioo hδ.ne]
    exact ⟨le_rfl,hδ.le⟩
  have himage : σ '' Ioo 0 δ ⊆ surfaceDoublePairs F := by
    rintro z ⟨s,hsδ,rfl⟩
    have hsabs : dist s 0 < δ := by rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos hsδ.1]; exact hsδ.2
    obtain ⟨hsp,hsm⟩ := hδnear hsabs
    have hpT := hball (ball_subset_closedBall hsp)
    have hmT := hball (ball_subset_closedBall hsm)
    refine ⟨?_,?_⟩
    · intro hsame
      have hcoord : a+s • w = a-s • w := (chart q).symm.injOn hpT hmT hsame
      have htwo : (2 : ℝ) • (s • w) = 0 := by
        calc
          _ = (a+s • w)-(a-s • w) := by module
          _ = 0 := sub_eq_zero.mpr hcoord
      have hsw : s • w = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      have hs0 : s = 0 := (smul_eq_zero.mp hsw).resolve_right (tangentRay_ne_zero b t)
      exact hsδ.1.ne' hs0
    · change F ((chart q).symm (a+s • w)) = F ((chart q).symm (a-s • w))
      rw [hformula _ hsp,hformula _ hsm]
      apply (centeredSurfaceTaylor_reflected_eq_iff hφ a (s • w)).mpr
      rw [map_smul]
      change s • surfaceDirection φ b (a,t) = 0
      rw [hz,smul_zero]
  have hcl := closure_mono himage (mem_closure_image hσ h0)
  rwa [hσ0] at hcl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactifiedDoubleCurve
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactifying distinct unordered double pairs retains precisely the
prepared crosscaps on the diagonal. -/
noncomputable section
open Set Topology Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M]

lemma compactifiedDoubleCurve_diagonal (f : M → ProjectionTarget 3) (p : M) :
    unorderedPair (p,p) ∈ compactifiedDoubleCurve f ↔ (p,p) ∈ closure (surfaceDoublePairs f) := by
  constructor
  · rintro ⟨z,hz,he⟩
    have hzp : z = (p,p) := by
      rcases unorderedPair_eq.mp he with he | he
      · exact he
      · simpa only [Prod.swap_prod_mk] using he
    rwa [← hzp]
  · intro hp
    exact ⟨(p,p),hp,rfl⟩

lemma compactifiedDoubleCurve_compact [CompactSpace M] (f : M → ProjectionTarget 3) :
    IsCompact (compactifiedDoubleCurve f) :=
  isClosed_closure.isCompact.image unorderedPair_continuous

variable [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

lemma compactifiedDoubleCurve_finite_diagonal {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfinite : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite) :
    (compactifiedDoubleCurve f ∩ Set.range (fun p : M => unorderedPair (p,p))).Finite := by
  apply (hfinite.image (fun p : M => unorderedPair (p,p))).subset
  rintro z ⟨hz,⟨p,rfl⟩⟩
  exact ⟨p,doublePairs_closure_diagonal_singular hf p ((compactifiedDoubleCurve_diagonal f p).mp hz),rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapCompactArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded compact half-arc in the actual unordered double curve,
with its endpoint at the prepared crosscap. -/
noncomputable section
open Set Filter Metric Manifold Topology
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem crosscap_compact_half_arc (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ γ : Icc (0 : ℝ) δ → UnorderedSurfacePairs M,
      IsClosedEmbedding γ ∧
      (∀ s, γ s = unorderedPair
        ((chart q).symm (chart q p+(s:ℝ) • tangentRay b t),
          (chart q).symm (chart q p-(s:ℝ) • tangentRay b t))) ∧
      γ ⟨0,le_rfl,hδ.le⟩ = unorderedPair (p,p) ∧
      ∀ s, γ s ∈ compactifiedDoubleCurve F := by
  obtain ⟨r,hr,hball,hformula,_hsing,_hdouble⟩ :=
    surface_quadratic_crosscap_chart F p q hp hφ he b t hz hreg
  let a := chart q p
  let w := tangentRay b t
  let δ := r/(2*(‖w‖+1))
  have hden : 0 < 2*(‖w‖+1) := by positivity
  have hδ : 0 < δ := div_pos hr hden
  have hδr : δ*‖w‖ < r := by
    have heq : δ*(2*(‖w‖+1)) = r := div_mul_cancel₀ r hden.ne'
    have hlt : ‖w‖ < 2*(‖w‖+1) := by linarith [norm_nonneg w]
    exact (mul_lt_mul_of_pos_left hlt hδ).trans_eq heq
  have hcoords (s : Icc (0 : ℝ) δ) : a+(s:ℝ) • w ∈ ball a r ∧ a-(s:ℝ) • w ∈ ball a r := by
    have hn : ‖(s:ℝ) • w‖ < r := by
      rw [norm_smul,Real.norm_of_nonneg s.property.1]
      exact (mul_le_mul_of_nonneg_right s.property.2 (norm_nonneg w)).trans_lt hδr
    constructor
    · simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left] using hn
    · simpa only [mem_ball,dist_eq_norm,sub_sub_cancel_left,norm_neg] using hn
  let γ : Icc (0 : ℝ) δ → UnorderedSurfacePairs M := fun s =>
    unorderedPair ((chart q).symm (a+(s:ℝ) • w),(chart q).symm (a-(s:ℝ) • w))
  have hγcont : Continuous γ := by
    apply unorderedPair_continuous.comp
    apply Continuous.prodMk
    · apply continuous_iff_continuousAt.mpr
      intro s
      have hc : ContinuousAt (fun u : Icc (0 : ℝ) δ => a+(u:ℝ) • w) s := by fun_prop
      exact ContinuousAt.comp (f := fun u : Icc (0 : ℝ) δ => a+(u:ℝ) • w)
        ((chart q).symm.continuousAt (hball (ball_subset_closedBall (hcoords s).1))) hc
    · apply continuous_iff_continuousAt.mpr
      intro s
      have hc : ContinuousAt (fun u : Icc (0 : ℝ) δ => a-(u:ℝ) • w) s := by fun_prop
      exact ContinuousAt.comp (f := fun u : Icc (0 : ℝ) δ => a-(u:ℝ) • w)
        ((chart q).symm.continuousAt (hball (ball_subset_closedBall (hcoords s).2))) hc
  have hchart (s : Icc (0 : ℝ) δ) :
      unorderedPairMap (chart q) (γ s) = unorderedLinePair a w s := by
    change unorderedPair (chart q ((chart q).symm (a+(s:ℝ) • w)),
      chart q ((chart q).symm (a-(s:ℝ) • w))) = _
    rw [(chart q).right_inv (hball (ball_subset_closedBall (hcoords s).1)),
      (chart q).right_inv (hball (ball_subset_closedBall (hcoords s).2))]
    rfl
  have hγinj : Function.Injective γ := by
    intro s u hsu
    apply Subtype.ext
    apply unorderedLinePair_injOn_nonneg a w (tangentRay_ne_zero b t) s.property.1 u.property.1
    rw [← hchart s,← hchart u,hsu]
  refine ⟨δ,hδ,γ,hγcont.isClosedEmbedding hγinj,(fun _ => rfl),?_,?_⟩
  · simp [γ,a,(chart q).left_inv hp]
  · intro s
    by_cases hs : (s:ℝ) = 0
    · have hγs : γ s = unorderedPair (p,p) := by simp [γ,hs,a,(chart q).left_inv hp]
      rw [hγs,compactifiedDoubleCurve_diagonal]
      exact crosscap_diagonal_mem_closure F p q hp hφ he b t hz hreg
    · have hsp := (hcoords s).1
      have hsm := (hcoords s).2
      have hneq : (chart q).symm (a+(s:ℝ) • w) ≠ (chart q).symm (a-(s:ℝ) • w) := by
        intro hsame
        have hcoord := (chart q).symm.injOn (hball (ball_subset_closedBall hsp))
          (hball (ball_subset_closedBall hsm)) hsame
        have htwo : (2 : ℝ) • ((s:ℝ) • w) = 0 := by
          calc
            _ = (a+(s:ℝ) • w)-(a-(s:ℝ) • w) := by module
            _ = 0 := sub_eq_zero.mpr hcoord
        have hsw : (s:ℝ) • w = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
        exact hs ((smul_eq_zero.mp hsw).resolve_right (tangentRay_ne_zero b t))
      have hEq : F ((chart q).symm (a+(s:ℝ) • w)) = F ((chart q).symm (a-(s:ℝ) • w)) := by
        rw [hformula _ hsp,hformula _ hsm]
        apply (centeredSurfaceTaylor_reflected_eq_iff hφ a _).mpr
        rw [map_smul]
        change (s:ℝ) • surfaceDirection φ b (a,t) = 0
        rw [hz,smul_zero]
      exact ⟨_,subset_closure ⟨hneq,hEq⟩,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapArcNeighborhood
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact half-arc contains a whole neighborhood of its endpoint
in the compactified double curve. -/
noncomputable section
open Set Filter Metric Manifold Topology
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M] in
lemma unorderedPair_mem_square {U : Set M} {z : M × M} :
    unorderedPair z ∈ unorderedPair '' (U ×ˢ U) ↔ z ∈ U ×ˢ U := by
  change z ∈ unorderedPair ⁻¹' (unorderedPair '' (U ×ˢ U)) ↔ _
  rw [unorderedPair_preimage_image]
  simp only [mem_union,mem_prod,mem_preimage,Prod.fst_swap,Prod.snd_swap]
  tauto

theorem crosscap_arc_contains_neighborhood {F : M → ProjectionTarget 3}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    {δ : ℝ} (hδ : 0 < δ) (γ : Icc (0 : ℝ) δ → UnorderedSurfacePairs M)
    (hγ : ∀ s, γ s = unorderedPair
      ((chart q).symm (chart q p+(s:ℝ) • tangentRay b t),
        (chart q).symm (chart q p-(s:ℝ) • tangentRay b t))) :
    ∃ V : Set (UnorderedSurfacePairs M), IsOpen V ∧ unorderedPair (p,p) ∈ V ∧
      compactifiedDoubleCurve F ∩ V ⊆ Set.range γ := by
  obtain ⟨r,hr,_hball,_hformula,hiso,hdouble⟩ :=
    surface_quadratic_crosscap_chart F p q hp hφ he b t hz hreg
  let a := chart q p
  let w := tangentRay b t
  have hw : w ≠ 0 := tangentRay_ne_zero b t
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let ρ := min r (δ*‖w‖)
  have hρ : 0 < ρ := lt_min hr (mul_pos hδ hwn)
  let U := (chart q).source ∩ (chart q) ⁻¹' ball a ρ
  have hU : IsOpen U := (chart q).isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hp,mem_ball_self hρ⟩
  let V := unorderedPair '' (U ×ˢ U)
  refine ⟨V,unorderedPair_isOpenMap _ (hU.prod hU),⟨(p,p),⟨hpU,hpU⟩,rfl⟩,?_⟩
  rintro z ⟨⟨⟨u,v⟩,hcl,hzq⟩,hzV⟩
  rw [← hzq] at hzV ⊢
  have hUV : (u,v) ∈ U ×ˢ U := unorderedPair_mem_square.mp hzV
  have huS : u ∈ (chart q).source := hUV.1.1
  have hvS : v ∈ (chart q).source := hUV.2.1
  let x := chart q u
  let y := chart q v
  have hxρ : x ∈ ball a ρ := hUV.1.2
  have hyρ : y ∈ ball a ρ := hUV.2.2
  have hxr : x ∈ ball a r := ball_subset_ball (min_le_left _ _) hxρ
  have hyr : y ∈ ball a r := ball_subset_ball (min_le_left _ _) hyρ
  by_cases huv : u = v
  · have hdiag : (u,u) ∈ closure (surfaceDoublePairs F) := by simpa only [huv] using hcl
    have hbad := doublePairs_closure_diagonal_singular hF u hdiag
    have hxsing : ¬ Function.Injective
        (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F ((chart q).symm x)) := by
      rw [show (chart q).symm x = u from (chart q).left_inv huS]
      exact hbad
    have hxa : x = a := (hiso x hxr).mp hxsing
    have hup : u = p := (chart q).injOn huS hp hxa
    refine ⟨⟨0,le_rfl,hδ.le⟩,?_⟩
    rw [hγ]
    simp [hup,← huv,(chart q).left_inv hp]
  · have hxy : x ≠ y := fun h => huv ((chart q).injOn huS hvS h)
    have heqF : F u = F v := doublePairs_closure_equal hF.continuous hcl
    have hfxy : F ((chart q).symm x) = F ((chart q).symm y) := by
      rw [show (chart q).symm x = u from (chart q).left_inv huS,
        show (chart q).symm y = v from (chart q).left_inv hvS]
      exact heqF
    obtain ⟨s,_hs,hxs,hys⟩ := (hdouble x hxr y hyr hxy).mp hfxy
    have hnorm : |s| * ‖w‖ < ρ := by
      have h := mem_ball.mp hxρ
      change ‖x-a‖ < ρ at h
      rw [hxs,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] at h
      exact h
    have hsδ : |s| < δ := by
      exact (mul_lt_mul_iff_left₀ hwn).mp (hnorm.trans_le (min_le_right _ _))
    let s' : Icc (0 : ℝ) δ := ⟨|s|,abs_nonneg s,hsδ.le⟩
    refine ⟨s',?_⟩
    have hu : u = (chart q).symm (a+s • w) := by rw [← hxs]; exact ((chart q).left_inv huS).symm
    have hv : v = (chart q).symm (a-s • w) := by rw [← hys]; exact ((chart q).left_inv hvS).symm
    have habs : unorderedLinePair a w s = unorderedLinePair a w |s| := by
      apply (unorderedLinePair_eq_iff a w hw s |s|).mpr
      rcases le_total 0 s with hs | hs
      · exact Or.inl (abs_of_nonneg hs).symm
      · exact Or.inr (by rw [abs_of_nonpos hs,neg_neg])
    have hmap := congrArg (unorderedPairMap (chart q).symm) habs
    rw [hγ,hu,hv]
    exact hmap.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapEndpoint
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each prepared crosscap has a genuine embedded half-interval
neighborhood in the compactified unordered double curve. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem crosscap_half_arc_neighborhood {F : M → ProjectionTarget 3}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ γ : Icc (0 : ℝ) δ → UnorderedSurfacePairs M,
      IsClosedEmbedding γ ∧ γ ⟨0,le_rfl,hδ.le⟩ = unorderedPair (p,p) ∧
      (∀ s, γ s ∈ compactifiedDoubleCurve F) ∧
      ∃ V : Set (UnorderedSurfacePairs M), IsOpen V ∧ unorderedPair (p,p) ∈ V ∧
        compactifiedDoubleCurve F ∩ V ⊆ Set.range γ := by
  obtain ⟨δ,hδ,γ,hγ,hformula,hzero,hmem⟩ :=
    crosscap_compact_half_arc F p q hp hφ he b t hz hreg
  obtain ⟨V,hV,hpV,hsub⟩ :=
    crosscap_arc_contains_neighborhood hF p q hp hφ he b t hz hreg hδ γ hformula
  exact ⟨δ,hδ,γ,hγ,hzero,hmem,V,hV,hpV,hsub⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapHalfLineChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prepared crosscaps are genuine boundary points of the compactified
unordered double curve. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem crosscap_half_line_chart {F : M → ProjectionTarget 3}
    (hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve F) (Ici (0:ℝ)),
      ∃ hpK : unorderedPair (p,p) ∈ compactifiedDoubleCurve F,
        (⟨unorderedPair (p,p),hpK⟩ : compactifiedDoubleCurve F) ∈ c.source ∧
        c ⟨unorderedPair (p,p),hpK⟩ = ⟨0,by simp⟩ := by
  obtain ⟨δ,hδ,γ,hγ,hγ0,hmem,V,hV,hpV,hsub⟩ :=
    crosscap_half_arc_neighborhood hF p q hp hφ he b t hz hreg
  have hpγ : γ ⟨0,le_rfl,hδ.le⟩ ∈ V := by rwa [hγ0]
  obtain ⟨c,hc,hc0⟩ := closed_arc_half_chart hδ γ hγ.isEmbedding hmem hV hpγ hsub
  have hpK : unorderedPair (p,p) ∈ compactifiedDoubleCurve F := by
    rw [← hγ0]
    exact hmem _
  refine ⟨c,hpK,?_,?_⟩
  · simpa only [hγ0] using hc
  · simpa only [hγ0] using hc0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_UnorderedPairChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from the diagonal the quotient by interchanging the two points
is locally a homeomorphism, using disjoint coordinate neighborhoods. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem unordered_pair_local_chart {M : Type*} [TopologicalSpace M] [T2Space M]
    (p q : M) (hpq : p ≠ q) :
    ∃ e : OpenPartialHomeomorph (M × M) (UnorderedSurfacePairs M),
      (p,q) ∈ e.source ∧ (∀ z, e z = unorderedPair z) ∧
      ∀ z ∈ e.source, z.1 ≠ z.2 := by
  have : Nonempty (M × M) := ⟨(p,q)⟩
  obtain ⟨U,V,hU,hV,hp,hq,hd⟩ := t2_separation hpq
  let E := (unorderedPair_injOn_product hd).toPartialEquiv unorderedPair (U ×ˢ V)
  let e := OpenPartialHomeomorph.ofContinuousOpen E unorderedPair_continuous.continuousOn
    unorderedPair_isOpenMap (hU.prod hV)
  refine ⟨e,⟨hp,hq⟩,(fun _ => rfl),?_⟩
  intro z hz heq
  exact Set.disjoint_left.mp hd hz.1 (heq ▸ hz.2)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleCurveMembership
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Off the diagonal, membership in the compactified curve is exactly
membership in the actual double-pair locus. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem compactifiedDoubleCurve_pair_equality {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {z : M × M}
    (hz : unorderedPair z ∈ compactifiedDoubleCurve f) : f z.1 = f z.2 := by
  obtain ⟨w,hw,he⟩ := hz
  have hwf := doublePairs_closure_equal hf.continuous hw
  change f w.1 = f w.2 at hwf
  rcases unorderedPair_eq.mp he with he | he
  · simpa only [he] using hwf
  · rw [he] at hwf
    exact hwf.symm

theorem compactifiedDoubleCurve_off_diagonal {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {z : M × M}
    (hne : z.1 ≠ z.2) :
    unorderedPair z ∈ compactifiedDoubleCurve f ↔ z ∈ surfaceDoublePairs f := by
  constructor
  · intro hz
    exact ⟨hne,compactifiedDoubleCurve_pair_equality hf hz⟩
  · intro hz
    exact ⟨z,subset_closure hz,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ZeroSliceLineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero slice in a product is a copy of the line; this converts
submersion coordinates into charts on matched zero subsets. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [Zero E]

theorem matched_zero_subset_line_chart (e : OpenPartialHomeomorph X (E × ℝ))
    (S : Set X) (p : X) (hp : p ∈ e.source) (hpS : p ∈ S)
    (hmatch : ∀ x ∈ e.source, x ∈ S ↔ (e x).1 = 0) :
    ∃ c : OpenPartialHomeomorph S ℝ, (⟨p,hpS⟩ : S) ∈ c.source := by
  obtain ⟨a,ha,_,_,_,_⟩ := matched_subset_chart e S {z | z.1 = 0} p hp hpS hmatch
  let h := (zeroSliceLineHomeomorph (E := E)).toOpenPartialHomeomorph
  refine ⟨a.trans h,?_⟩
  change (⟨p,hpS⟩ : S) ∈ a.source ∧ a ⟨p,hpS⟩ ∈ h.source
  exact ⟨ha,mem_univ _⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceDoublePairChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every transverse distinct double pair has an open real-line chart
in the actual surface double-pair locus. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem surface_double_pair_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    ∃ c : OpenPartialHomeomorph (surfaceDoublePairs f) ℝ,
      (⟨(x,y),hxy,heq⟩ : surfaceDoublePairs f) ∈ c.source := by
  obtain ⟨U,F,hU,hxU,hUs,hF,heF⟩ := surface_chart_representative hf x
  obtain ⟨V,G,hV,hyV,hVs,hG,heG⟩ := surface_chart_representative hf y
  let H : Base × Base → ProjectionTarget 3 := fun z => F z.1-G z.2
  have hH : ContDiff ℝ ∞ H := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
  have hD : Function.Surjective (fderiv ℝ H (chart x x,chart y y)) :=
    (surface_pair_coordinate_regular_iff x y (hUs hxU) (hVs hyV) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hxU))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hyV))).mp hreg
  obtain ⟨b,hb,hbf,_,_⟩ := double_locus_submersion_chart hH (chart x x,chart y y) hD
  let R : Set (M × M) := (U ×ˢ V) ∩ {z | z.1 ≠ z.2}
  have hR : IsOpen R := (hU.prod hV).inter isClosed_diagonal.isOpen_compl
  let a := ((chart x).prod (chart y)).restrOpen R hR
  let e := a.trans b
  have hp : (x,y) ∈ e.source := by
    exact ⟨⟨⟨hUs hxU,hVs hyV⟩,⟨⟨hxU,hyV⟩,hxy⟩⟩,hb⟩
  apply matched_zero_subset_line_chart e (surfaceDoublePairs f) (x,y) hp ⟨hxy,heq⟩
  intro z hz
  have hsrc : z ∈ (U ×ˢ V) ∩ {z | z.1 ≠ z.2} := hz.1.2
  have hfirst : (e z).1 = f z.1-f z.2 := by
    change (b (chart x z.1,chart y z.2)).1 = _
    rw [hbf]
    change F (chart x z.1)-G (chart y z.2) = _
    change (F ∘ chart x) z.1-(G ∘ chart y) z.2 = _
    rw [← heF hsrc.1.1,← heG hsrc.1.2]
  rw [hfirst,sub_eq_zero]
  exact and_iff_right hsrc.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_UnorderedDoubleCurveChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regular unordered double curve has genuine open line charts in
its actual quotient-subspace topology. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem unordered_double_curve_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve f) ℝ,
      (⟨unorderedPair (x,y),⟨(x,y),subset_closure ⟨hxy,heq⟩,rfl⟩⟩ : compactifiedDoubleCurve f) ∈ c.source := by
  obtain ⟨e,hpe,he,hne⟩ := unordered_pair_local_chart x y hxy
  obtain ⟨a,hpa,_,_,haf,_⟩ := matched_subset_chart e
    (surfaceDoublePairs f) (compactifiedDoubleCurve f) (x,y) hpe ⟨hxy,heq⟩
    (fun z hz => by rw [he z]; exact (compactifiedDoubleCurve_off_diagonal hf (hne z hz)).symm)
  obtain ⟨b,hpb⟩ := surface_double_pair_chart hf x y hxy heq hreg
  let p : surfaceDoublePairs f := ⟨(x,y),hxy,heq⟩
  let q : compactifiedDoubleCurve f := ⟨unorderedPair (x,y),⟨(x,y),subset_closure ⟨hxy,heq⟩,rfl⟩⟩
  have haq : a p = q := by
    apply Subtype.ext
    exact (haf p hpa).trans (he (x,y))
  refine ⟨a.symm.trans b,?_⟩
  change q ∈ a.target ∧ a.symm q ∈ b.source
  refine ⟨?_,?_⟩
  · rw [← haq]
    exact a.map_source hpa
  · rw [← haq,a.left_inv hpa]
    exact hpb

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TransverseCompactCurveCharts
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An unconditional compact double curve with genuine line charts in
its interior and half-line charts at precisely its finite diagonal set. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [T2Space M] in
theorem doubleCurveBoundary_finite {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite) :
    (doubleCurveBoundary f).Finite := by
  have hD := compactifiedDoubleCurve_finite_diagonal hf hfin
  apply Set.Finite.of_finite_image (f := fun z : compactifiedDoubleCurve f => z.val)
  · apply hD.subset
    rintro z ⟨w,hw,rfl⟩
    exact ⟨w.property,hw⟩
  · exact Subtype.val_injective.injOn

theorem transverse_double_curve_interior_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (z : compactifiedDoubleCurve f) (hz : z ∉ doubleCurveBoundary f) :
    ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve f) ℝ, z ∈ c.source := by
  obtain ⟨w,hw,hew⟩ := z.property
  have hne : w.1 ≠ w.2 := by
    intro he
    apply hz
    refine ⟨w.1,?_⟩
    have hw' : (w.1,w.1) = w := Prod.ext rfl he
    rw [hw',hew]
  have heq := doublePairs_closure_equal hf.continuous hw
  obtain ⟨c,hc⟩ := unordered_double_curve_chart hf w.1 w.2 hne heq (hreg _ _ hne heq)
  refine ⟨c,?_⟩
  have hz' : (⟨unorderedPair (w.1,w.2),⟨(w.1,w.2),subset_closure ⟨hne,heq⟩,rfl⟩⟩ : compactifiedDoubleCurve f) = z :=
    Subtype.ext hew
  rwa [hz'] at hc

theorem transverse_double_curve_boundary_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    (z : compactifiedDoubleCurve f) (hz : z ∈ doubleCurveBoundary f) :
    ∃ c : OpenPartialHomeomorph (compactifiedDoubleCurve f) (Ici (0:ℝ)),
      z ∈ c.source ∧ c z = ⟨0,by simp⟩ := by
  obtain ⟨p,hp⟩ := hz
  have hpK : unorderedPair (p,p) ∈ compactifiedDoubleCurve f := hp.symm ▸ z.property
  have hs : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) :=
    doublePairs_closure_diagonal_singular hf p ((compactifiedDoubleCurve_diagonal f p).mp hpK)
  obtain ⟨q,φ,b,t,hpq,hφ,he,hzero,hR⟩ := hrep p hs
  obtain ⟨c,hmem,hc,hc0⟩ := crosscap_half_line_chart hf p q hpq hφ he b t hzero hR
  have hez : (⟨unorderedPair (p,p),hmem⟩ : compactifiedDoubleCurve f) = z := Subtype.ext hp
  exact ⟨c,hez ▸ hc,hez ▸ hc0⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactCurveArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact embedded arcs with open interior, used to reduce the
compact one-dimensional curve to finitely many interval pieces. -/
noncomputable section
open Set Filter Metric Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable (X : Type*) [TopologicalSpace X]

variable {X} [T2Space X]

theorem line_chart_compact_arc_data (c : OpenPartialHomeomorph X ℝ) {p : X}
    (hp : p ∈ c.source) :
    ∃ (A : CompactCurveArc X) (V : Set X), IsOpen V ∧ p ∈ V ∧ V ⊆ range A.map ∧
      ∃ t : Icc A.left A.right, A.left < (t:ℝ) ∧ (t:ℝ) < A.right ∧ A.map t = p ∧
        V = A.map '' {u | A.left < (u:ℝ) ∧ (u:ℝ) < A.right} ∧ V ⊆ c.source := by
  obtain ⟨r,hr,hrt⟩ := nhds_basis_closedBall.mem_iff.mp (c.open_target.mem_nhds (c.map_source hp))
  let a := c p-r
  let b := c p+r
  have hab : a < b := by dsimp [a,b] <;> linarith
  have hinterval : Icc a b ⊆ c.target := by
    intro t ht
    apply hrt
    rw [mem_closedBall,Real.dist_eq,abs_le]
    constructor <;> dsimp [a,b] at ht <;> linarith [ht.1,ht.2]
  let γ : Icc a b → X := fun t => c.symm t
  have hγcont : Continuous γ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (c.symm.continuousAt (hinterval t.property)).comp continuous_subtype_val.continuousAt
  have hγinj : Function.Injective γ := by
    intro s t hst
    exact Subtype.ext (c.symm.injOn (hinterval s.property) (hinterval t.property) hst)
  have heq : γ '' {t | a < (t:ℝ) ∧ (t:ℝ) < b} = c.symm '' Ioo a b := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht.1.le,ht.2.le⟩,ht,rfl⟩
  have hV : IsOpen (c.symm '' Ioo a b) :=
    c.isOpen_image_symm_of_subset_target isOpen_Ioo (fun _ ht => hinterval ⟨ht.1.le,ht.2.le⟩)
  let A : CompactCurveArc X := ⟨a,b,hab,γ,hγcont.isClosedEmbedding hγinj,by rw [heq]; exact hV⟩
  refine ⟨A,c.symm '' Ioo a b,hV,?_,?_,?_⟩
  · refine ⟨c p,?_,c.left_inv hp⟩
    constructor <;> dsimp [a,b] <;> linarith
  · rintro z ⟨t,ht,rfl⟩
    exact ⟨⟨t,ht.1.le,ht.2.le⟩,rfl⟩

  · have ht : a < c p ∧ c p < b := by constructor <;> dsimp [a,b] <;> linarith
    refine ⟨⟨c p,ht.1.le,ht.2.le⟩,ht.1,ht.2,c.left_inv hp,heq.symm,?_⟩
    rintro z ⟨u,hu,rfl⟩
    exact c.map_target (hinterval ⟨hu.1.le,hu.2.le⟩)

theorem line_chart_compact_arc (c : OpenPartialHomeomorph X ℝ) {p : X}
    (hp : p ∈ c.source) :
    ∃ (A : CompactCurveArc X) (V : Set X), IsOpen V ∧ p ∈ V ∧ V ⊆ range A.map := by
  obtain ⟨A,V,hV,hpV,hAV,_⟩ := line_chart_compact_arc_data c hp
  exact ⟨A,V,hV,hpV,hAV⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_EmbeddedOpenSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open subarcs remain open in the ambient curve. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem embedded_open_subset {f : X → Y} (hf : IsEmbedding f)
    {U S : Set X} (hU : IsOpen (f '' U)) (hS : IsOpen S) (hSU : S ⊆ U) :
    IsOpen (f '' S) := by
  obtain ⟨V,hV,hVS⟩ := hf.isInducing.isOpen_iff.mp hS
  have heq : f '' S = (f '' U) ∩ V := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hSU hx,rfl⟩,by rw [← hVS] at hx; exact hx⟩
    · rintro ⟨⟨x,hx,rfl⟩,hy⟩
      exact ⟨x,by rw [← hVS]; exact hy,rfl⟩
  rw [heq]
  exact hU.inter hV

variable {Z : Type*} [TopologicalSpace Z]

lemma CompactCurveArc.openSubarc_open (A : CompactCurveArc Z) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) : IsOpen (A.openSubarc u v) := by
  apply embedded_open_subset A.embedding.isEmbedding A.interior_open
  · exact isOpen_Ioo.preimage continuous_subtype_val
  · intro t ht
    exact ⟨hu.trans_lt ht.1,ht.2.trans_le hv⟩

lemma CompactCurveArc.closedSubarc_compact (A : CompactCurveArc Z) (u v : ℝ) :
    IsCompact (A.closedSubarc u v) := by
  exact (IsClosed.isCompact (isClosed_Icc.preimage continuous_subtype_val)).image A.embedding.continuous

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SubarcTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Open subarcs are connected, and their only possible frontier points
are their two endpoints. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem CompactCurveArc.subarc_frontier (A : CompactCurveArc X) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) (huv : u < v)
    {x : X} (hx : x ∈ closure (A.openSubarc u v)) (hnot : x ∉ A.openSubarc u v) :
    x = A.map ⟨u,hu,huv.le.trans hv⟩ ∨ x = A.map ⟨v,hu.trans huv.le,hv⟩ := by
  have hsub : A.openSubarc u v ⊆ A.closedSubarc u v := by
    rintro z ⟨t,ht,rfl⟩
    exact ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
  have hc := closure_minimal hsub (A.closedSubarc_compact u v).isClosed
  obtain ⟨t,ht,rfl⟩ := hc hx
  have hnt : ¬ (u < (t:ℝ) ∧ (t:ℝ) < v) := fun h => hnot ⟨t,h,rfl⟩
  rcases eq_or_lt_of_le ht.1 with he | he
  · left
    congr 1
    exact Subtype.ext he.symm
  · right
    have heq : (t:ℝ) = v := le_antisymm ht.2 (le_of_not_gt fun h => hnt ⟨he,h⟩)
    congr 1
    exact Subtype.ext heq

omit [T2Space X] in
theorem CompactCurveArc.subarc_connected (A : CompactCurveArc X) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) (huv : u < v) :
    IsConnected (A.openSubarc u v) := by
  let j : Ioo u v → Icc A.left A.right := fun t =>
    ⟨t.val,hu.trans t.property.1.le,t.property.2.le.trans hv⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let : ConnectedSpace (Ioo u v) := isConnected_iff_connectedSpace.mp (isConnected_Ioo huv)
  have hconn : IsConnected (range (A.map ∘ j)) := isConnected_range (A.embedding.continuous.comp hj)
  have heq : range (A.map ∘ j) = A.openSubarc u v := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨j t,t.property,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t.val,ht⟩,rfl⟩
  rwa [heq] at hconn

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SubarcClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each nonempty interval piece has exactly the two expected endpoints
in its closure. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
theorem CompactCurveArc.subarc_closure (A : CompactCurveArc X) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) (huv : u < v) :
    closure (A.openSubarc u v) = A.closedSubarc u v := by
  let S : Set (Icc A.left A.right) := {t | u < (t:ℝ) ∧ (t:ℝ) < v}
  have himage : (Subtype.val '' S : Set ℝ) = Ioo u v := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ht
    · intro hr
      exact ⟨⟨r,hu.trans hr.1.le,hr.2.le.trans hv⟩,hr,rfl⟩
  have hclosure : closure S = {t : Icc A.left A.right | u ≤ (t:ℝ) ∧ (t:ℝ) ≤ v} := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,himage,closure_Ioo huv.ne]
    rfl
  change closure (A.map '' S) = _
  rw [A.embedding.closure_image_eq,hclosure]
  rfl

theorem CompactCurveArc.subarc_boundary_eq (A : CompactCurveArc X) {u v : ℝ}
    (hu : A.left ≤ u) (hv : v ≤ A.right) (huv : u < v) :
    closure (A.openSubarc u v) \ A.openSubarc u v =
      {A.map ⟨u,hu,huv.le.trans hv⟩,A.map ⟨v,hu.trans huv.le,hv⟩} := by
  apply Subset.antisymm
  · intro x hx
    rcases A.subarc_frontier hu hv huv hx.1 hx.2 with h | h
    · exact Or.inl h
    · exact Or.inr (mem_singleton_iff.mpr h)
  · intro x hx
    rw [A.subarc_closure hu hv huv]
    rcases hx with h | h
    · rw [h]
      refine ⟨⟨⟨u,hu,huv.le.trans hv⟩,⟨le_rfl,huv.le⟩,rfl⟩,?_⟩
      rintro ⟨t,ht,he⟩
      have heq := congrArg Subtype.val (A.embedding.injective he)
      exact (ne_of_gt ht.1) heq
    · have h := mem_singleton_iff.mp h
      rw [h]
      refine ⟨⟨⟨v,hu.trans huv.le,hv⟩,⟨huv.le,le_rfl⟩,rfl⟩,?_⟩
      rintro ⟨t,ht,he⟩
      have heq := congrArg Subtype.val (A.embedding.injective he)
      exact (ne_of_lt ht.2) heq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveEdgeWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each finite curve edge retains its actual compact interval
parametrization, two distinct endpoints, and exact frontier. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

lemma CurveEdgeWitness.endpoints_ne {V E : Set X} (w : CurveEdgeWitness V E) :
    w.leftPoint ≠ w.rightPoint := by
  intro he
  have ht := w.arc.embedding.injective he
  exact w.ordered.ne (congrArg Subtype.val ht)

variable [T2Space X]
lemma CurveEdgeWitness.frontier_eq {V E : Set X} (w : CurveEdgeWitness V E) :
    closure E \ E = {w.leftPoint,w.rightPoint} := by
  conv_lhs => rw [w.piece_eq]
  exact w.arc.subarc_boundary_eq w.lower w.upper w.ordered

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConnectedOpenPieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connected open pieces with frontier in a deleted vertex set either
coincide or are disjoint. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem connected_open_pieces_equal_or_disjoint
    {S T V : Set X} (hSo : IsOpen S) (hTo : IsOpen T)
    (hSc : IsPreconnected S) (hTc : IsPreconnected T)
    (hSb : closure S \ S ⊆ V) (hTb : closure T \ T ⊆ V)
    (hSV : Disjoint S V) (hTV : Disjoint T V) : S = T ∨ Disjoint S T := by
  by_cases hd : Disjoint S T
  · exact Or.inr hd
  left
  have hi : (S ∩ T).Nonempty := not_disjoint_iff_nonempty_inter.mp hd
  have hTS : T ⊆ S := hTc.subset_of_closure_inter_subset hSo (by simpa only [inter_comm] using hi)
    (by
      intro x hx
      by_contra hn
      exact disjoint_left.mp hTV hx.2 (hSb ⟨hx.1,hn⟩))
  have hST : S ⊆ T := hSc.subset_of_closure_inter_subset hTo hi
    (by
      intro x hx
      by_contra hn
      exact disjoint_left.mp hSV hx.2 (hTb ⟨hx.1,hn⟩))
  exact Subset.antisymm hST hTS

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteIntervalChopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutting a real interval at a finite vertex set produces uniquely
determined consecutive open subintervals. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem exists_consecutive_interval (S : Finset ℝ) {x : ℝ} (hx : x ∉ S)
    (hleft : ∃ a ∈ S, a < x) (hright : ∃ b ∈ S, x < b) :
    ∃ a b, ConsecutiveVertices S a b ∧ a < x ∧ x < b := by
  classical
  let L := S.filter (fun a => a < x)
  let R := S.filter (fun b => x < b)
  have hL : L.Nonempty := by
    obtain ⟨a,ha,hax⟩ := hleft
    exact ⟨a,Finset.mem_filter.mpr ⟨ha,hax⟩⟩
  have hR : R.Nonempty := by
    obtain ⟨b,hb,hxb⟩ := hright
    exact ⟨b,Finset.mem_filter.mpr ⟨hb,hxb⟩⟩
  let a := L.max' hL
  let b := R.min' hR
  have ha : a ∈ S ∧ a < x := Finset.mem_filter.mp (L.max'_mem hL)
  have hb : b ∈ S ∧ x < b := Finset.mem_filter.mp (R.min'_mem hR)
  refine ⟨a,b,⟨ha.1,hb.1,ha.2.trans hb.2,?_⟩,ha.2,hb.2⟩
  intro t ht hab
  rcases lt_trichotomy t x with htx | rfl | hxt
  · have hta : t ≤ a := L.le_max' t (Finset.mem_filter.mpr ⟨ht,htx⟩)
    linarith [hab.1]
  · exact hx ht
  · have hbt : b ≤ t := R.min'_le t (Finset.mem_filter.mpr ⟨ht,hxt⟩)
    linarith [hab.2]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ArcVertexCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite ambient vertex set induces a finite ordered cut set in
each embedded arc. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem arc_vertex_coordinates (A : CompactCurveArc X) (V : Set X) (hV : V.Finite) :
    ∃ S : Finset ℝ,
      (∀ t : Icc A.left A.right, (t:ℝ) ∈ S ↔ A.map t ∈ V) ∧
      ∀ r ∈ S, A.left ≤ r ∧ r ≤ A.right := by
  classical
  have hpre : (A.map ⁻¹' V).Finite := hV.preimage A.embedding.injective.injOn
  let R : Set ℝ := Subtype.val '' (A.map ⁻¹' V)
  have hR : R.Finite := hpre.image Subtype.val
  refine ⟨hR.toFinset,?_,?_⟩
  · intro t
    rw [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨u,hu,he⟩
      change A.map u ∈ V at hu
      have hut : u = t := Subtype.ext he
      simpa only [hut] using hu
    · intro ht
      exact ⟨t,ht,rfl⟩
  · intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨t,_,rfl⟩ := hr
    exact t.property

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactArcSubdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Subdivide a compact embedded arc at every prescribed finite vertex.
The resulting pieces are connected open sets with frontier in that set. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem subdivide_compact_arc (A : CompactCurveArc X) (V : Set X) (hV : V.Finite)
    (hleft : A.map ⟨A.left,le_rfl,A.ordered.le⟩ ∈ V)
    (hright : A.map ⟨A.right,A.ordered.le,le_rfl⟩ ∈ V) :
    ∃ S : Finset ℝ,
      (∀ t : Icc A.left A.right, (t:ℝ) ∈ S ↔ A.map t ∈ V) ∧
      (∀ r ∈ S, A.left ≤ r ∧ r ≤ A.right) ∧
      (∀ x ∈ range A.map, x ∉ V → ∃ u v,
        ConsecutiveVertices S u v ∧ x ∈ A.openSubarc u v) ∧
      ∀ u v, ConsecutiveVertices S u v →
        IsOpen (A.openSubarc u v) ∧ IsConnected (A.openSubarc u v) ∧
        Disjoint (A.openSubarc u v) V ∧ closure (A.openSubarc u v) \ A.openSubarc u v ⊆ V := by
  classical
  obtain ⟨S,hS,hbound⟩ := arc_vertex_coordinates A V hV
  have hlS : A.left ∈ S := (hS ⟨A.left,le_rfl,A.ordered.le⟩).mpr hleft
  have hrS : A.right ∈ S := (hS ⟨A.right,A.ordered.le,le_rfl⟩).mpr hright
  refine ⟨S,hS,hbound,?_,?_⟩
  · rintro x ⟨t,rfl⟩ hx
    have htS : (t:ℝ) ∉ S := fun ht => hx ((hS t).mp ht)
    have hlt : A.left < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun h => htS (h ▸ hlS))
    have htr : (t:ℝ) < A.right := lt_of_le_of_ne t.property.2 (fun h => htS (h.symm ▸ hrS))
    obtain ⟨u,v,huv,hu,hv⟩ := exists_consecutive_interval S htS ⟨A.left,hlS,hlt⟩ ⟨A.right,hrS,htr⟩
    exact ⟨u,v,huv,t,⟨hu,hv⟩,rfl⟩
  · intro u v huv
    have hu := hbound u huv.1
    have hv := hbound v huv.2.1
    have hne := huv.2.2.1
    have huV : A.map ⟨u,hu⟩ ∈ V := (hS ⟨u,hu⟩).mp huv.1
    have hvV : A.map ⟨v,hv⟩ ∈ V := (hS ⟨v,hv⟩).mp huv.2.1
    refine ⟨A.openSubarc_open hu.1 hv.2,A.subarc_connected hu.1 hv.2 hne,?_,?_⟩
    · apply disjoint_left.mpr
      rintro x ⟨t,ht,rfl⟩ hxV
      exact huv.2.2.2 t ((hS t).mpr hxV) ht
    · intro x hx
      rcases A.subarc_frontier hu.1 hv.2 hne hx.1 hx.2 with he | he
      · exact he ▸ huV
      · exact he ▸ hvV

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteArcPieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite compact arc cover yields finitely many pairwise disjoint
connected open pieces after its finite vertices are deleted. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [Fintype ι]

theorem finite_arc_pieces (A : ι → CompactCurveArc X) (V : Set X) (hV : V.Finite)
    (hleft : ∀ i, (A i).map ⟨(A i).left,le_rfl,(A i).ordered.le⟩ ∈ V)
    (hright : ∀ i, (A i).map ⟨(A i).right,(A i).ordered.le,le_rfl⟩ ∈ V)
    (hcover : (univ : Set X) ⊆ ⋃ i, range (A i).map) :
    ∃ P : Finset (Set X),
      (∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V) ∧
      (∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F) ∧
      Vᶜ = ⋃ E ∈ P, E ∧ (∀ E ∈ P, Nonempty (CurveEdgeWitness V E)) := by
  classical
  choose S hS hbound hlocal hp using fun i => subdivide_compact_arc (A i) V hV (hleft i) (hright i)
  let L (i : ι) := ((S i) ×ˢ (S i)).filter (fun uv => ConsecutiveVertices (S i) uv.1 uv.2)
  let P := Finset.univ.biUnion fun i => (L i).image (fun uv => (A i).openSubarc uv.1 uv.2)
  have hmem (E : Set X) : E ∈ P ↔ ∃ i u v,
      ConsecutiveVertices (S i) u v ∧ E = (A i).openSubarc u v := by
    constructor
    · intro he
      obtain ⟨i,_,hei⟩ := Finset.mem_biUnion.mp he
      obtain ⟨uv,huv,heq⟩ := Finset.mem_image.mp hei
      exact ⟨i,uv.1,uv.2,(Finset.mem_filter.mp huv).2,heq.symm⟩
    · rintro ⟨i,u,v,huv,rfl⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨(u,v),?_,rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨huv.1,huv.2.1⟩,huv⟩
  have hprop : ∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V := by
    intro E he
    obtain ⟨i,u,v,huv,rfl⟩ := (hmem E).mp he
    exact hp i u v huv
  refine ⟨P,hprop,?_,?_,?_⟩
  · intro E he F hf hne
    have eprop := hprop E he
    have fprop := hprop F hf
    exact (connected_open_pieces_equal_or_disjoint eprop.1 fprop.1
      eprop.2.1.isPreconnected fprop.2.1.isPreconnected eprop.2.2.2 fprop.2.2.2
      eprop.2.2.1 fprop.2.2.1).resolve_left hne
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover (mem_univ x))
      obtain ⟨u,v,huv,hxuv⟩ := hlocal i x hi hx
      exact mem_iUnion₂.mpr ⟨(A i).openSubarc u v,(hmem _).mpr ⟨i,u,v,huv,rfl⟩,hxuv⟩
    · intro x hx
      obtain ⟨E,hE,hxE⟩ := mem_iUnion₂.mp hx
      exact fun hxV => disjoint_left.mp (hprop E hE).2.2.1 hxE hxV

  · intro E he
    obtain ⟨i,u,v,huv,rfl⟩ := (hmem E).mp he
    have hu := hbound i u huv.1
    have hv := hbound i v huv.2.1
    exact ⟨⟨A i,u,v,hu.1,hv.2,huv.2.2.1,rfl,
      (hS i _).mp huv.1,(hS i _).mp huv.2.1⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_HalfLineCompactArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact arcs at a half-line chart, including the boundary point in
an open neighborhood of the ambient curve. -/
noncomputable section
open Set Filter Metric Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem half_line_compact_arc_data (c : OpenPartialHomeomorph X (Ici (0:ℝ))) {p : X}
    (hp : p ∈ c.source) (hzero : c p = ⟨0,by simp⟩) :
    ∃ (A : CompactCurveArc X) (V : Set X), IsOpen V ∧ p ∈ V ∧ V ⊆ range A.map ∧
      A.map ⟨A.left,le_rfl,A.ordered.le⟩ = p ∧
      V \ {p} = A.openSubarc A.left A.right ∧ V ⊆ c.source := by
  let z : Ici (0:ℝ) := ⟨0,by simp⟩
  have hcz : c p = z := hzero
  have hz : z ∈ c.target := by rw [← hcz]; exact c.map_source hp
  obtain ⟨r,hr,hrt⟩ := nhds_basis_closedBall.mem_iff.mp (c.open_target.mem_nhds hz)
  have hT (t : Ici (0:ℝ)) (ht : (t:ℝ) ≤ r) : t ∈ c.target := by
    apply hrt
    change dist (t:ℝ) (0:ℝ) ≤ r
    have ht0 : 0 ≤ (t:ℝ) := t.property
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ht0] using ht
  let j : Icc (0:ℝ) r → Ici (0:ℝ) := fun t => ⟨t.val,t.property.1⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let γ : Icc (0:ℝ) r → X := fun t => c.symm (j t)
  have hγcont : Continuous γ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (c.symm.continuousAt (hT (j t) t.property.2)).comp hj.continuousAt
  have hγinj : Function.Injective γ := by
    intro s t hst
    have he := c.symm.injOn (hT (j s) s.property.2) (hT (j t) t.property.2) hst
    exact Subtype.ext (congrArg (fun u : Ici (0:ℝ) => (u:ℝ)) he)
  let O : Set (Ici (0:ℝ)) := {t | 0 < (t:ℝ) ∧ (t:ℝ) < r}
  have hO : IsOpen O := isOpen_Ioo.preimage continuous_subtype_val
  have hOT : O ⊆ c.target := fun t ht => hT t ht.2.le
  have heq : γ '' {t | 0 < (t:ℝ) ∧ (t:ℝ) < r} = c.symm '' O := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨j t,ht,rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t.val,ht.1.le,ht.2.le⟩,ht,rfl⟩
  let A : CompactCurveArc X := ⟨0,r,hr,γ,hγcont.isClosedEmbedding hγinj,
    by rw [heq]; exact c.isOpen_image_symm_of_subset_target hO hOT⟩
  let W : Set (Ici (0:ℝ)) := {t | (t:ℝ) < r}
  have hW : IsOpen W := isOpen_Iio.preimage continuous_subtype_val
  have hWT : W ⊆ c.target := fun t ht => hT t ht.le
  refine ⟨A,c.symm '' W,c.isOpen_image_symm_of_subset_target hW hWT,?_,?_,?_,?_,?_⟩
  · refine ⟨z,hr,?_⟩
    rw [← hcz,c.left_inv hp]
  · rintro x ⟨t,ht,rfl⟩
    exact ⟨⟨t.val,t.property,ht.le⟩,rfl⟩

  · change c.symm (j ⟨0,le_rfl,hr.le⟩) = p
    change c.symm z = p
    rw [← hcz,c.left_inv hp]
  · apply Subset.antisymm
    · rintro x ⟨⟨t,ht,rfl⟩,hne⟩
      have htpos : 0 < (t:ℝ) := by
        have ht0 : 0 ≤ (t:ℝ) := t.property
        apply lt_of_le_of_ne ht0
        intro he
        have htz : t = z := Subtype.ext he.symm
        apply hne
        change c.symm t = p
        rw [htz,← hcz,c.left_inv hp]
      exact ⟨⟨t.val,t.property,ht.le⟩,⟨htpos,ht⟩,rfl⟩
    · rintro x ⟨t,ht,rfl⟩
      refine ⟨⟨j t,ht.2,rfl⟩,?_⟩
      intro he
      change c.symm (j t) = p at he
      have heq : j t = z := c.symm.injOn (hT (j t) t.property.2) hz (by
        rw [he,← hcz,c.left_inv hp])
      have hv := congrArg (fun s : Ici (0:ℝ) => (s:ℝ)) heq
      have ht0 : (t:ℝ) = 0 := hv
      exact (ne_of_gt ht.1) ht0
  · rintro x ⟨t,ht,rfl⟩
    exact c.map_target (hWT ht)

theorem half_line_compact_arc (c : OpenPartialHomeomorph X (Ici (0:ℝ))) {p : X}
    (hp : p ∈ c.source) (hzero : c p = ⟨0,by simp⟩) :
    ∃ (A : CompactCurveArc X) (V : Set X), IsOpen V ∧ p ∈ V ∧ V ⊆ range A.map := by
  obtain ⟨A,V,hV,hpV,hAV,_,_,_⟩ := half_line_compact_arc_data c hp hzero
  exact ⟨A,V,hV,hpV,hAV⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteCurveArcCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactness reduces the actual local line and half-line charts to a
finite cover by compact embedded arcs with open interiors. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem finite_curve_arc_cover
    (hchart : ∀ x : X,
      (∃ c : OpenPartialHomeomorph X ℝ, x ∈ c.source) ∨
      (∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)), x ∈ c.source ∧ c x = ⟨0,by simp⟩)) :
    ∃ (A : X → CompactCurveArc X) (V : X → Set X) (s : Finset X),
      (∀ x, IsOpen (V x) ∧ x ∈ V x ∧ V x ⊆ range (A x).map) ∧
      (univ : Set X) ⊆ ⋃ x ∈ s, V x := by
  classical
  have hex (x : X) : ∃ (A : CompactCurveArc X) (V : Set X),
      IsOpen V ∧ x ∈ V ∧ V ⊆ range A.map := by
    rcases hchart x with ⟨c,hc⟩ | ⟨c,hc,hc0⟩
    · exact line_chart_compact_arc c hc
    · exact half_line_compact_arc c hc hc0
  choose A V hV hxV hsub using hex
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion.mpr ⟨x,hxV x⟩)
  exact ⟨A,V,s,fun x => ⟨hV x,hxV x,hsub x⟩,hs⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactCurvePieces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact curve with the proved line/half-line charts admits a finite
partition into open connected pieces and finitely many vertices. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

theorem compact_curve_pieces (D : Set X) (hD : D.Finite)
    (hchart : ∀ x : X,
      (∃ c : OpenPartialHomeomorph X ℝ, x ∈ c.source) ∨
      (∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)), x ∈ c.source ∧ c x = ⟨0,by simp⟩)) :
    ∃ (V : Set X) (P : Finset (Set X)), V.Finite ∧ D ⊆ V ∧
      (∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V) ∧
      (∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F) ∧ Vᶜ = ⋃ E ∈ P, E ∧ (∀ E ∈ P, Nonempty (CurveEdgeWitness V E)) := by
  classical
  obtain ⟨A,W,s,hW,hs⟩ := finite_curve_arc_cover hchart
  let A' : s → CompactCurveArc X := fun i => A i.val
  let l : s → X := fun i => (A' i).map ⟨(A' i).left,le_rfl,(A' i).ordered.le⟩
  let r : s → X := fun i => (A' i).map ⟨(A' i).right,(A' i).ordered.le,le_rfl⟩
  let V := D ∪ (range l ∪ range r)
  have hV : V.Finite := hD.union ((finite_range l).union (finite_range r))
  have hcover : (univ : Set X) ⊆ ⋃ i : s, range (A' i).map := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,(hW i).2.2 hxi⟩
  obtain ⟨P,hP,hd,hc,hE⟩ := finite_arc_pieces A' V hV
    (fun i => Or.inr (Or.inl (mem_range_self i)))
    (fun i => Or.inr (Or.inr (mem_range_self i))) hcover
  exact ⟨V,P,hV,subset_union_left,hP,hd,hc,hE⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryIncidentPiece
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A connected punctured boundary neighborhood meets exactly one
incident edge of the proved finite curve decomposition. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem unique_boundary_incident_piece (V : Set X) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) {p : X} (hp : p ∈ V)
    {W : Set X} (hW : IsOpen W) (hpW : p ∈ W)
    (hS : IsConnected (W \ {p})) (hSV : W \ {p} ⊆ Vᶜ)
    (hpS : p ∈ closure (W \ {p})) :
    ∃ E ∈ P, p ∈ closure E ∧ ∀ F ∈ P, p ∈ closure F → F = E := by
  classical
  obtain ⟨x,hx⟩ := hS.nonempty
  have hxV := hSV hx
  rw [hcover] at hxV
  obtain ⟨E,hE,hxE⟩ := mem_iUnion₂.mp hxV
  have hSE : W \ {p} ⊆ E :=
    hS.isPreconnected.subset_of_closure_inter_subset (hP E hE).1 ⟨x,hx,hxE⟩ (by
      intro y hy
      by_contra hn
      exact hSV hy.2 ((hP E hE).2.2 ⟨hy.1,hn⟩))
  refine ⟨E,hE,(closure_mono hSE) hpS,?_⟩
  intro F hF hpF
  obtain ⟨y,hyW,hyF⟩ := (mem_closure_iff.mp hpF) W hW hpW
  have hne : y ≠ p := by
    intro he
    exact disjoint_left.mp (hP F hF).2.1 hyF (he ▸ hp)
  have hyE := hSE ⟨hyW,by simpa only [mem_singleton_iff] using hne⟩
  by_contra hFE
  exact disjoint_left.mp (hdis F hF E hE hFE) hyF hyE

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_HalfLinePuncturedNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A boundary chart admits a connected punctured neighborhood avoiding
all other vertices of a prescribed finite set. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem half_line_punctured_neighborhood
    (c : OpenPartialHomeomorph X (Ici (0:ℝ))) {p : X}
    (hp : p ∈ c.source) (hzero : c p = ⟨0,by simp⟩)
    (V : Set X) (hV : V.Finite) :
    ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ IsConnected (W \ {p}) ∧
      W \ {p} ⊆ Vᶜ ∧ p ∈ closure (W \ {p}) := by
  have hD : IsClosed (V \ {p}) := (hV.subset sdiff_subset).isClosed
  let U : Set X := (V \ {p})ᶜ
  have hU : IsOpen U := hD.isOpen_compl
  have hpU : p ∈ U := by
    rintro ⟨_,hn⟩
    exact hn rfl
  let e := c.restrOpen U hU
  have hpe : p ∈ e.source := ⟨hp,hpU⟩
  have he0 : e p = ⟨0,by simp⟩ := hzero
  obtain ⟨A,W,hW,hpW,_,hleft,hWS,hWe⟩ := half_line_compact_arc_data e hpe he0
  refine ⟨W,hW,hpW,?_,?_,?_⟩
  · rw [hWS]
    exact A.subarc_connected le_rfl le_rfl A.ordered
  · rintro x ⟨hxW,hxp⟩ hxV
    exact (hWe hxW).2 ⟨hxV,hxp⟩
  · rw [hWS,A.subarc_closure le_rfl le_rfl A.ordered]
    exact ⟨⟨A.left,le_rfl,A.ordered.le⟩,⟨le_rfl,A.ordered.le⟩,hleft⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryDegreeOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary vertices of the actual finite decomposition have exactly
one incident open edge. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem boundary_vertex_degree_one (V : Set X) (hV : V.Finite) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) {p : X} (hp : p ∈ V)
    (c : OpenPartialHomeomorph X (Ici (0:ℝ))) (hc : p ∈ c.source)
    (hc0 : c p = ⟨0,by simp⟩) :
    ∃ E ∈ P, p ∈ closure E ∧ ∀ F ∈ P, p ∈ closure F → F = E := by
  obtain ⟨W,hW,hpW,hS,hSV,hpS⟩ := half_line_punctured_neighborhood c hc hc0 V hV
  exact unique_boundary_incident_piece V P hP hdis hcover hp hW hpW hS hSV hpS

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactSingletonFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact map with a singleton fiber detects convergence at that
fiber. This extends lifted double arcs to their diagonal endpoints. -/
noncomputable section
open Set Filter Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y A : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]

theorem tendsto_of_comp_singleton_fiber {f : X → Y} (hf : Continuous f) {x : X}
    (hfiber : ∀ z, f z = f x → z = x) {l : Filter A} {g : A → X}
    (h : Tendsto (f ∘ g) l (𝓝 (f x))) : Tendsto g l (𝓝 x) := by
  apply tendsto_nhds.mpr
  intro U hU hxU
  have hclosed : IsClosed (f '' Uᶜ) := (hU.isClosed_compl.isCompact.image hf).isClosed
  have hx : f x ∈ (f '' Uᶜ)ᶜ := by
    rintro ⟨z,hz,he⟩
    exact hz ((hfiber z he) ▸ hxU)
  have hevent := h (hclosed.isOpen_compl.mem_nhds hx)
  filter_upwards [hevent] with a ha
  by_contra hn
  exact ha ⟨g a,hn,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveEdgeParametrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained edge witnesses give actual compact interval
parametrizations of their closures. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
lemma CurveEdgeWitness.param_range {V E : Set X} (w : CurveEdgeWitness V E) :
    range w.param = closure E := by
  conv_rhs => rw [w.piece_eq,w.arc.subarc_closure w.lower w.upper w.ordered]
  apply Subset.antisymm
  · rintro x ⟨t,rfl⟩
    exact ⟨⟨t.val,w.lower.trans t.property.1,t.property.2.trans w.upper⟩,t.property,rfl⟩
  · rintro x ⟨t,ht,rfl⟩
    exact ⟨⟨t.val,ht⟩,rfl⟩

lemma CurveEdgeWitness.frontier_not_interior_closure {V E : Set X} (w : CurveEdgeWitness V E)
    (d : OpenPartialHomeomorph X ℝ) {p : X} (hp : p ∈ d.source)
    (hb : p ∈ closure E \ E) : p ∉ interior (closure E) := by
  have hend : p = w.param ⟨w.lo,le_rfl,w.ordered.le⟩ ∨
      p = w.param ⟨w.hi,w.ordered.le,le_rfl⟩ := by
    rw [w.frontier_eq] at hb
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (mem_singleton_iff.mp h)
  rw [← w.param_range]
  exact compact_arc_endpoint_not_interior d w.ordered.le w.param w.param_closedEmbedding.isEmbedding hp hend

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveIncidenceGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bipartite incidence graph remembers distinct parallel interval edges. -/
noncomputable section
open Set
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

lemma graph_degree_two {A : Type*} (G : SimpleGraph A) [Fintype A]
    (p a b : A) (hne : a ≠ b) (ha : G.Adj p a) (hb : G.Adj p b)
    (hall : ∀ z, G.Adj p z → z = a ∨ z = b) : G.degree p = 2 := by
  classical
  have hs : G.neighborSet p = {a,b} := by
    ext z
    constructor
    · exact hall z
    · rintro (rfl | hz)
      · exact ha
      · exact (mem_singleton_iff.mp hz) ▸ hb
  rw [← G.ncard_neighborSet,hs]
  simp [hne]

lemma curveIncidenceGraph_degree_left_one (V : Set X) (P : Finset (Set X)) [Fintype V]
    (v : V) (h : ∃ E ∈ P, v.val ∈ closure E ∧
      ∀ F ∈ P, v.val ∈ closure F → F = E) :
    (curveIncidenceGraph V P).degree (Sum.inl v) = 1 := by
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  obtain ⟨E,hE,hv,huniq⟩ := h
  refine ⟨Sum.inr ⟨E,hE⟩,hv,?_⟩
  rintro (w|F) hw
  · exact False.elim hw
  · exact congrArg Sum.inr (Subtype.ext (huniq F.val F.property hw))

lemma curveIncidenceGraph_degree_left_two (V : Set X) (P : Finset (Set X)) [Fintype V]
    (v : V) (h : ∃ E ∈ P, ∃ F ∈ P, E ≠ F ∧ v.val ∈ closure E ∧ v.val ∈ closure F ∧
      ∀ G ∈ P, v.val ∈ closure G → G = E ∨ G = F) :
    (curveIncidenceGraph V P).degree (Sum.inl v) = 2 := by
  obtain ⟨E,hE,F,hF,hne,hvE,hvF,hall⟩ := h
  apply graph_degree_two (curveIncidenceGraph V P) (Sum.inl v)
    (Sum.inr ⟨E,hE⟩) (Sum.inr ⟨F,hF⟩)
  · intro he
    exact hne (congrArg (fun z : P => z.val) (Sum.inr.inj he))
  · exact hvE
  · exact hvF
  · rintro (w|G) hg
    · exact False.elim hg
    · rcases hall G.val G.property hg with he | he
      · exact Or.inl (congrArg Sum.inr (Subtype.ext he))
      · exact Or.inr (congrArg Sum.inr (Subtype.ext he))

variable [T2Space X]
lemma curveIncidenceGraph_degree_right_two (V : Set X) (P : Finset (Set X)) [Fintype V]
    (E : P) (hdis : Disjoint E.val V) (w : CurveEdgeWitness V E.val) :
    (curveIncidenceGraph V P).degree (Sum.inr E) = 2 := by
  let l : V := ⟨w.leftPoint,w.left_mem⟩
  let r : V := ⟨w.rightPoint,w.right_mem⟩
  have hboundary : ∀ x ∈ V, x ∈ closure E.val ↔ x = w.leftPoint ∨ x = w.rightPoint := by
    intro x hxV
    have hn : x ∉ E.val := fun h => disjoint_left.mp hdis h hxV
    have h := w.frontier_eq
    constructor
    · intro hx
      have hb : x ∈ closure E.val \ E.val := ⟨hx,hn⟩
      rw [h] at hb
      simpa only [mem_insert_iff,mem_singleton_iff] using hb
    · intro hx
      have hb : x ∈ closure E.val \ E.val := by
        rw [h]
        simpa only [mem_insert_iff,mem_singleton_iff] using hx
      exact hb.1
  apply graph_degree_two (curveIncidenceGraph V P) (Sum.inr E) (Sum.inl l) (Sum.inl r)
  · intro he
    exact w.endpoints_ne (congrArg (fun z : V => z.val) (Sum.inl.inj he))
  · exact (hboundary _ w.left_mem).mpr (Or.inl rfl)
  · exact (hboundary _ w.right_mem).mpr (Or.inr rfl)
  · rintro (v|F) hv
    · rcases (hboundary _ v.property).mp hv with he | he
      · exact Or.inl (congrArg Sum.inl (Subtype.ext he))
      · exact Or.inr (congrArg Sum.inl (Subtype.ext he))
    · exact False.elim hv

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveEdgePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each retained compact interval edge is parametrized by an injective
path, in either orientation. -/
noncomputable section
open Set Topology unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

lemma CurveEdgeWitness.path_injective {V E : Set X} (w : CurveEdgeWitness V E) :
    Function.Injective w.path :=
  w.param_closedEmbedding.injective.comp (iccHomeoI w.lo w.hi w.ordered).symm.injective

lemma CurveEdgeWitness.path_range {V E : Set X} (w : CurveEdgeWitness V E) :
    range w.path = closure E := by
  change range (w.param ∘ (iccHomeoI w.lo w.hi w.ordered).symm) = _
  rw [range_comp,(iccHomeoI w.lo w.hi w.ordered).symm.surjective.range_eq,image_univ,w.param_range]

lemma CurveEdgeWitness.endpoint_iff {V E : Set X} (w : CurveEdgeWitness V E)
    (hdis : Disjoint E V) {p : X} (hp : p ∈ V) :
    p ∈ closure E ↔ p = w.leftPoint ∨ p = w.rightPoint := by
  have hnot : p ∉ E := fun h => disjoint_left.mp hdis h hp
  have he : p ∈ closure E ↔ p ∈ closure E \ E := by simp only [mem_sdiff,hnot,not_false_eq_true,and_true]
  rw [he,w.frontier_eq]
  simp only [mem_insert_iff,mem_singleton_iff]

lemma CurveEdgeWitness.oriented_path {V E : Set X} (w : CurveEdgeWitness V E)
    (hdis : Disjoint E V) {p q : X} (hp : p ∈ V) (hq : q ∈ V) (hne : p ≠ q)
    (hpE : p ∈ closure E) (hqE : q ∈ closure E) :
    ∃ γ : Path p q, Function.Injective γ ∧ range γ = closure E := by
  rcases (w.endpoint_iff hdis hp).mp hpE with hpl | hpr <;>
    rcases (w.endpoint_iff hdis hq).mp hqE with hql | hqr
  · exact False.elim (hne (hpl.trans hql.symm))
  · exact ⟨w.path.cast hpl hqr,w.path_injective,w.path_range⟩
  · refine ⟨w.path.symm.cast hpr hql,?_,?_⟩
    · exact w.path_injective.comp unitInterval.symm_bijective.injective
    · simpa only [Path.cast_coe,Path.symm_range] using w.path_range
  · exact False.elim (hne (hpr.trans hqr.symm))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveEdgeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localization of a full edge path at its two graph vertices and its
single open interval edge. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem curve_edge_frontier_endpoints {V : Set X} {E : Set X}
    (w : CurveEdgeWitness V E) (hdis : Disjoint E V) (a b : V) (hne : a ≠ b)
    (ha : a.val ∈ closure E) (hb : b.val ∈ closure E) :
    closure E \ E = {a.val,b.val} := by
  have hne' : a.val ≠ b.val := fun h => hne (Subtype.ext h)
  rcases (w.endpoint_iff hdis a.property).mp ha with hal | har <;>
    rcases (w.endpoint_iff hdis b.property).mp hb with hbl | hbr
  · exact False.elim (hne' (hal.trans hbl.symm))
  · rw [w.frontier_eq,hal,hbr]
  · rw [w.frontier_eq,har,hbl,pair_comm]
  · exact False.elim (hne' (har.trans hbr.symm))

theorem curve_edge_path_localization {V : Set X} {P : Finset (Set X)}
    (hP : ∀ E ∈ P, Disjoint E V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (E : P) (w : CurveEdgeWitness V E.val) (a b : V) (hne : a ≠ b)
    (ha : a.val ∈ closure E.val) (hb : b.val ∈ closure E.val)
    (γ : Path a.val b.val) (hrange : range γ = closure E.val) :
    (∀ v : V, v.val ∈ range γ → v = a ∨ v = b) ∧
    (∀ F : P, (range γ ∩ F.val).Nonempty → F = E) := by
  have hfront := curve_edge_frontier_endpoints w (hP E.val E.property) a b hne ha hb
  constructor
  · intro v hv
    have hn : v.val ∉ E.val := fun h => disjoint_left.mp (hP E.val E.property) h v.property
    have hv' : v.val ∈ closure E.val \ E.val := ⟨hrange ▸ hv,hn⟩
    rw [hfront] at hv'
    rcases hv' with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext (mem_singleton_iff.mp he))
  · rintro F ⟨x,hxγ,hxF⟩
    by_contra hFE
    have hxcl : x ∈ closure E.val := hrange ▸ hxγ
    by_cases hxE : x ∈ E.val
    · exact disjoint_left.mp (hdis F.val F.property E.val E.property
        (fun h => hFE (Subtype.ext h))) hxF hxE
    · have hxV : x ∈ V := by
        have hx : x ∈ closure E.val \ E.val := ⟨hxcl,hxE⟩
        rw [w.frontier_eq] at hx
        rcases hx with he | he
        · exact he ▸ w.left_mem
        · exact (mem_singleton_iff.mp he) ▸ w.right_mem
      exact disjoint_left.mp (hP F.val F.property) hxF hxV

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DegreeOneReachability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite graph of degrees one and two joins each degree-one vertex
to a distinct degree-one vertex by a simple path. -/
noncomputable section
open Set
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem degree_one_reaches_degree_one {A : Type*} [Fintype A]
    (G : SimpleGraph A) (hdegrees : ∀ x, G.degree x = 1 ∨ G.degree x = 2)
    (p : A) (hp : G.degree p = 1) :
    ∃ q : A, q ≠ p ∧ G.degree q = 1 ∧ Nonempty (G.Path p q) := by
  classical
  let C : Set A := {x | G.Reachable p x}
  let H := G.induce C
  let p' : C := ⟨p,SimpleGraph.Reachable.rfl⟩
  have hdegree (x : C) : H.degree x = G.degree x.val :=
    G.degree_induce_of_neighborSet_subset (fun _ hy => x.property.trans hy.reachable)
  have hodd : Odd (H.degree p') := by rw [hdegree,hp]; decide
  obtain ⟨q,hne,hq⟩ := H.exists_ne_odd_degree_of_exists_odd_degree p' hodd
  have hqp : q.val ≠ p := by
    intro he
    exact hne (Subtype.ext he)
  have hq1 : G.degree q.val = 1 := by
    rw [hdegree] at hq
    rcases hdegrees q.val with h | h
    · exact h
    · rw [h] at hq
      norm_num at hq
  obtain ⟨w,hw⟩ := q.property.exists_isPath
  exact ⟨q.val,hqp,hq1,⟨⟨w,hw⟩⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LinePuncturedNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At an ordinary curve point, deleting the point from a sufficiently
small vertex-free neighborhood leaves two connected sides. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem line_punctured_neighborhood
    (c : OpenPartialHomeomorph X ℝ) {p : X} (hp : p ∈ c.source)
    (V : Set X) (hV : V.Finite) :
    ∃ W S T : Set X, IsOpen W ∧ p ∈ W ∧ IsConnected S ∧ IsConnected T ∧
      Disjoint S T ∧ W \ {p} = S ∪ T ∧ S ∪ T ⊆ Vᶜ ∧
      p ∈ closure S ∧ p ∈ closure T := by
  have hD : IsClosed (V \ {p}) := (hV.subset sdiff_subset).isClosed
  let U : Set X := (V \ {p})ᶜ
  have hU : IsOpen U := hD.isOpen_compl
  have hpU : p ∈ U := by rintro ⟨_,hn⟩; exact hn rfl
  let e := c.restrOpen U hU
  obtain ⟨A,W,hW,hpW,_,t,hlt,htr,htp,heq,hWe⟩ := line_chart_compact_arc_data e ⟨hp,hpU⟩
  let S := A.openSubarc A.left t.val
  let T := A.openSubarc t.val A.right
  have hsplit : W \ {p} = S ∪ T := by
    rw [heq]
    apply Subset.antisymm
    · rintro x ⟨⟨u,hu,rfl⟩,hne⟩
      have hut : u ≠ t := by intro h; apply hne; rw [h,htp]; rfl
      have hval : (u:ℝ) ≠ (t:ℝ) := fun h => hut (Subtype.ext h)
      rcases lt_or_gt_of_ne hval with h | h
      · exact Or.inl ⟨u,⟨hu.1,h⟩,rfl⟩
      · exact Or.inr ⟨u,⟨h,hu.2⟩,rfl⟩
    · intro x hx
      rcases hx with ⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩
      · refine ⟨⟨u,⟨hu.1,hu.2.trans htr⟩,rfl⟩,?_⟩
        intro he
        have he' : A.map u = A.map t := by simpa only [mem_singleton_iff, htp] using he
        have hu' := congrArg Subtype.val (A.embedding.injective he')
        exact (ne_of_lt hu.2) hu'
      · refine ⟨⟨u,⟨hlt.trans hu.1,hu.2⟩,rfl⟩,?_⟩
        intro he
        have he' : A.map u = A.map t := by simpa only [mem_singleton_iff, htp] using he
        have hu' := congrArg Subtype.val (A.embedding.injective he')
        exact (ne_of_gt hu.1) hu'
  have hdis : Disjoint S T := by
    apply disjoint_left.mpr
    rintro x ⟨s,hs,rfl⟩ ⟨u,hu,he⟩
    have heq := congrArg Subtype.val (A.embedding.injective he)
    linarith [hs.2,hu.1]
  refine ⟨W,S,T,hW,hpW,A.subarc_connected le_rfl htr.le hlt,
    A.subarc_connected hlt.le le_rfl htr,hdis,hsplit,?_,?_,?_⟩
  · intro x hx hxV
    have hxW := hsplit.symm ▸ hx
    exact (hWe hxW.1).2 ⟨hxV,hxW.2⟩
  · rw [show S = A.openSubarc A.left t.val from rfl,A.subarc_closure le_rfl htr.le hlt]
    exact ⟨t,⟨t.property.1,le_rfl⟩,htp⟩
  · rw [show T = A.openSubarc t.val A.right from rfl,A.subarc_closure hlt.le le_rfl htr]
    exact ⟨t,⟨le_rfl,t.property.2⟩,htp⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OrdinaryDegreeTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary vertices of the interval decomposition have exactly two incident edges. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
private theorem connected_subset_piece (V : Set X) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hcover : Vᶜ = ⋃ E ∈ P, E) {S : Set X} (hS : IsConnected S)
    (hSV : S ⊆ Vᶜ) : ∃ E ∈ P, S ⊆ E := by
  obtain ⟨x,hx⟩ := hS.nonempty
  have hxV := hSV hx
  rw [hcover] at hxV
  obtain ⟨E,hE,hxE⟩ := mem_iUnion₂.mp hxV
  refine ⟨E,hE,hS.isPreconnected.subset_of_closure_inter_subset (hP E hE).1
    ⟨x,hx,hxE⟩ ?_⟩
  intro y hy
  by_contra hn
  exact hSV hy.2 ((hP E hE).2.2 ⟨hy.1,hn⟩)

theorem ordinary_vertex_degree_two (V : Set X) (hV : V.Finite) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E)
    (hwitness : ∀ E ∈ P, Nonempty (CurveEdgeWitness V E))
    {p : X} (hp : p ∈ V) (c : OpenPartialHomeomorph X ℝ) (hc : p ∈ c.source) :
    ∃ E ∈ P, ∃ F ∈ P, E ≠ F ∧ p ∈ closure E ∧ p ∈ closure F ∧
      ∀ G ∈ P, p ∈ closure G → G = E ∨ G = F := by
  classical
  obtain ⟨W,S,T,hW,hpW,hS,hT,_,hsplit,hSV,hpS,hpT⟩ :=
    line_punctured_neighborhood c hc V hV
  obtain ⟨E,hE,hSE⟩ := connected_subset_piece V P hP hcover hS
    (fun _ hx => hSV (Or.inl hx))
  obtain ⟨F,hF,hTF⟩ := connected_subset_piece V P hP hcover hT
    (fun _ hx => hSV (Or.inr hx))
  have hpE : p ∈ closure E := closure_mono hSE hpS
  have hpF : p ∈ closure F := closure_mono hTF hpT
  have hEF : E ≠ F := by
    intro heq
    have hWE : W ⊆ closure E := by
      intro x hx
      by_cases hxp : x = p
      · simpa only [hxp] using hpE
      · have hxs : x ∈ W \ {p} := ⟨hx,by simpa only [mem_singleton_iff] using hxp⟩
        rw [hsplit] at hxs
        rcases hxs with hs | ht
        · exact subset_closure (hSE hs)
        · exact subset_closure (heq.symm ▸ hTF ht)
    have hpInt : p ∈ interior (closure E) := interior_maximal hWE hW hpW
    have hpnot : p ∉ E := fun h => disjoint_left.mp (hP E hE).2.1 h hp
    exact (Classical.choice (hwitness E hE)).frontier_not_interior_closure c hc
      ⟨hpE,hpnot⟩ hpInt
  refine ⟨E,hE,F,hF,hEF,hpE,hpF,?_⟩
  intro G hG hpG
  obtain ⟨x,hxW,hxG⟩ := (mem_closure_iff.mp hpG) W hW hpW
  have hxp : x ≠ p := by
    intro heq
    exact disjoint_left.mp (hP G hG).2.1 hxG (heq ▸ hp)
  have hxST : x ∈ S ∪ T := hsplit ▸ ⟨hxW,by simpa only [mem_singleton_iff] using hxp⟩
  rcases hxST with hxS | hxT
  · left
    by_contra hGE
    exact disjoint_left.mp (hdis G hG E hE hGE) hxG (hSE hxS)
  · right
    by_contra hGF
    exact disjoint_left.mp (hdis G hG F hF hGF) hxG (hTF hxT)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveIncidenceBoundaryPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every boundary point of a compact curve is connected to a different
boundary point in its actual finite interval incidence graph. -/
noncomputable section
open Set Topology
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem curve_incidence_degrees (D V : Set X) (hV : V.Finite) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) (hwitness : ∀ E ∈ P, Nonempty (CurveEdgeWitness V E))
    (hline : ∀ p ∉ D, ∃ c : OpenPartialHomeomorph X ℝ, p ∈ c.source)
    (hhalf : ∀ p ∈ D, ∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)),
      p ∈ c.source ∧ c p = ⟨0,by simp⟩) [Fintype V] :
    (∀ p : V, (curveIncidenceGraph V P).degree (Sum.inl p) = if p.val ∈ D then 1 else 2) ∧
    (∀ E : P, (curveIncidenceGraph V P).degree (Sum.inr E) = 2) := by
  constructor
  · intro p
    by_cases hp : p.val ∈ D
    · simp only [hp, ↓reduceIte]
      obtain ⟨c,hc,hc0⟩ := hhalf p.val hp
      exact curveIncidenceGraph_degree_left_one V P p
        (boundary_vertex_degree_one V hV P hP hdis hcover p.property c hc hc0)
    · simp only [hp, ↓reduceIte]
      obtain ⟨c,hc⟩ := hline p.val hp
      exact curveIncidenceGraph_degree_left_two V P p
        (ordinary_vertex_degree_two V hV P hP hdis hcover hwitness p.property c hc)
  · intro E
    exact curveIncidenceGraph_degree_right_two V P E (hP E.val E.property).2.1
      (Classical.choice (hwitness E.val E.property))

theorem curve_boundary_pair (D V : Set X) (hDV : D ⊆ V) (hV : V.Finite)
    (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) (hwitness : ∀ E ∈ P, Nonempty (CurveEdgeWitness V E))
    (hline : ∀ p ∉ D, ∃ c : OpenPartialHomeomorph X ℝ, p ∈ c.source)
    (hhalf : ∀ p ∈ D, ∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)),
      p ∈ c.source ∧ c p = ⟨0,by simp⟩)
    (p : D) : ∃ (q : D), q ≠ p ∧ Nonempty
      ((curveIncidenceGraph V P).Path (Sum.inl ⟨p.val,hDV p.property⟩)
        (Sum.inl ⟨q.val,hDV q.property⟩)) := by
  let : Fintype V := hV.fintype
  let G := curveIncidenceGraph V P
  obtain ⟨hl,hr⟩ := curve_incidence_degrees D V hV P hP hdis hcover hwitness hline hhalf
  have hdegrees : ∀ x, G.degree x = 1 ∨ G.degree x = 2 := by
    rintro (v|E)
    · rw [hl]
      split_ifs <;> simp
    · exact Or.inr (hr E)
  have hp : G.degree (Sum.inl ⟨p.val,hDV p.property⟩) = 1 := by
    rw [hl]
    simp only [p.property, ↓reduceIte]
  obtain ⟨q,hqp,hq,hpath⟩ := degree_one_reaches_degree_one G hdegrees
    (Sum.inl ⟨p.val,hDV p.property⟩) hp
  cases q with
  | inr E => rw [hr] at hq; norm_num at hq
  | inl v =>
    have hvD : v.val ∈ D := by
      rw [hl] at hq
      by_contra hn
      simp only [hn, ↓reduceIte] at hq
      norm_num at hq
    refine ⟨⟨v.val,hvD⟩,?_,hpath⟩
    intro he
    exact hqp (congrArg Sum.inl (Subtype.ext (congrArg (fun z : D => z.val) he)))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InjectivePathConcatenation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concatenating two embedded arcs meeting only at their common endpoint. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] {x y z : X}

theorem path_trans_injective (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hsep : ∀ s t, γ s = δ t → s = 1 ∧ t = 0) : Function.Injective (γ.trans δ) := by
  intro s t h
  apply Subtype.ext
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · have hv := congrArg (fun u : I => (u:ℝ)) (hγ h)
    dsimp only at hv
    linarith
  · obtain ⟨ha,hb⟩ := hsep _ _ h
    have ha' := congrArg (fun u : I => (u:ℝ)) ha
    have hb' := congrArg (fun u : I => (u:ℝ)) hb
    dsimp only at ha' hb'
    norm_num at ha' hb'
    linarith
  · obtain ⟨ha,hb⟩ := hsep _ _ h.symm
    have ha' := congrArg (fun u : I => (u:ℝ)) ha
    have hb' := congrArg (fun u : I => (u:ℝ)) hb
    dsimp only at ha' hb'
    norm_num at ha' hb'
    linarith
  · have hv := congrArg (fun u : I => (u:ℝ)) (hδ h)
    dsimp only at hv
    linarith

theorem path_trans_injective_of_range (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hmeet : range γ ∩ range δ ⊆ {y}) : Function.Injective (γ.trans δ) := by
  apply path_trans_injective γ δ hγ hδ
  intro s t h
  have hy : γ s = y := mem_singleton_iff.mp (hmeet ⟨mem_range_self s,⟨t,h.symm⟩⟩)
  constructor
  · apply hγ
    simpa only [Path.target] using hy
  · apply hδ
    simpa only [Path.source] using h.symm.trans hy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_EmbeddedCurveGraphPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A simple path in the interval incidence graph has an actual
embedded realization in the compact curve. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem realize_simple_curve_walk {V : Set X} {P : Finset (Set X)}
    (hP : ∀ E ∈ P, Disjoint E V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (w : ∀ E : P, CurveEdgeWitness V E.val)
    {a b : V} (p : (curveIncidenceGraph V P).Walk (Sum.inl a) (Sum.inl b))
    (hp : p.IsPath) : Nonempty (RealizedCurveWalk p) := by
  classical
  suffices ∀ n (a b : V) (p : (curveIncidenceGraph V P).Walk (Sum.inl a) (Sum.inl b)),
      p.length = n → p.IsPath → Nonempty (RealizedCurveWalk p) by
    exact this p.length a b p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b p hn hp
    cases p with
    | nil =>
      refine ⟨⟨Path.refl a.val,?_,?_,?_⟩⟩
      · intro h
        exact False.elim (h rfl)
      · rintro v ⟨t,ht⟩
        have hv : v = a := Subtype.ext ht.symm
        simp [hv]
      · rintro E ⟨x,⟨t,ht⟩,hxE⟩
        have hx : x = a.val := ht.symm
        exact False.elim (disjoint_left.mp (hP E.val E.property) hxE (hx ▸ a.property))
    | cons h p =>
      rename_i c
      cases c with
      | inl c => exact False.elim h
      | inr E =>
        cases p with
        | cons h' q =>
          rename_i c
          cases c with
          | inr F => exact False.elim h'
          | inl c =>
            obtain ⟨hp',haNot⟩ := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hp
            obtain ⟨hq,hENot⟩ := (SimpleGraph.Walk.cons_isPath_iff _ _).mp hp'
            have hac : a ≠ c := by
              intro he
              apply haNot
              simp [he]
            obtain ⟨σ,hσ,hσrange⟩ := (w E).oriented_path (hP E.val E.property)
              a.property c.property (fun he => hac (Subtype.ext he)) h h'
            obtain ⟨hσV,hσE⟩ := curve_edge_path_localization hP hdis E (w E) a c hac h h' σ hσrange
            by_cases hcb : c = b
            · subst b
              refine ⟨⟨σ,fun _ => hσ,?_,?_⟩⟩
              · intro v hv
                rcases hσV v hv with he | he <;> simp [he]
              · intro F hF
                have he := hσE F hF
                simp [he]
            · have hqn : q.length < n := by
                simp only [SimpleGraph.Walk.length_cons] at hn
                omega
              obtain ⟨r⟩ := ih q.length hqn c b q rfl hq
              have hmeet : range σ ∩ range r.path ⊆ {c.val} := by
                rintro x ⟨hxσ,hxr⟩
                by_cases hxE : x ∈ E.val
                · exact False.elim (hENot (r.edge E ⟨x,hxr,hxE⟩))
                · have hfront : x ∈ closure E.val \ E.val := ⟨hσrange ▸ hxσ,hxE⟩
                  rw [curve_edge_frontier_endpoints (w E) (hP E.val E.property) a c hac h h'] at hfront
                  rcases hfront with he | he
                  · have ha : a.val ∈ range r.path := he ▸ hxr
                    exact False.elim (haNot (by simp [r.vertex a ha]))
                  · exact he
              refine ⟨⟨σ.trans r.path,fun _ => path_trans_injective_of_range σ r.path hσ
                (r.injective hcb) hmeet,?_,?_⟩⟩
              · intro v hv
                rw [Path.trans_range] at hv
                rcases hv with hv | hv
                · rcases hσV v hv with he | he <;> simp [he]
                · simp [r.vertex v hv]
              · intro F hF
                obtain ⟨x,hx,hxF⟩ := hF
                rw [Path.trans_range] at hx
                rcases hx with hx | hx
                · have he := hσE F ⟨x,hx,hxF⟩
                  simp [he]
                · simp [r.edge F ⟨x,hx,hxF⟩]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OpenIntervalExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend a map on the open unit interval by prescribed endpoint
values. Continuity in the interior is independent of endpoint limits. -/
noncomputable section
open Set Topology unitInterval
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*}

lemma openIntervalExtension_interior (F : Ioo (0:ℝ) 1 → X) (x y : X)
    (t : I) (ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1) :
    openIntervalExtension F x y t = F ⟨t.val,ht⟩ := by
  have h0 : t ≠ 0 := by intro h; subst t; norm_num at ht
  have h1 : t ≠ 1 := by intro h; subst t; norm_num at ht
  simp only [openIntervalExtension,h0,h1,↓reduceDIte]
  rfl

variable [TopologicalSpace X]

lemma openIntervalExtension_continuousOn (F : Ioo (0:ℝ) 1 → X) (hF : Continuous F)
    (x y : X) : ContinuousOn (openIntervalExtension F x y) {t : I | 0 < (t:ℝ) ∧ (t:ℝ) < 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let k : {t : I | 0 < (t:ℝ) ∧ (t:ℝ) < 1} → Ioo (0:ℝ) 1 :=
    fun t => ⟨t.val.val,t.property⟩
  have hk : Continuous k :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he : {t : I | 0 < (t:ℝ) ∧ (t:ℝ) < 1}.domRestrict (openIntervalExtension F x y) = F ∘ k := by
    funext t
    exact openIntervalExtension_interior F x y t.val t.property
  rw [he]
  exact hF.comp hk

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UnorderedPairCovering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unordered-pair quotient is a two-sheeted covering away from
the diagonal. At a diagonal point its fiber is a singleton. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*}

lemma unorderedPair_diagonal_iff (z : M × M) (p : M) :
    unorderedPair z = unorderedPair (p,p) ↔ z = (p,p) := by
  rw [unorderedPair_eq]
  simp only [Prod.swap_prod_mk,or_self]

lemma unorderedPair_mem_distinct_iff (z : M × M) :
    unorderedPair z ∈ unorderedDistinctPairs M ↔ z.1 ≠ z.2 := by
  constructor
  · intro hz he
    exact hz ⟨z.1,by rw [show (z.1,z.1) = z from Prod.ext rfl he]⟩
  · intro hz ⟨p,hp⟩
    have he := (unorderedPair_diagonal_iff z p).mp hp.symm
    exact hz (by rw [he])

variable [TopologicalSpace M] [T2Space M] [CompactSpace M]
theorem unorderedPair_covering :
    IsCoveringMapOn (unorderedPair : M × M → UnorderedSurfacePairs M) (unorderedDistinctPairs M) := by
  apply IsCoveringMapOn.of_isLocalHomeomorphOn unorderedPair_continuous
  intro z hz
  have hne : z.1 ≠ z.2 := (unorderedPair_mem_distinct_iff z).mp hz
  obtain ⟨e,he,heq,_⟩ := unordered_pair_local_chart z.1 z.2 hne
  exact ⟨e,he,funext fun z => (heq z).symm⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OpenDoubleArcLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lift an interior double arc to a continuous ordered pair. -/
noncomputable section
open Set Topology unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]

theorem open_double_arc_lift (γ : C(I, UnorderedSurfacePairs M))
    (hγ : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∈ unorderedDistinctPairs M) :
    ∃ F : C(Ioo (0:ℝ) 1, M × M), ∀ t,
      unorderedPair (F t) = γ ⟨t.val,t.property.1.le,t.property.2.le⟩ := by
  let A := Ioo (0:ℝ) 1
  let a : A := ⟨1/2,by constructor <;> norm_num⟩
  let : ContractibleSpace A := (convex_Ioo (0:ℝ) 1).contractibleSpace ⟨a.val,a.property⟩
  let : LocallyPathConnectedSpace A := isOpen_Ioo.locallyPathConnectedSpace
  let f : C(A,UnorderedSurfacePairs M) := ⟨fun t => γ ⟨t.val,t.property.1.le,t.property.2.le⟩,
    γ.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  obtain ⟨e,he⟩ := Quotient.exists_rep (f a)
  have he' : unorderedPair e = f a := he
  obtain ⟨F,⟨_,hF⟩,_⟩ := unorderedPair_covering.existsUnique_continuousMap_lifts f he'
    (fun t => hγ _ t.property.1 t.property.2)
  exact ⟨F,fun t => congrFun hF t⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ClosedDoubleArcLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An ordered lift of a double arc extends continuously to its two
crosscap endpoints, since each diagonal fiber is a singleton. -/
noncomputable section
open Set Filter Topology unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]

theorem closed_double_arc_lift (p q : M)
    (γ : Path (unorderedPair (p,p)) (unorderedPair (q,q)))
    (hγ : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∈ unorderedDistinctPairs M) :
    ∃ Γ : Path (p,p) (q,q), ∀ t, unorderedPair (Γ t) = γ t := by
  obtain ⟨F,hF⟩ := open_double_arc_lift γ.toContinuousMap hγ
  let G := openIntervalExtension F (p,p) (q,q)
  have hG0 : G 0 = (p,p) := openIntervalExtension_zero F _ _
  have hG1 : G 1 = (q,q) := openIntervalExtension_one F _ _
  have hG : ∀ t, unorderedPair (G t) = γ t := by
    intro t
    by_cases h0 : t = 0
    · subst t
      rw [hG0,γ.source]
    by_cases h1 : t = 1
    · subst t
      rw [hG1,γ.target]
    have ht := (intervalInteriorPoint t h0 h1).property
    rw [show G t = F ⟨t.val,ht⟩ from openIntervalExtension_interior F _ _ t ht]
    exact hF ⟨t.val,ht⟩
  have hbase : Continuous (unorderedPair ∘ G) := by
    have he : unorderedPair ∘ G = γ := funext hG
    rw [he]
    exact γ.continuous
  have hcont : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro t
    by_cases h0 : t = 0
    · subst t
      change Tendsto G (𝓝 0) (𝓝 (G 0))
      rw [hG0]
      apply tendsto_of_comp_singleton_fiber unorderedPair_continuous
        (fun z hz => (unorderedPair_diagonal_iff z p).mp hz)
      have hc : Tendsto (unorderedPair ∘ G) (𝓝 (0:I)) (𝓝 (unorderedPair (G 0))) := hbase.continuousAt
      simpa only [hG0] using hc
    by_cases h1 : t = 1
    · subst t
      change Tendsto G (𝓝 1) (𝓝 (G 1))
      rw [hG1]
      apply tendsto_of_comp_singleton_fiber unorderedPair_continuous
        (fun z hz => (unorderedPair_diagonal_iff z q).mp hz)
      have hc : Tendsto (unorderedPair ∘ G) (𝓝 (1:I)) (𝓝 (unorderedPair (G 1))) := hbase.continuousAt
      simpa only [hG1] using hc
    · have ht := (intervalInteriorPoint t h0 h1).property
      have hU : IsOpen {t : I | 0 < (t:ℝ) ∧ (t:ℝ) < 1} :=
        isOpen_Ioo.preimage continuous_subtype_val
      exact (openIntervalExtension_continuousOn F F.continuous _ _).continuousAt (hU.mem_nhds ht)
  exact ⟨⟨⟨G,hcont⟩,hG0,hG1⟩,hG⟩

theorem embedded_closed_double_arc_lift (p q : M)
    (γ : Path (unorderedPair (p,p)) (unorderedPair (q,q))) (hinj : Function.Injective γ)
    (hγ : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∈ unorderedDistinctPairs M) :
    ∃ Γ : Path (p,p) (q,q), IsClosedEmbedding Γ ∧ ∀ t, unorderedPair (Γ t) = γ t := by
  obtain ⟨Γ,hΓ⟩ := closed_double_arc_lift p q γ hγ
  have hΓinj : Function.Injective Γ := by
    intro s t h
    apply hinj
    rw [← hΓ s,← hΓ t,h]
  exact ⟨Γ,Γ.continuous.isClosedEmbedding hΓinj,hΓ⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CurveBoundaryEmbeddedArc
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual embedded interval joins two boundary points and has no
other boundary point in its interior. -/
noncomputable section
open Set Topology unitInterval
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem curve_boundary_embedded_arc (D V : Set X) (hDV : D ⊆ V) (hV : V.Finite)
    (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) (hwitness : ∀ E ∈ P, Nonempty (CurveEdgeWitness V E))
    (hline : ∀ p ∉ D, ∃ c : OpenPartialHomeomorph X ℝ, p ∈ c.source)
    (hhalf : ∀ p ∈ D, ∃ c : OpenPartialHomeomorph X (Ici (0:ℝ)),
      p ∈ c.source ∧ c p = ⟨0,by simp⟩)
    (p : D) : ∃ q : D, q ≠ p ∧ ∃ γ : Path p.val q.val, IsClosedEmbedding γ ∧
      ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∉ D := by
  classical
  let : Fintype V := hV.fintype
  let G := curveIncidenceGraph V P
  let a : V := ⟨p.val,hDV p.property⟩
  obtain ⟨q,hqp,⟨r⟩⟩ := curve_boundary_pair D V hDV hV P hP hdis hcover hwitness hline hhalf p
  let b : V := ⟨q.val,hDV q.property⟩
  let w (E : P) := Classical.choice (hwitness E.val E.property)
  obtain ⟨ρ⟩ := realize_simple_curve_walk (fun E hE => (hP E hE).2.1) hdis w r.val r.property
  have hab : a ≠ b := by
    intro he
    exact hqp (Subtype.ext (congrArg (fun v : V => v.val) he).symm)
  have hρ := ρ.injective hab
  obtain ⟨hl,_⟩ := curve_incidence_degrees D V hV P hP hdis hcover hwitness hline hhalf
  refine ⟨q,hqp,ρ.path,ρ.path.continuous.isClosedEmbedding hρ,?_⟩
  intro t ht0 ht1 htD
  let v : V := ⟨ρ.path t,hDV htD⟩
  have hva : v ≠ a := by
    intro he
    have hx : ρ.path t = ρ.path 0 := by simpa using congrArg (fun v : V => v.val) he
    have ht : (t:ℝ) = 0 := congrArg (fun t : I => (t:ℝ)) (hρ hx)
    linarith
  have hvb : v ≠ b := by
    intro he
    have hx : ρ.path t = ρ.path 1 := by simpa using congrArg (fun v : V => v.val) he
    have ht : (t:ℝ) = 1 := congrArg (fun t : I => (t:ℝ)) (hρ hx)
    linarith
  have hdeg : G.degree (Sum.inl v) = 1 := by
    rw [hl]
    change (if ρ.path t ∈ D then 1 else 2) = 1
    simp only [htD,↓reduceIte]
  obtain ⟨z,hz,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg
  have hsub : (G.neighborSet (Sum.inl v)).Subsingleton := by
    intro x hx y hy
    exact (hunique x hx).trans (hunique y hy).symm
  have hnot := r.property.isTrail.not_mem_support_of_subsingleton_neighborSet
    (fun he => hva (Sum.inl.inj he)) (fun he => hvb (Sum.inl.inj he)) hsub
  exact hnot (ρ.vertex v (mem_range_self t))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleCurveBoundaryPaths
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prepared self-transverse surface map has actual finite paths
joining every crosscap endpoint to another crosscap endpoint. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_double_curve_boundary_paths {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ (V : Set (compactifiedDoubleCurve f)) (P : Finset (Set (compactifiedDoubleCurve f))),
      V.Finite ∧ doubleCurveBoundary f ⊆ V ∧
      (∀ E ∈ P, IsOpen E ∧ IsConnected E ∧ Disjoint E V ∧ closure E \ E ⊆ V) ∧
      (∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F) ∧ Vᶜ = ⋃ E ∈ P, E ∧
      (∀ E ∈ P, Nonempty (CurveEdgeWitness V E)) ∧
      ∀ p : doubleCurveBoundary f, ∃ q : doubleCurveBoundary f, q ≠ p ∧
        ∃ (hp : p.val ∈ V) (hq : q.val ∈ V), Nonempty
          ((curveIncidenceGraph V P).Path (Sum.inl ⟨p.val,hp⟩) (Sum.inl ⟨q.val,hq⟩)) := by
  let : CompactSpace (compactifiedDoubleCurve f) :=
    isCompact_iff_compactSpace.mp (compactifiedDoubleCurve_compact f)
  have hline := transverse_double_curve_interior_chart hf hreg
  have hhalf := transverse_double_curve_boundary_chart hf hrep
  obtain ⟨V,P,hV,hDV,hP,hdis,hcover,hw⟩ := compact_curve_pieces (doubleCurveBoundary f)
    (doubleCurveBoundary_finite hf hfin) (fun p => by
      by_cases hp : p ∈ doubleCurveBoundary f
      · exact Or.inr (hhalf p hp)
      · exact Or.inl (hline p hp))
  refine ⟨V,P,hV,hDV,hP,hdis,hcover,hw,?_⟩
  intro p
  obtain ⟨q,hqp,hpath⟩ := curve_boundary_pair (doubleCurveBoundary f) V hDV hV P
    (fun E hE => ⟨(hP E hE).1,(hP E hE).2.2⟩) hdis hcover hw hline hhalf p
  exact ⟨q,hqp,hDV p.property,hDV q.property,hpath⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_DoubleCurveBoundaryArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every actual crosscap endpoint is joined to another one by an
embedded arc of the compactified double curve, with regular interior. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_double_curve_boundary_arc {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∀ p : doubleCurveBoundary f, ∃ q : doubleCurveBoundary f, q ≠ p ∧
      ∃ γ : Path p.val q.val, IsClosedEmbedding γ ∧
        ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∉ doubleCurveBoundary f := by
  obtain ⟨V,P,hV,hDV,hP,hdis,hcover,hw,_⟩ := prepared_double_curve_boundary_paths hf hfin hreg hrep
  exact curve_boundary_embedded_arc (doubleCurveBoundary f) V hDV hV P
    (fun E hE => ⟨(hP E hE).1,(hP E hE).2.2⟩) hdis hcover hw
    (transverse_double_curve_interior_chart hf hreg)
    (transverse_double_curve_boundary_chart hf hrep)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapOrderedArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prepared surface map has a continuously parametrized ordered
double arc connecting each crosscap to a distinct crosscap. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_crosscap_ordered_arc_oai {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    (p : M) (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ q : M, q ≠ p ∧ ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) ∧
      ∃ Γ : Path (p,p) (q,q), IsClosedEmbedding Γ ∧
        (∀ t, f (Γ t).1 = f (Γ t).2) ∧
        (∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) := by
  obtain ⟨c,φ,b,s,hpc,hφ,he,hz,hR⟩ := hrep p hp
  have hpK : unorderedPair (p,p) ∈ compactifiedDoubleCurve f :=
    (compactifiedDoubleCurve_diagonal f p).mpr (crosscap_diagonal_mem_closure f p c hpc hφ he b s hz hR)
  let P : doubleCurveBoundary f := ⟨⟨unorderedPair (p,p),hpK⟩,p,rfl⟩
  obtain ⟨Q,hQP,γ,hγ,hinter⟩ := prepared_double_curve_boundary_arc hf hfin hreg hrep P
  obtain ⟨q,hqeq⟩ := Q.property
  have hqp : q ≠ p := by
    intro h
    apply hQP
    apply Subtype.ext
    apply Subtype.ext
    exact hqeq.symm.trans (congrArg (fun x => unorderedPair (x,x)) h)
  have hqK : unorderedPair (q,q) ∈ compactifiedDoubleCurve f := hqeq.symm ▸ Q.val.property
  have hq : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) :=
    doublePairs_closure_diagonal_singular hf q ((compactifiedDoubleCurve_diagonal f q).mp hqK)
  let γU : Path (unorderedPair (p,p)) (unorderedPair (q,q)) :=
    (γ.map continuous_subtype_val).cast rfl hqeq
  have hγU : Function.Injective γU := Subtype.val_injective.comp hγ.injective
  have hgood : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → γU t ∈ unorderedDistinctPairs M := by
    intro t ht0 ht1 hbad
    exact hinter t ht0 ht1 hbad
  obtain ⟨Γ,hΓ,hΓeq⟩ := embedded_closed_double_arc_lift p q γU hγU hgood
  refine ⟨q,hqp,hq,Γ,hΓ,?_,?_⟩
  · intro t
    apply compactifiedDoubleCurve_pair_equality hf
    rw [hΓeq]
    exact (γ t).property
  · intro t ht0 ht1
    apply (unorderedPair_mem_distinct_iff (Γ t)).mp
    rw [hΓeq]
    exact hgood t ht0 ht1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_crosscap_ordered_arc_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_crosscap_ordered_arc_oai.{u_1}
