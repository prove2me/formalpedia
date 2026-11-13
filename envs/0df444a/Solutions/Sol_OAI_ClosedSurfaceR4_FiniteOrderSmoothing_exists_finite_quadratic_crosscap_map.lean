-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_finite_quadratic_crosscap_map
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:37:52.671206+00:00
-- url     : https://prove2.me/submissions/fb10b5a5-1d11-4ae3-841c-c69a2f439984

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI004
import Definitions.Def_OAIQ249SI005
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_regular_crosscap_map

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartPushforward
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extension by zero of a compactly supported coordinate correction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V]

lemma chartPushforward_source (p : M) (δ : Base → V) {q : M}
    (hq : q ∈ (chart p).source) : chartPushforward p δ q = δ (chart p q) :=
  indicator_of_mem hq _

lemma chartPushforward_zero_off (p : M) (δ : Base → V) {q : M}
    (hq : q ∉ (chart p).symm '' tsupport δ) : chartPushforward p δ q = 0 := by
  by_cases hs : q ∈ (chart p).source
  · rw [chartPushforward_source p δ hs]
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    exact hq ⟨chart p q,hz,(chart p).left_inv hs⟩
  · exact indicator_of_notMem hs _

variable [T2Space M]

lemma chartPushforward_tsupport (p : M) {δ : Base → V}
    (hc : HasCompactSupport δ) (hs : tsupport δ ⊆ (chart p).target) :
    tsupport (chartPushforward p δ) ⊆ (chart p).symm '' tsupport δ := by
  have hK : IsCompact ((chart p).symm '' tsupport δ) :=
    hc.image_of_continuousOn ((chart p).symm.continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro q hq
  by_contra hn
  exact hq (chartPushforward_zero_off p δ hn)

variable [IsManifold planeModel ∞ M] [NormedSpace ℝ V]

lemma chartPushforward_smooth (p : M) {δ : Base → V}
    (hd : ContDiff ℝ ∞ δ) (hc : HasCompactSupport δ)
    (hs : tsupport δ ⊆ (chart p).target) :
    ContMDiff planeModel 𝓘(ℝ,V) ∞ (chartPushforward p δ) := by
  intro q
  by_cases hq : q ∈ tsupport (chartPushforward p δ)
  · obtain ⟨z,hz,rfl⟩ := chartPushforward_tsupport p hc hs hq
    have hsource := (chart p).map_target (hs hz)
    have hlocal := hd.contMDiff.contMDiffAt.comp _
      ((chart_smooth p).contMDiffAt ((chart p).open_source.mem_nhds hsource))
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(chart p).open_source.mem_nhds hsource] with y hy
    exact chartPushforward_source p δ hy
  · exact contMDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hq)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionDirections
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartMapReplacement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compactly supported change of a coordinate representative produces
an actual global smooth map, retaining its local and exterior germs. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem chart_map_replacement (p : M) {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {f₀ F : Base → ProjectionTarget 3} (hF : ContDiff ℝ ∞ F) (hf₀ : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport (F-f₀))
    (hs : tsupport (F-f₀) ⊆ (chart p).target)
    {O : Set Base} (hO : IsOpen O)
    (hmatch : EqOn (f ∘ (chart p).symm) f₀ O) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      (∀ q ∈ (chart p).source, chart p q ∈ O →
        g =ᶠ[𝓝 q] F ∘ chart p) ∧
      ∀ q ∉ (chart p).symm '' tsupport (F-f₀), g =ᶠ[𝓝 q] f := by
  let δ := F-f₀
  let g := f+chartPushforward p δ
  refine ⟨g,hf.add (chartPushforward_smooth p (hF.sub hf₀) hc hs),?_,?_⟩
  · intro q hq hOq
    filter_upwards [(chart p).open_source.mem_nhds hq,
      ((chart p).continuousAt hq).preimage_mem_nhds (hO.mem_nhds hOq)] with y hy hOy
    have hm := hmatch hOy
    change f ((chart p).symm (chart p y)) = f₀ (chart p y) at hm
    rw [(chart p).left_inv hy] at hm
    change f y+chartPushforward p δ y = F (chart p y)
    rw [chartPushforward_source p δ hy,hm]
    exact add_sub_cancel _ _
  · intro q hq
    have hn : q ∉ tsupport (chartPushforward p δ) :=
      fun h => hq (chartPushforward_tsupport p hc hs h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change f y+chartPushforward p δ y = f y
    rw [hy]
    exact add_zero _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartGermImmersion
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteCorrectionGerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite disjoint corrections retain each prescribed local jet. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.SphericalJets

lemma finite_sum_germ_of_disjoint_supports {E V ι : Type*}
    [TopologicalSpace E] [AddCommMonoid V] [DecidableEq ι]
    (s : Finset ι) (q : ι → E → V) (K : ι → Set E)
    (hs : ∀ i ∈ s, tsupport (q i) ⊆ K i)
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (K i) (K j))
    {i : ι} (hi : i ∈ s) {p : E} (hp : p ∈ K i) :
    (fun x => ∑ j ∈ s, q j x) =ᶠ[𝓝 p] q i := by
  have he : ∀ᶠ x in 𝓝 p, ∀ j ∈ s, j ≠ i → q j x = 0 := by
    apply (eventually_all_finset s).mpr
    intro j hj
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ hn => False.elim (hn hji)
    · have hnot : p ∉ tsupport (q j) := by
        intro hq
        exact Set.disjoint_left.mp (hdisj hj hi hji) (hs j hj hq) hp
      exact (notMem_tsupport_iff_eventuallyEq.mp hnot).mono (fun _ hx _ => hx)
  filter_upwards [he] with x hx
  exact Finset.sum_eq_single i (fun j hj hji => hx j hj hji) (by simp [hi])

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceQuadraticTaylor
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
local instance secondJetNormed_r947dce_1 : NormedAddCommGroup (Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) := inferInstance
local instance secondJetSpace_r947dce_1 : NormedSpace ℝ (Base →L[ℝ] Base →L[ℝ] ProjectionTarget 3) := inferInstance
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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

local instance instContinuousSMulRealProdBase_r947dce_1 : ContinuousSMul ℝ (Base × ℝ) := Prod.continuousSMul
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
attribute [-simp] _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceCrosscapPreparation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported preparation of one actual surface crosscap. The change
creates no singularities and retains the chosen singular point. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem prepare_surface_crosscap {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (p q : M) (hp : p ∈ (chart q).source)
    (hbadp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p))
    {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    (heq : φ =ᶠ[𝓝 (chart q p)] f ∘ (chart q).symm) (b : Bool) (t : ℝ)
    (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      tsupport (g-f) ⊆ U ∧
      {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)} ⊆
        {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} ∧
      (¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p)) ∧
      g =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q := by
  let a := chart q p
  obtain ⟨W,hWeq,hW,haW⟩ := _root_.mem_nhds_iff.mp heq
  let O := ((chart q).target ∩ (chart q).symm ⁻¹' U) ∩ W
  have hO : IsOpen O := ((chart q).isOpen_inter_preimage_symm hU).inter hW
  have haO : a ∈ O := by
    refine ⟨⟨(chart q).map_source hp,?_⟩,haW⟩
    change (chart q).symm (chart q p) ∈ U
    rwa [(chart q).left_inv hp]
  obtain ⟨ρ,hρ,hρO⟩ := nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds haO)
  obtain ⟨r,G,hr,hrρ,hG,hGT,_hout,hGS,hGlocal⟩ :=
    centered_quadratic_crosscap_preparation hφ b a t hz hreg hρ
  have hSO : tsupport (G-φ) ⊆ O := by
    apply hGS.trans
    apply Subset.trans _ hρO
    apply closedBall_subset_closedBall
    linarith
  have hST : tsupport (G-φ) ⊆ (chart q).target := fun x hx => (hSO hx).1.1
  have hcompact : HasCompactSupport (G-φ) :=
    (isCompact_closedBall a (r/2)).of_isClosed_subset (isClosed_tsupport _) hGS
  obtain ⟨g,hg,hmodel,hext⟩ := chart_map_replacement q hf hG hφ hcompact hST hW
    (fun x hx => (hWeq hx).symm)
  let K := (chart q).symm '' tsupport (G-φ)
  have hK : IsCompact K := hcompact.image_of_continuousOn
    ((chart q).symm.continuousOn.mono hST)
  have hKS : tsupport (g-f) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (sub_eq_zero.mpr ((hext x hn).self_of_nhds))
  have hKU : K ⊆ U := by
    rintro x ⟨y,hy,rfl⟩
    exact (hSO hy).1.2
  have hpmodel : g =ᶠ[𝓝 p] G ∘ chart q := hmodel p hp haW
  refine ⟨g,hg,hKS.trans hKU,?_,?_,?_⟩
  · intro x hbad
    by_cases hx : x ∈ K
    · obtain ⟨y,hy,rfl⟩ := hx
      have hyT := hST hy
      have hs := (chart q).map_target hyT
      have hyW : chart q ((chart q).symm y) ∈ W := by
        rw [(chart q).right_inv hyT]
        exact (hSO hy).2
      have hgm := hmodel _ hs hyW
      have hbadG : ¬ Function.Injective (fderiv ℝ G y) := by
        intro hi
        apply hbad
        apply (chart_germ_immersion_iff q hs hG hgm).mpr
        simpa only [(chart q).right_inv hyT] using hi
      have hyball : y ∈ ball a r := by
        have hyhalf := hGS hy
        have hd : dist y a ≤ r/2 := hyhalf
        rw [mem_ball]
        linarith
      have hya := (hGlocal y hyball).mp hbadG
      have hp' : (chart q).symm y = p := by rw [hya]; exact (chart q).left_inv hp
      change ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f ((chart q).symm y))
      exact (congrArg (fun w : M => ¬ Function.Injective
        (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f w)) hp').mpr hbadp
    · intro hgood
      exact hbad (by rw [(hext x hx).mfderiv_eq]; exact hgood)
  · intro hgood
    have hi := (chart_germ_immersion_iff q hp hG hpmodel).mp hgood
    exact ((hGlocal a (mem_ball_self hr)).mpr rfl) hi
  · exact hpmodel.trans (hGT.comp_tendsto ((chart q).continuousAt hp))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteSurfaceReplacement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite supported replacements on a surface agree with the selected
replacement near its support and with the original map elsewhere. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem finite_disjoint_surface_replacement {ι : Type*} [Fintype ι]
    (f : M → ProjectionTarget 3)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (g : ι → M → ProjectionTarget 3)
    (hg : ∀ i, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ (g i))
    (K : ι → Set M) (hs : ∀ i, tsupport (g i-f) ⊆ K i)
    (hd : Pairwise fun i j => Disjoint (K i) (K j)) :
    ∃ F : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F ∧
      (∀ i p, p ∈ K i → F =ᶠ[𝓝 p] g i) ∧
      (∀ p, (∀ i, p ∉ K i) → F =ᶠ[𝓝 p] f) := by
  classical
  let F : M → ProjectionTarget 3 := fun x => f x + ∑ i, (g i x-f x)
  have hF : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F :=
    hf.add (ContMDiff.sum fun i _ => (hg i).sub hf)
  refine ⟨F,hF,?_,?_⟩
  · intro i p hp
    have he := SphericalJets.finite_sum_germ_of_disjoint_supports Finset.univ
      (fun i => g i-f) K (fun j _ => hs j)
      (fun j _ k _ hjk => hd hjk) (Finset.mem_univ i) hp
    filter_upwards [he] with x hx
    change f x + ∑ j, (g j x-f x) = g i x
    change (∑ j, (g j x-f x)) = g i x-f x at hx
    rw [hx]
    abel
  · intro p hp
    have he : ∀ᶠ x in 𝓝 p, ∀ i ∈ (Finset.univ : Finset ι), (g i-f) x = 0 := by
      apply (eventually_all_finset Finset.univ).mpr
      intro i _
      exact notMem_tsupport_iff_eventuallyEq.mp (fun h => hp i (hs i h))
    filter_upwards [he] with x hx
    change f x + ∑ i, (g i x-f x) = f x
    have hz : ∑ i, (g i x-f x) = 0 := Finset.sum_eq_zero fun i hi => hx i hi
    rw [hz,add_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteQuadraticCrosscaps
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic finite singular set can be prepared simultaneously: every
singularity is represented by its genuine second Taylor polynomial, and
no additional singularity is introduced anywhere on the surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_finite_quadratic_crosscap_map_oai :
    ∃ F : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ F ∧
      {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p)}.Finite ∧
      ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p) →
        ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
          p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
          F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
          surfaceDirection φ b (chart q p,t) = 0 ∧
          Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)) := by
  classical
  obtain ⟨f,hf,hfin,hrep⟩ := exists_regular_crosscap_map (M := M)
  let S : Set M := {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}
  let : Fintype S := hfin.fintype
  choose q φ b t hp hφ he hz hr using (fun p : S => hrep p p.property)
  obtain ⟨V,hV,hd⟩ := hfin.t2_separation
  have hprep (p : S) := prepare_surface_crosscap hf p (q p) (hp p) p.property
    (hφ p) (he p) (b p) (t p) (hz p) (hr p) (hV p).2 (hV p).1
  choose g hg hs hsub hbad hlocal using hprep
  have hd' : Pairwise fun p r : S => Disjoint (V p) (V r) := by
    intro p r hpr
    exact hd p.property r.property (fun h => hpr (Subtype.ext h))
  obtain ⟨F,hF,hFi,hFe⟩ := finite_disjoint_surface_replacement f hf g hg
    (fun p : S => V p) hs hd'
  have hsing (x : M) :
      (¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F x)) ↔ x ∈ S := by
    constructor
    · intro hx
      by_cases h : ∃ p : S, x ∈ V p
      · obtain ⟨p,hpV⟩ := h
        apply hsub p
        change ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) (g p) x)
        intro hgood
        exact hx (by rw [(hFi p x hpV).mfderiv_eq]; exact hgood)
      · have hh : ∀ p : S, x ∉ V p := by simpa only [not_exists] using h
        change ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)
        intro hgood
        exact hx (by rw [(hFe x hh).mfderiv_eq]; exact hgood)
    · intro hx
      let p : S := ⟨x,hx⟩
      rw [(hFi p x (hV p).1).mfderiv_eq]
      exact hbad p
  refine ⟨F,hF,?_,?_⟩
  · have heq : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) F p)} = S :=
      Set.ext hsing
    rw [heq]
    exact hfin
  · intro x hx
    let p : S := ⟨x,(hsing x).mp hx⟩
    refine ⟨q p,φ p,b p,t p,hp p,hφ p,?_,hz p,hr p⟩
    exact (hFi p x (hV p).1).trans (hlocal p)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_finite_quadratic_crosscap_map_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exists_finite_quadratic_crosscap_map_oai.{u_1}
