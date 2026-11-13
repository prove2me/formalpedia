-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T09:52:44.172505+00:00
-- url     : https://prove2.me/submissions/a6b363d3-4450-4f44-b840-059470ec51e1

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI008
import Definitions.Def_OAIQ249SI000
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_crosscap_source_embedded_path
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_prepared_crosscap_ordered_arc

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartGermImmersion
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
attribute [-instance] _root_.instVAddIntReal_solutions
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
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapDoubleRay
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The image of the local double curve is an actual regular half-ray.
Its acceleration is forced to be nonzero by the regular direction jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma centeredSurfaceTaylor_value {f : Base → ProjectionTarget 3}
    (a v : Base) :
    centeredSurfaceTaylor f a (a+v) =
      f a+fderiv ℝ f a v+(1/2 : ℝ) • fderiv ℝ (fderiv ℝ f) a v v := by
  have hfirst : fderiv ℝ (translatedSurface f a) = fun y => fderiv ℝ f (y+a) := by
    funext y
    exact fderiv_comp_add_right a
  unfold centeredSurfaceTaylor surfaceTaylorTwo surfaceQuadratic
  rw [hfirst,fderiv_comp_add_right]
  simp only [translatedSurface,zero_add,add_sub_cancel_left]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapLinearCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit invertible linear coordinates adapted to the kernel of a crosscap. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscapParameterLinear_apply (b : Bool) (t : ℝ) (z : Base × ℝ) :
    crosscapParameterLinear b t z =
      (z.1 0 • tangentRayVelocity b + (z.1 1/2) • tangentRay b t,z.2) := by
  change (z.1 0 • tangentRayVelocity b + ((1/2 : ℝ)*z.1 1) • tangentRay b t,z.2) = _
  congr 2
  congr 1
  ring

lemma crosscapParameterLinear_bijective (b : Bool) (t : ℝ) :
    Function.Bijective (crosscapParameterLinear b t) := by
  have hcoord (z : Base × ℝ) :
      tangentTransverseCoefficient b t (crosscapParameterLinear b t z).1 = z.1 0 ∧
      tangentRayCoefficient b (crosscapParameterLinear b t z).1 = z.1 1/2 := by
    have h := crosscapSourceLinear_coordinates b t (![z.1 0,z.1 1/2] : Base)
    simpa only [crosscapParameterLinear_apply,crosscapSourceLinear_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one] using h
  constructor
  · intro z w h
    have he := congrArg Prod.fst h
    have h0 := congrArg (tangentTransverseCoefficient b t) he
    have h1 := congrArg (tangentRayCoefficient b) he
    rw [(hcoord z).1,(hcoord w).1] at h0
    rw [(hcoord z).2,(hcoord w).2] at h1
    apply Prod.ext
    · ext i
      fin_cases i
      · exact h0
      · change z.1 1 = w.1 1
        linarith
    · simpa only [crosscapParameterLinear_apply] using congrArg Prod.snd h
  · intro z
    refine ⟨(![tangentTransverseCoefficient b t z.1,2*tangentRayCoefficient b z.1],z.2),?_⟩
    rw [crosscapParameterLinear_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]
    apply Prod.ext
    · convert (tangentRay_decomposition b t z.1).symm using 1
    · rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicPrimitive
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rawPrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (rawPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem rawPrimitive_contDiff {f : ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (rawPrimitive f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (rawPrimitive_hasDerivAt hf.continuous x).differentiableAt, ?_⟩
  have he : deriv (rawPrimitive f) = f := by
    funext x
    exact (rawPrimitive_hasDerivAt hf.continuous x).deriv
  rwa [he]

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MonotoneGermExtension
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extending an oriented smooth coordinate germ to a globally increasing
smooth real function, with derivative one outside a compact set. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem increasing_smooth_germ_extension {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : 0 < deriv h a) :
    ∃ (g : ℝ → ℝ) (K : Set ℝ), ContDiff ℝ ∞ g ∧ StrictMono g ∧
      g =ᶠ[𝓝 a] h ∧ (∀ x, 0 < deriv g x) ∧ IsCompact K ∧
      ∀ x ∉ K, deriv g x = 1 := by
  have hd : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  let U := {x | 0 < deriv h x}
  have hU : IsOpen U := isOpen_lt continuous_const hd.continuous
  obtain ⟨W,hW,haW,hWU,φ,χ,hφ,hχ,hφc,hχc,hφr,hχr,hχs,hφs,hφone,hχone⟩ :=
    CollarVelocity.nested_compact_cutoffs (isCompact_singleton (x := a)) hU
      (singleton_subset_iff.mpr ha)
  let v : ℝ → ℝ := fun x => φ x * deriv h x + (1-φ x)
  have hv : ContDiff ℝ ∞ v := (hφ.mul hd).add (contDiff_const.sub hφ)
  have hvpos : ∀ x, 0 < v x := by
    intro x
    by_cases hx : x ∈ U
    · have hdpos : 0 < deriv h x := hx
      have hφnonneg := (hφr x).1
      have hφle := (hφr x).2
      by_cases hzero : φ x = 0
      · simp [v,hzero]
      · have hφpos : 0 < φ x := lt_of_le_of_ne hφnonneg (Ne.symm hzero)
        have hmul := mul_pos hφpos hdpos
        dsimp [v]
        linarith
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hin => hx (hφs hin))
      simp [v,hz]
  let g : ℝ → ℝ := fun x => h a +
    PeriodicPrimitive.rawPrimitive v x - PeriodicPrimitive.rawPrimitive v a
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_const.add (PeriodicPrimitive.rawPrimitive_contDiff hv)).sub contDiff_const
  have hgder : ∀ x, deriv g x = v x := by
    intro x
    exact (((PeriodicPrimitive.rawPrimitive_hasDerivAt hv.continuous x).const_add (h a)).sub_const _).deriv
  have hag : g a = h a := by dsimp [g] <;> ring
  obtain ⟨r,hr,hrW⟩ := Metric.isOpen_iff.mp hW a (haW (by simp))
  have heq : EqOn g h (Metric.ball a r) := by
    apply isOpen_ball.eqOn_of_deriv_eq (convex_ball a r).isPreconnected
      (hg.differentiable (by simp)).differentiableOn (hh.differentiable (by simp)).differentiableOn
    · intro x hx
      rw [hgder]
      dsimp [v]
      rw [hφone x (hrW hx)]
      ring
    · exact Metric.mem_ball_self hr
    · exact hag
  refine ⟨g,tsupport φ,hg,strictMono_of_deriv_pos (fun x => (hgder x) ▸ hvpos x),
    heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds (Metric.mem_ball_self hr)),
    fun x => (hgder x) ▸ hvpos x,hφc,?_⟩
  intro x hx
  rw [hgder]
  have hz := image_eq_zero_of_notMem_tsupport hx
  simp [v,hz]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MonotoneGermDiffeomorphism
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The increasing extensions are global diffeomorphisms, allowing local
arc coordinates to be joined without changing their germs. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma affine_tails_of_deriv_one {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hd : ∀ x ∉ K, deriv g x = 1) :
    ∃ R cPos cNeg : ℝ, (∀ x, R < x → g x = x+cPos) ∧
      ∀ x, x < -R → g x = x+cNeg := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : ℝ → ℝ)).continuousOn
  let R := |C|+1
  have hout : ∀ x, R < |x| → x ∉ K := by
    intro x hx hin
    have hb := hC x hin
    change ‖x‖ ≤ C at hb
    rw [Real.norm_eq_abs] at hb
    have hc := le_abs_self C
    dsimp [R] at hx
    linarith
  have hplus : EqOn g (fun x => x+(g (R+1)-(R+1))) (Ioi R) := by
    apply isOpen_Ioi.eqOn_of_deriv_eq (convex_Ioi R).isPreconnected
      (hg.differentiable (by simp)).differentiableOn
      (differentiable_id.add_const _).differentiableOn
    · intro x hx
      rw [hd x (hout x (lt_of_lt_of_le hx (le_abs_self x)))]
      simp
    · change R < R+1
      linarith
    · dsimp only [id]
      ring
  have hminus : EqOn g (fun x => x+(g (-R-1)-(-R-1))) (Iio (-R)) := by
    apply isOpen_Iio.eqOn_of_deriv_eq (convex_Iio (-R)).isPreconnected
      (hg.differentiable (by simp)).differentiableOn
      (differentiable_id.add_const _).differentiableOn
    · intro x hx
      have hxr : x < -R := hx
      have habs : R < |x| := by linarith [neg_le_abs x]
      rw [hd x (hout x habs)]
      simp
    · change -R-1 < -R
      linarith
    · dsimp only [id]
      ring
  exact ⟨R,g (R+1)-(R+1),g (-R-1)-(-R-1),fun x hx => hplus hx,fun x hx => hminus hx⟩

lemma surjective_of_deriv_one_off_compact {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (hd : ∀ x ∉ K, deriv g x = 1) :
    Function.Surjective g := by
  obtain ⟨R,cPos,cNeg,hplus,hminus⟩ := affine_tails_of_deriv_one hg hK hd
  have htop : Tendsto g atTop atTop := by
    apply (tendsto_atTop_add_const_right atTop cPos tendsto_id).congr'
    filter_upwards [eventually_gt_atTop R] with x hx
    exact (hplus x hx).symm
  have hbot : Tendsto g atBot atBot := by
    apply (tendsto_atBot_add_const_right atBot cNeg tendsto_id).congr'
    filter_upwards [eventually_lt_atBot (-R)] with x hx
    exact (hminus x hx).symm
  exact hg.continuous.surjective htop hbot

theorem increasing_smooth_germ_diffeomorphism {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : 0 < deriv h a) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      StrictMono e ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨g,K,hg,hmono,he,hpos,hK,hd⟩ := increasing_smooth_germ_extension hh a ha
  have hsurj := surjective_of_deriv_one_off_compact hg hK hd
  let e := (hmono.orderIsoOfSurjective g hsurj).toHomeomorph
  have heq : (e : ℝ → ℝ) = g := rfl
  refine ⟨e,by simpa only [heq] using hg,?_,by simpa only [heq] using hmono,by simpa only [heq] using he⟩
  apply e.contDiff_symm_deriv (f' := deriv g)
  · intro x
    exact ne_of_gt (hpos x)
  · intro x
    change HasDerivAt g (deriv g x) x
    exact (hg.differentiable (by simp) x).hasDerivAt
  · simpa only [heq] using hg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneCurveGraph
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular coordinate projection gives an actual local graph of a smooth
plane curve, with a globally smooth graph function available for cutoff gluing. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem plane_curve_graph {γ : ℝ → Base} (hγ : ContDiff ℝ ∞ γ) (t : ℝ)
    (h0 : deriv (fun u => γ u 0) t ≠ 0) :
    ∃ (g : ℝ → ℝ) (U : Set ℝ), ContDiff ℝ ∞ g ∧ IsOpen U ∧ t ∈ U ∧
      ∀ u ∈ U, γ u = ![γ u 0,g (γ u 0)] := by
  let d := deriv (fun u => γ u 0) t
  let s : ℝ := if 0 < d then 1 else -1
  have hd : 0 < s*d := by
    dsimp only [s]
    split_ifs with hp
    · simpa using hp
    · have hn : d < 0 := lt_of_le_of_ne (not_lt.mp hp) h0
      simpa using hn
  let h : ℝ → ℝ := fun u => s*γ u 0
  have hγ0 : ContDiff ℝ ∞ (fun u => γ u 0) := (contDiff_apply ℝ ℝ 0).comp hγ
  have hh : ContDiff ℝ ∞ h := contDiff_const.mul hγ0
  have hdt : deriv h t = s*d := (hγ0.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t |>.hasDerivAt.const_mul s).deriv
  obtain ⟨e,_,hei,_,he⟩ := increasing_smooth_germ_diffeomorphism hh t (hdt ▸ hd)
  let g : ℝ → ℝ := fun x => γ (e.symm (s*x)) 1
  have hg : ContDiff ℝ ∞ g := (contDiff_apply ℝ ℝ 1).comp
    (hγ.comp (hei.comp (contDiff_const.mul contDiff_id)))
  obtain ⟨U,hU,htU,hsub⟩ := mem_nhds_iff.mp he
  refine ⟨g,U,hg,htU,hsub,?_⟩
  intro u hu
  have heu : e u = s*γ u 0 := hU hu
  have hu' : e.symm (s*γ u 0) = u := by rw [← heu,e.symm_apply_apply]
  ext i
  fin_cases i
  · rfl
  · change γ u 1 = γ (e.symm (s*γ u 0)) 1
    rw [hu']

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PlaneCommonCoordinate
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common linear plane coordinate is regular on either of two nonzero
curve velocities, including the case of collinear opposite velocities. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma plane_second_ne_zero {v : Base} (hv : v ≠ 0) (hv0 : v 0 = 0) : v 1 ≠ 0 := by
  intro hv1
  apply hv
  ext i
  fin_cases i
  · exact hv0
  · exact hv1

theorem exists_common_plane_parameter {v w : Base} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ a : ℝ, v 0+a*v 1 ≠ 0 ∧ w 0+a*w 1 ≠ 0 := by
  by_cases hv0 : v 0 = 0
  · have hv1 := plane_second_ne_zero hv hv0
    by_cases hw0 : w 0 = 0
    · have hw1 := plane_second_ne_zero hw hw0
      exact ⟨1,by simpa only [hv0,zero_add,one_mul] using hv1,
        by simpa only [hw0,zero_add,one_mul] using hw1⟩
    · by_cases hw1 : w 0+w 1 = 0
      · refine ⟨2,?_,?_⟩
        · simpa only [hv0,zero_add] using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hv1
        · intro h; apply hw0; linarith
      · exact ⟨1,by simpa only [hv0,zero_add,one_mul] using hv1,by simpa only [one_mul] using hw1⟩
  · by_cases hw0 : w 0 = 0
    · have hw1 := plane_second_ne_zero hw hw0
      by_cases hv1 : v 0+v 1 = 0
      · refine ⟨2,?_,?_⟩
        · intro h; apply hv0; linarith
        · simpa only [hw0,zero_add] using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hw1
      · exact ⟨1,by simpa only [one_mul] using hv1,by simpa only [hw0,zero_add,one_mul] using hw1⟩
    · exact ⟨0,by simpa using hv0,by simpa using hw0⟩

theorem exists_common_plane_coordinate {v w : Base} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : Base ≃L[ℝ] Base, (e v) 0 ≠ 0 ∧ (e w) 0 ≠ 0 := by
  obtain ⟨a,hv',hw'⟩ := exists_common_plane_parameter hv hw
  exact ⟨planeShearEquiv a,hv',hw'⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticCrosscapFactorization
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every nondegenerate quadratic crosscap is a standard umbrella followed
by a target map whose derivative at the origin is invertible. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tripleNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tripleSpace
lemma standardCrosscap_smooth : ContDiff ℝ ∞ standardCrosscap := by
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [standardCrosscap] <;> fun_prop
  · change ContDiff ℝ ∞ (fun x : Base => x 0)
    fun_prop

lemma crosscapTargetShear_smooth (β : Base × ℝ) :
    ContDiff ℝ ∞ (crosscapTargetShear β) := by
  exact contDiff_id.add ((contDiff_snd.pow 2).smul contDiff_const)

lemma crosscapTargetShear_fderiv (β : Base × ℝ) :
    fderiv ℝ (crosscapTargetShear β) 0 = ContinuousLinearMap.id ℝ (Base × ℝ) := by
  have h := (hasFDerivAt_id (0 : Base × ℝ)).add
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : Base × ℝ))).pow 2).smul_const β)
  have he : (id + fun z : Base × ℝ => z.2^2 • β) = crosscapTargetShear β := by
    funext z
    rfl
  rw [he] at h
  simpa using h.fderiv

lemma quadratic_crosscap_factorization {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    ∃ (R : (Base × ℝ) ≃L[ℝ] ProjectionTarget 3) (β : Base × ℝ),
      ∀ x, centeredSurfaceTaylor f a (a+crosscapSourceEquiv b t x) =
        f a + R (crosscapTargetShear β (standardCrosscap x)) := by
  let H := fderiv ℝ (surfaceDirection f b) (a,t)
  let R : (Base × ℝ) ≃L[ℝ] ProjectionTarget 3 :=
    ContinuousLinearEquiv.ofBijective (H.comp (crosscapParameterLinear b t))
      (LinearMap.ker_eq_bot.mpr (hreg.comp (crosscapParameterLinear_bijective b t)).1)
      (LinearMap.range_eq_top.mpr (hreg.comp (crosscapParameterLinear_bijective b t)).2)
  let v := tangentRayVelocity b
  let k := tangentRay b t
  let B := fderiv ℝ (fderiv ℝ f) a
  let β := R.symm ((1/2 : ℝ) • B v v)
  have hsym : B k v = B v k := hf.contDiffAt.isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) k v
  have hker : fderiv ℝ f a k = 0 := hz
  refine ⟨R,β,?_⟩
  intro x
  have hR : R (standardCrosscap x) =
      x 0 • fderiv ℝ f a v + (x 0*x 1) • B v k + ((x 1)^2/2) • B k k := by
    change H (crosscapParameterLinear b t (standardCrosscap x)) = _
    rw [crosscapParameterLinear_apply]
    simp only [standardCrosscap,Matrix.cons_val_zero,Matrix.cons_val_one]
    dsimp only [H]
    rw [(surfaceDirection_hasFDerivAt hf b (a,t)).fderiv]
    change fderiv ℝ f a (x 0 • v) + B ((x 0*x 1) • v + ((x 1)^2/2) • k) k = _
    simp only [map_smul,map_add,add_apply,smul_apply]
    abel
  have hβ : R β = (1/2 : ℝ) • B v v := R.apply_symm_apply _
  rw [centeredSurfaceTaylor_value]
  change f a + fderiv ℝ f a (crosscapSourceLinear b t x) +
      (1/2 : ℝ) • B (crosscapSourceLinear b t x) (crosscapSourceLinear b t x) = _
  rw [crosscapSourceLinear_apply]
  change f a + fderiv ℝ f a (x 0 • v+x 1 • k) +
      (1/2 : ℝ) • B (x 0 • v+x 1 • k) (x 0 • v+x 1 • k) = _
  simp only [map_add,map_smul,smul_apply,add_apply,hker,smul_zero,add_zero,hsym]
  rw [crosscapTargetShear,map_add,map_smul,hR,hβ]
  simp only [standardCrosscap]
  module

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_StandardCrosscapDerivative
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The standard umbrella has one singular point and a transverse double ray. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardBaseNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardBaseSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardTripleNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.standardTripleSpace
lemma standardCrosscap_double_iff {x y : Base} (hne : x ≠ y) :
    standardCrosscap x = standardCrosscap y ↔
      x 0 = 0 ∧ y 0 = 0 ∧ x 1 = -y 1 ∧ x 1 ≠ 0 := by
  constructor
  · intro he
    have h0 : x 0 = y 0 := congrArg Prod.snd he
    have h1 : x 0*x 1 = y 0*y 1 := congrFun (congrArg Prod.fst he) 0
    have h2 : (x 1)^2 = (y 1)^2 := congrFun (congrArg Prod.fst he) 1
    have hxy1 : x 1 ≠ y 1 := by
      intro h
      apply hne
      ext i
      fin_cases i
      · exact h0
      · exact h
    have hx0 : x 0 = 0 := by
      by_contra h
      apply hxy1
      rw [← h0] at h1
      exact mul_left_cancel₀ h h1
    have hneg : x 1 = -y 1 := (sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left hxy1
    refine ⟨hx0,h0 ▸ hx0,hneg,?_⟩
    intro hx1
    apply hxy1
    linarith
  · rintro ⟨hx,hy,hneg,_⟩
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap,hx,hy,hneg]
    · exact hx.trans hy.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticCrosscapNormalForm
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smooth target coordinates identifying a prepared quadratic jet
with the standard Whitney umbrella. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.normalSourceNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.normalSourceSpace
theorem quadratic_crosscap_normal_form {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    ∃ (S : Base ≃L[ℝ] Base) (e : OpenPartialHomeomorph (Base × ℝ) (ProjectionTarget 3)),
      0 ∈ e.source ∧ e 0 = f a ∧ ContDiff ℝ ∞ e ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x, centeredSurfaceTaylor f a (a+S x) = e (standardCrosscap x) := by
  obtain ⟨R,β,hfactor⟩ := quadratic_crosscap_factorization hf a b t hz hreg
  let g : Base × ℝ → ProjectionTarget 3 := fun z => f a + R (crosscapTargetShear β z)
  have hg : ContDiff ℝ ∞ g := contDiff_const.add (R.contDiff.comp (crosscapTargetShear_smooth β))
  have hd : HasFDerivAt g R.toContinuousLinearMap 0 := by
    have hs := ((crosscapTargetShear_smooth β).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) 0).hasFDerivAt
    rw [crosscapTargetShear_fderiv] at hs
    refine ((R.hasFDerivAt.comp 0 hs).const_add (f a)).congr_fderiv (Eq.symm ?_)
    · apply ContinuousLinearMap.ext
      intro z
      rfl
  let e₀ := hg.contDiffAt.toOpenPartialHomeomorph g hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let W : Set (Base × ℝ) := {z | IsUnit (R.symm.toContinuousLinearMap.comp (fderiv ℝ g z))}
  have hcont : Continuous (fun z => R.symm.toContinuousLinearMap.comp (fderiv ℝ g z)) :=
    continuous_const.clm_comp (hg.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hW : IsOpen W := Units.isOpen.preimage hcont
  have h0W : (0 : Base × ℝ) ∈ W := by
    change IsUnit (R.symm.toContinuousLinearMap.comp (fderiv ℝ g 0))
    rw [hd.fderiv]
    have heq : R.symm.toContinuousLinearMap.comp R.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (Base × ℝ) := by
      apply ContinuousLinearMap.ext
      intro z
      exact R.symm_apply_apply z
    rw [heq]
    exact isUnit_one
  let e := e₀.restrOpen W hW
  have he : (e : Base × ℝ → ProjectionTarget 3) = g := rfl
  refine ⟨crosscapSourceEquiv b t,e,
    ⟨hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),h0W⟩,?_,?_,?_,?_⟩
  · change f a+R (crosscapTargetShear β 0) = f a
    simp [crosscapTargetShear]
  · simpa only [he] using hg
  · intro y hy
    obtain ⟨u,hu⟩ := (e.map_target hy).2
    let D := (ContinuousLinearEquiv.ofUnit u).trans R
    have hD : D.toContinuousLinearMap = fderiv ℝ g (e.symm y) := by
      apply ContinuousLinearMap.ext
      intro z
      change R ((u : (Base × ℝ) →L[ℝ] (Base × ℝ)) z) = _
      rw [hu]
      exact R.apply_symm_apply _
    have hdy : HasFDerivAt e D.toContinuousLinearMap (e.symm y) := by
      rw [he,hD]
      exact (hg.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy hdy (by rw [he]; exact hg.contDiffAt)).contDiffWithinAt
  · exact hfactor

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SurfaceCrosscapNormalForm
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source and target charts putting an actual prepared surface crosscap
into the standard umbrella form. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_crosscap_normal_form (F : M → ProjectionTarget 3) (p q : M)
    (hp : p ∈ (chart q).source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ)
    (he : F =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q)
    (b : Bool) (t : ℝ) (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t))) :
    ∃ (c : OpenPartialHomeomorph M Base)
      (e : OpenPartialHomeomorph (Base × ℝ) (ProjectionTarget 3)),
      p ∈ c.source ∧ c p = 0 ∧ 0 ∈ e.source ∧ e 0 = F p ∧
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x ∈ c.source, standardCrosscap (c x) ∈ e.source ∧ F x = e (standardCrosscap (c x))) := by
  let a := chart q p
  obtain ⟨S,e,h0e,he0,heS,heI,hfactor⟩ := quadratic_crosscap_normal_form hφ a b t hz hreg
  let h : Base ≃ₜ Base := (Homeomorph.addRight (-a)).trans S.symm.toHomeomorph
  let c₀ := (chart q).transHomeomorph h
  have hc₀ : (c₀ : M → Base) = fun x => S.symm (chart q x-a) := rfl
  have hc₀i : (c₀.symm : Base → M) = fun x => (chart q).symm (S x+a) := by
    funext x
    change (chart q).symm (S x - -a) = _
    rw [sub_neg_eq_add]
  have hpc : p ∈ c₀.source := hp
  have hcp : c₀ p = 0 := by rw [hc₀]; simp [a]
  have hcS : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c₀ c₀.source := by
    rw [hc₀]
    exact S.symm.contDiff.contMDiff.comp_contMDiffOn ((chart_smooth q).sub contMDiffOn_const)
  have hcI : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c₀.symm c₀.target := by
    rw [hc₀i]
    apply (chart_symm_smooth q).comp
      (S.contDiff.contMDiff.add contMDiff_const).contMDiffOn
    intro x hx
    change S x - -a ∈ (chart q).target at hx
    change S x+a ∈ (chart q).target
    simpa only [sub_neg_eq_add] using hx
  have hpval : F p = φ a := by
    have hh := he.eq_of_nhds
    change F p = centeredSurfaceTaylor φ a a at hh
    have ha := centeredSurfaceTaylor_value (f := φ) a 0
    have ha' : centeredSurfaceTaylor φ a a = φ a := by
      simpa only [add_zero,map_zero,smul_zero] using ha
    exact hh.trans ha'
  obtain ⟨U,hEq,hU,hpU⟩ := eventually_nhds_iff.mp he
  let W := U ∩ (c₀.source ∩ c₀ ⁻¹' (standardCrosscap ⁻¹' e.source))
  have hW : IsOpen W := hU.inter (c₀.isOpen_inter_preimage
    (e.open_source.preimage standardCrosscap_smooth.continuous))
  have hstd : standardCrosscap (0 : Base) = 0 := by
    apply Prod.ext
    · ext i
      fin_cases i <;> (first | (simp [standardCrosscap]; all_goals first | (norm_num [standardCrosscap]; done) | rfl | decide) | (norm_num [standardCrosscap]; done) | norm_num [standardCrosscap])
    · rfl
  have hpW : p ∈ W := ⟨hpU,hpc,by simpa only [mem_preimage,hcp,hstd] using h0e⟩
  let c := c₀.restrOpen W hW
  refine ⟨c,e,⟨hpc,hpW⟩,hcp,h0e,he0.trans hpval.symm,
    hcS.mono (fun _ hx => hx.1),?_,heS,heI,?_⟩
  · exact hcI.mono (fun x hx => hx.1)
  · intro x hx
    refine ⟨hx.2.2.2,?_⟩
    have hEqx := hEq x hx.2.1
    change F x = centeredSurfaceTaylor φ a (chart q x) at hEqx
    rw [hEqx]
    have hfac := hfactor (c₀ x)
    have hcoord : a+S (c₀ x) = chart q x := by
      rw [hc₀,S.apply_symm_apply]
      abel
    rw [hcoord] at hfac
    exact hfac

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapPairCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two branches of a double point near an actual prepared crosscap
are exactly the two opposite nonzero kernel-axis coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}
namespace SurfaceCrosscapCoordinates

theorem double_pair (c : SurfaceCrosscapCoordinates f p) {x y : M}
    (hx : x ∈ c.source.source) (hy : y ∈ c.source.source)
    (hne : x ≠ y) (heq : f x = f y) :
    c.source x 0 = 0 ∧ c.source y 0 = 0 ∧
      c.source x 1 = -c.source y 1 ∧ c.source x 1 ≠ 0 := by
  have hcne : c.source x ≠ c.source y := fun h => hne (c.source.injOn hx hy h)
  apply (standardCrosscap_double_iff hcne).mp
  apply c.target.injOn (c.model_mem x hx) (c.model_mem y hy)
  rw [← c.model_eq x hx,← c.model_eq y hy]
  exact heq

end SurfaceCrosscapCoordinates
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CenteredSmoothStep
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A centered flat step with strict separation of opposite parameters,
used to round a tangential return between two disjoint curve branches. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma centeredSmoothStep_smooth : ContDiff ℝ ∞ centeredSmoothStep :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const 2)

lemma centeredSmoothStep_zero {t : ℝ} (ht : t ≤ -1) : centeredSmoothStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma centeredSmoothStep_one {t : ℝ} (ht : 1 ≤ t) : centeredSmoothStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma centeredSmoothStep_bounds (t : ℝ) : centeredSmoothStep t ∈ Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma expNegInvGlue_strict {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    expNegInvGlue x < expNegInvGlue y := by
  simp only [expNegInvGlue,not_le.mpr hx,not_le.mpr (hx.trans hxy),ite_false, if_false]
  apply Real.exp_lt_exp.mpr
  exact neg_lt_neg (inv_strictAnti₀ hx hxy)

lemma centeredSmoothStep_opposite_lt {t : ℝ} (ht : 0 < t) :
    centeredSmoothStep (-t) < centeredSmoothStep t := by
  let u := (t+1)/2
  let v := (-t+1)/2
  have hu : 0 < u := by dsimp [u] <;> linarith
  have hvu : v < u := by dsimp [u,v] <;> linarith
  have hev : expNegInvGlue v < expNegInvGlue u := by
    by_cases hv : 0 < v
    · exact expNegInvGlue_strict hv hvu
    · rw [expNegInvGlue.zero_of_nonpos (not_lt.mp hv)]
      exact expNegInvGlue.pos_of_pos hu
  have huv : 1-u = v := by dsimp [u,v] <;> ring
  have hvu' : 1-v = u := by dsimp [u,v] <;> ring
  change Real.smoothTransition v < Real.smoothTransition u
  rw [Real.smoothTransition,Real.smoothTransition,huv,hvu',add_comm (expNegInvGlue v)]
  exact div_lt_div_of_pos_right hev (Real.smoothTransition.pos_denom u |>.trans_eq (by rw [huv]))

lemma expNegInvGlue_hasDerivAt (x : ℝ) :
    HasDerivAt expNegInvGlue ((x⁻¹)^2 * expNegInvGlue x) x := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) x

lemma centeredSmoothStep_hasDerivAt_zero : HasDerivAt centeredSmoothStep 1 0 := by
  let e := expNegInvGlue (1/2)
  have he : 0 < e := expNegInvGlue.pos_of_pos (by norm_num)
  have hE : HasDerivAt expNegInvGlue (4*e) (1/2) := by
    convert expNegInvGlue_hasDerivAt (1/2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num [e]
  have hL : HasDerivAt (fun t : ℝ => (t+1)/2) (1/2) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).add_const 1).div_const 2 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hR : HasDerivAt (fun t : ℝ => 1-(t+1)/2) (-1/2) 0 := by
    convert hL.const_sub 1 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hA : HasDerivAt (fun t : ℝ => expNegInvGlue ((t+1)/2)) (2*e) 0 := by
    have hE' : HasDerivAt expNegInvGlue (4*e) ((0+1)/2) := by
      convert hE using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    convert hE'.comp 0 hL using 1 <;> first | rfl | ring
  have hB : HasDerivAt (fun t : ℝ => expNegInvGlue (1-(t+1)/2)) (-2*e) 0 := by
    have hE' : HasDerivAt expNegInvGlue (4*e) (1-(0+1)/2) := by
      convert hE using 1
      all_goals try with_reducible_and_instances rfl
      norm_num
    convert hE'.comp 0 hR using 1 <;> first | rfl | ring
  have hD := hA.div (hA.add hB) (by
    norm_num only [Pi.add_apply,zero_add]
    change e+e ≠ 0
    positivity)
  refine hD.congr_deriv (Eq.symm ?_)
  · norm_num only [Pi.add_apply,zero_add]
    change 1 = ((2*e)*(e+e)-e*(2*e+ -2*e))/(e+e)^2
    field_simp [ne_of_gt he]
    ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalMonotoneTransition
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth oriented transition on an open real interval extends to a
global smooth change of parameter while retaining its germ. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem local_increasing_diffeomorphism {h : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) {a : ℝ}
    (haU : a ∈ U) (ha : 0 < deriv h a) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      StrictMono e ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨W,hW,haW,hWU,H,hH,heq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := a)) hU (singleton_subset_iff.mpr haU) hh
  have he : H =ᶠ[𝓝 a] h := heq.eventuallyEq_of_mem (hW.mem_nhds (haW (by simp)))
  have hd : 0 < deriv H a := by rw [he.deriv_eq]; exact ha
  obtain ⟨e,hes,hei,hem,hee⟩ := increasing_smooth_germ_diffeomorphism hH a hd
  exact ⟨e,hes,hei,hem,hee.trans he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcJoin
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth joining at a common germ, with regularity and injectivity
retained on the two ordered pieces of the parameter interval. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*}

lemma joinedCurve_germ_left (a : ℝ) (γ δ : ℝ → M) {t : ℝ} (ht : t < a) :
    joinedCurve a γ δ =ᶠ[𝓝 t] γ := by
  filter_upwards [eventually_lt_nhds ht] with s hs
  simp only [joinedCurve,ite_eq_left hs.le]

lemma joinedCurve_germ_right (a : ℝ) (γ δ : ℝ → M) {t : ℝ} (ht : a < t) :
    joinedCurve a γ δ =ᶠ[𝓝 t] δ := by
  filter_upwards [eventually_gt_nhds ht] with s hs
  simp only [joinedCurve,ite_eq_right (not_le.mpr hs)]

lemma joinedCurve_germ_center (a : ℝ) {γ δ : ℝ → M} (he : γ =ᶠ[𝓝 a] δ) :
    joinedCurve a γ δ =ᶠ[𝓝 a] γ := by
  filter_upwards [he] with s hs
  dsimp only [joinedCurve]
  split_ifs
  · rfl
  · exact hs.symm

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem joinedCurve_smooth_on (a : ℝ) {γ δ : ℝ → M} {U : Set ℝ}
    (hγ : ∀ t ∈ U, t ≤ a → ContMDiffAt 𝓘(ℝ) I ∞ γ t)
    (hδ : ∀ t ∈ U, a ≤ t → ContMDiffAt 𝓘(ℝ) I ∞ δ t)
    (he : γ =ᶠ[𝓝 a] δ) :
    ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve a γ δ) U := by
  intro t ht
  rcases lt_trichotomy t a with h | heq | h
  · exact ((hγ t ht h.le).congr_of_eventuallyEq (joinedCurve_germ_left a γ δ h)).contMDiffWithinAt
  · subst t
    exact ((hγ a ht le_rfl).congr_of_eventuallyEq (joinedCurve_germ_center a he)).contMDiffWithinAt
  · exact ((hδ t ht h.le).congr_of_eventuallyEq (joinedCurve_germ_right a γ δ h)).contMDiffWithinAt

theorem joinedCurve_regular_on (a : ℝ) {γ δ : ℝ → M} {U : Set ℝ}
    (hγ : ∀ t ∈ U, t ≤ a → Function.Injective (mfderiv 𝓘(ℝ) I γ t))
    (hδ : ∀ t ∈ U, a ≤ t → Function.Injective (mfderiv 𝓘(ℝ) I δ t))
    (he : γ =ᶠ[𝓝 a] δ) :
    ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I (joinedCurve a γ δ) t) := by
  intro t ht
  rcases lt_trichotomy t a with h | heq | h
  · rw [(joinedCurve_germ_left a γ δ h).mfderiv_eq]
    exact hγ t ht h.le
  · subst t
    rw [(joinedCurve_germ_center a he).mfderiv_eq]
    exact hγ a ht le_rfl
  · rw [(joinedCurve_germ_right a γ δ h).mfderiv_eq]
    exact hδ t ht h.le

end Smooth

theorem joinedCurve_injective_on (a : ℝ) (γ δ : ℝ → M) (U : Set ℝ)
    (hγ : (U ∩ Iic a).InjOn γ) (hδ : (U ∩ Ioi a).InjOn δ)
    (hcross : ∀ s ∈ U, s ≤ a → ∀ t ∈ U, a < t → γ s ≠ δ t) :
    U.InjOn (joinedCurve a γ δ) := by
  intro s hs t ht he
  by_cases hsa : s ≤ a <;> by_cases hta : t ≤ a
  · exact hγ ⟨hs,hsa⟩ ⟨ht,hta⟩ (by simpa [joinedCurve,hsa,hta] using he)
  · exact False.elim (hcross s hs hsa t ht (lt_of_not_ge hta) (by simpa [joinedCurve,hsa,hta] using he))
  · exact False.elim (hcross t ht hta s hs (lt_of_not_ge hsa) (by simpa [joinedCurve,hsa,hta] using he.symm))
  · exact hδ ⟨hs,lt_of_not_ge hsa⟩ ⟨ht,lt_of_not_ge hta⟩ (by simpa [joinedCurve,hsa,hta] using he)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CompactArcJoin
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joining compact parameterized arcs preserves their precise image and
injectivity when their only shared point is the common endpoint. -/
noncomputable section
open Set
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*}

theorem joinedCurve_compact_image (γ δ : ℝ → N) (e : ℝ ≃ₜ ℝ)
    (he : StrictMono e) {l a d : ℝ} (hla : l ≤ a) (had : e a < d)
    (hpoint : γ a = δ (e a)) :
    joinedCurve a γ (δ ∘ e) '' Icc l (e.symm d) =
      γ '' Icc l a ∪ δ '' Icc (e a) d := by
  have haw : a < e.symm d := by
    apply he.lt_iff_lt.mp
    simpa only [e.apply_symm_apply] using had
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    by_cases hta : t ≤ a
    · exact Or.inl ⟨t,⟨ht.1,hta⟩,by simp only [joinedCurve,ite_eq_left hta]⟩
    · refine Or.inr ⟨e t,⟨he.monotone (le_of_not_ge hta),?_⟩,?_⟩
      · simpa only [e.apply_symm_apply] using he.monotone ht.2
      · simp only [joinedCurve,ite_eq_right hta,Function.comp_apply]
  · rintro y (⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩)
    · exact ⟨t,⟨ht.1,ht.2.trans haw.le⟩,by simp only [joinedCurve,ite_eq_left ht.2]⟩
    · have hlow : a ≤ e.symm t := by
        apply he.le_iff_le.mp
        simpa only [e.apply_symm_apply] using ht.1
      have hhigh : e.symm t ≤ e.symm d := (he.le_iff_le).mp (by simpa using ht.2)
      refine ⟨e.symm t,⟨hla.trans hlow,hhigh⟩,?_⟩
      by_cases hta : e.symm t ≤ a
      · have hta' : e.symm t = a := le_antisymm hta hlow
        have ht' : t = e a := by simpa only [e.apply_symm_apply] using congrArg e hta'
        rw [hta',ht']
        simpa only [joinedCurve,le_refl,ite_true, if_true] using hpoint
      · simp only [joinedCurve,ite_eq_right hta,Function.comp_apply,e.apply_symm_apply]

theorem joinedCurve_compact_injective (γ δ : ℝ → N) (e : ℝ ≃ₜ ℝ)
    (he : StrictMono e) {l a d : ℝ}
    (hγ : (Icc l a).InjOn γ) (hδ : (Icc (e a) d).InjOn δ)
    (hcross : ∀ s ∈ Icc l a, ∀ t ∈ Ioc (e a) d, γ s ≠ δ t) :
    (Icc l (e.symm d)).InjOn (joinedCurve a γ (δ ∘ e)) := by
  apply joinedCurve_injective_on
  · intro x hx y hy hxy
    exact hγ ⟨hx.1.1,hx.2⟩ ⟨hy.1.1,hy.2⟩ hxy
  · intro x hx y hy hxy
    apply e.injective
    apply hδ _ _ hxy
    · exact ⟨(he hx.2).le,by simpa only [e.apply_symm_apply] using he.monotone hx.1.2⟩
    · exact ⟨(he hy.2).le,by simpa only [e.apply_symm_apply] using he.monotone hy.1.2⟩
  · intro x hx hxa y hy hay
    exact hcross x ⟨hx.1,hxa⟩ (e y)
      ⟨he hay,by simpa only [e.apply_symm_apply] using he.monotone hy.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothCompactArc
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact regular embedded smooth arcs, and the actual joining operation
for arcs meeting through an oriented smooth parameter germ. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (N : Type*) [TopologicalSpace N] [ChartedSpace H N]

namespace SmoothCompactArc
variable {I N}

theorem join_with_parameter (P Q : SmoothCompactArc I N) (e : ℝ ≃ₜ ℝ)
    (hes : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hem : StrictMono e)
    (hea : e P.finish = Q.start)
    (hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ e)
    (hcross : ∀ s ∈ Icc P.start P.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.curve s ≠ Q.curve t) :
    ∃ R : SmoothCompactArc I N,
      R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve = joinedCurve P.finish P.curve (Q.curve ∘ e) ∧
      R.curve '' Icc R.start R.finish =
        P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish := by
  have haw : P.finish < e.symm Q.finish := by
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact Q.start_lt_finish
  let V := e ⁻¹' Q.domain
  let U := (P.domain ∩ Iio P.finish) ∪ (V ∩ Ioi P.finish) ∪ (P.domain ∩ V)
  have hV : IsOpen V := Q.domain_open.preimage e.continuous
  have hU : IsOpen U := (P.domain_open.inter isOpen_Iio).union (hV.inter isOpen_Ioi) |>.union (P.domain_open.inter hV)
  have hleft : ∀ t ∈ U, t ≤ P.finish → t ∈ P.domain := by
    intro t ht hta
    rcases ht with (ht | ht) | ht
    · exact ht.1
    · exact False.elim (not_lt_of_ge hta ht.2)
    · exact ht.1
  have hright : ∀ t ∈ U, P.finish ≤ t → e t ∈ Q.domain := by
    intro t ht hat
    rcases ht with (ht | ht) | ht
    · exact False.elim (not_lt_of_ge hat ht.2)
    · exact ht.1
    · exact ht.2
  have hsub : Icc P.start (e.symm Q.finish) ⊆ U := by
    intro t ht
    rcases lt_trichotomy t P.finish with h | rfl | h
    · exact Or.inl (Or.inl ⟨P.interval_subset ⟨ht.1,h.le⟩,h⟩)
    · exact Or.inr ⟨P.interval_subset (right_mem_Icc.mpr P.start_lt_finish.le),by
        change e P.finish ∈ Q.domain
        rw [hea]
        exact Q.interval_subset (left_mem_Icc.mpr Q.start_lt_finish.le)⟩
    · refine Or.inl (Or.inr ⟨?_,h⟩)
      apply Q.interval_subset
      refine ⟨?_,?_⟩
      · rw [← hea]; exact (hem h).le
      · simpa only [e.apply_symm_apply] using hem.monotone ht.2
  have hdif : e.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ) 𝓘(ℝ) :=
    ⟨hes.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
  have hsmooth : ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve P.finish P.curve (Q.curve ∘ e)) U := by
    apply joinedCurve_smooth_on
    · intro t ht hta
      exact P.smooth.contMDiffAt (P.domain_open.mem_nhds (hleft t ht hta))
    · intro t ht hat
      exact (Q.smooth.contMDiffAt (Q.domain_open.mem_nhds (hright t ht hat))).comp t hes.contMDiff.contMDiffAt
    · exact hmatch
  have hregular : ∀ t ∈ U, Function.Injective
      (mfderiv 𝓘(ℝ) I (joinedCurve P.finish P.curve (Q.curve ∘ e)) t) := by
    apply joinedCurve_regular_on
    · intro t ht hta
      exact P.regular t (hleft t ht hta)
    · intro t ht hat
      rw [mfderiv_comp t
        ((Q.smooth.contMDiffAt (Q.domain_open.mem_nhds (hright t ht hat))).mdifferentiableAt (by simp))
        (hes.contMDiff.mdifferentiable (by simp) t)]
      exact (Q.regular _ (hright t ht hat)).comp (hdif.mfderiv_injective (mem_univ t))
    · exact hmatch
  have hinj := joinedCurve_compact_injective P.curve Q.curve e hem P.injective
    (by simpa only [hea] using Q.injective) (by simpa only [hea] using hcross)
  let R : SmoothCompactArc I N := ⟨_,P.start,e.symm Q.finish,
    P.start_lt_finish.trans haw,U,hU,hsub,hsmooth,hregular,hinj⟩
  refine ⟨R,rfl,rfl,rfl,?_⟩
  exact (joinedCurve_compact_image P.curve Q.curve e hem P.start_lt_finish.le
    (by rw [hea]; exact Q.start_lt_finish) hmatch.eq_of_nhds).trans (by rw [hea])

theorem join (P Q : SmoothCompactArc I N) {h : ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) (hh : ContDiffOn ℝ ∞ h V) (haV : P.finish ∈ V)
    (hpos : 0 < deriv h P.finish) (hea : h P.finish = Q.start)
    (hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ h)
    (hcross : ∀ s ∈ Icc P.start P.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.curve s ≠ Q.curve t) :
    ∃ (R : SmoothCompactArc I N) (e : ℝ ≃ₜ ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
      e P.finish = Q.start ∧ R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve = joinedCurve P.finish P.curve (Q.curve ∘ e) ∧
      R.curve '' Icc R.start R.finish =
        P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish := by
  obtain ⟨e,hes,hei,hem,he⟩ := local_increasing_diffeomorphism hV hh haV hpos
  have he' : e P.finish = Q.start := he.eq_of_nhds.trans hea
  have hm : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ e := by
    filter_upwards [hmatch,he] with t ht ht'
    exact ht.trans (congrArg Q.curve ht'.symm)
  obtain ⟨R,hR⟩ := P.join_with_parameter Q e hes hei hem he' hm hcross
  exact ⟨R,e,hes,hei,hem,he',hR⟩

end SmoothCompactArc
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteRegularPathCover
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite expression of regular smooth path pieces has a finite
closed-interval cover by its actual affine-parametrized smooth pieces. -/
noncomputable section
open Set Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}

theorem FiniteRegularPath.cover (hγ : FiniteRegularPath J γ) :
    Nonempty (RegularPathCover (J := J) γ) := by
  induction hγ with
  | arc P => exact ⟨RegularPathCover.ofArc P⟩
  | subpath hγ s t ih => exact ⟨ih.some.subpath s t⟩
  | trans hγ hδ ihγ ihδ => exact ⟨ihγ.some.trans ihδ.some⟩
  | cast hγ hx hy ih => exact ⟨ih.some.cast hx hy⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularPathCoverGerms
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An embedded finite regular path has genuine regular smooth arc germs
outside a finite set of parameter values. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}
namespace RegularPathCover

theorem region_eq_interval (P : RegularPathCover (J := J) γ) (i : P.Index)
    (hne : (P.region i).Nonempty) :
    P.region i = Icc (sInf (P.region i)) (sSup (P.region i)) := by
  apply eq_Icc_of_connected_compact
  · exact ⟨hne,(P.convex i).isPreconnected⟩
  · exact isCompact_Icc.of_isClosed_subset (P.closed i) (P.subset i)

theorem regular_germs_outside_finite (P : RegularPathCover (J := J) γ)
    (hγ : Function.Injective γ) :
    ∃ S : Set ℝ, S.Finite ∧ ∀ t ∈ Ioo (0:ℝ) 1, t ∉ S →
      ∃ (A : SmoothCompactArc J M) (a b : ℝ), a ≠ 0 ∧
        a*t+b ∈ A.domain ∧ γ.extend =ᶠ[𝓝 t] (fun u => A.curve (a*u+b)) := by
  let _ := P.finite
  let S := range (fun i => sInf (P.region i)) ∪ range (fun i => sSup (P.region i))
  refine ⟨S,(finite_range _).union (finite_range _),?_⟩
  intro t ht htS
  let tI : I := ⟨t,⟨ht.1.le,ht.2.le⟩⟩
  obtain ⟨i,hi⟩ := P.cover tI
  have heq := P.region_eq_interval i ⟨t,hi⟩
  have hti : t ∈ Ioo (sInf (P.region i)) (sSup (P.region i)) := by
    have htcc : t ∈ Icc (sInf (P.region i)) (sSup (P.region i)) := heq ▸ hi
    refine ⟨lt_of_le_of_ne htcc.1 ?_,lt_of_le_of_ne htcc.2 ?_⟩
    · intro he
      exact htS (Or.inl ⟨i,he⟩)
    · intro he
      exact htS (Or.inr ⟨i,he.symm⟩)
  have hlr : sInf (P.region i) < sSup (P.region i) := hti.1.trans hti.2
  have hlmem : sInf (P.region i) ∈ P.region i := heq.symm.subset (left_mem_Icc.mpr hlr.le)
  have hrmem : sSup (P.region i) ∈ P.region i := heq.symm.subset (right_mem_Icc.mpr hlr.le)
  let l : I := ⟨sInf (P.region i),P.subset i hlmem⟩
  let r : I := ⟨sSup (P.region i),P.subset i hrmem⟩
  have ha : P.slope i ≠ 0 := by
    intro hz
    have hsame : γ l = γ r := by rw [P.agree i l hlmem,P.agree i r hrmem,hz]; simp
    have hval := congrArg (fun u : I => (u:ℝ)) (hγ hsame)
    exact hlr.ne hval
  refine ⟨P.arc i,P.slope i,P.offset i,ha,(P.arc i).interval_subset (P.parameter i t hi),?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds hti,isOpen_Ioo.mem_nhds ht] with u hu hu01
  have humem : u ∈ P.region i := by rw [heq]; exact ⟨hu.1.le,hu.2.le⟩
  rw [Path.extend_apply γ ⟨hu01.1.le,hu01.2.le⟩]
  exact P.agree i ⟨u,⟨hu01.1.le,hu01.2.le⟩⟩ humem

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteRegularPathSmooth
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from finitely many corners, an embedded finite regular path is
an actual smooth immersion of the real parameter. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}

lemma affine_parameter_regular {a b : ℝ} (ha : a ≠ 0) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun u : ℝ => a*u+b) t) := by
  have hA : HasDerivAt (fun u : ℝ => a*u+b) a t := by simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul a).add_const b
  have hD := hA.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hD]
  intro u v huv
  change ℝ at u v
  change u*a = v*a at huv
  exact (mul_right_cancel₀ ha huv : (u:ℝ) = (v:ℝ))

theorem FiniteRegularPath.smooth_outside_finite (hP : FiniteRegularPath J γ)
    (hi : Function.Injective γ) :
    ∃ S : Set ℝ, S.Finite ∧ ∀ t ∈ Ioo (0:ℝ) 1, t ∉ S →
      ContMDiffAt 𝓘(ℝ) J ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) J γ.extend t) := by
  obtain ⟨S,hS,hgerms⟩ := hP.cover.some.regular_germs_outside_finite hi
  refine ⟨S,hS,?_⟩
  intro t ht htS
  obtain ⟨A,a,b,ha,hab,he⟩ := hgerms t ht htS
  have hA := A.smooth.contMDiffAt (A.domain_open.mem_nhds hab)
  have hparam : ContDiff ℝ ∞ (fun u : ℝ => a*u+b) := by fun_prop
  have hC : ContMDiffAt 𝓘(ℝ) J ∞ (fun u : ℝ => A.curve (a*u+b)) t :=
    hA.comp t hparam.contMDiff.contMDiffAt
  refine ⟨hC.congr_of_eventuallyEq he,?_⟩
  have hreg : Function.Injective (mfderiv 𝓘(ℝ) J (fun u : ℝ => A.curve (a*u+b)) t) := by
    change Function.Injective (mfderiv 𝓘(ℝ) J (A.curve ∘ fun u : ℝ => a*u+b) t)
    rw [mfderiv_comp t (hA.mdifferentiableAt (by simp)) (hparam.contMDiff.mdifferentiable (by simp) t)]
    exact (A.regular _ hab).comp (affine_parameter_regular ha t)
  have hD := ((hC.mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq he).mfderiv
  exact hD.symm ▸ hreg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CommonCurveGraphs
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two regular plane curves admit actual smooth graph representatives in
one common linear coordinate system. No angle condition is required. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem common_curve_graphs {γ δ : ℝ → Base} (hγ : ContDiff ℝ ∞ γ)
    (hδ : ContDiff ℝ ∞ δ) {s t : ℝ} (hs : deriv γ s ≠ 0) (ht : deriv δ t ≠ 0) :
    ∃ (e : Base ≃L[ℝ] Base) (g h : ℝ → ℝ) (U V : Set ℝ),
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧ IsOpen U ∧ IsOpen V ∧ s ∈ U ∧ t ∈ V ∧
      (∀ u ∈ U, e (γ u) = ![(e (γ u)) 0,g ((e (γ u)) 0)]) ∧
      (∀ v ∈ V, e (δ v) = ![(e (δ v)) 0,h ((e (δ v)) 0)]) ∧
      deriv (fun u => (e (γ u)) 0) s ≠ 0 ∧ deriv (fun v => (e (δ v)) 0) t ≠ 0 := by
  obtain ⟨e,hes,het⟩ := exists_common_plane_coordinate hs ht
  have hγe : HasDerivAt (e ∘ γ) (e (deriv γ s)) s :=
    e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hγ.differentiable (by simp) s).hasDerivAt
  have hδe : HasDerivAt (e ∘ δ) (e (deriv δ t)) t :=
    e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hδ.differentiable (by simp) t).hasDerivAt
  have hs0 : deriv (fun u => (e (γ u)) 0) s ≠ 0 := by
    have h := (hasDerivAt_pi.mp hγe 0).deriv
    dsimp only [Function.comp_apply] at h
    rw [h]
    exact hes
  have ht0 : deriv (fun v => (e (δ v)) 0) t ≠ 0 := by
    have h := (hasDerivAt_pi.mp hδe 0).deriv
    dsimp only [Function.comp_apply] at h
    rw [h]
    exact het
  obtain ⟨g,U,hg,hU,hsU,hγgraph⟩ := plane_curve_graph (e.contDiff.comp hγ) s hs0
  obtain ⟨h,V,hh,hV,htV,hδgraph⟩ := plane_curve_graph (e.contDiff.comp hδ) t ht0
  exact ⟨e,g,h,U,V,hg,hh,hU,hV,hsU,htV,hγgraph,hδgraph,hs0,ht0⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceCurveRepresentative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular surface curve has an actual smooth Euclidean representative
in any selected surface chart through its base point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_curve_chart_representative {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    {t : ℝ} (ht : t ∈ U) (p : M) (hp : γ t ∈ (chart p).source)
    (hr : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)) :
    ∃ (F : ℝ → Base) (V : Set ℝ), ContDiff ℝ ∞ F ∧ IsOpen V ∧ t ∈ V ∧ V ⊆ U ∧
      (∀ u ∈ V, γ u ∈ (chart p).source ∧ F u = chart p (γ u)) ∧ deriv F t ≠ 0 := by
  let W := U ∩ γ ⁻¹' (chart p).source
  have hW : IsOpen W := hγ.continuousOn.isOpen_inter_preimage hU (chart p).open_source
  have htW : t ∈ W := ⟨ht,hp⟩
  let φ : ℝ → Base := chart p ∘ γ
  have hφ : ContDiffOn ℝ ∞ φ W :=
    ((chart_smooth p).comp (hγ.mono inter_subset_left) (fun _ hu => hu.2)).contDiffOn
  obtain ⟨V,hV,htV,hVW,F,hF,hFφ⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := t)) hW (singleton_subset_iff.mpr htW) hφ
  have he : F =ᶠ[𝓝 t] φ := hFφ.eventuallyEq_of_mem (hV.mem_nhds (htV (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)))
  have hφi : Function.Injective (fderiv ℝ φ t) := by
    rw [← mfderiv_eq_fderiv,mfderiv_comp t
      (((chart_smooth p).contMDiffAt ((chart p).open_source.mem_nhds hp)).mdifferentiableAt (by simp))
      ((hγ.contMDiffAt (hU.mem_nhds ht)).mdifferentiableAt (by simp))]
    exact ((chart_mdifferentiable p).mfderiv_injective hp).comp hr
  have hFi : Function.Injective (fderiv ℝ F t) := by rw [he.fderiv_eq]; exact hφi
  have hFn : deriv F t ≠ 0 := by
    intro hz
    have h01 : fderiv ℝ F t 1 = fderiv ℝ F t 0 := by
      rw [fderiv_apply_one_eq_deriv,hz,map_zero]
    have hn := hFi h01
    norm_num at hn
  refine ⟨F,V,hF,hV,htV (by simp),hVW.trans inter_subset_left,?_,hFn⟩
  intro u hu
  exact ⟨(hVW hu).2,hFφ hu⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CommonSurfaceCurveGraphs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual common smooth surface coordinates and graph representatives
for two regular curve germs meeting at one surface point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem common_surface_curve_graphs {γ δ : ℝ → M} {A B : Set ℝ}
    (hA : IsOpen A) (hB : IsOpen B)
    (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ A) (hδ : ContMDiffOn 𝓘(ℝ) planeModel ∞ δ B)
    {s t : ℝ} (hs : s ∈ A) (ht : t ∈ B) (hpoint : γ s = δ t)
    (hγr : Function.Injective (mfderiv 𝓘(ℝ) planeModel γ s))
    (hδr : Function.Injective (mfderiv 𝓘(ℝ) planeModel δ t)) :
    ∃ (c : OpenPartialHomeomorph M Base) (g h : ℝ → ℝ) (U V : Set ℝ),
      ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target ∧
      ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ h ∧ IsOpen U ∧ IsOpen V ∧
      s ∈ U ∧ t ∈ V ∧ U ⊆ A ∧ V ⊆ B ∧
      (∀ u ∈ U, γ u ∈ c.source ∧ c (γ u) = ![c (γ u) 0,g (c (γ u) 0)]) ∧
      (∀ v ∈ V, δ v ∈ c.source ∧ c (δ v) = ![c (δ v) 0,h (c (δ v) 0)]) ∧
      deriv (fun u => c (γ u) 0) s ≠ 0 ∧ deriv (fun v => c (δ v) 0) t ≠ 0 := by
  let p := γ s
  have hp : γ s ∈ (chart p).source := by
    simpa only [p,chart_source] using mem_chart_source Plane (γ s)
  have hp' : δ t ∈ (chart p).source := hpoint ▸ hp
  obtain ⟨F,I,hF,hI,hsI,hIA,hFI,hFr⟩ := surface_curve_chart_representative hA hγ hs p hp hγr
  obtain ⟨G,J,hG,hJ,htJ,hJB,hGJ,hGr⟩ := surface_curve_chart_representative hB hδ ht p hp' hδr
  obtain ⟨e,g,h,U,V,hg,hh,hU,hV,hsU,htV,hFg,hGh,hFd,hGd⟩ := common_curve_graphs hF hG hFr hGr
  let c := (chart p).trans e.toHomeomorph.toOpenPartialHomeomorph
  have hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source :=
    e.contDiff.contMDiff.comp_contMDiffOn ((chart_smooth p).mono inter_subset_left)
  have hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target :=
    (chart_symm_smooth p).comp e.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)
  refine ⟨c,g,h,I ∩ U,J ∩ V,hcs,hci,hg,hh,hI.inter hU,hJ.inter hV,
    ⟨hsI,hsU⟩,⟨htJ,htV⟩,inter_subset_left.trans hIA,inter_subset_left.trans hJB,?_,?_,?_,?_⟩
  · intro u hu
    refine ⟨⟨(hFI u hu.1).1,mem_univ _⟩,?_⟩
    have he := hFg u hu.2
    rw [(hFI u hu.1).2] at he
    exact he
  · intro v hv
    refine ⟨⟨(hGJ v hv.1).1,mem_univ _⟩,?_⟩
    have he := hGh v hv.2
    rw [(hGJ v hv.1).2] at he
    exact he
  · have he : (fun u => c (γ u) 0) =ᶠ[𝓝 s] (fun u => e (F u) 0) := by
      filter_upwards [hI.mem_nhds hsI] with u hu
      change e (chart p (γ u)) 0 = e (F u) 0
      rw [(hFI u hu).2]
    rw [he.deriv_eq]
    exact hFd
  · have he : (fun v => c (δ v) 0) =ᶠ[𝓝 t] (fun v => e (G v) 0) := by
      filter_upwards [hJ.mem_nhds htJ] with v hv
      change e (chart p (δ v)) 0 = e (G v) 0
      rw [(hGJ v hv).2]
    rw [he.deriv_eq]
    exact hGd

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NonzeroGermDiffeomorphism
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A scalar smooth coordinate with nonzero derivative has a global smooth
homeomorphism representative of either orientation. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem nonzero_smooth_germ_diffeomorphism {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (a : ℝ) (ha : deriv h a ≠ 0) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (StrictMono e ∨ StrictAnti e) ∧ e =ᶠ[𝓝 a] h := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hn : ContDiff ℝ ∞ (fun x => -h x) := hh.neg
    have hd : 0 < deriv (fun x => -h x) a := by
      rw [show (fun x => -h x) = -h from rfl, deriv.neg]
      exact neg_pos.mpr hneg
    obtain ⟨e,hes,hei,hem,he⟩ := increasing_smooth_germ_diffeomorphism hn a hd
    let E := e.trans (Homeomorph.neg ℝ)
    have hEs : ContDiff ℝ ∞ E := contDiff_neg.comp hes
    have hEi : ContDiff ℝ ∞ E.symm := hei.comp contDiff_neg
    have hEm : StrictAnti E := by
      intro x y hxy
      exact neg_lt_neg (hem hxy)
    refine ⟨E,hEs,hEi,Or.inr hEm,?_⟩
    filter_upwards [he] with x hx
    change -e x = h x
    rw [hx,neg_neg]
  · obtain ⟨e,hes,hei,hem,he⟩ := increasing_smooth_germ_diffeomorphism hh a hpos
    exact ⟨e,hes,hei,Or.inl hem,he⟩

theorem nonzero_local_germ_diffeomorphism {h : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U) {a : ℝ}
    (haU : a ∈ U) (ha : deriv h a ≠ 0) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (StrictMono e ∨ StrictAnti e) ∧ e =ᶠ[𝓝 a] h := by
  obtain ⟨W,hW,haW,_,H,hH,hEH⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := a)) hU (singleton_subset_iff.mpr haU) hh
  have he : H =ᶠ[𝓝 a] h := hEH.eventuallyEq_of_mem (hW.mem_nhds (haW (by simp)))
  have hd : deriv H a ≠ 0 := by rw [he.deriv_eq]; exact ha
  obtain ⟨e,hes,hei,hem,hee⟩ := nonzero_smooth_germ_diffeomorphism hH a hd
  exact ⟨e,hes,hei,hem,hee.trans he⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceGraphParameter
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth inverse parameters for actual graph branches in a surface chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem surface_graph_parameter {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ U)
    (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (g : ℝ → ℝ) (hgraph : ∀ u ∈ U, γ u ∈ c.source ∧
      c (γ u) = ![c (γ u) 0,g (c (γ u) 0)])
    {s : ℝ} (hs : s ∈ U) (hd : deriv (fun u => c (γ u) 0) s ≠ 0) :
    ∃ (e : ℝ ≃ₜ ℝ) (W : Set ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      (StrictMono e ∨ StrictAnti e) ∧ IsOpen W ∧ s ∈ W ∧ W ⊆ U ∧
      (∀ u ∈ W, e u = c (γ u) 0) ∧
      IsOpen (e '' W) ∧ e s ∈ e '' W ∧
      (∀ x ∈ e '' W, ![x,g x] ∈ c.target ∧
        c.symm ![x,g x] = γ (e.symm x)) := by
  have hcoord : ContDiffOn ℝ ∞ (fun u => c (γ u) 0) U :=
    (contDiff_apply ℝ ℝ 0).comp_contDiffOn
      (hcs.comp hγ (fun u hu => (hgraph u hu).1)).contDiffOn
  obtain ⟨e,he,hei,hem,hee⟩ := nonzero_local_germ_diffeomorphism hU hcoord hs hd
  obtain ⟨V,hV,hsV,hVe⟩ := mem_nhds_iff.mp hee
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hsV
  have hsW : s ∈ W := ⟨hs,hVe⟩
  refine ⟨e,W,he,hei,hem,hW,hsW,inter_subset_left,?_,e.isOpenMap _ hW,
    mem_image_of_mem e hsW,?_⟩
  · intro u hu
    exact hV hu.2
  · rintro x ⟨u,hu,rfl⟩
    have heq : c (γ u) = ![e u,g (e u)] := by
      rw [hV hu.2]
      exact (hgraph u hu.1).2
    refine ⟨heq ▸ c.map_source (hgraph u hu.1).1,?_⟩
    rw [e.symm_apply_apply,← heq,c.left_inv (hgraph u hu.1).1]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularPathCornerPieces
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At each interior parameter, a finite interval cover supplies actual
regular smooth pieces on both sides, including their common endpoint. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}
namespace RegularPathCover

theorem one_sided_intervals (P : RegularPathCover (J := J) γ) {t : ℝ}
    (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ (i j : P.Index) (l r : ℝ), l < t ∧ t < r ∧
      Icc l t ⊆ P.region i ∧ Icc t r ⊆ P.region j := by
  let _ := P.finite
  have hL : ∀ᶠ u in 𝓝[<] t, ∃ i, u ∈ P.region i := by
    filter_upwards [(eventually_gt_nhds ht.1).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hut
    exact P.cover ⟨u,⟨hu.le,hut.le.trans ht.2.le⟩⟩
  have hR : ∀ᶠ u in 𝓝[>] t, ∃ i, u ∈ P.region i := by
    filter_upwards [(eventually_lt_nhds ht.2).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hut
    exact P.cover ⟨u,⟨ht.1.le.trans hut.le,hu.le⟩⟩
  obtain ⟨i,hi⟩ := frequently_exists.mp hL.frequently
  obtain ⟨j,hj⟩ := frequently_exists.mp hR.frequently
  have hti : t ∈ P.region i := (P.closed i).mem_of_frequently_of_tendsto hi
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  have htj : t ∈ P.region j := (P.closed j).mem_of_frequently_of_tendsto hj
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  obtain ⟨l,hli,hlt⟩ := (hi.and_eventually self_mem_nhdsWithin).exists
  obtain ⟨r,hrj,htr⟩ := (hj.and_eventually self_mem_nhdsWithin).exists
  exact ⟨i,j,l,r,hlt,htr,(P.convex i).ordConnected.out hli hti,
    (P.convex j).ordConnected.out htj hrj⟩

theorem nonzero_slope_on_interval (P : RegularPathCover (J := J) γ)
    (hγ : Function.Injective γ) (i : P.Index) {l r : ℝ}
    (hlr : l < r) (hsub : Icc l r ⊆ P.region i) : P.slope i ≠ 0 := by
  intro hz
  have hl := hsub (left_mem_Icc.mpr hlr.le)
  have hr := hsub (right_mem_Icc.mpr hlr.le)
  let lI : I := ⟨l,P.subset i hl⟩
  let rI : I := ⟨r,P.subset i hr⟩
  have he : γ lI = γ rI := by rw [P.agree i lI hl,P.agree i rI hr,hz]; simp
  have hh := congrArg (fun t : I => (t:ℝ)) (hγ he)
  exact hlr.ne hh

theorem one_sided_regular_pieces (P : RegularPathCover (J := J) γ)
    (hγ : Function.Injective γ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    ∃ (A B : SmoothCompactArc J M) (a b c d l r : ℝ),
      l < t ∧ t < r ∧ a ≠ 0 ∧ c ≠ 0 ∧
      (∀ u ∈ Icc l t, a*u+b ∈ A.domain ∧ γ.extend u = A.curve (a*u+b)) ∧
      (∀ u ∈ Icc t r, c*u+d ∈ B.domain ∧ γ.extend u = B.curve (c*u+d)) := by
  obtain ⟨i,j,l,r,hlt,htr,hL,hR⟩ := P.one_sided_intervals ht
  refine ⟨P.arc i,P.arc j,P.slope i,P.offset i,P.slope j,P.offset j,l,r,
    hlt,htr,P.nonzero_slope_on_interval hγ i hlt hL,P.nonzero_slope_on_interval hγ j htr hR,?_,?_⟩
  · intro u hu
    have humem := hL hu
    have hu01 := P.subset i humem
    refine ⟨(P.arc i).interval_subset (P.parameter i u humem),?_⟩
    rw [Path.extend_apply γ hu01]
    exact P.agree i ⟨u,hu01⟩ humem
  · intro u hu
    have humem := hR hu
    have hu01 := P.subset j humem
    refine ⟨(P.arc j).interval_subset (P.parameter j u humem),?_⟩
    rw [Path.extend_apply γ hu01]
    exact P.agree j ⟨u,hu01⟩ humem

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularPathCornerChart
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual common graph charts at every corner of an embedded finite regular path. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem regular_path_corner_chart {x y : M} {γ : Path x y}
    (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : Nonempty (RegularPathCornerChart γ t) := by
  obtain ⟨A,B,a,b,c,d,l,r,hlt,htr,ha,hc,hL,hR⟩ :=
    hγ.cover.some.one_sided_regular_pieces hi ht
  let F : ℝ → M := fun u => A.curve (a*u+b)
  let G : ℝ → M := fun u => B.curve (c*u+d)
  let U : Set ℝ := (fun u : ℝ => a*u+b) ⁻¹' A.domain
  let V : Set ℝ := (fun u : ℝ => c*u+d) ⁻¹' B.domain
  have hsF : ContDiff ℝ ∞ (fun u : ℝ => a*u+b) := by fun_prop
  have hsG : ContDiff ℝ ∞ (fun u : ℝ => c*u+d) := by fun_prop
  have hU : IsOpen U := A.domain_open.preimage hsF.continuous
  have hV : IsOpen V := B.domain_open.preimage hsG.continuous
  have htU : t ∈ U := (hL t ⟨hlt.le,le_rfl⟩).1
  have htV : t ∈ V := (hR t ⟨le_rfl,htr.le⟩).1
  have hF : ContMDiffOn 𝓘(ℝ) planeModel ∞ F U :=
    A.smooth.comp hsF.contMDiff.contMDiffOn (fun _ hu => hu)
  have hG : ContMDiffOn 𝓘(ℝ) planeModel ∞ G V :=
    B.smooth.comp hsG.contMDiff.contMDiffOn (fun _ hu => hu)
  have hFi : Function.Injective (mfderiv 𝓘(ℝ) planeModel F t) := by
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (A.curve ∘ fun u : ℝ => a*u+b) t)
    rw [mfderiv_comp t ((A.smooth.contMDiffAt (A.domain_open.mem_nhds htU)).mdifferentiableAt (by simp))
      (hsF.contMDiff.mdifferentiable (by simp) t)]
    exact (A.regular _ htU).comp (affine_parameter_regular ha t)
  have hGi : Function.Injective (mfderiv 𝓘(ℝ) planeModel G t) := by
    change Function.Injective (mfderiv 𝓘(ℝ) planeModel (B.curve ∘ fun u : ℝ => c*u+d) t)
    rw [mfderiv_comp t ((B.smooth.contMDiffAt (B.domain_open.mem_nhds htV)).mdifferentiableAt (by simp))
      (hsG.contMDiff.mdifferentiable (by simp) t)]
    exact (B.regular _ htV).comp (affine_parameter_regular hc t)
  have hmeet : F t = G t := (hL t ⟨hlt.le,le_rfl⟩).2.symm.trans (hR t ⟨le_rfl,htr.le⟩).2
  obtain ⟨q,f,g,U1,V1,hqs,hqi,hf,hg,hI,hJ,htI,htJ,hIU,hJV,hIF,hJG,hdF,hdG⟩ :=
    common_surface_curve_graphs hU hV hF hG htU htV hmeet hFi hGi
  obtain ⟨e,W,he,hei,hem,hW,htW,hWI,heW,_⟩ :=
    surface_graph_parameter hI (hF.mono hIU) q hqs f hIF htI hdF
  obtain ⟨e',W',he',hei',hem',hW',htW',hWJ,heW',_⟩ :=
    surface_graph_parameter hJ (hG.mono hJV) q hqs g hJG htJ hdG
  have hn : W ∩ W' ∩ Ioo l r ∩ Ioo (0:ℝ) 1 ∈ 𝓝 t :=
    by
      filter_upwards [hW.mem_nhds htW,hW'.mem_nhds htW',
        isOpen_Ioo.mem_nhds ⟨hlt,htr⟩,isOpen_Ioo.mem_nhds ht] with u hu hv hlr h01
      exact ⟨⟨⟨hu,hv⟩,hlr⟩,h01⟩
  obtain ⟨l₀,r₀,⟨hl₀,hr₀⟩,hsub₀⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  obtain ⟨l',hll₀,hlt'⟩ := exists_between hl₀
  obtain ⟨r',htr',hrr₀⟩ := exists_between hr₀
  have hsub : Icc l' r' ⊆ W ∩ W' ∩ Ioo l r ∩ Ioo (0:ℝ) 1 :=
    fun _ hu => hsub₀ ⟨hll₀.trans_le hu.1,hu.2.trans_lt hrr₀⟩
  have hll := hsub (left_mem_Icc.mpr (hlt'.trans htr').le)
  have hrr := hsub (right_mem_Icc.mpr (hlt'.trans htr').le)
  have hleft : ∀ u ∈ Icc l' t, γ.extend u ∈ q.source ∧
      q (γ.extend u) = ![e u,f (e u)] := by
    intro u hu
    have hum := hsub ⟨hu.1,hu.2.trans htr'.le⟩
    have hp := hL u ⟨hll.1.2.1.le.trans hu.1,hu.2⟩
    rw [hp.2]
    exact ⟨(hIF u (hWI hum.1.1.1)).1,by
      rw [heW u hum.1.1.1]
      exact (hIF u (hWI hum.1.1.1)).2⟩
  have hright : ∀ u ∈ Icc t r', γ.extend u ∈ q.source ∧
      q (γ.extend u) = ![e' u,g (e' u)] := by
    intro u hu
    have hum := hsub ⟨hlt'.le.trans hu.1,hu.2⟩
    have hp := hR u ⟨hu.1,hu.2.trans hrr.1.2.2.le⟩
    rw [hp.2]
    exact ⟨(hJG u (hWJ hum.1.1.2)).1,by
      rw [heW' u hum.1.1.2]
      exact (hJG u (hWJ hum.1.1.2)).2⟩
  refine ⟨⟨q,hqs,hqi,f,g,hf,hg,e,e',he,he',hei,hei',hem,hem',l',r',hll.2.1,
    hlt',htr',hrr.2.2,hleft,hright,?_⟩⟩
  have H := (hleft t ⟨hlt'.le,le_rfl⟩).2.symm.trans (hright t ⟨le_rfl,htr'.le⟩).2
  exact congrFun H 0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_PathCornerNeighborhood
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small neighborhood of an interior point of an embedded compact path
avoids any prescribed compact exterior parameter intervals. -/
noncomputable section
open Set Filter unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] {p q : M}

lemma embeddedPath_extend_injOn (γ : Path p q) (hi : Function.Injective γ) :
    InjOn γ.extend (Icc (0:ℝ) 1) := by
  intro u hu v hv he
  rw [Path.extend_apply γ hu,Path.extend_apply γ hv] at he
  exact congrArg (fun z : I => (z:ℝ)) (hi he)

variable [T2Space M]

theorem embedded_path_corner_neighborhood (γ : Path p q) (hi : Function.Injective γ)
    {a t b : ℝ} (ha : 0 ≤ a) (hat : a < t) (htb : t < b) (hb : b ≤ 1)
    {O : Set M} (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ V : Set M, IsOpen V ∧ γ.extend t ∈ V ∧ V ⊆ O ∧
      ∀ u ∈ Icc (0:ℝ) a ∪ Icc b 1, γ.extend u ∉ V := by
  let K := γ.extend '' (Icc (0:ℝ) a ∪ Icc b 1)
  have hK : IsCompact K := (isCompact_Icc.union isCompact_Icc).image γ.continuous_extend
  have htK : γ.extend t ∉ K := by
    rintro ⟨u,hu,he⟩
    have ht01 : t ∈ Icc (0:ℝ) 1 := ⟨ha.trans hat.le,htb.le.trans hb⟩
    have hu01 : u ∈ Icc (0:ℝ) 1 := by
      rcases hu with hu | hu
      · exact ⟨hu.1,hu.2.trans (hat.le.trans ht01.2)⟩
      · exact ⟨(ht01.1.trans htb.le).trans hu.1,hu.2⟩
    have heu := embeddedPath_extend_injOn γ hi hu01 ht01 he
    subst u
    rcases hu with hu | hu
    · exact (not_le_of_gt hat) hu.2
    · exact (not_le_of_gt htb) hu.1
  refine ⟨O \ K,hO.sdiff hK.isClosed,⟨htO,htK⟩,sdiff_subset,?_⟩
  intro u hu hv
  exact hv.2 ⟨u,hu,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OriginalRegularSegment
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact unchanged portions of the path between its exceptional
parameters are actual smooth regular embedded arcs. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q}

theorem original_regular_segment (hi : Function.Injective γ)
    {U : Set ℝ} (hU : IsOpen U) (hU01 : U ⊆ Ioo (0:ℝ) 1)
    (hreg : ∀ t ∈ U, ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t))
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ U) :
    ∃ P : SmoothCompactArc planeModel M,
      P.start = a ∧ P.finish = b ∧ P.curve = γ.extend := by
  have hs : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ.extend U :=
    fun t ht => (hreg t ht).1.contMDiffWithinAt
  have hsub01 : Icc a b ⊆ Icc (0:ℝ) 1 :=
    fun t ht => ⟨(hU01 (hsub ht)).1.le,(hU01 (hsub ht)).2.le⟩
  have hinj : InjOn γ.extend (Icc a b) := (embeddedPath_extend_injOn γ hi).mono hsub01
  exact ⟨⟨γ.extend,a,b,hab,U,hU,hsub,hs,fun t ht => (hreg t ht).2,hinj⟩,rfl,rfl,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RoundedReturnCurve
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit embedded U-turn between disjoint graph branches. It is
flatly equal to the lower and upper graphs at the two ends. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma roundedReturnCurve_smooth {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (a b : ℝ) : ContDiff ℝ ∞ (roundedReturnCurve f g a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t : ℝ => a+b*t^2)
    fun_prop
  · change ContDiff ℝ ∞ (fun t : ℝ =>
      (1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2))
    exact ((contDiff_const.sub centeredSmoothStep_smooth).mul (hf.comp (by fun_prop))).add
      (centeredSmoothStep_smooth.mul (hg.comp (by fun_prop)))

lemma roundedReturnCurve_left {f g : ℝ → ℝ} {a b t : ℝ} (ht : t ≤ -1) :
    roundedReturnCurve f g a b t = ![a+b*t^2,f (a+b*t^2)] := by
  simp [roundedReturnCurve,centeredSmoothStep_zero ht]

lemma roundedReturnCurve_right {f g : ℝ → ℝ} {a b t : ℝ} (ht : 1 ≤ t) :
    roundedReturnCurve f g a b t = ![a+b*t^2,g (a+b*t^2)] := by
  simp [roundedReturnCurve,centeredSmoothStep_one ht]

lemma roundedReturnCurve_coordinate_bound {f g : ℝ → ℝ} {a b T t : ℝ}
    (hb : 0 ≤ b) (ht : t ∈ Icc (-T) T) :
    (roundedReturnCurve f g a b t) 0 ∈ Icc a (a+b*T^2) := by
  change a+b*t^2 ∈ Icc a (a+b*T^2)
  have hsq : t^2 ≤ T^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ T+t by linarith [ht.1])
    nlinarith
  constructor
  · nlinarith [mul_nonneg hb (sq_nonneg t)]
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hb)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RoundedReturnRegular
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit graph U-turn has nonzero velocity even at its turning
point; away from it, the first coordinate already has nonzero derivative. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma plane_curve_regular_of_hasDerivAt {C : ℝ → Base} {v : Base} {t : ℝ}
    (hC : HasDerivAt C v t) {i : Fin 2} (hi : v i ≠ 0) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) C t) := by
  have hD := hC.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hD]
  intro x y hxy
  change ℝ at x y
  have h := congrFun hxy i
  change x*v i = y*v i at h
  exact (mul_right_cancel₀ hi h : (x : ℝ) = (y : ℝ))

lemma roundedReturnCurve_hasDerivAt_zero {f g : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a) :
    HasDerivAt (roundedReturnCurve f g a b) (![0,g a-f a] : Base) 0 := by
  have hx : HasDerivAt (fun t : ℝ => a+b*t^2) 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).const_mul b).const_add a using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  have hF : HasDerivAt (fun t : ℝ => f (a+b*t^2)) 0 0 := by
    have hf' : HasDerivAt f (deriv f a) (a+b*(0:ℝ)^2) := by simpa using hf.hasDerivAt
    simpa only [mul_zero,Function.comp_def] using hf'.comp 0 hx
  have hG : HasDerivAt (fun t : ℝ => g (a+b*t^2)) 0 0 := by
    have hg' : HasDerivAt g (deriv g a) (a+b*(0:ℝ)^2) := by simpa using hg.hasDerivAt
    simpa only [mul_zero,Function.comp_def] using hg'.comp 0 hx
  have hy : HasDerivAt (fun t : ℝ =>
      (1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2)) (g a-f a) 0 := by
    convert ((centeredSmoothStep_hasDerivAt_zero.const_sub 1).mul hF).add
      (centeredSmoothStep_hasDerivAt_zero.mul hG) using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (norm_num; ring)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hx
  · exact hy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SmallGraphBlends
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All convex interpolations between two graphs remain in a prescribed
neighborhood when their common base point is approached. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma graphPoint_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (graphPoint f) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_id
  · exact hf

lemma roundedReturnCurve_eq_blend (f g : ℝ → ℝ) (a b t : ℝ) :
    roundedReturnCurve f g a b t =
      (1-centeredSmoothStep t) • graphPoint f (a+b*t^2) +
        centeredSmoothStep t • graphPoint g (a+b*t^2) := by
  ext i
  fin_cases i
  · change a+b*t^2 = (1-centeredSmoothStep t)*(a+b*t^2)+centeredSmoothStep t*(a+b*t^2)
    ring
  · rfl

theorem small_graph_blends {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (x : ℝ) (he : f x = g x) {V : Set Base} (hV : IsOpen V)
    (hx : graphPoint f x ∈ V) :
    ∃ δ > 0, ∀ y ∈ Ioo (x-δ) (x+δ), ∀ s ∈ Icc (0:ℝ) 1,
      (1-s) • graphPoint f y + s • graphPoint g y ∈ V := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hV _ hx
  have hcenter : graphPoint f x = graphPoint g x := by simp [graphPoint,he]
  have hF : ∀ᶠ y in 𝓝 x, graphPoint f y ∈ Metric.ball (graphPoint f x) ε :=
    (graphPoint_continuous hf).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  have hG : ∀ᶠ y in 𝓝 x, graphPoint g y ∈ Metric.ball (graphPoint f x) ε := by
    rw [hcenter]
    exact (graphPoint_continuous hg).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
  obtain ⟨δ,hδ,hsmall⟩ := Metric.eventually_nhds_iff.mp (hF.and hG)
  refine ⟨δ,hδ,?_⟩
  intro y hy s hs
  have hyd : dist y x < δ := by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩
  obtain ⟨hfy,hgy⟩ := hsmall hyd
  apply hball
  exact (convex_ball (graphPoint f x) ε) hfy hgy (sub_nonneg.mpr hs.2) hs.1 (by ring)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledGraphJoin
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A graph corner can be rounded at an arbitrarily small horizontal scale. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma scaledGraphJoin_smooth {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (a b : ℝ) : ContDiff ℝ ∞ (scaledGraphJoin f g a b) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun t => a+b*t)
    fun_prop
  · change ContDiff ℝ ∞ (fun t => (1-centeredSmoothStep t)*f (a+b*t)+centeredSmoothStep t*g (a+b*t))
    exact ((contDiff_const.sub centeredSmoothStep_smooth).mul (hf.comp (by fun_prop))).add
      (centeredSmoothStep_smooth.mul (hg.comp (by fun_prop)))

lemma scaledGraphJoin_injective (f g : ℝ → ℝ) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Function.Injective (scaledGraphJoin f g a b) := by
  intro t u he
  have hx := congrFun he 0
  change a+b*t = a+b*u at hx
  exact mul_left_cancel₀ hb (add_left_cancel hx)

lemma scaledGraphJoin_regular {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (a : ℝ) {b : ℝ} (hb : b ≠ 0) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (scaledGraphJoin f g a b) t) := by
  have hC := (scaledGraphJoin_smooth hf hg a b).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t
  have hc0 := hasDerivAt_pi.mp hC.hasDerivAt 0
  have hx : HasDerivAt (fun u : ℝ => a+b*u) b t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul b).const_add a
  apply plane_curve_regular_of_hasDerivAt hC.hasDerivAt (i := 0)
  rw [hc0.unique hx]
  exact hb

lemma scaledGraphJoin_eq_blend (f g : ℝ → ℝ) (a b t : ℝ) :
    scaledGraphJoin f g a b t = (1-centeredSmoothStep t) • graphPoint f (a+b*t) +
      centeredSmoothStep t • graphPoint g (a+b*t) := by
  ext i
  fin_cases i
  · change a+b*t = (1-centeredSmoothStep t)*(a+b*t)+centeredSmoothStep t*(a+b*t)
    ring
  · rfl

theorem scaled_graph_join_arc {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ∃ P : SmoothCompactArc 𝓘(ℝ,Base) Base,
      P.start = -2 ∧ P.finish = 2 ∧ P.curve = scaledGraphJoin f g a b ∧
      P.curve =ᶠ[𝓝 P.start] (fun t => ![a+b*t,f (a+b*t)]) ∧
      P.curve =ᶠ[𝓝 P.finish] (fun t => ![a+b*t,g (a+b*t)]) := by
  let P : SmoothCompactArc 𝓘(ℝ,Base) Base :=
    ⟨scaledGraphJoin f g a b,-2,2,by norm_num,univ,isOpen_univ,subset_univ _,
      (scaledGraphJoin_smooth hf hg a b).contMDiff.contMDiffOn,
      fun t _ => scaledGraphJoin_regular hf hg a hb t,
      (scaledGraphJoin_injective f g a hb).injOn⟩
  refine ⟨P,rfl,rfl,rfl,?_,?_⟩
  · filter_upwards [eventually_lt_nhds (show (-2:ℝ) < -1 by norm_num)] with t ht
    simp [P,scaledGraphJoin,centeredSmoothStep_zero ht.le]
  · filter_upwards [eventually_gt_nhds (show (1:ℝ) < 2 by norm_num)] with t ht
    simp [P,scaledGraphJoin,centeredSmoothStep_one ht.le]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CornerGraphSeparation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embeddedness forces strict separation of the two returning graph branches. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

lemma left_graph_realized (C : RegularPathCornerChart γ t) {x : ℝ}
    (hx : x ∈ C.leftParameter '' Icc C.lower t) :
    ![x,C.leftGraph x] ∈ C.chart.target ∧
      C.chart.symm ![x,C.leftGraph x] = γ.extend (C.leftParameter.symm x) := by
  obtain ⟨u,hu,rfl⟩ := hx
  have h := C.left_chart u hu
  refine ⟨h.2 ▸ C.chart.map_source h.1,?_⟩
  rw [C.leftParameter.symm_apply_apply,← h.2,C.chart.left_inv h.1]

lemma right_graph_realized (C : RegularPathCornerChart γ t) {x : ℝ}
    (hx : x ∈ C.rightParameter '' Icc t C.upper) :
    ![x,C.rightGraph x] ∈ C.chart.target ∧
      C.chart.symm ![x,C.rightGraph x] = γ.extend (C.rightParameter.symm x) := by
  obtain ⟨u,hu,rfl⟩ := hx
  have h := C.right_chart u hu
  refine ⟨h.2 ▸ C.chart.map_source h.1,?_⟩
  rw [C.rightParameter.symm_apply_apply,← h.2,C.chart.left_inv h.1]

lemma branch_graphs_ne (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    {u v : ℝ} (hu : u ∈ Ico C.lower t) (hv : v ∈ Ioc t C.upper) :
    ![C.leftParameter u,C.leftGraph (C.leftParameter u)] ≠
      ![C.rightParameter v,C.rightGraph (C.rightParameter v)] := by
  intro he
  have hl := C.left_chart u ⟨hu.1,hu.2.le⟩
  have hr := C.right_chart v ⟨hv.1.le,hv.2⟩
  have hp : γ.extend u = γ.extend v := C.chart.injOn hl.1 hr.1 (hl.2.trans (he.trans hr.2.symm))
  have hu01 : u ∈ Icc (0:ℝ) 1 :=
    ⟨C.lower_pos.le.trans hu.1,hu.2.le.trans (C.lt_upper.trans C.upper_lt_one).le⟩
  have hv01 : v ∈ Icc (0:ℝ) 1 :=
    ⟨(C.lower_pos.trans C.lower_lt).le.trans hv.1.le,hv.2.trans C.upper_lt_one.le⟩
  rw [Path.extend_apply γ hu01,Path.extend_apply γ hv01] at hp
  have huv := congrArg (fun z : I => (z:ℝ)) (hi hp)
  exact (hu.2.trans hv.1).ne huv

lemma graphs_ne_on_overlap (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    {x : ℝ} (hx : x ∈ C.leftParameter '' Ico C.lower t)
    (hx' : x ∈ C.rightParameter '' Ioc t C.upper) : C.leftGraph x ≠ C.rightGraph x := by
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨v,hv,he'⟩ := hx'
  intro hg
  apply C.branch_graphs_ne hi hu hv
  rw [he,he',hg]

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ReturningCornerParameters
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine returning corner has separated graph traces arbitrarily near
its common endpoint, on an interval available for the explicit rounding. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

lemma graphs_meet (C : RegularPathCornerChart γ t) :
    C.leftGraph (C.leftParameter t) = C.rightGraph (C.leftParameter t) := by
  have hl := (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).2
  have hr := (C.right_chart t ⟨le_rfl,C.lt_upper.le⟩).2
  rw [← C.parameter_match] at hr
  exact congrFun (hl.symm.trans hr) 1

lemma returning_overlap (C : RegularPathCornerChart γ t)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter) :
    ∃ R > C.leftParameter t, ∀ x ∈ Ioo (C.leftParameter t) R,
      x ∈ C.leftParameter '' Ioo C.lower t ∧
      x ∈ C.rightParameter '' Ioo t C.upper := by
  let R := min (C.leftParameter C.lower) (C.rightParameter C.upper)
  have hR : C.leftParameter t < R := by
    apply lt_min
    · exact hl C.lower_lt
    · rw [C.parameter_match]
      exact hr C.lt_upper
  refine ⟨R,hR,?_⟩
  intro x hx
  constructor
  · rw [C.leftParameter.continuous.continuousOn.image_Ioo_of_strictAntiOn
      C.lower_lt.le (hl.strictAntiOn _)]
    exact ⟨hx.1,hx.2.trans_le (min_le_left _ _)⟩
  · rw [C.rightParameter.continuous.continuousOn.image_Ioo_of_strictMonoOn
      C.lt_upper.le (hr.strictMonoOn _),← C.parameter_match]
    exact ⟨hx.1,hx.2.trans_le (min_le_right _ _)⟩

theorem returning_corner_parameters (C : RegularPathCornerChart γ t)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter)
    {V : Set Base} (hV : IsOpen V) (htV : C.chart (γ.extend t) ∈ V) :
    ∃ a b : ℝ, 0 < b ∧ C.leftParameter t < a ∧
      (∀ x ∈ Icc a (a+4*b), x ∈ C.leftParameter '' Ioo C.lower t ∧
        x ∈ C.rightParameter '' Ioo t C.upper) ∧
      (∀ x ∈ Icc a (a+4*b), ∀ s ∈ Icc (0:ℝ) 1,
        (1-s) • graphPoint C.leftGraph x + s • graphPoint C.rightGraph x ∈ V) := by
  have hp : graphPoint C.leftGraph (C.leftParameter t) ∈ V := by
    rw [graphPoint,← (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).2]
    exact htV
  obtain ⟨δ,hδ,hblend⟩ := small_graph_blends C.left_smooth.continuous C.right_smooth.continuous
    (C.leftParameter t) C.graphs_meet hV hp
  obtain ⟨R,hR,hoverlap⟩ := C.returning_overlap hl hr
  let w := min δ (R-C.leftParameter t)
  have hw : 0 < w := lt_min hδ (sub_pos.mpr hR)
  have hwδ : w ≤ δ := min_le_left _ _
  have hwR : w ≤ R-C.leftParameter t := min_le_right _ _
  let a := C.leftParameter t+w/4
  let b := w/16
  have hb : 0 < b := div_pos hw (by norm_num)
  have hx : ∀ x ∈ Icc a (a+4*b), x ∈ Ioo (C.leftParameter t) R ∧
      x ∈ Ioo (C.leftParameter t-δ) (C.leftParameter t+δ) := by
    intro x hx
    dsimp only [a,b] at hx
    constructor
    · constructor <;> linarith [hx.1,hx.2]
    · constructor <;> linarith [hx.1,hx.2]
  refine ⟨a,b,hb,by dsimp [a] <;> linarith,?_,?_⟩
  · intro x hxx
    exact hoverlap x (hx x hxx).1
  · intro x hxx s hs
    exact hblend x (hx x hxx).2 s hs

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_AdvancingCornerParameters
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small-scale data for graph branches advancing in the same horizontal direction. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

theorem advancing_corner_parameters (C : RegularPathCornerChart γ t)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    {V : Set Base} (hV : IsOpen V) (htV : C.chart (γ.extend t) ∈ V) :
    ∃ b > 0,
      C.leftParameter t-2*b ∈ C.leftParameter '' Ioo C.lower t ∧
      C.leftParameter t+2*b ∈ C.rightParameter '' Ioo t C.upper ∧
      ∀ s ∈ Icc (-2:ℝ) 2, ∀ θ ∈ Icc (0:ℝ) 1,
        (1-θ) • graphPoint C.leftGraph (C.leftParameter t+b*s) +
          θ • graphPoint C.rightGraph (C.leftParameter t+b*s) ∈ V := by
  have hp : graphPoint C.leftGraph (C.leftParameter t) ∈ V := by
    rw [graphPoint,← (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).2]
    exact htV
  obtain ⟨δ,hδ,hblend⟩ := small_graph_blends C.left_smooth.continuous C.right_smooth.continuous
    (C.leftParameter t) C.graphs_meet hV hp
  let w := min δ (min (C.leftParameter t-C.leftParameter C.lower)
    (C.rightParameter C.upper-C.leftParameter t))
  have hL : 0 < C.leftParameter t-C.leftParameter C.lower := sub_pos.mpr (hl C.lower_lt)
  have hR : 0 < C.rightParameter C.upper-C.leftParameter t := by
    rw [C.parameter_match]
    exact sub_pos.mpr (hr C.lt_upper)
  have hw : 0 < w := lt_min hδ (lt_min hL hR)
  have hwδ : w ≤ δ := min_le_left _ _
  have hwL : w ≤ C.leftParameter t-C.leftParameter C.lower :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hwR : w ≤ C.rightParameter C.upper-C.leftParameter t :=
    (min_le_right _ _).trans (min_le_right _ _)
  let b := w/4
  have hb : 0 < b := div_pos hw (by norm_num)
  refine ⟨b,hb,?_,?_,?_⟩
  · rw [C.leftParameter.continuous.continuousOn.image_Ioo_of_strictMonoOn
      C.lower_lt.le (hl.strictMonoOn _)]
    dsimp only [b]
    constructor <;> linarith
  · rw [C.rightParameter.continuous.continuousOn.image_Ioo_of_strictMonoOn
      C.lt_upper.le (hr.strictMonoOn _),← C.parameter_match]
    dsimp only [b]
    constructor <;> linarith
  · intro s hs θ hθ
    apply hblend _ _ θ hθ
    dsimp only [b]
    have h1 := mul_le_mul_of_nonneg_left hs.1 hw.le
    have h2 := mul_le_mul_of_nonneg_left hs.2 hw.le
    constructor <;> linarith

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcChartTransport
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport a compact regular embedded model arc through actual smooth
surface coordinates, using only the target neighborhood containing the arc. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem smooth_arc_chart_transport (P : SmoothCompactArc 𝓘(ℝ,Base) Base)
    (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    (htarget : MapsTo P.curve (Icc P.start P.finish) c.target) :
    ∃ Q : SmoothCompactArc planeModel M,
      Q.start = P.start ∧ Q.finish = P.finish ∧ Q.curve = c.symm ∘ P.curve ∧
      ∀ t ∈ Q.domain, Q.curve t ∈ c.source ∧ c (Q.curve t) = P.curve t := by
  let U := P.domain ∩ P.curve ⁻¹' c.target
  have hU : IsOpen U := P.smooth.continuousOn.isOpen_inter_preimage P.domain_open c.open_target
  have hsub : Icc P.start P.finish ⊆ U := fun t ht => ⟨P.interval_subset ht,htarget ht⟩
  have hs : ContMDiffOn 𝓘(ℝ) planeModel ∞ (c.symm ∘ P.curve) U :=
    hci.comp (P.smooth.mono inter_subset_left) (fun _ ht => ht.2)
  have hdif : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hr : ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) planeModel (c.symm ∘ P.curve) t) := by
    intro t ht
    rw [mfderiv_comp t ((hci.contMDiffAt (c.open_target.mem_nhds ht.2)).mdifferentiableAt (by simp))
      ((P.smooth.contMDiffAt (P.domain_open.mem_nhds ht.1)).mdifferentiableAt (by simp))]
    exact (hdif.mfderiv_injective ht.2).comp (P.regular t ht.1)
  have hi : (Icc P.start P.finish).InjOn (c.symm ∘ P.curve) := by
    intro t ht u hu he
    exact P.injective ht hu (c.symm.injOn (htarget ht) (htarget hu) he)
  let Q : SmoothCompactArc planeModel M :=
    ⟨c.symm ∘ P.curve,P.start,P.finish,P.start_lt_finish,U,hU,hsub,hs,hr,hi⟩
  refine ⟨Q,rfl,rfl,rfl,?_⟩
  intro t ht
  exact ⟨c.map_target ht.2,c.right_inv ht.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_AdvancingCornerArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An advancing corner has an actual regular embedded surface rounding in
any prescribed open neighborhood, with the original branch germs at both ends. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

theorem advancing_corner_arc (C : RegularPathCornerChart γ t)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    {O : Set M} (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ (P : SmoothCompactArc planeModel M) (a b l r : ℝ),
      P.start = -2 ∧ P.finish = 2 ∧ 0 < b ∧
      C.lower < l ∧ l < t ∧ t < r ∧ r < C.upper ∧
      P.curve P.start = γ.extend l ∧ P.curve P.finish = γ.extend r ∧
      MapsTo P.curve (Icc P.start P.finish) O ∧
      (∀ s ∈ Icc P.start P.finish,
        P.curve s ∈ C.chart.source ∧ C.chart (P.curve s) =
          scaledGraphJoin C.leftGraph C.rightGraph a b s) ∧
      P.curve =ᶠ[𝓝 P.start]
        (fun s => γ.extend (C.leftParameter.symm (a+b*s))) ∧
      P.curve =ᶠ[𝓝 P.finish]
        (fun s => γ.extend (C.rightParameter.symm (a+b*s))) := by
  let V := C.chart.target ∩ C.chart.symm ⁻¹' O
  have hV : IsOpen V := C.chart.continuousOn_symm.isOpen_inter_preimage C.chart.open_target hO
  have htS := (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).1
  have htV : C.chart (γ.extend t) ∈ V :=
    ⟨C.chart.map_source htS,by simpa only [mem_preimage,C.chart.left_inv htS] using htO⟩
  let a := C.leftParameter t
  obtain ⟨b,hb,htraceL,htraceR,hblend⟩ := C.advancing_corner_parameters hl hr hV htV
  obtain ⟨Q,hQs,hQf,hQc,hQL,hQR⟩ := scaled_graph_join_arc C.left_smooth C.right_smooth a hb.ne'
  have hQV : MapsTo Q.curve (Icc Q.start Q.finish) V := by
    intro s hs
    rw [hQc,scaledGraphJoin_eq_blend]
    apply hblend s (by simpa only [hQs,hQf] using hs)
    exact centeredSmoothStep_bounds s
  obtain ⟨P,hPs,hPf,hPc,hcoord⟩ := smooth_arc_chart_transport Q C.chart
    C.chart_smooth C.inverse_smooth (fun s hs => (hQV hs).1)
  have hPs' : P.start = -2 := hPs.trans hQs
  have hPf' : P.finish = 2 := hPf.trans hQf
  obtain ⟨l,hlt,hel⟩ := htraceL
  obtain ⟨r,hrt,her⟩ := htraceR
  have hLn : ∀ᶠ s in 𝓝 P.start,
      a+b*s ∈ C.leftParameter '' Ioo C.lower t := by
    have he : a+b*P.start = a-2*b := by rw [hPs']; ring
    apply (show Continuous (fun s : ℝ => a+b*s) by fun_prop).continuousAt.preimage_mem_nhds
    rw [he]
    exact (C.leftParameter.isOpenMap _ isOpen_Ioo).mem_nhds ⟨l,hlt,hel⟩
  have hRn : ∀ᶠ s in 𝓝 P.finish,
      a+b*s ∈ C.rightParameter '' Ioo t C.upper := by
    have he : a+b*P.finish = a+2*b := by rw [hPf']; ring
    apply (show Continuous (fun s : ℝ => a+b*s) by fun_prop).continuousAt.preimage_mem_nhds
    rw [he]
    exact (C.rightParameter.isOpenMap _ isOpen_Ioo).mem_nhds ⟨r,hrt,her⟩
  have hPL : P.curve =ᶠ[𝓝 P.start]
      (fun s => γ.extend (C.leftParameter.symm (a+b*s))) := by
    have hQL' : Q.curve =ᶠ[𝓝 P.start] (fun s => ![a+b*s,C.leftGraph (a+b*s)]) := by
      simpa only [hPs] using hQL
    filter_upwards [hQL',hLn] with s hs hxs
    rw [hPc]
    change C.chart.symm (Q.curve s) = _
    rw [hs]
    exact (C.left_graph_realized (image_mono Ioo_subset_Icc_self hxs)).2
  have hPR : P.curve =ᶠ[𝓝 P.finish]
      (fun s => γ.extend (C.rightParameter.symm (a+b*s))) := by
    have hQR' : Q.curve =ᶠ[𝓝 P.finish] (fun s => ![a+b*s,C.rightGraph (a+b*s)]) := by
      simpa only [hPf] using hQR
    filter_upwards [hQR',hRn] with s hs hxs
    rw [hPc]
    change C.chart.symm (Q.curve s) = _
    rw [hs]
    exact (C.right_graph_realized (image_mono Ioo_subset_Icc_self hxs)).2
  refine ⟨P,a,b,l,r,hPs',hPf',hb,hlt.1,hlt.2,hrt.1,hrt.2,?_,?_,?_,?_,hPL,hPR⟩
  · have he : a+b*P.start = a-2*b := by rw [hPs']; ring
    rw [hPL.eq_of_nhds,he,← hel,C.leftParameter.symm_apply_apply]
  · have he : a+b*P.finish = a+2*b := by rw [hPf']; ring
    rw [hPR.eq_of_nhds,he,← her,C.rightParameter.symm_apply_apply]
  · intro s hs
    have hsQ : s ∈ Icc Q.start Q.finish := by simpa only [hPs,hPf] using hs
    rw [hPc]
    exact (hQV hsQ).2
  · intro s hs
    have hc := hcoord s (P.interval_subset hs)
    rw [hQc] at hc
    exact hc

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RoundedReturnSeparated
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both vertical orders of two separated graphs admit the same regular rounding. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma roundedReturnCurve_opposite_ne_of_ne {f g : ℝ → ℝ} {a b t : ℝ}
    (ht : 0 < t) (hgap : f (a+b*t^2) ≠ g (a+b*t^2)) :
    roundedReturnCurve f g a b (-t) ≠ roundedReturnCurve f g a b t := by
  intro he
  have hy := congrFun he 1
  change (1-centeredSmoothStep (-t))*f (a+b*(-t)^2)+centeredSmoothStep (-t)*g (a+b*(-t)^2) =
    (1-centeredSmoothStep t)*f (a+b*t^2)+centeredSmoothStep t*g (a+b*t^2) at hy
  rw [neg_sq] at hy
  have hn := mul_ne_zero
    (sub_ne_zero.mpr (ne_of_gt (centeredSmoothStep_opposite_lt ht)))
    (sub_ne_zero.mpr hgap.symm)
  apply hn
  nlinarith [hy]

lemma roundedReturnCurve_regular_of_ne {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {a b : ℝ} (hb : b ≠ 0) (hgap : f a ≠ g a) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (roundedReturnCurve f g a b) t) := by
  by_cases ht : t = 0
  · subst t
    apply plane_curve_regular_of_hasDerivAt
      (roundedReturnCurve_hasDerivAt_zero (hf.differentiable (by simp) a) (hg.differentiable (by simp) a))
      (i := 1)
    exact sub_ne_zero.mpr hgap.symm
  · have hx : HasDerivAt (fun u : ℝ => a+b*u^2) (2*b*t) t := by
      exact ((((hasDerivAt_pow 2 t).const_mul b).const_add a).congr_deriv (by simp; ring))
    have hC := (roundedReturnCurve_smooth hf hg a b).differentiable (by simp) t
    have hc0 := hasDerivAt_pi.mp hC.hasDerivAt 0
    have hcoord : deriv (roundedReturnCurve f g a b) t 0 = 2*b*t := hc0.unique hx
    apply plane_curve_regular_of_hasDerivAt hC.hasDerivAt (i := 0)
    rw [hcoord]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hb) ht

lemma roundedReturnCurve_injective_of_ne {f g : ℝ → ℝ} {a b T : ℝ}
    (hb : b ≠ 0) (hgap : ∀ t ∈ Icc (-T) T, f (a+b*t^2) ≠ g (a+b*t^2)) :
    (Icc (-T) T).InjOn (roundedReturnCurve f g a b) := by
  intro s hs t ht he
  have hx := congrFun he 0
  change a+b*s^2 = a+b*t^2 at hx
  have hsq : s^2 = t^2 := by
    apply mul_left_cancel₀ hb
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
  · exact heq
  rcases lt_trichotomy 0 t with hp | hz | hn
  · exact False.elim (roundedReturnCurve_opposite_ne_of_ne hp (hgap _ ht) (heq ▸ he))
  · simpa only [← hz,neg_zero] using heq
  · have hps : 0 < s := by linarith
    apply False.elim
    apply roundedReturnCurve_opposite_ne_of_ne hps (hgap _ hs)
    have hts : t = -s := by linarith
    simpa only [hts] using he.symm

theorem rounded_return_arc_of_ne {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {a b : ℝ} (hb : b ≠ 0)
    (hgap : ∀ t ∈ Icc (-2:ℝ) 2, f (a+b*t^2) ≠ g (a+b*t^2)) :
    ∃ P : SmoothCompactArc 𝓘(ℝ,Base) Base,
      P.start = -2 ∧ P.finish = 2 ∧ P.curve = roundedReturnCurve f g a b ∧
      P.curve =ᶠ[𝓝 P.start] (fun t => ![a+b*t^2,f (a+b*t^2)]) ∧
      P.curve =ᶠ[𝓝 P.finish] (fun t => ![a+b*t^2,g (a+b*t^2)]) := by
  have hgap0 : f a ≠ g a := by simpa using hgap 0 (by norm_num)
  let P : SmoothCompactArc 𝓘(ℝ,Base) Base :=
    ⟨roundedReturnCurve f g a b,-2,2,by norm_num,univ,isOpen_univ,subset_univ _,
      (roundedReturnCurve_smooth hf hg a b).contMDiff.contMDiffOn,
      fun t _ => roundedReturnCurve_regular_of_ne hf hg hb hgap0 t,
      roundedReturnCurve_injective_of_ne hb hgap⟩
  refine ⟨P,rfl,rfl,rfl,?_,?_⟩
  · filter_upwards [eventually_lt_nhds (show (-2:ℝ) < -1 by norm_num)] with t ht
    exact roundedReturnCurve_left ht.le
  · filter_upwards [eventually_gt_nhds (show (1:ℝ) < 2 by norm_num)] with t ht
    exact roundedReturnCurve_right ht.le

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_ReturningCornerArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A returning corner has an actual regular embedded surface rounding in
any prescribed open neighborhood, with the original branch germs at both ends. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

theorem returning_corner_arc (C : RegularPathCornerChart γ t)
    (hi : Function.Injective γ)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter)
    {O : Set M} (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ (P : SmoothCompactArc planeModel M) (a b l r : ℝ),
      P.start = -2 ∧ P.finish = 2 ∧ 0 < b ∧
      C.lower < l ∧ l < t ∧ t < r ∧ r < C.upper ∧
      P.curve P.start = γ.extend l ∧ P.curve P.finish = γ.extend r ∧
      MapsTo P.curve (Icc P.start P.finish) O ∧
      (∀ s ∈ Icc P.start P.finish,
        P.curve s ∈ C.chart.source ∧ C.chart (P.curve s) =
          roundedReturnCurve C.leftGraph C.rightGraph a b s) ∧
      P.curve =ᶠ[𝓝 P.start]
        (fun s => γ.extend (C.leftParameter.symm (a+b*s^2))) ∧
      P.curve =ᶠ[𝓝 P.finish]
        (fun s => γ.extend (C.rightParameter.symm (a+b*s^2))) := by
  let V := C.chart.target ∩ C.chart.symm ⁻¹' O
  have hV : IsOpen V := C.chart.continuousOn_symm.isOpen_inter_preimage C.chart.open_target hO
  have htS := (C.left_chart t ⟨C.lower_lt.le,le_rfl⟩).1
  have htV : C.chart (γ.extend t) ∈ V :=
    ⟨C.chart.map_source htS,by simpa only [mem_preimage,C.chart.left_inv htS] using htO⟩
  obtain ⟨a,b,hb,ha,htraces,hblend⟩ := C.returning_corner_parameters hl hr hV htV
  have hx : ∀ s ∈ Icc (-2:ℝ) 2, a+b*s^2 ∈ Icc a (a+4*b) := by
    intro s hs
    have h := roundedReturnCurve_coordinate_bound (f := C.leftGraph) (g := C.rightGraph) (a := a) hb.le hs
    change a ≤ a+b*s^2 ∧ a+b*s^2 ≤ a+b*(2:ℝ)^2 at h
    exact ⟨h.1,by nlinarith [h.2]⟩
  have hgap : ∀ s ∈ Icc (-2:ℝ) 2,
      C.leftGraph (a+b*s^2) ≠ C.rightGraph (a+b*s^2) := by
    intro s hs
    obtain ⟨hL,hR⟩ := htraces _ (hx s hs)
    exact C.graphs_ne_on_overlap hi
      (image_mono Ioo_subset_Ico_self hL) (image_mono Ioo_subset_Ioc_self hR)
  obtain ⟨Q,hQs,hQf,hQc,hQL,hQR⟩ := rounded_return_arc_of_ne C.left_smooth C.right_smooth hb.ne' hgap
  have hQV : MapsTo Q.curve (Icc Q.start Q.finish) V := by
    intro s hs
    rw [hQc,roundedReturnCurve_eq_blend]
    apply hblend _ (hx s (by simpa only [hQs,hQf] using hs))
    exact centeredSmoothStep_bounds s
  obtain ⟨P,hPs,hPf,hPc,hcoord⟩ := smooth_arc_chart_transport Q C.chart
    C.chart_smooth C.inverse_smooth (fun s hs => (hQV hs).1)
  have hPs' : P.start = -2 := hPs.trans hQs
  have hPf' : P.finish = 2 := hPf.trans hQf
  obtain ⟨l,hlt,hel⟩ := (htraces (a+4*b) (right_mem_Icc.mpr (by linarith))).1
  obtain ⟨r,hrt,her⟩ := (htraces (a+4*b) (right_mem_Icc.mpr (by linarith))).2
  have hLn : ∀ᶠ s in 𝓝 P.start,
      a+b*s^2 ∈ C.leftParameter '' Ioo C.lower t := by
    have he : a+b*P.start^2 = a+4*b := by rw [hPs']; ring
    apply (show Continuous (fun s : ℝ => a+b*s^2) by fun_prop).continuousAt.preimage_mem_nhds
    rw [he]
    exact (C.leftParameter.isOpenMap _ isOpen_Ioo).mem_nhds ⟨l,hlt,hel⟩
  have hRn : ∀ᶠ s in 𝓝 P.finish,
      a+b*s^2 ∈ C.rightParameter '' Ioo t C.upper := by
    have he : a+b*P.finish^2 = a+4*b := by rw [hPf']; ring
    apply (show Continuous (fun s : ℝ => a+b*s^2) by fun_prop).continuousAt.preimage_mem_nhds
    rw [he]
    exact (C.rightParameter.isOpenMap _ isOpen_Ioo).mem_nhds ⟨r,hrt,her⟩
  have hPL : P.curve =ᶠ[𝓝 P.start]
      (fun s => γ.extend (C.leftParameter.symm (a+b*s^2))) := by
    have hQL' : Q.curve =ᶠ[𝓝 P.start] (fun s => ![a+b*s^2,C.leftGraph (a+b*s^2)]) := by
      simpa only [hPs] using hQL
    filter_upwards [hQL',hLn] with s hs hxs
    rw [hPc]
    change C.chart.symm (Q.curve s) = _
    rw [hs]
    exact (C.left_graph_realized (image_mono Ioo_subset_Icc_self hxs)).2
  have hPR : P.curve =ᶠ[𝓝 P.finish]
      (fun s => γ.extend (C.rightParameter.symm (a+b*s^2))) := by
    have hQR' : Q.curve =ᶠ[𝓝 P.finish] (fun s => ![a+b*s^2,C.rightGraph (a+b*s^2)]) := by
      simpa only [hPf] using hQR
    filter_upwards [hQR',hRn] with s hs hxs
    rw [hPc]
    change C.chart.symm (Q.curve s) = _
    rw [hs]
    exact (C.right_graph_realized (image_mono Ioo_subset_Icc_self hxs)).2
  refine ⟨P,a,b,l,r,hPs',hPf',hb,hlt.1,hlt.2,hrt.1,hrt.2,?_,?_,?_,?_,hPL,hPR⟩
  · have he : a+b*P.start^2 = a+4*b := by rw [hPs']; ring
    rw [hPL.eq_of_nhds,he,← hel,C.leftParameter.symm_apply_apply]
  · have he : a+b*P.finish^2 = a+4*b := by rw [hPf']; ring
    rw [hPR.eq_of_nhds,he,← her,C.rightParameter.symm_apply_apply]
  · intro s hs
    have hsQ : s ∈ Icc Q.start Q.finish := by simpa only [hPs,hPf] using hs
    rw [hPc]
    exact (hQV hsQ).2
  · intro s hs
    have hc := hcoord s (P.interval_subset hs)
    rw [hQc] at hc
    exact hc

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CornerArcSeparation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rounded graph cannot meet the portions of either old branch
lying beyond its attachment points. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

theorem returning_arc_local_separation (C : RegularPathCornerChart γ t)
    (P : SmoothCompactArc planeModel M)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter)
    {a b l r : ℝ} (hb : 0 < b) (hlt : l < t) (htr : t < r)
    (hPs : P.start = -2) (hPf : P.finish = 2)
    (hleft : C.leftParameter l = a+4*b) (hright : C.rightParameter r = a+4*b)
    (hcoord : ∀ s ∈ Icc P.start P.finish,
      C.chart (P.curve s) 0 = a+b*s^2) :
    ∀ s ∈ Icc P.start P.finish, ∀ u ∈ Ico C.lower l ∪ Ioc r C.upper,
      P.curve s ≠ γ.extend u := by
  intro s hs u hu he
  have hxy : C.chart (γ.extend u) 0 = a+b*s^2 := by rw [← he]; exact hcoord s hs
  have hs' : s ∈ Icc (-2:ℝ) 2 := by simpa only [hPs,hPf] using hs
  have hsq : s^2 ≤ 4 := by nlinarith [sq_nonneg (s+2),sq_nonneg (s-2),mul_nonneg (by linarith [hs'.1] : 0 ≤ s+2) (by linarith [hs'.2] : 0 ≤ 2-s)]
  have hxbound : a+b*s^2 ≤ a+4*b := by nlinarith
  rcases hu with hu | hu
  · have hC := congrFun (C.left_chart u ⟨hu.1,hu.2.le.trans hlt.le⟩).2 0
    change C.chart (γ.extend u) 0 = C.leftParameter u at hC
    have hm := hl hu.2
    rw [hleft,← hC,hxy] at hm
    exact (not_lt_of_ge hxbound) hm
  · have hC := congrFun (C.right_chart u ⟨htr.le.trans hu.1.le,hu.2⟩).2 0
    change C.chart (γ.extend u) 0 = C.rightParameter u at hC
    have hm := hr hu.1
    rw [hright,← hC,hxy] at hm
    exact (not_lt_of_ge hxbound) hm

theorem advancing_arc_local_separation (C : RegularPathCornerChart γ t)
    (P : SmoothCompactArc planeModel M)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    {a b l r : ℝ} (hb : 0 < b) (hlt : l < t) (htr : t < r)
    (hPs : P.start = -2) (hPf : P.finish = 2)
    (hleft : C.leftParameter l = a-2*b) (hright : C.rightParameter r = a+2*b)
    (hcoord : ∀ s ∈ Icc P.start P.finish,
      C.chart (P.curve s) 0 = a+b*s) :
    ∀ s ∈ Icc P.start P.finish, ∀ u ∈ Ico C.lower l ∪ Ioc r C.upper,
      P.curve s ≠ γ.extend u := by
  intro s hs u hu he
  have hxy : C.chart (γ.extend u) 0 = a+b*s := by rw [← he]; exact hcoord s hs
  have hs' : s ∈ Icc (-2:ℝ) 2 := by simpa only [hPs,hPf] using hs
  have hxlo : a-2*b ≤ a+b*s := by nlinarith [hs'.1]
  have hxhi : a+b*s ≤ a+2*b := by nlinarith [hs'.2]
  rcases hu with hu | hu
  · have hC := congrFun (C.left_chart u ⟨hu.1,hu.2.le.trans hlt.le⟩).2 0
    change C.chart (γ.extend u) 0 = C.leftParameter u at hC
    have hm := hl hu.2
    rw [hleft,← hC,hxy] at hm
    exact (not_lt_of_ge hxlo) hm
  · have hC := congrFun (C.right_chart u ⟨htr.le.trans hu.1.le,hu.2⟩).2 0
    change C.chart (γ.extend u) 0 = C.rightParameter u at hC
    have hm := hr hu.1
    rw [hright,← hC,hxy] at hm
    exact (not_lt_of_ge hxhi) hm

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CornerChartReflection
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reversing both chart coordinates interchanges the two horizontal
orientations without changing the actual surface branches. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

lemma reflect_left_strictMono (C : RegularPathCornerChart γ t) (h : StrictAnti C.leftParameter) :
    StrictMono C.reflect.leftParameter := fun _ _ hxy => neg_lt_neg (h hxy)
lemma reflect_left_strictAnti (C : RegularPathCornerChart γ t) (h : StrictMono C.leftParameter) :
    StrictAnti C.reflect.leftParameter := fun _ _ hxy => neg_lt_neg (h hxy)
lemma reflect_right_strictMono (C : RegularPathCornerChart γ t) (h : StrictAnti C.rightParameter) :
    StrictMono C.reflect.rightParameter := fun _ _ hxy => neg_lt_neg (h hxy)

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CornerParameterOrientation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit corner parameters run forward along the original path
at each joining endpoint. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma smooth_homeomorph_inverse_deriv_ne (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (x : ℝ) :
    deriv e.symm x ≠ 0 := by
  have hd := ((he.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (e.symm x)).hasDerivAt).comp x
    ((hei.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasDerivAt)
  have hd' : HasDerivAt (fun x : ℝ => x)
      (deriv e (e.symm x)*deriv e.symm x) x := by simpa only [Function.comp_def,e.apply_symm_apply] using hd
  have hh := hd'.unique (hasDerivAt_id x)
  intro hz
  rw [hz,mul_zero] at hh
  norm_num at hh

lemma smooth_homeomorph_inverse_deriv_pos (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    (hm : StrictMono e) (x : ℝ) : 0 < deriv e.symm x := by
  have hmi : StrictMono e.symm := by
    intro x y hxy
    apply hm.lt_iff_lt.mp
    simpa only [e.apply_symm_apply] using hxy
  exact lt_of_le_of_ne hmi.monotone.deriv_nonneg
    (smooth_homeomorph_inverse_deriv_ne e he hei x).symm

lemma smooth_homeomorph_inverse_deriv_neg (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm)
    (hm : StrictAnti e) (x : ℝ) : deriv e.symm x < 0 := by
  have hmi : StrictAnti e.symm := by
    intro x y hxy
    apply lt_of_not_ge
    intro hyx
    have h := hm.antitone hyx
    simp only [e.apply_symm_apply] at h
    exact (not_le_of_gt hxy) h
  exact lt_of_le_of_ne hmi.antitone.deriv_nonpos
    (smooth_homeomorph_inverse_deriv_ne e he hei x)

lemma returning_left_parameter_deriv_pos (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hm : StrictAnti e)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    0 < deriv (fun s : ℝ => e.symm (a+b*s^2)) (-2) := by
  have hx : HasDerivAt (fun s : ℝ => a+b*s^2) (2*b*(-2)) (-2) := by
    refine ((((hasDerivAt_id (-2:ℝ)).pow 2).const_mul b).const_add a).congr_deriv (Eq.symm ?_)
    · dsimp only [id_eq] <;> ring
  have hd := ((hei.differentiable (by simp) (a+b*(-2:ℝ)^2)).hasDerivAt).comp (-2) hx
  have hdv := hd.deriv
  dsimp only [Function.comp_def] at hdv
  rw [hdv]
  exact mul_pos_of_neg_of_neg (smooth_homeomorph_inverse_deriv_neg e he hei hm _) (by linarith)

lemma returning_right_parameter_deriv_pos (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hm : StrictMono e)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    0 < deriv (fun s : ℝ => e.symm (a+b*s^2)) 2 := by
  have hx : HasDerivAt (fun s : ℝ => a+b*s^2) (2*b*2) 2 := by
    refine ((((hasDerivAt_id (2:ℝ)).pow 2).const_mul b).const_add a).congr_deriv (Eq.symm ?_)
    · dsimp only [id_eq] <;> ring
  have hd := ((hei.differentiable (by simp) (a+b*(2:ℝ)^2)).hasDerivAt).comp 2 hx
  have hdv := hd.deriv
  dsimp only [Function.comp_def] at hdv
  rw [hdv]
  exact mul_pos (smooth_homeomorph_inverse_deriv_pos e he hei hm _) (by linarith)

lemma advancing_parameter_deriv_pos (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (hei : ContDiff ℝ ∞ e.symm) (hm : StrictMono e)
    (a : ℝ) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    0 < deriv (fun s : ℝ => e.symm (a+b*s)) t := by
  have hx : HasDerivAt (fun s : ℝ => a+b*s) b t := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul b).const_add a
  have hd := ((hei.differentiable (by simp) (a+b*t)).hasDerivAt).comp t hx
  have hdv := hd.deriv
  dsimp only [Function.comp_def] at hdv
  rw [hdv]
  exact mul_pos (smooth_homeomorph_inverse_deriv_pos e he hei hm _) hb

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_LocalCornerBridgeSeparation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retaining actual old-branch separation with the constructed corner bridge. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {O : Set M}
namespace RegularPathCornerChart

theorem returning_bridge_local_separation (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ B : LocalCornerBridge γ t O, C.lower < B.left ∧ B.right < C.upper ∧
      ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico C.lower B.left ∪ Ioc B.right C.upper,
        B.arc.curve s ≠ γ.extend u := by
  obtain ⟨P,a,b,l,r,hPs,hPf,hb,hLl,hlt,htr,hrU,hPleft,hPright,hPO,hPc,hPL,hPR⟩ :=
    C.returning_corner_arc hi hl hr hO htO
  have hlx : C.leftParameter l = a+b*P.start^2 := by
    have H := (hPc P.start (left_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPleft,(C.left_chart l ⟨hLl.le,hlt.le⟩).2] at H
    exact congrFun H 0
  have hrx : C.rightParameter r = a+b*P.finish^2 := by
    have H := (hPc P.finish (right_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPright,(C.right_chart r ⟨htr.le,hrU.le⟩).2] at H
    exact congrFun H 0
  let L : ℝ → ℝ := fun s => C.leftParameter.symm (a+b*s^2)
  let R : ℝ → ℝ := fun s => C.rightParameter.symm (a+b*s^2)
  have hLs : ContDiff ℝ ∞ L := C.left_inverse_smooth.comp (by fun_prop)
  have hRs : ContDiff ℝ ∞ R := C.right_inverse_smooth.comp (by fun_prop)
  refine ⟨⟨P,l,r,C.lower_pos.trans hLl,hlt,htr,hrU.trans C.upper_lt_one,
    L,R,hLs,hRs,?_,?_,?_,?_,hPL,hPR,hPO⟩,hLl,hrU,?_⟩
  · change C.leftParameter.symm (a+b*P.start^2) = l
    rw [← hlx,C.leftParameter.symm_apply_apply]
  · change C.rightParameter.symm (a+b*P.finish^2) = r
    rw [← hrx,C.rightParameter.symm_apply_apply]
  · rw [hPs]
    exact returning_left_parameter_deriv_pos C.leftParameter C.left_parameter_smooth
      C.left_inverse_smooth hl a hb
  · rw [hPf]
    exact returning_right_parameter_deriv_pos C.rightParameter C.right_parameter_smooth
      C.right_inverse_smooth hr a hb

  · apply C.returning_arc_local_separation P hl hr hb hlt htr hPs hPf
    · rw [hlx,hPs]
      ring
    · rw [hrx,hPf]
      ring
    · intro s hs
      exact congrFun (hPc s hs).2 0

theorem advancing_bridge_local_separation (C : RegularPathCornerChart γ t)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ B : LocalCornerBridge γ t O, C.lower < B.left ∧ B.right < C.upper ∧
      ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico C.lower B.left ∪ Ioc B.right C.upper,
        B.arc.curve s ≠ γ.extend u := by
  obtain ⟨P,a,b,l,r,hPs,hPf,hb,hLl,hlt,htr,hrU,hPleft,hPright,hPO,hPc,hPL,hPR⟩ :=
    C.advancing_corner_arc hl hr hO htO
  have hlx : C.leftParameter l = a+b*P.start := by
    have H := (hPc P.start (left_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPleft,(C.left_chart l ⟨hLl.le,hlt.le⟩).2] at H
    exact congrFun H 0
  have hrx : C.rightParameter r = a+b*P.finish := by
    have H := (hPc P.finish (right_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPright,(C.right_chart r ⟨htr.le,hrU.le⟩).2] at H
    exact congrFun H 0
  let L : ℝ → ℝ := fun s => C.leftParameter.symm (a+b*s)
  let R : ℝ → ℝ := fun s => C.rightParameter.symm (a+b*s)
  have hLs : ContDiff ℝ ∞ L := C.left_inverse_smooth.comp (by fun_prop)
  have hRs : ContDiff ℝ ∞ R := C.right_inverse_smooth.comp (by fun_prop)
  refine ⟨⟨P,l,r,C.lower_pos.trans hLl,hlt,htr,hrU.trans C.upper_lt_one,
    L,R,hLs,hRs,?_,?_,?_,?_,hPL,hPR,hPO⟩,hLl,hrU,?_⟩
  · change C.leftParameter.symm (a+b*P.start) = l
    rw [← hlx,C.leftParameter.symm_apply_apply]
  · change C.rightParameter.symm (a+b*P.finish) = r
    rw [← hrx,C.rightParameter.symm_apply_apply]
  · exact advancing_parameter_deriv_pos C.leftParameter C.left_parameter_smooth
      C.left_inverse_smooth hl a hb P.start
  · exact advancing_parameter_deriv_pos C.rightParameter C.right_parameter_smooth
      C.right_inverse_smooth hr a hb P.finish

  · apply C.advancing_arc_local_separation P hl hr hb hlt htr hPs hPf
    · rw [hlx,hPs]
      ring
    · rw [hrx,hPf]
      ring
    · intro s hs
      exact congrFun (hPc s hs).2 0

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SeparatedCornerBridge
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local rounding can be chosen disjoint from the entire unchanged
part of the embedded compact source path. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {U O : Set M}

namespace RegularPathCornerChart

theorem bridge_local_separation (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ B : LocalCornerBridge γ t O, C.lower < B.left ∧ B.right < C.upper ∧
      ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico C.lower B.left ∪ Ioc B.right C.upper,
        B.arc.curve s ≠ γ.extend u := by
  rcases C.left_monotone with hl | hl <;> rcases C.right_monotone with hr | hr
  · exact C.advancing_bridge_local_separation hl hr hO htO
  · exact C.reflect.returning_bridge_local_separation hi (C.reflect_left_strictAnti hl)
      (C.reflect_right_strictMono hr) hO htO
  · exact C.returning_bridge_local_separation hi hl hr hO htO
  · exact C.reflect.advancing_bridge_local_separation (C.reflect_left_strictMono hl)
      (C.reflect_right_strictMono hr) hO htO

end RegularPathCornerChart

variable [IsManifold planeModel ∞ M] [T2Space M]

theorem separated_corner_bridge (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) (ht : t ∈ Ioo (0:ℝ) 1)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ B : LocalCornerBridge γ t O,
      ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico (0:ℝ) B.left ∪ Ioc B.right 1,
        B.arc.curve s ≠ γ.extend u := by
  obtain ⟨C⟩ := regular_path_corner_chart hγ hi ht
  obtain ⟨V,hV,htV,hVO,hfar⟩ := embedded_path_corner_neighborhood γ hi C.lower_pos.le
    C.lower_lt C.lt_upper C.upper_lt_one.le hO htO
  obtain ⟨B,hleft,hright,hlocal⟩ := C.bridge_local_separation hi hV htV
  refine ⟨B.mono hVO,?_⟩
  intro s hs u hu he
  rcases hu with hu | hu
  · by_cases hl : C.lower ≤ u
    · exact hlocal s hs u (Or.inl ⟨hl,hu.2⟩) he
    · exact hfar u (Or.inl ⟨hu.1,(lt_of_not_ge hl).le⟩) (he ▸ B.image_subset hs)
  · by_cases hr : u ≤ C.upper
    · exact hlocal s hs u (Or.inr ⟨hu.1,hr⟩) he
    · exact hfar u (Or.inr ⟨(lt_of_not_ge hr).le,hu.2⟩) (he ▸ B.image_subset hs)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CornerBridgePath
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Turning a separated smooth corner bridge into an embedded replacement
path, retaining finite regular pieces and the exact unchanged trace. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {O : Set M}
namespace LocalCornerBridge

lemma source_eq (B : LocalCornerBridge γ t O) : B.arc.curve B.arc.start = γ B.leftPoint := by
  have he := B.left_germ.eq_of_nhds
  dsimp only [Function.comp_apply] at he
  rw [B.left_value] at he
  exact he.trans (Path.extend_extends' γ B.leftPoint)

lemma target_eq (B : LocalCornerBridge γ t O) : B.arc.curve B.arc.finish = γ B.rightPoint := by
  have he := B.right_germ.eq_of_nhds
  dsimp only [Function.comp_apply] at he
  rw [B.right_value] at he
  exact he.trans (Path.extend_extends' γ B.rightPoint)

end LocalCornerBridge
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ResolvedPrefixImage
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete trace invariant used while joining the ordered smooth
bridges: old path points plus only the bridges already inserted. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} (γ : Path p q) {T : ι → ℝ} {O : Set M}

variable {γ}

lemma resolvedPrefixImage_mono (B : ∀ i, LocalCornerBridge γ (T i) O)
    {J K : Set ι} (hJK : J ⊆ K) {a b : ℝ} (hab : a ≤ b) :
    resolvedPrefixImage γ B J a ⊆ resolvedPrefixImage γ B K b := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (image_mono (Icc_subset_Icc_right hab) hx)
  · obtain ⟨i,hi,hx⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion₂.mpr ⟨i,hJK hi,hx⟩)

lemma resolvedPrefixImage_avoids_future (B : ∀ i, LocalCornerBridge γ (T i) O)
    (hi : Function.Injective γ) {J : Set ι} {a : ℝ} (ha : a ≤ 1)
    (hJ : ∀ i ∈ J, (B i).right ≤ a)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u) :
    ∀ x ∈ resolvedPrefixImage γ B J a, ∀ u ∈ Ioc a 1, x ≠ γ.extend u := by
  intro x hx u hu he
  rcases hx with hx | hx
  · obtain ⟨v,hv,hvx⟩ := hx
    have h := embeddedPath_extend_injOn γ hi ⟨hv.1,hv.2.trans ha⟩
      ⟨hv.1.trans (hv.2.trans hu.1.le),hu.2⟩ (hvx.trans he)
    exact (not_le_of_gt hu.1) (h ▸ hv.2)
  · obtain ⟨i,hiJ,s,hs,hsx⟩ := mem_iUnion₂.mp hx
    exact hsep i s hs u (Or.inr ⟨(hJ i hiJ).trans_lt hu.1,hu.2⟩) (hsx.trans he)

lemma resolvedPrefixImage_avoids_bridge (B : ∀ i, LocalCornerBridge γ (T i) O)
    {J : Set ι} {k : ι} (hk : k ∉ J)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hdis : Pairwise (fun i j => Disjoint
      ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
      ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish))) :
    ∀ x ∈ resolvedPrefixImage γ B J (B k).left,
      ∀ t ∈ Ioc (B k).arc.start (B k).arc.finish, x ≠ (B k).arc.curve t := by
  intro x hx t ht he
  rcases hx with hx | hx
  · obtain ⟨u,hu,hux⟩ := hx
    by_cases hul : u < (B k).left
    · exact hsep k t ⟨ht.1.le,ht.2⟩ u (Or.inl ⟨hu.1,hul⟩) (hux.trans he).symm
    · have hul' : u = (B k).left := le_antisymm hu.2 (le_of_not_gt hul)
      subst u
      have hstart : (B k).arc.curve (B k).arc.start = γ.extend (B k).left :=
        (B k).left_germ.eq_of_nhds.trans (by rw [Function.comp_apply,(B k).left_value])
      have het : (B k).arc.start = t := (B k).arc.injective
        (left_mem_Icc.mpr (B k).arc.start_lt_finish.le) ⟨ht.1.le,ht.2⟩
        (hstart.trans (hux.trans he))
      exact ht.1.ne het
  · obtain ⟨i,hiJ,s,hs,hsx⟩ := mem_iUnion₂.mp hx
    have hik : i ≠ k := fun he => hk (he ▸ hiJ)
    have hxI : x ∈ (B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish := ⟨s,hs,hsx⟩
    have hxK : x ∈ (B k).arc.curve '' Icc (B k).arc.start (B k).arc.finish :=
      ⟨t,⟨ht.1.le,ht.2⟩,he.symm⟩
    exact disjoint_left.mp (hdis hik) hxI hxK

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SharedParameterArcJoin
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual arc joining through two forward smooth germs of the same
underlying path parameter. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

 theorem join_shared_parameter_arcs (f : ℝ → M) (P Q : SmoothCompactArc planeModel M)
    (p q : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hdp : 0 < deriv p P.finish) (hdq : 0 < deriv q Q.start)
    (hpq : p P.finish = q Q.start)
    (hP : P.curve =ᶠ[𝓝 P.finish] f ∘ p)
    (hQ : Q.curve =ᶠ[𝓝 Q.start] f ∘ q)
    (hcross : ∀ s ∈ Icc P.start P.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.curve s ≠ Q.curve t) :
    ∃ (R : SmoothCompactArc planeModel M) (e : ℝ ≃ₜ ℝ),
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
      R.start = P.start ∧ R.finish = e.symm Q.finish ∧
      R.curve '' Icc R.start R.finish = P.curve '' Icc P.start P.finish ∪ Q.curve '' Icc Q.start Q.finish ∧
      R.curve R.start = P.curve P.start ∧ R.curve R.finish = Q.curve Q.finish ∧
      R.curve =ᶠ[𝓝 R.start] P.curve ∧ R.curve =ᶠ[𝓝 R.finish] Q.curve ∘ e := by
  obtain ⟨E,hEs,hEi,hEm,hEq⟩ := increasing_smooth_germ_diffeomorphism hq Q.start hdq
  let k : ℝ → ℝ := E.symm ∘ p
  have hks : ContDiff ℝ ∞ k := hEi.comp hp
  have hkvalue : k P.finish = Q.start := by
    change E.symm (p P.finish) = Q.start
    rw [hpq,← hEq.eq_of_nhds,E.symm_apply_apply]
  have hkpos : 0 < deriv k P.finish := by
    have hd := ((hEi.differentiable (by simp) (p P.finish)).hasDerivAt).comp P.finish
      ((hp.differentiable (by simp) P.finish).hasDerivAt)
    rw [hd.deriv]
    exact mul_pos (smooth_homeomorph_inverse_deriv_pos E hEs hEi hEm _) hdp
  have hkt : Tendsto k (𝓝 P.finish) (𝓝 Q.start) := by
    rw [← hkvalue]
    exact hks.continuous.continuousAt
  have hmatch : P.curve =ᶠ[𝓝 P.finish] Q.curve ∘ k := by
    filter_upwards [hP,hQ.comp_tendsto hkt,hEq.comp_tendsto hkt] with x hx hqx heqx
    dsimp only [Function.comp_apply] at heqx
    have heqp : q (k x) = p x := by
      rw [← heqx]
      exact E.apply_symm_apply (p x)
    change P.curve x = Q.curve (k x)
    dsimp only [Function.comp_apply] at hx hqx
    rw [hx,hqx,heqp]
  obtain ⟨R,e,hes,hei,hem,hea,hRs,hRf,hRc,hRi⟩ :=
    P.join Q isOpen_univ hks.contDiffOn (mem_univ _) hkpos hkvalue hmatch hcross
  have hcut : P.finish < R.finish := by
    rw [hRf]
    apply hem.lt_iff_lt.mp
    rw [e.apply_symm_apply,hea]
    exact Q.start_lt_finish
  have hleft : R.curve =ᶠ[𝓝 R.start] P.curve := by
    rw [hRc]
    exact joinedCurve_germ_left P.finish P.curve (Q.curve ∘ e) (hRs ▸ P.start_lt_finish)
  have hright : R.curve =ᶠ[𝓝 R.finish] Q.curve ∘ e := by
    rw [hRc]
    exact joinedCurve_germ_right P.finish P.curve (Q.curve ∘ e) hcut
  refine ⟨R,e,hes,hei,hem,hRs,hRf,hRi,?_,?_,hleft,hright⟩
  · exact hleft.eq_of_nhds.trans (congrArg P.curve hRs)
  · have heR : e R.finish = Q.finish := by rw [hRf,e.apply_symm_apply]
    exact hright.eq_of_nhds.trans (congrArg Q.curve heR)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothArcTail
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth arc tails retain the exact forward germ needed by the next
piece in the finite source-arc assembly. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SmoothArcTail
variable {f : ℝ → M} {a b : ℝ}

theorem append (P : SmoothArcTail f a) (Q : SmoothCompactArc planeModel M)
    (l r : ℝ → ℝ) (hl : ContDiff ℝ ∞ l) (hr : ContDiff ℝ ∞ r)
    (hld : 0 < deriv l Q.start) (hrd : 0 < deriv r Q.finish)
    (hlv : l Q.start = a) (hrv : r Q.finish = b)
    (hlg : Q.curve =ᶠ[𝓝 Q.start] f ∘ l)
    (hrg : Q.curve =ᶠ[𝓝 Q.finish] f ∘ r)
    (hcross : ∀ s ∈ Icc P.arc.start P.arc.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.arc.curve s ≠ Q.curve t) :
    ∃ R : SmoothArcTail f b,
      R.arc.curve '' Icc R.arc.start R.arc.finish =
        P.arc.curve '' Icc P.arc.start P.arc.finish ∪ Q.curve '' Icc Q.start Q.finish ∧
      R.arc.curve R.arc.start = P.arc.curve P.arc.start ∧
      R.arc.curve =ᶠ[𝓝 R.arc.start] P.arc.curve := by
  obtain ⟨A,e,hes,hei,hem,hAs,hAf,hAi,hAleft,hAright,hAL,hAR⟩ :=
    join_shared_parameter_arcs f P.arc Q P.parameter l P.smooth hl P.forward hld
      (P.value.trans hlv.symm) P.germ hlg hcross
  have hev : e A.finish = Q.finish := by rw [hAf,e.apply_symm_apply]
  have het : Tendsto e (𝓝 A.finish) (𝓝 Q.finish) := by
    rw [← hev]
    exact e.continuous.continuousAt
  have hrval : (r ∘ e) A.finish = b := by
    dsimp only [Function.comp_apply]
    rw [hev,hrv]
  have hrgerm : A.curve =ᶠ[𝓝 A.finish] f ∘ (r ∘ e) :=
    hAR.trans (hrg.comp_tendsto het)
  have hre : 0 < deriv (r ∘ e) A.finish := by
    have hd := ((hr.differentiable (by simp) (e A.finish)).hasDerivAt).comp A.finish
      ((hes.differentiable (by simp) A.finish).hasDerivAt)
    rw [hd.deriv,hev]
    apply mul_pos hrd
    exact smooth_homeomorph_inverse_deriv_pos e.symm hei hes
      (by intro x y hxy; apply hem.lt_iff_lt.mp; simpa only [e.apply_symm_apply] using hxy) _
  let R : SmoothArcTail f b := ⟨A,r ∘ e,hr.comp hes,hre,hrval,hrgerm⟩
  exact ⟨R,hAi,hAleft,hAL⟩

end SmoothArcTail
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ResolvedPrefixAppend
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two actual induction steps: add a prepared bridge, or add the
unchanged regular segment before the next bridge. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {T : ι → ℝ} {O : Set M}

 theorem append_resolved_bridge (B : ∀ i, LocalCornerBridge γ (T i) O)
    {J : Set ι} {k : ι} (hk : k ∉ J)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hdis : Pairwise (fun i j => Disjoint
      ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
      ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)))
    (P : SmoothArcTail γ.extend (B k).left)
    (hP : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆ resolvedPrefixImage γ B J (B k).left) :
    ∃ R : SmoothArcTail γ.extend (B k).right,
      R.arc.curve '' Icc R.arc.start R.arc.finish ⊆ resolvedPrefixImage γ B (insert k J) (B k).right ∧
      R.arc.curve R.arc.start = P.arc.curve P.arc.start := by
  have hcross : ∀ s ∈ Icc P.arc.start P.arc.finish,
      ∀ t ∈ Ioc (B k).arc.start (B k).arc.finish, P.arc.curve s ≠ (B k).arc.curve t := by
    intro s hs t ht
    exact resolvedPrefixImage_avoids_bridge B hk hsep hdis _
      (hP (mem_image_of_mem P.arc.curve hs)) t ht
  obtain ⟨R,hRi,hRs,_⟩ := P.append (B k).arc (B k).leftParameter (B k).rightParameter
    (B k).left_smooth (B k).right_smooth (B k).left_forward (B k).right_forward
    (B k).left_value (B k).right_value (B k).left_germ (B k).right_germ hcross
  refine ⟨R,?_,hRs⟩
  rw [hRi]
  apply union_subset
  · exact hP.trans (resolvedPrefixImage_mono B (subset_insert k J) ((B k).left_lt.trans (B k).lt_right).le)
  · intro x hx
    exact Or.inr (mem_iUnion₂.mpr ⟨k,mem_insert k J,hx⟩)

theorem append_resolved_segment (B : ∀ i, LocalCornerBridge γ (T i) O)
    (hi : Function.Injective γ) {J : Set ι} {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hJ : ∀ i ∈ J, (B i).right ≤ a)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (P : SmoothArcTail γ.extend a)
    (hP : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆ resolvedPrefixImage γ B J a)
    (Q : SmoothCompactArc planeModel M) (hQs : Q.start = a) (hQf : Q.finish = b)
    (hQc : Q.curve = γ.extend) :
    ∃ R : SmoothArcTail γ.extend b,
      R.arc.curve '' Icc R.arc.start R.arc.finish ⊆ resolvedPrefixImage γ B J b ∧
      R.arc.curve R.arc.start = P.arc.curve P.arc.start := by
  have hcross : ∀ s ∈ Icc P.arc.start P.arc.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.arc.curve s ≠ Q.curve t := by
    intro s hs t ht
    rw [hQs,hQf] at ht
    rw [hQc]
    exact resolvedPrefixImage_avoids_future B hi (hab.le.trans hb) hJ hsep _
      (hP (mem_image_of_mem P.arc.curve hs)) t ⟨ht.1,ht.2.trans hb⟩
  have hgL : Q.curve =ᶠ[𝓝 Q.start] γ.extend ∘ id := by rw [hQc]; rfl
  have hgR : Q.curve =ᶠ[𝓝 Q.finish] γ.extend ∘ id := by rw [hQc]; rfl
  obtain ⟨R,hRi,hRs,_⟩ := P.append Q id id contDiff_id contDiff_id
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hQs hQf hgL hgR hcross
  refine ⟨R,?_,hRs⟩
  rw [hRi]
  apply union_subset
  · exact hP.trans (resolvedPrefixImage_mono B (Subset.refl _) hab.le)
  · intro x hx
    rw [hQc,hQs,hQf] at hx
    exact Or.inl (image_mono (Icc_subset_Icc ha le_rfl) hx)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_RegularPathEndpointPieces
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first and last pieces of a finite embedded regular path give actual
regular smooth germs even at the two endpoints. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}
namespace RegularPathCover

theorem first_interval (P : RegularPathCover (J := J) γ) :
    ∃ (i : P.Index) (r : ℝ), 0 < r ∧ Icc 0 r ⊆ P.region i := by
  let _ := P.finite
  have hR : ∀ᶠ u in 𝓝[>] (0:ℝ), ∃ i, u ∈ P.region i := by
    filter_upwards [(eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hut
    exact P.cover ⟨u,⟨hut.le,hu.le⟩⟩
  obtain ⟨i,hi⟩ := frequently_exists.mp hR.frequently
  have h0i : (0:ℝ) ∈ P.region i := (P.closed i).mem_of_frequently_of_tendsto hi
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  obtain ⟨r,hri,hr⟩ := (hi.and_eventually self_mem_nhdsWithin).exists
  exact ⟨i,r,hr,(P.convex i).ordConnected.out h0i hri⟩

theorem last_interval (P : RegularPathCover (J := J) γ) :
    ∃ (i : P.Index) (l : ℝ), l < 1 ∧ Icc l 1 ⊆ P.region i := by
  let _ := P.finite
  have hL : ∀ᶠ u in 𝓝[<] (1:ℝ), ∃ i, u ∈ P.region i := by
    filter_upwards [(eventually_gt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with u hu hut
    exact P.cover ⟨u,⟨hu.le,hut.le⟩⟩
  obtain ⟨i,hi⟩ := frequently_exists.mp hL.frequently
  have h1i : (1:ℝ) ∈ P.region i := (P.closed i).mem_of_frequently_of_tendsto hi
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  obtain ⟨l,hli,hl⟩ := (hi.and_eventually self_mem_nhdsWithin).exists
  exact ⟨i,l,hl,(P.convex i).ordConnected.out hli h1i⟩

theorem first_regular_piece (P : RegularPathCover (J := J) γ)
    (hi : Function.Injective γ) :
    ∃ (A : SmoothCompactArc J M) (a b r : ℝ), 0 < r ∧ a ≠ 0 ∧
      ∀ u ∈ Icc 0 r, a*u+b ∈ A.domain ∧ γ.extend u = A.curve (a*u+b) := by
  obtain ⟨i,r,hr,hsub⟩ := P.first_interval
  refine ⟨P.arc i,P.slope i,P.offset i,r,hr,P.nonzero_slope_on_interval hi i hr hsub,?_⟩
  intro u hu
  have humem := hsub hu
  have hu01 := P.subset i humem
  refine ⟨(P.arc i).interval_subset (P.parameter i u humem),?_⟩
  rw [Path.extend_apply γ hu01]
  exact P.agree i ⟨u,hu01⟩ humem

theorem last_regular_piece (P : RegularPathCover (J := J) γ)
    (hi : Function.Injective γ) :
    ∃ (A : SmoothCompactArc J M) (a b l : ℝ), l < 1 ∧ a ≠ 0 ∧
      ∀ u ∈ Icc l 1, a*u+b ∈ A.domain ∧ γ.extend u = A.curve (a*u+b) := by
  obtain ⟨i,l,hl,hsub⟩ := P.last_interval
  refine ⟨P.arc i,P.slope i,P.offset i,l,hl,P.nonzero_slope_on_interval hi i hl hsub,?_⟩
  intro u hu
  have humem := hsub hu
  have hu01 := P.subset i humem
  refine ⟨(P.arc i).interval_subset (P.parameter i u humem),?_⟩
  rw [Path.extend_apply γ hu01]
  exact P.agree i ⟨u,hu01⟩ humem

end RegularPathCover
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_EndpointRegularArcs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine smooth compact arcs at both ends of the finite source path,
with unchanged interior germs for later attachment. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q}

lemma affine_arc_smooth_regular (A : SmoothCompactArc planeModel M) {a b : ℝ} (ha : a ≠ 0) :
    ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun u : ℝ => A.curve (a*u+b))
      ((fun u : ℝ => a*u+b) ⁻¹' A.domain) ∧
      ∀ u, a*u+b ∈ A.domain → Function.Injective
        (mfderiv 𝓘(ℝ) planeModel (fun v : ℝ => A.curve (a*v+b)) u) := by
  have hparam : ContDiff ℝ ∞ (fun u : ℝ => a*u+b) := by fun_prop
  refine ⟨A.smooth.comp hparam.contMDiff.contMDiffOn (fun _ hu => hu),?_⟩
  intro u hu
  change Function.Injective (mfderiv 𝓘(ℝ) planeModel (A.curve ∘ fun v : ℝ => a*v+b) u)
  rw [mfderiv_comp u ((A.smooth.contMDiffAt (A.domain_open.mem_nhds hu)).mdifferentiableAt (by simp))
    (hparam.contMDiff.mdifferentiable (by simp) u)]
  exact (A.regular _ hu).comp (affine_parameter_regular ha u)

theorem first_regular_arc (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (P : SmoothCompactArc planeModel M) (r : ℝ),
      0 < r ∧ r < η ∧ P.start = 0 ∧ P.finish = r ∧
      (∀ u ∈ Icc 0 r, P.curve u = γ.extend u) ∧ P.curve P.start = p ∧
      P.curve =ᶠ[𝓝 P.finish] γ.extend := by
  obtain ⟨A,a,b,r₀,hr₀,ha,hpiece⟩ := hγ.cover.some.first_regular_piece hi
  let r := min (r₀/2) (η/2)
  have hr : 0 < r := lt_min (half_pos hr₀) (half_pos hη)
  have hrr₀ : r < r₀ := (min_le_left _ _).trans_lt (half_lt_self hr₀)
  have hrη : r < η := (min_le_right _ _).trans_lt (half_lt_self hη)
  let U := (fun u : ℝ => a*u+b) ⁻¹' A.domain
  have hU : IsOpen U := A.domain_open.preimage (by fun_prop)
  have hmatch : ∀ u ∈ Icc 0 r, A.curve (a*u+b) = γ.extend u :=
    fun u hu => (hpiece u ⟨hu.1,hu.2.trans hrr₀.le⟩).2.symm
  have hsub : Icc 0 r ⊆ U := fun u hu => (hpiece u ⟨hu.1,hu.2.trans hrr₀.le⟩).1
  have hd := affine_arc_smooth_regular A (b := b) ha
  have hinj : InjOn (fun u : ℝ => A.curve (a*u+b)) (Icc 0 r) := by
    intro u hu v hv he
    apply embeddedPath_extend_injOn γ hi ⟨hu.1,hu.2.trans (hrη.le.trans hη1)⟩
      ⟨hv.1,hv.2.trans (hrη.le.trans hη1)⟩
    rwa [← hmatch u hu,← hmatch v hv]
  let P : SmoothCompactArc planeModel M :=
    ⟨fun u => A.curve (a*u+b),0,r,hr,U,hU,hsub,hd.1,fun u hu => hd.2 u hu,hinj⟩
  refine ⟨P,r,hr,hrη,rfl,rfl,hmatch,?_,?_⟩
  · change A.curve (a*0+b) = p
    rw [hmatch 0 ⟨le_rfl,hr.le⟩]
    exact γ.extend_zero
  · filter_upwards [Ioo_mem_nhds hr hrr₀] with u hu
    exact (hpiece u ⟨hu.1.le,hu.2.le⟩).2.symm

theorem last_regular_arc (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (P : SmoothCompactArc planeModel M) (l : ℝ),
      1-η < l ∧ l < 1 ∧ P.start = l ∧ P.finish = 1 ∧
      (∀ u ∈ Icc l 1, P.curve u = γ.extend u) ∧ P.curve P.finish = q ∧
      P.curve =ᶠ[𝓝 P.start] γ.extend := by
  obtain ⟨A,a,b,l₀,hl₀,ha,hpiece⟩ := hγ.cover.some.last_regular_piece hi
  let d := min ((1-l₀)/2) (η/2)
  let l := 1-d
  have hdpos : 0 < d := lt_min (half_pos (sub_pos.mpr hl₀)) (half_pos hη)
  have hdl : d < 1-l₀ := (min_le_left _ _).trans_lt (half_lt_self (sub_pos.mpr hl₀))
  have hdη : d < η := (min_le_right _ _).trans_lt (half_lt_self hη)
  have hll₀ : l₀ < l := by dsimp only [l] <;> linarith
  have hl1 : l < 1 := by dsimp only [l] <;> linarith
  have hηl : 1-η < l := by dsimp only [l] <;> linarith
  have hl0 : 0 < l := lt_of_le_of_lt (sub_nonneg.mpr hη1) hηl
  let U := (fun u : ℝ => a*u+b) ⁻¹' A.domain
  have hU : IsOpen U := A.domain_open.preimage (by fun_prop)
  have hmatch : ∀ u ∈ Icc l 1, A.curve (a*u+b) = γ.extend u :=
    fun u hu => (hpiece u ⟨hll₀.le.trans hu.1,hu.2⟩).2.symm
  have hsub : Icc l 1 ⊆ U := fun u hu => (hpiece u ⟨hll₀.le.trans hu.1,hu.2⟩).1
  have hdata := affine_arc_smooth_regular A (b := b) ha
  have hinj : InjOn (fun u : ℝ => A.curve (a*u+b)) (Icc l 1) := by
    intro u hu v hv he
    apply embeddedPath_extend_injOn γ hi ⟨hl0.le.trans hu.1,hu.2⟩ ⟨hl0.le.trans hv.1,hv.2⟩
    rwa [← hmatch u hu,← hmatch v hv]
  let P : SmoothCompactArc planeModel M :=
    ⟨fun u => A.curve (a*u+b),l,1,hl1,U,hU,hsub,hdata.1,fun u hu => hdata.2 u hu,hinj⟩
  refine ⟨P,l,hηl,hl1,rfl,rfl,hmatch,?_,?_⟩
  · change A.curve (a*1+b) = q
    rw [hmatch 1 ⟨hl1.le,le_rfl⟩]
    exact γ.extend_one
  · filter_upwards [Ioo_mem_nhds hll₀ hl1] with u hu
    exact (hpiece u ⟨hu.1.le,hu.2.le⟩).2.symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FinishSmoothTail
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finish a resolved smooth prefix at the original final endpoint. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {T : ι → ℝ} {O : Set M}

theorem finish_smooth_tail (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    (B : ∀ i, LocalCornerBridge γ (T i) O) {J : Set ι} {a A : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hAa : A < a) (hA : 0 ≤ A)
    (hJ : ∀ i ∈ J, (B i).right ≤ a)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hreg : ∀ t ∈ Ioo A 1, ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t))
    (P : SmoothArcTail γ.extend a)
    (hPi : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆ resolvedPrefixImage γ B J a) :
    ∃ R : SmoothCompactArc planeModel M,
      R.curve R.start = P.arc.curve P.arc.start ∧ R.curve R.finish = q ∧
      R.curve '' Icc R.start R.finish ⊆ resolvedPrefixImage γ B J 1 := by
  obtain ⟨Q,l,hal,hl1,hQs,hQf,hQmatch,hQend,hQgerm⟩ :=
    last_regular_arc hγ hi (sub_pos.mpr ha1) (by linarith)
  have hal' : a < l := by linarith
  obtain ⟨S,hSs,hSf,hSc⟩ := original_regular_segment hi isOpen_Ioo
    (fun _ ht => ⟨hA.trans_lt ht.1,ht.2⟩) hreg hal'
    (fun u hu => ⟨hAa.trans_le hu.1,hu.2.trans_lt hl1⟩)
  obtain ⟨P',hP'i,hP's⟩ := append_resolved_segment B hi ha.le hal' hl1.le hJ hsep P hPi S hSs hSf hSc
  have hJ' : ∀ i ∈ J, (B i).right ≤ l := fun i hiJ => (hJ i hiJ).trans hal'.le
  have hcross : ∀ s ∈ Icc P'.arc.start P'.arc.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P'.arc.curve s ≠ Q.curve t := by
    intro s hs t ht
    have ht' : t ∈ Ioc l 1 := by simpa only [hQs,hQf] using ht
    rw [hQmatch t ⟨ht'.1.le,ht'.2⟩]
    exact resolvedPrefixImage_avoids_future B hi hl1.le hJ' hsep _
      (hP'i (mem_image_of_mem P'.arc.curve hs)) t ht'
  have hidg : Q.curve =ᶠ[𝓝 Q.start] γ.extend ∘ id := hQgerm
  obtain ⟨R,e,hes,hei,hem,hRs,hRf,hRi,hRstart,hRend,_,_⟩ :=
    join_shared_parameter_arcs γ.extend P'.arc Q P'.parameter id P'.smooth contDiff_id
      P'.forward (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (P'.value.trans hQs.symm) P'.germ hidg hcross
  refine ⟨R,hRstart.trans hP's,hRend.trans hQend,?_⟩
  rw [hRi]
  apply union_subset
  · exact hP'i.trans (resolvedPrefixImage_mono B (Subset.refl _) hl1.le)
  · intro x hx
    obtain ⟨u,hu,rfl⟩ := hx
    have hu' : u ∈ Icc l 1 := by simpa only [hQs,hQf] using hu
    rw [hQmatch u hu']
    exact Or.inl ⟨u,⟨ha.le.trans (hal'.le.trans hu'.1),hu'.2⟩,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InitialSmoothTail
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Start the finite smooth assembly at the original source endpoint,
retaining its actual regular germ and an exact unchanged initial trace. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q}

theorem initial_smooth_tail (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (r : ℝ) (P : SmoothArcTail γ.extend r), 0 < r ∧ r < η ∧
      P.arc.curve P.arc.start = p ∧
      P.arc.curve '' Icc P.arc.start P.arc.finish = γ.extend '' Icc 0 r := by
  obtain ⟨A,r,hr,hrη,hAs,hAf,hmatch,hsource,hgerm⟩ := first_regular_arc hγ hi hη hη1
  have hf : 0 < deriv (id : ℝ → ℝ) A.finish := by simp
  let P : SmoothArcTail γ.extend r := ⟨A,id,contDiff_id,hf,hAf,hgerm⟩
  refine ⟨r,P,hr,hrη,hsource,?_⟩
  change A.curve '' Icc A.start A.finish = _
  rw [hAs,hAf]
  exact Set.EqOn.image_eq (fun u hu => hmatch u hu)

theorem initial_smooth_tail_until (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) {d D : ℝ} (hd : 0 < d) (hdD : d < D) (hD : D ≤ 1)
    (hreg : ∀ t ∈ Ioo (0:ℝ) D, ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t)) :
    ∃ P : SmoothArcTail γ.extend d, P.arc.curve P.arc.start = p ∧
      P.arc.curve '' Icc P.arc.start P.arc.finish = γ.extend '' Icc 0 d := by
  obtain ⟨r,P,hr,hrd,hPsource,hPimage⟩ := initial_smooth_tail hγ hi hd (hdD.le.trans hD)
  obtain ⟨Q,hQs,hQf,hQc⟩ := original_regular_segment hi isOpen_Ioo
    (fun _ ht => ⟨ht.1,ht.2.trans_le hD⟩) hreg hrd
    (fun u hu => ⟨hr.trans_le hu.1,hu.2.trans_lt hdD⟩)
  have hcross : ∀ s ∈ Icc P.arc.start P.arc.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.arc.curve s ≠ Q.curve t := by
    intro s hs t ht he
    obtain ⟨u,hu,huP⟩ := hPimage.subset (mem_image_of_mem P.arc.curve hs)
    rw [hQs,hQf] at ht
    rw [hQc] at he
    have hue : u = t := embeddedPath_extend_injOn γ hi
      ⟨hu.1,hu.2.trans (hrd.le.trans (hdD.le.trans hD))⟩
      ⟨hr.le.trans ht.1.le,ht.2.trans (hdD.le.trans hD)⟩ (huP.trans he)
    exact (not_le_of_gt ht.1) (hue ▸ hu.2)
  have hleft : Q.curve =ᶠ[𝓝 Q.start] γ.extend ∘ id := by rw [hQc]; rfl
  have hright : Q.curve =ᶠ[𝓝 Q.finish] γ.extend ∘ id := by rw [hQc]; rfl
  obtain ⟨R,hRimage,hRsource,_⟩ := P.append Q id id contDiff_id contDiff_id
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hQs hQf hleft hright hcross
  refine ⟨R,hRsource.trans hPsource,?_⟩
  rw [hRimage,hPimage,hQc,hQs,hQf,← image_union,Icc_union_Icc_eq_Icc hr.le hrd.le]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FinitePointNeighborhoods
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pairwise disjoint open neighborhoods of finitely many distinct points,
refining any prescribed neighborhoods. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [Finite ι]

theorem finite_disjoint_open_neighborhoods (p : ι → X) (hi : Function.Injective p)
    (O : ι → Set X) (hO : ∀ i, IsOpen (O i)) (hpO : ∀ i, p i ∈ O i) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i) ∧ p i ∈ U i ∧ U i ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  have hpair : ∀ i j : ι, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ p i ∈ U ∧ p j ∈ V ∧ (i ≠ j → Disjoint U V) := by
    intro i j
    by_cases hij : i = j
    · exact ⟨univ,univ,isOpen_univ,isOpen_univ,mem_univ _,mem_univ _,fun h => False.elim (h hij)⟩
    · obtain ⟨U,V,hU,hV,hpU,hpV,hUV⟩ := t2_separation (fun he => hij (hi he))
      exact ⟨U,V,hU,hV,hpU,hpV,fun _ => hUV⟩
  choose U V hU hV hpU hpV hUV using hpair
  let W : ι → Set X := fun i => O i ∩ (⋂ j, U i j) ∩ (⋂ j, V j i)
  have hW : ∀ i, IsOpen (W i) ∧ p i ∈ W i ∧ W i ⊆ O i := by
    intro i
    refine ⟨((hO i).inter (isOpen_iInter_of_finite (hU i))).inter
      (isOpen_iInter_of_finite (fun j => hV j i)),?_,?_⟩
    · exact ⟨⟨hpO i,mem_iInter.mpr (hpU i)⟩,mem_iInter.mpr (fun j => hpV j i)⟩
    · exact fun _ hx => hx.1.1
  refine ⟨W,hW,?_⟩
  intro i j hij
  apply (hUV i j hij).mono
  · intro x hx
    exact mem_iInter.mp hx.1.2 j
  · intro x hx
    exact mem_iInter.mp hx.2 i

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteCornerBridges
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous separated smooth bridges at finitely many path corners,
with attachment points inside prescribed parameter windows. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [Finite ι]
variable {p q : M} {γ : Path p q}

theorem finite_corner_bridges (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) (T : ι → ℝ) (hT : Function.Injective T)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (haT : ∀ i, a i < T i)
    (hTb : ∀ i, T i < b i) (hb : ∀ i, b i ≤ 1)
    {O : Set M} (hO : IsOpen O) (hTO : ∀ i, γ.extend (T i) ∈ O) :
    ∃ B : ∀ i, LocalCornerBridge γ (T i) O,
      (∀ i, a i < (B i).left ∧ (B i).right < b i) ∧
      (∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
        ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
          (B i).arc.curve s ≠ γ.extend u) ∧
      Pairwise (fun i j => Disjoint
        ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
        ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)) := by
  classical
  have hTi : ∀ i, T i ∈ Ioo (0:ℝ) 1 := fun i =>
    ⟨lt_of_le_of_lt (ha i) (haT i),lt_of_lt_of_le (hTb i) (hb i)⟩
  choose U hU hTU hUO hUavoid using fun i =>
    embedded_path_corner_neighborhood γ hi (ha i) (haT i) (hTb i) (hb i) hO (hTO i)
  have hp : Function.Injective (fun i => γ.extend (T i)) := by
    intro i j hij
    exact hT (embeddedPath_extend_injOn γ hi ⟨(hTi i).1.le,(hTi i).2.le⟩
      ⟨(hTi j).1.le,(hTi j).2.le⟩ hij)
  obtain ⟨V,hV,hVdis⟩ := finite_disjoint_open_neighborhoods (fun i => γ.extend (T i)) hp U hU hTU
  choose B hBsep using fun i => separated_corner_bridge hγ hi (hTi i) (hV i).1 (hV i).2.1
  let B' : ∀ i, LocalCornerBridge γ (T i) O := fun i => (B i).mono ((hV i).2.2.trans (hUO i))
  have hbounds : ∀ i, a i < (B i).left ∧ (B i).right < b i := by
    intro i
    constructor
    · apply lt_of_not_ge
      intro hle
      apply hUavoid i (B i).left (Or.inl ⟨(B i).left_pos.le,hle⟩)
      have hm := (hV i).2.2 ((B i).image_subset
        (left_mem_Icc.mpr (B i).arc.start_lt_finish.le))
      have he := (B i).source_eq
      rw [he] at hm
      have he' : γ.extend (B i).left = γ (B i).leftPoint := Path.extend_extends' γ (B i).leftPoint
      rwa [he']
    · apply lt_of_not_ge
      intro hle
      apply hUavoid i (B i).right (Or.inr ⟨hle,(B i).right_lt_one.le⟩)
      have hm := (hV i).2.2 ((B i).image_subset
        (right_mem_Icc.mpr (B i).arc.start_lt_finish.le))
      have he := (B i).target_eq
      rw [he] at hm
      have he' : γ.extend (B i).right = γ (B i).rightPoint := Path.extend_extends' γ (B i).rightPoint
      rwa [he']
  refine ⟨B',hbounds,hBsep,?_⟩
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨s,hs,hxs⟩ ⟨u,hu,hxu⟩
  have hxVi : x ∈ V i := by
    rw [← hxs]
    exact (B i).image_subset hs
  have hxVj : x ∈ V j := by
    rw [← hxu]
    exact (B j).image_subset hu
  exact disjoint_left.mp (hVdis hij) hxVi hxVj

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FiniteCornerWindows
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite distinct interior parameters have disjoint compact interval
windows, in their original order. -/
noncomputable section
open Set Filter
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {ι : Type*} [Finite ι]

theorem finite_corner_windows (T : ι → ℝ) (hi : Function.Injective T)
    (hT : ∀ i, T i ∈ Ioo (0:ℝ) 1) :
    ∃ a b : ι → ℝ, (∀ i, 0 < a i ∧ a i < T i ∧ T i < b i ∧ b i < 1) ∧
      Pairwise (fun i j => Disjoint (Icc (a i) (b i)) (Icc (a j) (b j))) ∧
      ∀ i j, T i < T j → b i < a j := by
  obtain ⟨U,hU,hdis⟩ := finite_disjoint_open_neighborhoods T hi
    (fun _ => Ioo (0:ℝ) 1) (fun _ => isOpen_Ioo) hT
  have hchoice : ∀ i, ∃ a b : ℝ, 0 < a ∧ a < T i ∧ T i < b ∧ b < 1 ∧ Icc a b ⊆ U i := by
    intro i
    obtain ⟨l,r,⟨hlt,htr⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp ((hU i).1.mem_nhds (hU i).2.1)
    obtain ⟨a,hla,hat⟩ := exists_between hlt
    obtain ⟨b,htb,hbr⟩ := exists_between htr
    have hs : Icc a b ⊆ U i := fun _ hx => hsub ⟨hla.trans_le hx.1,hx.2.trans_lt hbr⟩
    have hab : a ≤ b := (hat.trans htb).le
    exact ⟨a,b,((hU i).2.2 (hs (left_mem_Icc.mpr hab))).1,hat,htb,
      ((hU i).2.2 (hs (right_mem_Icc.mpr hab))).2,hs⟩
  choose a b ha haT hTb hb hsub using hchoice
  have hd : Pairwise (fun i j => Disjoint (Icc (a i) (b i)) (Icc (a j) (b j))) :=
    fun i j hij => (hdis hij).mono (hsub i) (hsub j)
  refine ⟨a,b,fun i => ⟨ha i,haT i,hTb i,hb i⟩,hd,?_⟩
  intro i j hij
  have hne : i ≠ j := fun he => (ne_of_lt hij) (congrArg T he)
  by_contra hn
  have hji : a j ≤ b i := le_of_not_gt hn
  by_cases haij : a i ≤ a j
  · exact disjoint_left.mp (hd hne) ⟨haij,hji⟩ ⟨le_rfl,(haT j).le.trans (hTb j).le⟩
  · have haj : a j ≤ a i := (lt_of_not_ge haij).le
    have hai : a i ≤ b i := (haT i).le.trans (hTb i).le
    have hbaj : a i ≤ b j := ((haT i).trans hij |>.trans (hTb j)).le
    exact disjoint_left.mp (hd hne) ⟨le_rfl,hai⟩ ⟨haj,hbaj⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OrderedCornerBridges
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite nonsmooth parameter set can be rounded by an ordered
family of mutually disjoint smooth bridges. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {p q : M} {γ : Path p q}

theorem ordered_corner_bridges_interior (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) {O : Set M} (hO : IsOpen O)
    (hγO : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ O) :
    ∃ (n : ℕ) (T : Fin n → ℝ), StrictMono T ∧
      (∀ i, T i ∈ Ioo (0:ℝ) 1) ∧
      ∃ B : ∀ i, LocalCornerBridge γ (T i) O,
        (∀ i j, i < j → (B i).right < (B j).left) ∧
        (∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
          ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
            (B i).arc.curve s ≠ γ.extend u) ∧
        Pairwise (fun i j => Disjoint
          ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
          ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)) ∧
        ∀ t ∈ Ioo (0:ℝ) 1, t ∉ range T →
          ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
          Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
  classical
  obtain ⟨S,hS,hregular⟩ := hγ.smooth_outside_finite hi
  let F : Finset ℝ := hS.toFinset.filter (fun t => t ∈ Ioo (0:ℝ) 1)
  let T : Fin F.card → ℝ := F.orderEmbOfFin rfl
  have hTm : StrictMono T := (F.orderEmbOfFin rfl).strictMono
  have hTi : ∀ i, T i ∈ Ioo (0:ℝ) 1 := by
    intro i
    exact (Finset.mem_filter.mp (F.orderEmbOfFin_mem rfl i)).2
  obtain ⟨a,b,hab,_,horder⟩ := finite_corner_windows T hTm.injective hTi
  have hTO : ∀ i, γ.extend (T i) ∈ O := fun i => hγO _ (hTi i)
  obtain ⟨B,hB,hsep,hdis⟩ := finite_corner_bridges hγ hi T hTm.injective a b
    (fun i => (hab i).1.le) (fun i => (hab i).2.1) (fun i => (hab i).2.2.1)
    (fun i => (hab i).2.2.2.le) hO hTO
  refine ⟨F.card,T,hTm,hTi,B,?_,hsep,hdis,?_⟩
  · intro i j hij
    exact (hB i).2.trans ((horder i j (hTm hij)).trans (hB j).1)
  · intro t ht hn
    apply hregular t ht
    intro hts
    have htF : t ∈ F := Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hts,ht⟩
    apply hn
    have hr : range T = (F : Set ℝ) := F.range_orderEmbOfFin rfl
    rw [hr]
    exact htF

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_OrderedNodeIntervals
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Consecutive ordered corner parameters leave genuine regular open
intervals of the original path between them. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma not_mem_range_before_first {n : ℕ} (T : Fin (n+1) → ℝ) (hT : StrictMono T)
    {t : ℝ} (ht : t < T 0) : t ∉ range T := by
  rintro ⟨k,rfl⟩
  exact (not_lt_of_ge (hT.monotone (show (0:Fin (n+1)) ≤ k from bot_le))) ht

lemma not_mem_range_between_successive {n : ℕ} (T : Fin n → ℝ) (hT : StrictMono T)
    {i j : Fin n} (hij : j.val = i.val+1) {t : ℝ} (hi : T i < t) (hj : t < T j) :
    t ∉ range T := by
  rintro ⟨k,rfl⟩
  have hik := hT.lt_iff_lt.mp hi
  have hkj := hT.lt_iff_lt.mp hj
  change i.val < k.val at hik
  change k.val < j.val at hkj
  omega

lemma not_mem_range_after_last {n : ℕ} (T : Fin (n+1) → ℝ) (hT : StrictMono T)
    {t : ℝ} (ht : T (Fin.last n) < t) : t ∉ range T := by
  rintro ⟨k,rfl⟩
  have hk : k ≤ Fin.last n := k.le_last
  exact (not_lt_of_ge (hT.monotone hk)) ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothOrderedPrefix
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite induction assembles the actual ordered bridges and unchanged
regular segments, preserving embeddedness and the initial endpoint. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {n : ℕ} {O : Set M}

theorem smooth_ordered_prefix (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) (T : Fin (n+1) → ℝ) (hT : StrictMono T)
    (hTi : ∀ i, T i ∈ Ioo (0:ℝ) 1)
    (B : ∀ i, LocalCornerBridge γ (T i) O)
    (horder : ∀ i j, i < j → (B i).right < (B j).left)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hdis : Pairwise (fun i j => Disjoint
      ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
      ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)))
    (hreg : ∀ t ∈ Ioo (0:ℝ) 1, t ∉ range T →
      ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t)) :
    ∀ j : Fin (n+1), ∃ P : SmoothArcTail γ.extend (B j).right,
      P.arc.curve P.arc.start = p ∧
      P.arc.curve '' Icc P.arc.start P.arc.finish ⊆
        resolvedPrefixImage γ B {i | i ≤ j} (B j).right := by
  intro j
  induction j using Fin.induction with
  | zero =>
    have hpre : ∀ t ∈ Ioo (0:ℝ) (T 0),
        ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
      intro t ht
      exact hreg t ⟨ht.1,ht.2.trans (hTi 0).2⟩ (not_mem_range_before_first T hT ht.2)
    obtain ⟨P,hPs,hPi⟩ := initial_smooth_tail_until hγ hi (B 0).left_pos (B 0).left_lt (hTi 0).2.le hpre
    have hp : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆
        resolvedPrefixImage γ B ∅ (B 0).left := by
      intro x hx
      exact Or.inl (hPi ▸ hx)
    obtain ⟨R,hRi,hRs⟩ := append_resolved_bridge B (notMem_empty 0) hsep hdis P hp
    have hJ : insert (0 : Fin (n+1)) (∅ : Set (Fin (n+1))) = {i | i ≤ 0} := by
      ext i
      simp
    refine ⟨R,hRs.trans hPs,?_⟩
    simpa only [hJ] using hRi
  | succ i ih =>
    obtain ⟨P,hPs,hPi⟩ := ih
    have hik : i.castSucc < i.succ := Fin.castSucc_lt_succ
    have hgap := horder i.castSucc i.succ hik
    have hbetween : ∀ t ∈ Ioo (T i.castSucc) (T i.succ),
        ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
      intro t ht
      exact hreg t ⟨(hTi i.castSucc).1.trans ht.1,ht.2.trans (hTi i.succ).2⟩
        (not_mem_range_between_successive T hT (by rfl) ht.1 ht.2)
    obtain ⟨Q,hQs,hQf,hQc⟩ := original_regular_segment hi isOpen_Ioo
      (fun _ ht => ⟨(hTi i.castSucc).1.trans ht.1,ht.2.trans (hTi i.succ).2⟩)
      hbetween hgap (fun u hu =>
        ⟨(B i.castSucc).lt_right.trans_le hu.1,hu.2.trans_lt (B i.succ).left_lt⟩)
    have hJ : ∀ k ∈ {k : Fin (n+1) | k ≤ i.castSucc}, (B k).right ≤ (B i.castSucc).right := by
      intro k hk
      change k ≤ i.castSucc at hk
      rcases lt_or_eq_of_le hk with hk | rfl
      · exact (horder k i.castSucc hk).le.trans ((B i.castSucc).left_lt.trans (B i.castSucc).lt_right).le
      · exact le_rfl
    obtain ⟨P',hP'i,hP's⟩ := append_resolved_segment B hi (B i.castSucc).rightPoint.property.1
      hgap (B i.succ).leftPoint.property.2 hJ hsep P hPi Q hQs hQf hQc
    have hk : i.succ ∉ {k : Fin (n+1) | k ≤ i.castSucc} := by
      change ¬ i.succ ≤ i.castSucc
      exact not_le_of_gt Fin.castSucc_lt_succ
    obtain ⟨R,hRi,hRs⟩ := append_resolved_bridge B hk hsep hdis P' hP'i
    have hJ' : insert i.succ {k : Fin (n+1) | k ≤ i.castSucc} = {k | k ≤ i.succ} := by
      ext k
      simp only [mem_insert_iff,mem_ofPred_eq,Fin.le_castSucc_iff]
      exact le_iff_eq_or_lt.symm
    refine ⟨R,hRs.trans (hP's.trans hPs),?_⟩
    simpa only [hJ'] using hRi

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothOrderedArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finishing the finite ordered construction gives one smooth embedded
source arc, with the prescribed original endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {n : ℕ} {O : Set M}

theorem smooth_ordered_arc (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) (T : Fin (n+1) → ℝ) (hT : StrictMono T)
    (hTi : ∀ i, T i ∈ Ioo (0:ℝ) 1)
    (B : ∀ i, LocalCornerBridge γ (T i) O)
    (horder : ∀ i j, i < j → (B i).right < (B j).left)
    (hsep : ∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
      ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
        (B i).arc.curve s ≠ γ.extend u)
    (hdis : Pairwise (fun i j => Disjoint
      ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
      ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)))
    (hreg : ∀ t ∈ Ioo (0:ℝ) 1, t ∉ range T →
      ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t)) :
    ∃ R : SmoothCompactArc planeModel M,
      R.curve R.start = p ∧ R.curve R.finish = q ∧
      R.curve '' Icc R.start R.finish ⊆ range γ ∪
        ⋃ i, (B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish := by
  obtain ⟨P,hPs,hPi⟩ := smooth_ordered_prefix hγ hi T hT hTi B horder hsep hdis hreg (Fin.last n)
  have hJ : ∀ i ∈ {i : Fin (n+1) | i ≤ Fin.last n},
      (B i).right ≤ (B (Fin.last n)).right := by
    intro i hiJ
    change i ≤ Fin.last n at hiJ
    rcases lt_or_eq_of_le hiJ with hiJ | rfl
    · exact (horder i (Fin.last n) hiJ).le.trans
        ((B (Fin.last n)).left_lt.trans (B (Fin.last n)).lt_right).le
    · exact le_rfl
  have hafter : ∀ t ∈ Ioo (T (Fin.last n)) 1,
      ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
    intro t ht
    exact hreg t ⟨(hTi (Fin.last n)).1.trans ht.1,ht.2⟩
      (not_mem_range_after_last T hT ht.1)
  obtain ⟨R,hRs,hRf,hRi⟩ := finish_smooth_tail hγ hi B
    ((B (Fin.last n)).left_pos.trans (B (Fin.last n)).left_lt |>.trans (B (Fin.last n)).lt_right)
    (B (Fin.last n)).right_lt_one (B (Fin.last n)).lt_right (hTi (Fin.last n)).1.le
    hJ hsep hafter P hPi
  refine ⟨R,hRs.trans hPs,hRf,?_⟩
  intro x hx
  rcases hRi hx with hx | hx
  · obtain ⟨u,hu,rfl⟩ := hx
    exact Or.inl ⟨⟨u,hu⟩,(Path.extend_apply γ hu).symm⟩
  · obtain ⟨i,_,hx⟩ := mem_iUnion₂.mp hx
    exact Or.inr (mem_iUnion.mpr ⟨i,hx⟩)

theorem smooth_regular_path (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    (hreg : ∀ t ∈ Ioo (0:ℝ) 1,
      ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t)) :
    ∃ R : SmoothCompactArc planeModel M,
      R.curve R.start = p ∧ R.curve R.finish = q ∧ R.curve '' Icc R.start R.finish ⊆ range γ := by
  let T : Fin 0 → ℝ := Fin.elim0
  let B : ∀ i : Fin 0, LocalCornerBridge γ (T i) (univ : Set M) := fun i => Fin.elim0 i
  obtain ⟨P,hPs,hPi⟩ := initial_smooth_tail_until hγ hi (d := 1/2) (D := 3/4)
    (by norm_num) (by norm_num) (by norm_num)
    (fun t ht => hreg t ⟨ht.1,by linarith [ht.2]⟩)
  have hPimage : P.arc.curve '' Icc P.arc.start P.arc.finish ⊆ resolvedPrefixImage γ B ∅ (1/2) := by
    intro x hx
    exact Or.inl (hPi ▸ hx)
  obtain ⟨R,hRs,hRf,hRi⟩ := finish_smooth_tail hγ hi B (a := 1/2) (A := 0)
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hreg P hPimage
  refine ⟨R,hRs.trans hPs,hRf,?_⟩
  intro x hx
  rcases hRi hx with hx | hx
  · obtain ⟨u,hu,rfl⟩ := hx
    exact ⟨⟨u,hu⟩,(Path.extend_apply γ hu).symm⟩
  · obtain ⟨i,_,_⟩ := mem_iUnion₂.mp hx
    exact Fin.elim0 i

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothFiniteRegularPath
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite embedded regular-piece path can be smoothed inside any open
set containing its interior. All new points lie in a compact subset of
that open set, while its two endpoints remain fixed. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {p q : M} {γ : Path p q}

theorem smooth_finite_regular_path (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) {O : Set M} (hO : IsOpen O)
    (hγO : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ O) :
    ∃ (P : SmoothCompactArc planeModel M) (K : Set M),
      IsCompact K ∧ K ⊆ O ∧ P.curve P.start = p ∧ P.curve P.finish = q ∧
      P.curve '' Icc P.start P.finish ⊆ range γ ∪ K := by
  obtain ⟨n,T,hT,hTi,B,horder,hsep,hdis,hreg⟩ := ordered_corner_bridges_interior hγ hi hO hγO
  cases n with
  | zero =>
    have hreg' : ∀ t ∈ Ioo (0:ℝ) 1,
        ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
        Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
      intro t ht
      apply hreg t ht
      rintro ⟨i,_⟩
      exact Fin.elim0 i
    obtain ⟨P,hPs,hPf,hPi⟩ := smooth_regular_path hγ hi hreg'
    exact ⟨P,∅,isCompact_empty,empty_subset _,hPs,hPf,fun x hx => Or.inl (hPi hx)⟩
  | succ n =>
    obtain ⟨P,hPs,hPf,hPi⟩ := smooth_ordered_arc hγ hi T hT hTi B horder hsep hdis hreg
    let K := ⋃ i, (B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish
    have hK : IsCompact K := isCompact_iUnion (fun i =>
      isCompact_Icc.image_of_continuousOn ((B i).arc.smooth.continuousOn.mono (B i).arc.interval_subset))
    have hKO : K ⊆ O := by
      intro x hx
      obtain ⟨i,s,hs,rfl⟩ := mem_iUnion.mp hx
      exact (B i).image_subset hs
    exact ⟨P,K,hK,hKO,hPs,hPf,hPi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPathRegularInterior
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interior regularity survives the finite smoothing: injectivity excludes
both fixed endpoints from every interior parameter. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q}

theorem smoothed_arc_interior {O : Set M}
    (hγO : ∀ t : unitInterval, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∈ O)
    (P : SmoothCompactArc planeModel M) {K : Set M} (hKO : K ⊆ O)
    (hPs : P.curve P.start = p) (hPf : P.curve P.finish = q)
    (hPi : P.curve '' Icc P.start P.finish ⊆ range γ ∪ K) :
    ∀ t ∈ Ioo P.start P.finish, P.curve t ∈ O := by
  intro t ht
  rcases hPi ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩ with h | h
  · obtain ⟨u,hu⟩ := h
    have hu0 : u ≠ 0 := by
      intro he
      have heq : P.curve t = P.curve P.start := by rw [← hu,he,Path.source,hPs]
      exact (ne_of_gt ht.1) (P.injective ⟨ht.1.le,ht.2.le⟩
        (left_mem_Icc.mpr P.start_lt_finish.le) heq)
    have hu1 : u ≠ 1 := by
      intro he
      have heq : P.curve t = P.curve P.finish := by rw [← hu,he,Path.target,hPf]
      exact (ne_of_lt ht.2) (P.injective ⟨ht.1.le,ht.2.le⟩
        (right_mem_Icc.mpr P.start_lt_finish.le) heq)
    rw [← hu]
    exact hγO u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm)))
      (lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he)))
  · exact hKO h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactCurveEndpoint
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact curve with a unique endpoint preimage has no distant
parameter values accumulating at that endpoint, even after a compact
set avoiding the endpoint is added. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [T2Space M]

theorem compact_curve_endpoint_neighborhood {γ : I → M} (hγ : Continuous γ)
    {p : M} (hunique : ∀ t, γ t = p → t = 0)
    {K : Set M} (hK : IsCompact K) (hpK : p ∉ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ x ∈ V, x ∈ range γ ∪ K → ∃ t : I, (t:ℝ) < ε ∧ γ t = x := by
  let A : Set I := {t | ε ≤ (t:ℝ)}
  have hA : IsCompact A := (isClosed_le continuous_const continuous_subtype_val).isCompact
  have hL : IsCompact (γ '' A ∪ K) := (hA.image hγ).union hK
  have hpL : p ∉ γ '' A ∪ K := by
    rintro (⟨t,ht,he⟩ | ht)
    · have hz := hunique t he
      subst t
      change ε ≤ 0 at ht
      exact (not_le_of_gt hε) ht
    · exact hpK ht
  refine ⟨(γ '' A ∪ K)ᶜ,hL.isClosed.isOpen_compl,hpL,?_⟩
  intro x hx hxi
  rcases hxi with ⟨t,rfl⟩ | hxi
  · refine ⟨t,?_,rfl⟩
    by_contra hn
    exact hx (Or.inl ⟨t,le_of_not_gt hn,rfl⟩)
  · exact False.elim (hx (Or.inr hxi))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceRegularLocus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The regular locus of a smooth surface map is open in the actual surface. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem surface_regular_locus_open {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    IsOpen {p | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨U,F,hU,hpU,hUs,hF,heF⟩ := surface_chart_representative hf p
  let V : Set Base := {z | Function.Injective (fderiv ℝ F z)}
  have hV : IsOpen V := ContinuousLinearMap.isOpen_injective.preimage
    (hF.continuous_fderiv (by simp))
  have hpV : chart p p ∈ V :=
    (chart_germ_immersion_iff p (hUs hpU) hF
      (heF.eventuallyEq_of_mem (hU.mem_nhds hpU))).mp hp
  have hW : IsOpen (U ∩ (chart p) ⁻¹' V) :=
    ((chart p).continuousOn.mono hUs).isOpen_inter_preimage hU hV
  apply Filter.mem_of_superset (hW.mem_nhds ⟨hpU,hpV⟩)
  rintro x ⟨hxU,hxV⟩
  exact (chart_germ_immersion_iff p (hUs hxU) hF
    (heF.eventuallyEq_of_mem (hU.mem_nhds hxU))).mpr hxV

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapArcEndpoint
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous ordered double arc ending at a prepared crosscap lies
in its source chart on a full initial parameter interval. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

 theorem crosscap_arc_endpoint (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hzero : Γ 0 = (p,p))
    (heq : ∀ t, f (Γ t).1 = f (Γ t).2)
    (hne : ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1/3 ∧ ∀ t : I, (t:ℝ) ≤ ε →
      (Γ t).1 ∈ c.source.source ∧ (Γ t).2 ∈ c.source.source ∧
      c.source (Γ t).1 0 = 0 ∧ c.source (Γ t).2 0 = 0 ∧
      c.source (Γ t).1 1 = -c.source (Γ t).2 1 ∧
      (0 < (t:ℝ) → c.source (Γ t).1 1 ≠ 0) := by
  let Θ : ℝ → M × M := Γ ∘ projIcc 0 1 zero_le_one
  have hΘ : Continuous Θ := hΓ.comp continuous_projIcc
  have hΘ0 : Θ 0 = (p,p) := by
    change Γ (projIcc 0 1 zero_le_one 0) = _
    have hp : projIcc 0 1 zero_le_one 0 = (0:I) := Subtype.ext (by simp [projIcc_left])
    rw [hp]
    exact hzero
  have hU : IsOpen (Θ ⁻¹' (c.source.source ×ˢ c.source.source)) :=
    (c.source.open_source.prod c.source.open_source).preimage hΘ
  have h0 : (0:ℝ) ∈ Θ ⁻¹' (c.source.source ×ˢ c.source.source) := by
    change (Θ 0).1 ∈ c.source.source ∧ (Θ 0).2 ∈ c.source.source
    rw [hΘ0]
    exact ⟨c.source_mem,c.source_mem⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let ε : ℝ := min (r/2) (1/4)
  have hε : 0 < ε := lt_min (half_pos hr) (by norm_num)
  have hεsmall : ε < 1/3 := (min_le_right _ _).trans_lt (by norm_num)
  have hε1 : ε < 1 := hεsmall.trans (by norm_num)
  have hεr : ε < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  refine ⟨ε,hε,hεsmall,?_⟩
  intro t ht
  have hmem : Θ (t:ℝ) ∈ c.source.source ×ˢ c.source.source := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg t.property.1]
    exact ht.trans_lt hεr
  have hΘt : Θ (t:ℝ) = Γ t := by
    change Γ (projIcc 0 1 zero_le_one (t:ℝ)) = Γ t
    rw [projIcc_val]
  rw [hΘt] at hmem
  refine ⟨hmem.1,hmem.2,?_⟩
  by_cases ht0 : (t:ℝ) = 0
  · have htz : t = 0 := Subtype.ext ht0
    rw [htz,hzero]
    simp [c.source_center]
  · have hp := c.double_pair hmem.1 hmem.2
      (hne t (lt_of_le_of_ne t.property.1 (Ne.symm ht0)) (ht.trans_lt hε1)) (heq t)
    exact ⟨hp.1,hp.2.1,hp.2.2.1,fun _ => hp.2.2.2⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SimpleCrosscapArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For the prepared map with simple singular fibers, the connecting ordered
arc has two regular sheets at every interior point. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem simple_prepared_crosscap_ordered_arc {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hsimple : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∀ q, f q = f p → q = p)
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
        (∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 → (Γ t).1 ≠ (Γ t).2 ∧
          Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ t).1) ∧
          Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ t).2)) := by
  classical
  obtain ⟨q,hqp,hq,Γ,hΓ,heq,hne⟩ := prepared_crosscap_ordered_arc hf hfin hreg hrep p hp
  refine ⟨q,hqp,hq,Γ,hΓ,heq,?_⟩
  intro t ht0 ht1
  have htne := hne t ht0 ht1
  refine ⟨htne,?_,?_⟩
  · by_contra hbad
    exact htne (hsimple (Γ t).1 hbad (Γ t).2 (heq t).symm).symm
  · by_contra hbad
    exact htne (hsimple (Γ t).2 hbad (Γ t).1 (heq t))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_OrderedArcEndpointUnique
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton fibers over crosscaps prevent the source projection of an
ordered connecting arc from revisiting either singular endpoint. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} {Y : Type*} {f : M → Y} {p q : M} {Γ : I → M × M}

lemma ordered_arc_endpoints_distinct (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q)) : p ≠ q := by
  intro hpq
  have hpair : Γ 0 = Γ 1 := by rw [hzero,hone,hpq]
  have h := congrArg (fun t : I => (t:ℝ)) (hi hpair)
  norm_num at h

lemma ordered_arc_source_start_unique (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hne : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2)
    (hsing : ∀ x, f x = f p → x = p) :
    ∀ u : I, (Γ u).1 = p → u = 0 := by
  intro u hu
  by_contra hu0
  have hu1 : u ≠ 1 := by
    intro he
    rw [he,hone] at hu
    exact ordered_arc_endpoints_distinct hi hzero hone hu.symm
  have h0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (by
    intro he
    exact hu0 (Subtype.ext he.symm))
  have h1 : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2 (by
    intro he
    exact hu1 (Subtype.ext he))
  have hsecond : (Γ u).2 = p := hsing _ ((heq u).symm.trans (congrArg f hu))
  exact hne u h0 h1 (hu.trans hsecond.symm)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapPathInterior
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The embedded source path obtained by loop removal meets no other
singular point: every interior point belongs to a regular original sheet. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_source_embedded_path_regular
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2 ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (hsing : ∀ x, f x = f p → x = p) :
    ∃ P : Path p q, FiniteRegularPath planeModel P ∧ Function.Injective P ∧
      range P ⊆ Prod.fst '' range Γ ∧
      ∀ t : I, 0 < (t:ℝ) → (t:ℝ) < 1 →
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P t)) := by
  obtain ⟨P,hPp,hPi,hPr⟩ := crosscap_source_embedded_path hf hreg cp cq hΓ hi hzero hone heq hgood hsing
  refine ⟨P,hPp,hPi,hPr,?_⟩
  intro t ht0 ht1
  obtain ⟨z,⟨u,hu⟩,hz⟩ := hPr (mem_range_self t)
  have hpnt : (Γ u).1 = P t := by rw [hu]; exact hz
  have hu0 : u ≠ 0 := by
    intro he
    have htzero : t = 0 := hPi (by rw [Path.source,← hpnt,he,hzero])
    have hval := congrArg (fun s : I => (s:ℝ)) htzero
    change (t:ℝ) = 0 at hval
    linarith
  have hu1 : u ≠ 1 := by
    intro he
    have htone : t = 1 := hPi (by rw [Path.target,← hpnt,he,hone])
    have hval := congrArg (fun s : I => (s:ℝ)) htone
    change (t:ℝ) = 1 at hval
    linarith
  have hu0' : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))
  have hu1' : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he))
  rw [← hpnt]
  exact (hgood u hu0' hu1').2.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapSourceEndpoint
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact regular insertions do not change the kernel-axis geometry
of an actual crosscap connection near its singular endpoint. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_source_endpoint_neighborhood (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hne : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2)
    (hsing : ∀ x, f x = f p → x = p)
    {K : Set M} (hK : IsCompact K) (hpK : p ∉ K) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ x ∈ V, x ∈ Prod.fst '' range Γ ∪ K →
        x ∈ c.source.source ∧ c.source x 0 = 0 := by
  obtain ⟨ε,hε,_,hcoords⟩ := crosscap_arc_endpoint c hΓ hzero heq hne
  obtain ⟨V,hV,hpV,hsmall⟩ := compact_curve_endpoint_neighborhood hΓ.fst
    (ordered_arc_source_start_unique hi hzero hone heq hne hsing) hK hpK hε
  refine ⟨V,hV,hpV,?_⟩
  intro x hx hxi
  have hxrange : x ∈ range (fun t => (Γ t).1) ∪ K := by
    rcases hxi with ⟨z,⟨u,hu⟩,hz⟩ | hk
    · exact Or.inl ⟨u,(congrArg Prod.fst hu).trans hz⟩
    · exact Or.inr hk
  obtain ⟨u,hu,rfl⟩ := hsmall x hx hxrange
  exact ⟨(hcoords u hu.le).1,(hcoords u hu.le).2.2.1⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothCrosscapSourceArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual smooth embedded source arc joining the two crosscaps. Its
interior is regular, and every newly inserted point lies in a compact
regular set, so the original endpoint geometry remains accessible. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem smooth_crosscap_source_arc
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2 ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (hsing : ∀ x, f x = f p → x = p) :
    ∃ (P : SmoothCompactArc planeModel M) (K : Set M),
      IsCompact K ∧ K ⊆ {x | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} ∧
      P.curve P.start = p ∧ P.curve P.finish = q ∧
      P.curve '' Icc P.start P.finish ⊆ Prod.fst '' range Γ ∪ K ∧
      ∀ t ∈ Ioo P.start P.finish,
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.curve t)) := by
  obtain ⟨γ,hγ,hiγ,himage,hregular⟩ := crosscap_source_embedded_path_regular hf hreg
    cp cq hΓ hi hzero hone heq hgood hsing
  let O := {x | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)}
  have hO : IsOpen O := surface_regular_locus_open hf
  have hγO : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ O := by
    intro t ht
    let u : I := ⟨t,ht.1.le,ht.2.le⟩
    have he : γ.extend t = γ u := Path.extend_extends' γ u
    rw [he]
    exact hregular u ht.1 ht.2
  obtain ⟨P,K,hK,hKO,hPs,hPf,hPi⟩ := smooth_finite_regular_path hγ hiγ hO hγO
  refine ⟨P,K,hK,hKO,hPs,hPf,?_,?_⟩
  · intro x hx
    rcases hPi hx with h | h
    · exact Or.inl (himage h)
    · exact Or.inr h
  · exact smoothed_arc_interior hregular P hKO hPs hPf hPi

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SmoothCrosscapSourceGeometry
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The smooth embedded source connection retains both actual kernel
axes near its singular endpoints, in the original crosscap coordinates. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem smooth_crosscap_source_geometry
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p))
    (hq : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q))
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2 ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (hsingp : ∀ x, f x = f p → x = p) (hsingq : ∀ x, f x = f q → x = q) :
    ∃ (P : SmoothCompactArc planeModel M) (V W : Set M),
      IsOpen V ∧ p ∈ V ∧ IsOpen W ∧ q ∈ W ∧
      P.curve P.start = p ∧ P.curve P.finish = q ∧
      (∀ t ∈ Ioo P.start P.finish,
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.curve t))) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ V →
        P.curve t ∈ cp.source.source ∧ cp.source (P.curve t) 0 = 0) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ W →
        P.curve t ∈ cq.source.source ∧ cq.source (P.curve t) 0 = 0) := by
  obtain ⟨P,K,hK,hKO,hPs,hPf,hPi,hPr⟩ := smooth_crosscap_source_arc hf hreg cp cq
    hΓ hi hzero hone heq hgood hsingp
  have hne := fun u h0 h1 => (hgood u h0 h1).1
  obtain ⟨V,hV,hpV,hVp⟩ := crosscap_source_endpoint_neighborhood cp hΓ hi hzero hone
    heq hne hsingp hK (fun hk => hp (hKO hk))
  let Δ := Γ ∘ unitInterval.symm
  have hΔ : Continuous Δ := hΓ.comp continuous_symm
  have hΔi : Function.Injective Δ := hi.comp symm_bijective.injective
  have hΔ0 : Δ 0 = (q,q) := by simpa [Δ] using hone
  have hΔ1 : Δ 1 = (p,p) := by simpa [Δ] using hzero
  have hΔe : ∀ u, f (Δ u).1 = f (Δ u).2 := fun u => heq (unitInterval.symm u)
  have hΔn : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Δ u).1 ≠ (Δ u).2 := by
    intro u h0 h1
    apply hne
    · change 0 < 1-(u:ℝ); linarith
    · change 1-(u:ℝ) < 1; linarith
  have hrange : range Δ = range Γ := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨unitInterval.symm u,rfl⟩
    · rintro ⟨u,rfl⟩
      refine ⟨unitInterval.symm u,?_⟩
      simp [Δ]
  obtain ⟨W,hW,hqW,hWq⟩ := crosscap_source_endpoint_neighborhood cq hΔ hΔi hΔ0 hΔ1
    hΔe hΔn hsingq hK (fun hk => hq (hKO hk))
  refine ⟨P,V,W,hV,hpV,hW,hqW,hPs,hPf,hPr,?_,?_⟩
  · intro t ht htv
    exact hVp _ htv (hPi ⟨t,ht,rfl⟩)
  · intro t ht htw
    apply hWq _ htw
    rw [hrange]
    exact hPi ⟨t,ht,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_PreparedSmoothCrosscapArc
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual generic surface map admits a smooth embedded regular
source connection between a chosen crosscap and a distinct crosscap,
with both original kernel-axis endpoint coordinates retained. -/
noncomputable section
open Set Filter Manifold Topology unitInterval
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem prepared_smooth_crosscap_arc_oai {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hfin : {p | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)}.Finite)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (hsimple : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∀ q, f q = f p → q = p)
    (hrep : ∀ p, ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p) →
      ∃ (q : M) (φ : Base → ProjectionTarget 3) (b : Bool) (t : ℝ),
        p ∈ (chart q).source ∧ ContDiff ℝ ∞ φ ∧
        f =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q ∧
        surfaceDirection φ b (chart q p,t) = 0 ∧
        Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    (p : M) (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p)) :
    ∃ (q : M) (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
      (P : SmoothCompactArc planeModel M) (V W : Set M),
      q ≠ p ∧ ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q) ∧
      IsOpen V ∧ p ∈ V ∧ IsOpen W ∧ q ∈ W ∧
      P.curve P.start = p ∧ P.curve P.finish = q ∧
      (∀ t ∈ Ioo P.start P.finish,
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.curve t))) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ V →
        P.curve t ∈ cp.source.source ∧ cp.source (P.curve t) 0 = 0) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ W →
        P.curve t ∈ cq.source.source ∧ cq.source (P.curve t) 0 = 0) := by
  obtain ⟨q,hqp,hq,Γ,hΓ,heq,hgood⟩ := simple_prepared_crosscap_ordered_arc hf hfin hreg hsimple hrep p hp
  have hcoords (x : M) (hx : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)) :
      Nonempty (SurfaceCrosscapCoordinates f x) := by
    obtain ⟨c,φ,b,t,hxc,hφ,he,hz,hR⟩ := hrep x hx
    obtain ⟨C,T,hxC,hCx,h0T,hT0,hCS,hCI,hTS,hTI,hmodel⟩ :=
      surface_crosscap_normal_form f x c hxc hφ he b t hz hR
    exact ⟨⟨C,T,hxC,hCx,h0T,hT0,hCS,hCI,hTS,hTI,
      fun y hy => (hmodel y hy).1,fun y hy => (hmodel y hy).2⟩⟩
  let cp := (hcoords p hp).some
  let cq := (hcoords q hq).some
  obtain ⟨P,V,W,h⟩ := smooth_crosscap_source_geometry hf hreg cp cq hp hq Γ.continuous
    hΓ.injective Γ.source Γ.target heq hgood (hsimple p hp) (hsimple q hq)
  exact ⟨q,cp,cq,P,V,W,hqp,hq,h⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.prepared_smooth_crosscap_arc_oai.{u_1}
