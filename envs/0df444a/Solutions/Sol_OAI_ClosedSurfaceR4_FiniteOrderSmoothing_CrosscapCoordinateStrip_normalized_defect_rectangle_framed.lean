-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:22:48.185847+00:00
-- url     : https://prove2.me/submissions/559355d7-bc53-4b4f-b5c7-08e0bf938e6e

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
import Mathlib.LinearAlgebra.CrossProduct
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
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI008

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectionDirections
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LinearEquivNullImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear coordinate changes preserve null sets, including between the
finite-dimensional models used in the Sard argument. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem linear_equiv_null_image (e : E ≃L[ℝ] F)
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (ν : Measure F) [Measure.IsAddHaarMeasure ν]
    {s : Set E} (hs : μ s = 0) : ν (e '' s) = 0 := by
  have hm : ν.map e.symm ≪ μ :=
    Measure.absolutelyContinuous_isAddHaarMeasure (ν.map e.symm) μ
  have hz := hm hs
  have he : MeasurableEmbedding (e.symm : F → E) := e.symm.toHomeomorph.measurableEmbedding
  rw [he.map_apply] at hz
  simpa only [e.image_eq_preimage_symm] using hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowerDimensionalImage
attribute [-simp] _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The triple-radius exceptional set is null. Extend a map from two to
three coordinates constantly in the final coordinate and apply the proved
fixed-dimensional Jacobian null-image theorem. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs

local instance tripleVolumeHaar : (volume : Measure (Plane × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem smooth_surface_image_volume_zero (f : Plane → Plane × ℝ)
    (hf : ContDiff ℝ ∞ f) : volume (Set.range f) = 0 := by
  let g : Plane × ℝ → Plane × ℝ := fun x => f x.1
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_fst
  have hdet (x : Plane × ℝ) : LinearMap.det (fderiv ℝ g x).toLinearMap = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    intro hinj
    have hd : fderiv ℝ g x = (fderiv ℝ f x.1).comp (ContinuousLinearMap.fst ℝ Plane ℝ) := by
      change fderiv ℝ (f ∘ (Prod.fst : Plane × ℝ → Plane)) x = _
      rw [fderiv_comp x (hf.differentiable (by simp) x.1) differentiableAt_fst, fderiv_fst]
    have hzero : fderiv ℝ g x (0,1) = fderiv ℝ g x 0 := by
      rw [hd]
      simp
    have he := congrArg Prod.snd (hinj hzero)
    exact one_ne_zero he
  have hnull : volume (g '' (univ : Set (Plane × ℝ))) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ g x)
    · intro x _
      exact (hg.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
    · intro x _
      exact hdet x
  have he : g '' (univ : Set (Plane × ℝ)) = Set.range f := by
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      exact ⟨x.1,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨(x,0),mem_univ _,rfl⟩
  rwa [he] at hnull

end ClosedSurfaceR4.PublishedInputs

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_EuclideanSurfaceImageNull
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_one _root_.OAI.ClosedSurfaceR4.PublishedInputs.radiusPairProjection_apply_zero _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth two-dimensional images in three-space are null, in the
actual coordinate models used by the surface perturbations. -/
noncomputable section
open Set MeasureTheory Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
local instance instIsAddHaarMeasureProdPlaneRealVolume : (volume : Measure (Plane × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem euclidean_surface_image_null (f : Base → ProjectionTarget 3) (hf : ContDiff ℝ ∞ f) :
    volume (range f) = 0 := by
  let L : Plane ≃L[ℝ] Base := ContinuousLinearEquiv.ofFinrankEq (by simp [Base])
  let T : ProjectionTarget 3 ≃L[ℝ] Plane × ℝ := ContinuousLinearEquiv.ofFinrankEq (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hnull := PublishedInputs.smooth_surface_image_volume_zero (T ∘ f ∘ L)
    (T.contDiff.comp (hf.comp L.contDiff))
  have hnull' := linear_equiv_null_image T.symm volume volume hnull
  have he : T.symm '' range (T ∘ f ∘ L) = range f := by
    ext y
    constructor
    · rintro ⟨z,⟨x,rfl⟩,rfl⟩
      exact ⟨L x,by simp⟩
    · rintro ⟨x,rfl⟩
      exact ⟨T (f x),⟨L.symm x,by simp⟩,by simp⟩
  rwa [he] at hnull'

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveTransverseVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth curve in three-space admits one constant vector transverse
to every nonzero velocity.  This uses the proved two-dimensional image estimate. -/
noncomputable section
open Set Filter MeasureTheory Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem exists_curve_transverse_vector (v : ℝ → (Fin 3 → ℝ))
    (hv : ContDiff ℝ ∞ v) :
    ∃ a : Fin 3 → ℝ, ∀ t r : ℝ, r • v t ≠ a := by
  let E := EuclideanSpace.equiv (Fin 3) ℝ
  let f : Base → ProjectionTarget 3 := fun x => E.symm (x 0 • v (x 1))
  have hf : ContDiff ℝ ∞ f :=
    E.symm.contDiff.comp ((contDiff_apply ℝ ℝ 0).smul (hv.comp (contDiff_apply ℝ ℝ 1)))
  have hn : volume (range f) = 0 := euclidean_surface_image_null f hf
  have hae : ∀ᵐ x ∂volume, x ∉ range f := by
    simp only [ae_iff,not_not]
    exact hn
  obtain ⟨a,_,ha⟩ := (Measure.dense_of_ae hae).inter_open_nonempty
    univ isOpen_univ Set.univ_nonempty
  refine ⟨E a,?_⟩
  intro t r heq
  apply ha
  refine ⟨![r,t],?_⟩
  change E.symm (r • v t) = a
  rw [heq,E.symm_apply_apply]

lemma curve_transverse_vector_independent {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : LinearIndependent ℝ ![v,a] :=
  (LinearIndependent.pair_iff' hv).mpr ha

lemma curve_transverse_cross_ne_zero {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : v ⨯₃ a ≠ 0 :=
  crossProduct_ne_zero_iff_linearIndependent.mpr (curve_transverse_vector_independent hv ha)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveNormalFrame
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit invertible three-dimensional frame along a regular curve. -/
noncomputable section
open Set Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma curveNormalLinear_apply (v a : Fin 3 → ℝ) (z : Base × ℝ) :
    curveNormalLinear v a z = z.2 • v+z.1 0 • a+z.1 1 • (v ⨯₃ a) := rfl

lemma curveNormalLinear_bijective {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) :
    Function.Bijective (curveNormalLinear v a) := by
  have hli := curve_transverse_vector_independent hv ha
  have hw := curve_transverse_cross_ne_zero hv ha
  have hwv : (v ⨯₃ a) ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact dot_self_cross v a
  have hwa : (v ⨯₃ a) ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact dot_cross_self v a
  have hww : (v ⨯₃ a) ⬝ᵥ (v ⨯₃ a) ≠ 0 := (dotProduct_self_eq_zero).not.mpr hw
  have hz : ∀ z : Base × ℝ, curveNormalLinear v a z = 0 → z = 0 := by
    intro z h
    have hd := congrArg (fun w => (v ⨯₃ a) ⬝ᵥ w) h
    rw [curveNormalLinear_apply] at hd
    simp only [dotProduct_add,dotProduct_smul,hwv,hwa,smul_eq_mul,mul_zero,zero_add,dotProduct_zero] at hd
    have hz1 : z.1 1 = 0 := (mul_eq_zero.mp hd).resolve_right hww
    have hsum : z.2 • v+z.1 0 • a = 0 := by
      simpa only [curveNormalLinear_apply,hz1,zero_smul,add_zero] using h
    obtain ⟨hz2,hz0⟩ := (LinearIndependent.pair_iff.mp hli) z.2 (z.1 0) hsum
    apply Prod.ext
    · ext i
      fin_cases i
      · exact hz0
      · exact hz1
    · exact hz2
  have hi : Function.Injective (curveNormalLinear v a) := by
    intro z w h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,h,sub_self]
  refine ⟨hi,?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (curveNormalLinear v a).toLinearMap) _).mp hi
  simp [Base]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_QuadraticCrosscapFactorization
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_StandardCrosscapDerivative
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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
lemma standardCrosscap_hasFDerivAt (x : Base) :
    HasFDerivAt standardCrosscap (standardCrosscapDerivative x) x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) x
  have h := (((h0.mul h1).smul_const ((![1,0],0) : Base × ℝ)).add
    ((h1.pow 2).smul_const ((![0,1],0) : Base × ℝ))).add
      (h0.smul_const ((0,1) : Base × ℝ))
  have he : (fun y : Base => (y 0*y 1) • ((![1,0],0) : Base × ℝ) +
      (y 1)^2 • ((![0,1],0) : Base × ℝ) + y 0 • ((0,1) : Base × ℝ)) =
      standardCrosscap := by
    funext y
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]
  change HasFDerivAt (fun y : Base => (y 0*y 1) • ((![1,0],0) : Base × ℝ) +
    (y 1)^2 • ((![0,1],0) : Base × ℝ) + y 0 • ((0,1) : Base × ℝ)) _ x at h
  rw [he] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [standardCrosscapDerivative]
    ring
  · simp [standardCrosscapDerivative]

lemma standardCrosscap_immersion_iff (x : Base) :
    Function.Injective (fderiv ℝ standardCrosscap x) ↔ x ≠ 0 := by
  rw [(standardCrosscap_hasFDerivAt x).fderiv]
  constructor
  · intro h hx
    have he : standardCrosscapDerivative x (![0,1] : Base) = standardCrosscapDerivative x 0 := by
      subst x
      apply Prod.ext
      · ext i
        fin_cases i <;> simp [standardCrosscapDerivative]
      · rfl
    have hh := congrFun (h he) 1
    norm_num at hh
  · intro hx u v he
    have h0 : u 0 = v 0 := congrArg Prod.snd he
    have h1 : x 1 * u 0 + x 0 * u 1 = x 1 * v 0 + x 0 * v 1 := congrFun (congrArg Prod.fst he) 0
    have h2 : (2*x 1)*u 1 = (2*x 1)*v 1 := congrFun (congrArg Prod.fst he) 1
    have huv : u 1 = v 1 := by
      by_cases hx0 : x 0 = 0
      · have hx1 : x 1 ≠ 0 := by
          intro hz
          apply hx
          ext i
          fin_cases i
          · exact hx0
          · exact hz
        exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hx1) h2
      · rw [h0] at h1
        exact mul_left_cancel₀ hx0 (add_left_cancel h1)
    ext i
    fin_cases i
    · exact h0
    · exact huv

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedJetCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second jets of radial normalization, for the finite-point flattening
of the starting spherical immersion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma secondDerivative_apply {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {f : E → H} {p : E}
    (hf : ContDiffAt ℝ ∞ f p) (v w : E) :
    fderiv ℝ (fun q => fderiv ℝ f q w) p v = fderiv ℝ (fderiv ℝ f) p v w := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (differentiableAt_const w)]
  simp

lemma secondDerivative_comp {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → H} {g : H → Z} {U : Set H} (hf : ContDiff ℝ ∞ f)
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {p : E} (hp : f p ∈ U) (v w : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) p v w =
      fderiv ℝ (fderiv ℝ g) (f p) (fderiv ℝ f p v) (fderiv ℝ f p w) +
      fderiv ℝ g (f p) (fderiv ℝ (fderiv ℝ f) p v w) := by
  have hgp := hg.contDiffAt (hU.mem_nhds hp)
  have hDg := hgp.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD1 := (hDg.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp p
    (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  have hD2 := (((hf.fderiv_right (m := ∞) (by simp)).clm_apply
    (show ContDiff ℝ ∞ (fun _ : E => w) from contDiff_const)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  have hd := hD1.clm_apply hD2
  have he : (fun q => fderiv ℝ g (f q) (fderiv ℝ f q w)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ (g ∘ f) q w) := by
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hp)] with q hq
    rw [fderiv_comp q ((hg.contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) q)]
    rfl
  have hev := congrArg (fun L : E →L[ℝ] Z => L v) (he.fderiv_eq.symm.trans hd.fderiv)
  rw [secondDerivative_apply (hgp.comp p hf.contDiffAt)] at hev
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    Function.comp_apply] at hev
  rw [secondDerivative_apply hf.contDiffAt] at hev
  simpa only [add_comm] using hev

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapAxisCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The kernel axis of an actual crosscap chart gives a smooth regular
source curve through the singular point, even though its image velocity vanishes. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscapAxis_apply (t : ℝ) : crosscapAxis t = ![0,t] := by
  ext i
  fin_cases i <;> rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactAxisRectangle
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact axis segment in an open plane set has a uniform rectangular collar. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma open_interval_collar {a b : ℝ} (hab : a ≤ b) {U : Set ℝ}
    (hU : IsOpen U) (hI : Icc a b ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (a-δ) (b+δ) ⊆ U := by
  obtain ⟨δ,hδ,hsub⟩ := isCompact_Icc.exists_cthickening_subset_open hU hI
  refine ⟨δ,hδ,?_⟩
  intro x hx
  apply hsub
  by_cases hxa : x < a
  · apply mem_cthickening_of_dist_le x a δ (Icc a b) ⟨le_rfl,hab⟩
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxa.le)]
    linarith [hx.1]
  · by_cases hbx : b < x
    · apply mem_cthickening_of_dist_le x b δ (Icc a b) ⟨hab,le_rfl⟩
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hbx.le)]
      linarith [hx.2]
    · exact mem_cthickening_of_dist_le x x δ (Icc a b)
        ⟨le_of_not_gt hxa,le_of_not_gt hbx⟩ (by simpa using hδ.le)

theorem compact_axis_rectangle {a b : ℝ} (hab : a ≤ b) {U : Set Base}
    (hU : IsOpen U) (haxis : ∀ t ∈ Icc a b, (![0,t] : Base) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (a-δ) (b+δ),
      (![x,t] : Base) ∈ U := by
  let T : ℝ × ℝ → Base := fun z => ![z.1,z.2]
  have hT : Continuous T := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have hTU : ({0} : Set ℝ) ×ˢ Icc a b ⊆ T ⁻¹' U := by
    rintro ⟨x,t⟩ ⟨hx,ht⟩
    obtain rfl : x = 0 := hx
    exact haxis t ht
  obtain ⟨V,W,hV,hW,h0V,hIW,hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc (hU.preimage hT) hTU
  obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (by simp))
  obtain ⟨η,hη,hηW⟩ := open_interval_collar hab hW hIW
  let δ := min (r/2) η
  have hδ : 0 < δ := lt_min (half_pos hr) hη
  refine ⟨δ,hδ,?_⟩
  intro x hx t ht
  change (x,t) ∈ T ⁻¹' U
  apply hVW
  constructor
  · apply hrV
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
    have hδr : δ < r := (min_le_left _ _).trans_lt (half_lt_self hr)
    constructor <;> linarith [hx.1,hx.2]
  · apply hηW
    have hδη : δ ≤ η := min_le_right _ _
    constructor <;> linarith [ht.1,ht.2]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceRegularLocus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_SourceMapRepresentative
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original surface map in the constructed full-arc coordinates,
with an actual globally smooth representative near the entire rectangle. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
theorem coordinate_representative_immersion_iff (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    {f : M → V} (hf : ContMDiff planeModel 𝓘(ℝ,V) ∞ f)
    {φ : Base → V} {U : Set Base} (hU : IsOpen U) (hUt : U ⊆ c.target)
    (hEq : EqOn φ (f ∘ c.symm) U) {x : Base} (hx : x ∈ U) :
    Function.Injective (fderiv ℝ φ x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f (c.symm x)) := by
  have hcD : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hbij := hcD.mfderiv_bijective (hUt hx)
  rw [(hEq.eventuallyEq_of_mem (hU.mem_nhds hx)).fderiv_eq,← mfderiv_eq_fderiv,
    mfderiv_comp x (hf.mdifferentiable (by simp) _) (hcD.mdifferentiableAt (hUt hx))]
  change Function.Injective ((mfderiv planeModel 𝓘(ℝ,V) f (c.symm x)) ∘
    (mfderiv 𝓘(ℝ,Base) planeModel c.symm x)) ↔ _
  constructor
  · intro h v w hvw
    obtain ⟨v',rfl⟩ := hbij.2 v
    obtain ⟨w',rfl⟩ := hbij.2 w
    exact congrArg (mfderiv 𝓘(ℝ,Base) planeModel c.symm x) (h hvw)
  · intro h
    exact h.comp hbij.1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapStripFrame
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth invertible target frame on a neighborhood of the actual strip axis. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
lemma CrosscapCoordinateStrip.transverseVector_smooth (S : CrosscapCoordinateStrip A) :
    ContDiff ℝ ∞ S.transverseVector := by
  have hD := S.model_smooth.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (EuclideanSpace.equiv (Fin 3) ℝ).contDiff.comp
    ((hD.comp crosscapAxis.contDiff).clm_apply contDiff_const)

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
lemma CrosscapCoordinateStrip.transverseVector_ne_zero (S : CrosscapCoordinateStrip A)
    {t : ℝ} (ht : t ∈ Icc A.arc.start A.arc.finish) : S.transverseVector t ≠ 0 := by
  intro hz
  apply S.transverse t ht
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  simpa only [CrosscapCoordinateStrip.transverseVector,map_zero,crosscapAxis_apply] using hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveFrameInverse
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth inverse frames and the exact normal-coordinate immersion criterion. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma curveNormalLinear_invertible {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : (curveNormalLinear v a).IsInvertible := by
  have hb := curveNormalLinear_bijective hv ha
  exact ⟨ContinuousLinearEquiv.ofBijective (curveNormalLinear v a)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

lemma curveNormalLinear_inverse_velocity {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) :
    (curveNormalLinear v a).inverse v = ((0 : Base),1) := by
  apply ((curveNormalLinear_invertible hv ha).inverse_apply_eq).mpr
  simp [curveNormalLinear_apply]

lemma normal_coordinates_injective_iff (L : Base →L[ℝ] (Base × ℝ))
    (hL : L (![1,0] : Base) = ((0:Base),1)) :
    Function.Injective L ↔ (L (![0,1] : Base)).1 ≠ 0 := by
  have hsplit : ∀ x : Base, L x = (x 0) • L (![1,0] : Base) + (x 1) • L (![0,1] : Base) := by
    intro x
    have hx : x = (x 0) • (![1,0] : Base) + (x 1) • (![0,1] : Base) := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hx]
    rw [map_add,map_smul,map_smul]
  constructor
  · intro h hz
    have hEq : L (![0,1] : Base) = L (((L (![0,1] : Base)).2) • (![1,0] : Base)) := by
      rw [map_smul,hL]
      apply Prod.ext
      · simpa using hz
      · simp
    have h0 := congrFun (h hEq) 1
    norm_num at h0
  · intro hn x y hxy
    have hd : L (x-y) = 0 := by rw [map_sub,hxy,sub_self]
    rw [hsplit,hL] at hd
    have hfst := congrArg Prod.fst hd
    have h1 : (x-y) 1 = 0 := by
      have hm : (x-y) 1 • (L (![0,1] : Base)).1 = 0 := by simpa using hfst
      exact (smul_eq_zero.mp hm).resolve_right hn
    have hsnd := congrArg Prod.snd hd
    have h0 : (x-y) 0 = 0 := by simpa [h1] using hsnd
    apply sub_eq_zero.mp
    ext i
    fin_cases i
    · exact h0
    · exact h1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NormalDefectCoordinates
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine two-component normal defect for the derivative of a surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma coordinateDifferential_smooth {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (coordinateDifferential φ) :=
  contDiff_const.clm_comp (hφ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

lemma transverseDerivative_smooth {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (transverseDerivative φ) :=
  (coordinateDifferential_smooth hφ).clm_apply contDiff_const

lemma normalDefect_smooth {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    {a : Fin 3 → ℝ} {U : Set Base}
    (hu : ∀ x ∈ U, transverseDerivative φ x ≠ 0)
    (ha : ∀ x ∈ U, ∀ r : ℝ, r • transverseDerivative φ x ≠ a) :
    ContDiffOn ℝ ∞ (normalDefect φ a) U := by
  have hu' := transverseDerivative_smooth hφ
  have hcross : ContDiff ℝ ∞ (fun x => transverseDerivative φ x ⨯₃ a) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  have hframe : ContDiff ℝ ∞ (fun x => curveNormalLinear (transverseDerivative φ x) a) :=
    ((contDiff_const.smulRight hu').add contDiff_const).add (contDiff_const.smulRight hcross)
  intro x hx
  have hI := (curveNormalLinear_invertible (hu x hx) (ha x hx)).contDiffAt_map_inverse.comp x hframe.contDiffAt
  exact (hI.clm_apply ((coordinateDifferential_smooth hφ).clm_apply contDiff_const).contDiffAt).fst.contDiffWithinAt

lemma normalDefect_immersion_iff (φ : Base → ProjectionTarget 3) (a : Fin 3 → ℝ) (x : Base)
    (hu : transverseDerivative φ x ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ x ≠ a) :
    Function.Injective (fderiv ℝ φ x) ↔ normalDefect φ a x ≠ 0 := by
  let L := (curveNormalLinear (transverseDerivative φ x) a).inverse.comp (coordinateDifferential φ x)
  have hframe := curveNormalLinear_invertible hu ha
  have hI : Function.Injective (curveNormalLinear (transverseDerivative φ x) a).inverse := by
    intro v w hvw
    have hh := congrArg (curveNormalLinear (transverseDerivative φ x) a) hvw
    simpa only [hframe.self_apply_inverse] using hh
  have hL : L (![1,0] : Base) = ((0:Base),1) := curveNormalLinear_inverse_velocity hu ha
  have hequiv : Function.Injective (fderiv ℝ φ x) ↔ Function.Injective L := by
    constructor
    · intro h v w hEq
      apply h
      apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
      apply hI
      exact hEq
    · intro h v w hEq
      apply h
      change (curveNormalLinear (transverseDerivative φ x) a).inverse
        (EuclideanSpace.equiv (Fin 3) ℝ (fderiv ℝ φ x v)) = _
      rw [hEq]
      rfl
  exact hequiv.trans (normal_coordinates_injective_iff L hL)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothZeroFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact smooth division by a real coordinate vanishing at one point. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma smoothZeroFactor_smooth {f : ℝ → V} (hf : ContDiff ℝ ∞ f) (p : ℝ) :
    ContDiff ℝ ∞ (smoothZeroFactor f p) := by
  have hD : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  have hF : ContDiff ℝ ∞ (fun z : ℝ × ℝ => deriv f (p+z.2*(z.1-p))) :=
    hD.comp (contDiff_const.add (contDiff_snd.mul (contDiff_fst.sub contDiff_const)))
  exact SmoothParameterIntegral.contDiff_integral hF 0 1

lemma smoothZeroFactor_identity {f : ℝ → V} (hf : ContDiff ℝ ∞ f) (p t : ℝ) :
    (t-p) • smoothZeroFactor f p t = f t-f p := by
  have hD : Continuous (deriv f) := (hf.deriv' (n := ∞)).continuous
  have hcont : Continuous (fun s : ℝ => (t-p) • deriv f (p+s*(t-p))) := by fun_prop
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => f (p+s*(t-p)))
      ((t-p) • deriv f (p+s*(t-p))) s := by
    simpa [Function.comp_def] using ((hf.differentiable (by simp) _).hasDerivAt).scomp s
      (((hasDerivAt_id s).mul_const (t-p)).const_add p)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hcont.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_smul] at hi
  simpa only [smoothZeroFactor,zero_mul,add_zero,one_mul,add_sub_cancel] using hi

lemma smoothZeroFactor_self (f : ℝ → V) (p : ℝ) :
    smoothZeroFactor f p p = deriv f p := by
  simp [smoothZeroFactor]

/-- Division by two distinct simple-zero coordinates is globally smooth. -/
theorem two_zero_smooth_factor {f : ℝ → V} (hf : ContDiff ℝ ∞ f)
    {p q : ℝ} (hpq : p ≠ q) (hp : f p = 0) (hq : f q = 0) :
    ∃ d : ℝ → V, ContDiff ℝ ∞ d ∧
      (∀ t, f t = ((t-p)*(t-q)) • d t) ∧
      deriv f p = (p-q) • d p ∧ deriv f q = (q-p) • d q := by
  let h := smoothZeroFactor f p
  have hh : ContDiff ℝ ∞ h := smoothZeroFactor_smooth hf p
  have he (t : ℝ) : f t = (t-p) • h t := by
    simpa only [hp,sub_zero] using (smoothZeroFactor_identity hf p t).symm
  have hhq : h q = 0 := by
    have hz := he q
    rw [hq] at hz
    exact (smul_eq_zero.mp hz.symm).resolve_left (sub_ne_zero.mpr hpq.symm)
  let d := smoothZeroFactor h q
  have hd : ContDiff ℝ ∞ d := smoothZeroFactor_smooth hh q
  have hed (t : ℝ) : h t = (t-q) • d t := by
    simpa only [hhq,sub_zero] using (smoothZeroFactor_identity hh q t).symm
  have hef (t : ℝ) : f t = ((t-p)*(t-q)) • d t := by
    rw [he t,hed t,smul_smul]
  have hep : deriv f p = (p-q) • d p := by
    rw [←hed p]
    exact (smoothZeroFactor_self f p).symm
  have heq : deriv f q = (q-p) • d q := by
    have hder := (((hasDerivAt_id q).sub_const p).smul
      (hh.differentiable (by simp) q).hasDerivAt)
    have hefun : f = fun t => (t-p) • h t := funext he
    change HasDerivAt (fun t => (t-p) • h t)
      ((q-p) • deriv h q+1 • h q) q at hder
    rw [←hefun] at hder
    rw [hder.deriv,hhq,smul_zero,add_zero]
    exact congrArg ((q-p) • ·) (smoothZeroFactor_self h q).symm
  exact ⟨d,hd,hef,hep,heq⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PlaneComplexFrame
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real coordinate frame from a nonzero vector in the normal plane. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma planeComplexFrame_apply (w v : Base) :
    planeComplexFrame w v = ![w 0*v 0-w 1*v 1,w 1*v 0+w 0*v 1] := by
  ext i
  fin_cases i <;> simp [planeComplexFrame] <;> ring

lemma planeComplexFrame_smooth : ContDiff ℝ ∞ planeComplexFrame := by
  have hJ : ContDiff ℝ ∞ (fun w : Base => (![-w 1,w 0] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ 1).neg
    · exact contDiff_apply ℝ ℝ 0
  exact (contDiff_const.smulRight contDiff_id).add (contDiff_const.smulRight hJ)

lemma planeComplexFrame_injective {w : Base} (hw : w ≠ 0) :
    Function.Injective (planeComplexFrame w) := by
  have hs : (w 0)^2+(w 1)^2 ≠ 0 := by
    intro hz
    have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0),sq_nonneg (w 1)]
    have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0),sq_nonneg (w 1)]
    apply hw
    ext i
    fin_cases i
    · exact h0
    · exact h1
  intro u v he
  have h0 : w 0*u 0-w 1*u 1 = w 0*v 0-w 1*v 1 := by
    simpa only [planeComplexFrame_apply,Matrix.cons_val_zero] using congrFun he 0
  have h1 : w 1*u 0+w 0*u 1 = w 1*v 0+w 0*v 1 := by
    simpa only [planeComplexFrame_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using congrFun he 1
  have hd0 : ((w 0)^2+(w 1)^2)*(u 0-v 0) = 0 := by
    linear_combination w 0*h0+w 1*h1
  have hd1 : ((w 0)^2+(w 1)^2)*(u 1-v 1) = 0 := by
    linear_combination w 0*h1-w 1*h0
  ext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hd0).resolve_left hs)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hd1).resolve_left hs)

lemma planeComplexFrame_bijective {w : Base} (hw : w ≠ 0) :
    Function.Bijective (planeComplexFrame w) := by
  have hi := planeComplexFrame_injective hw
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (planeComplexFrame w).toLinearMap) rfl).mp hi⟩

lemma planeComplexFrame_axis (w : Base) (r : ℝ) :
    planeComplexFrame w ![r,0] = r • w := by
  ext i
  fin_cases i <;> simp [planeComplexFrame_apply,mul_comm]

lemma planeComplexFrame_invertible {w : Base} (hw : w ≠ 0) :
    (planeComplexFrame w).IsInvertible := by
  have hb := planeComplexFrame_bijective hw
  exact ⟨ContinuousLinearEquiv.ofBijective (planeComplexFrame w)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

lemma planeComplexFrame_inverse_axis {w : Base} (hw : w ≠ 0) (r : ℝ) :
    (planeComplexFrame w).inverse (r • w) = ![r,0] := by
  apply ((planeComplexFrame_invertible hw).inverse_apply_eq).mpr
  exact (planeComplexFrame_axis w r).symm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TwoZeroAxisFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing two simple zero factors from a vector-valued axis curve. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem nonzero_two_zero_factor {f : ℝ → V} (hf : ContDiff ℝ ∞ f)
    {p q : ℝ} (hpq : p ≠ q) (hp : f p = 0) (hq : f q = 0)
    (hdp : deriv f p ≠ 0) (hdq : deriv f q ≠ 0)
    {K : Set ℝ} (hz : ∀ t ∈ K, f t = 0 → t = p ∨ t = q) :
    ∃ d : ℝ → V, ContDiff ℝ ∞ d ∧ (∀ t, f t = ((t-p)*(t-q)) • d t) ∧
      (∀ t ∈ K, d t ≠ 0) ∧
      deriv f p = (p-q) • d p ∧ deriv f q = (q-p) • d q := by
  obtain ⟨d,hd,he,hep,heq⟩ := two_zero_smooth_factor hf hpq hp hq
  refine ⟨d,hd,he,?_,hep,heq⟩
  intro t ht hdt
  have hft : f t = 0 := by rw [he t,hdt,smul_zero]
  rcases hz t ht hft with rfl | rfl
  · exact hdp (by rw [hep,hdt,smul_zero])
  · exact hdq (by rw [heq,hdt,smul_zero])

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalDefectDomain
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal-defect coordinates exist on a genuine open neighborhood
of the entire compact crosscap strip axis. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma normalFrameDomain_open {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    (a : Fin 3 → ℝ) : IsOpen (normalFrameDomain φ a) := by
  have hu : Continuous (transverseDerivative φ) := (transverseDerivative_smooth hφ).continuous
  have hcross : Continuous (fun x => transverseDerivative φ x ⨯₃ a) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  exact isOpen_ne.preimage hcross

lemma normalFrameDomain_nonzero {φ : Base → ProjectionTarget 3} {a : Fin 3 → ℝ}
    {x : Base} (hx : x ∈ normalFrameDomain φ a) : transverseDerivative φ x ≠ 0 := by
  intro hz
  apply hx
  rw [hz]
  simp

lemma normalFrameDomain_transverse {φ : Base → ProjectionTarget 3} {a : Fin 3 → ℝ}
    {x : Base} (hx : x ∈ normalFrameDomain φ a) :
    ∀ r : ℝ, r • transverseDerivative φ x ≠ a := by
  exact (LinearIndependent.pair_iff' (normalFrameDomain_nonzero hx)).mp
    (crossProduct_ne_zero_iff_linearIndependent.mp hx)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

omit [IsManifold planeModel ∞ M] [T2Space M] [SigmaCompactSpace M] in
lemma CrosscapCoordinateStrip.transverseDerivative_axis (S : CrosscapCoordinateStrip A) (t : ℝ) :
    transverseDerivative S.model (![0,t] : Base) = S.transverseVector t := by
  simp only [transverseDerivative,coordinateDifferential,
    CrosscapCoordinateStrip.transverseVector,crosscapAxis_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalFrameJet
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A regular three-dimensional direction jet induces a regular
normal-defect jet in the transverse two-plane. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma directionBlock_apply (K : Base →L[ℝ] (Fin 3 → ℝ)) (u : Fin 3 → ℝ) (z : Base × ℝ) :
    directionBlock K u z = K z.1 + z.2 • u := rfl

lemma normal_frame_jet_bijective {u a : Fin 3 → ℝ} (hu : u ≠ 0)
    (ha : ∀ r : ℝ, r • u ≠ a) (K : Base →L[ℝ] (Fin 3 → ℝ))
    (hK : Function.Bijective (directionBlock K u)) :
    Function.Bijective ((ContinuousLinearMap.fst ℝ Base ℝ).comp
      ((curveNormalLinear u a).inverse.comp K)) := by
  let F := curveNormalLinear u a
  let J := F.inverse
  let P := (ContinuousLinearMap.fst ℝ Base ℝ).comp (J.comp K)
  have hI : F.IsInvertible := curveNormalLinear_invertible hu ha
  have hJu : J u = ((0:Base),1) := curveNormalLinear_inverse_velocity hu ha
  have hJinj : Function.Injective J := by
    intro v w he
    have hh := congrArg F he
    change F (F.inverse v) = F (F.inverse w) at hh
    simpa only [hI.self_apply_inverse] using hh
  have hnormal : ∀ z : Base × ℝ, (J (directionBlock K u z)).1 = P z.1 := by
    intro z
    rw [directionBlock_apply,map_add,map_smul,hJu]
    simp [P]
  change Function.Bijective P
  constructor
  · intro v w he
    have hz : P (v-w) = 0 := by rw [map_sub,he,sub_self]
    let z : Base × ℝ := (v-w,-(J (K (v-w))).2)
    have hzero : directionBlock K u z = 0 := by
      apply hJinj
      rw [map_zero,directionBlock_apply,map_add,map_smul,hJu]
      apply Prod.ext
      · simpa [P,z] using hz
      · simp [z]
    have hzz := hK.1 (hzero.trans (map_zero _).symm)
    have hdiff : v-w = 0 := congrArg Prod.fst hzz
    exact sub_eq_zero.mp hdiff
  · intro v
    obtain ⟨z,hz⟩ := hK.2 (F (v,0))
    refine ⟨z.1,?_⟩
    rw [← hnormal,hz,hI.inverse_apply_self]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalDefectJet
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the genuine normal defect at a singular point.
The derivative of the moving frame cancels because the vertical column is zero. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma normalDefect_fderiv_at_zero {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : Fin 3 → ℝ) (p : Base)
    (hu : transverseDerivative φ p ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ p ≠ a)
    (hz : fderiv ℝ φ p (![0,1] : Base) = 0) :
    fderiv ℝ (normalDefect φ a) p = (ContinuousLinearMap.fst ℝ Base ℝ).comp
      ((curveNormalLinear (transverseDerivative φ p) a).inverse.comp
        (fderiv ℝ (fun x => coordinateDifferential φ x (![0,1] : Base)) p)) := by
  let J := fun x => (curveNormalLinear (transverseDerivative φ x) a).inverse
  let W := fun x => coordinateDifferential φ x (![0,1] : Base)
  have hU := transverseDerivative_smooth hφ
  have hcross : ContDiff ℝ ∞ (fun x => transverseDerivative φ x ⨯₃ a) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  have hframe : ContDiff ℝ ∞ (fun x => curveNormalLinear (transverseDerivative φ x) a) :=
    ((contDiff_const.smulRight hU).add contDiff_const).add (contDiff_const.smulRight hcross)
  have hJ : ContDiffAt ℝ ∞ J p := by
    change ContDiffAt ℝ ∞ (ContinuousLinearMap.inverse ∘
      (fun x => curveNormalLinear (transverseDerivative φ x) a)) p
    exact (curveNormalLinear_invertible hu ha).contDiffAt_map_inverse.comp p hframe.contDiffAt
  have hW : ContDiff ℝ ∞ W := (coordinateDifferential_smooth hφ).clm_apply contDiff_const
  have hWp : W p = 0 := by simp [W,coordinateDifferential,hz]
  have hd := (hJ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.clm_apply
    (hW.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  have he := hd.fst.fderiv
  have hfun : (fun x => (J x (W x)).1) = normalDefect φ a := rfl
  rw [hfun] at he
  apply ContinuousLinearMap.ext
  intro v
  have hev := congrArg (fun L => L v) he
  simpa [J,W,hWp,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply] using hev

lemma normalDefect_jet_bijective {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : Fin 3 → ℝ) (p : Base)
    (hu : transverseDerivative φ p ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ p ≠ a)
    (hz : fderiv ℝ φ p (![0,1] : Base) = 0)
    (hK : Function.Bijective (directionBlock
      (fderiv ℝ (fun x => coordinateDifferential φ x (![0,1] : Base)) p)
      (transverseDerivative φ p))) :
    Function.Bijective (fderiv ℝ (normalDefect φ a) p) := by
  rw [normalDefect_fderiv_at_zero hφ a p hu ha hz]
  exact normal_frame_jet_bijective hu ha _ hK

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceDirectionBlock
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original derivative-direction transversality is exactly the
three-column block entering the normal-defect jet. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceDirection_true_block {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (p : Base) :
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.comp
      (fderiv ℝ (surfaceDirection φ true) (p,0)) =
    directionBlock (fderiv ℝ (fun x => coordinateDifferential φ x (![0,1] : Base)) p)
      (transverseDerivative φ p) := by
  let E := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
  let W := fun x => coordinateDifferential φ x (![0,1] : Base)
  let U := transverseDerivative φ
  have hW : ContDiff ℝ ∞ W := (coordinateDifferential_smooth hφ).clm_apply contDiff_const
  have hU : ContDiff ℝ ∞ U := transverseDerivative_smooth hφ
  have hWD := (hW.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.comp (p,(0:ℝ)) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p,(0:ℝ))))
  have hUD := (hU.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt.comp (p,(0:ℝ)) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p,(0:ℝ))))
  have hd := hWD.add ((hasFDerivAt_snd (𝕜 := ℝ) (p := (p,(0:ℝ)))).smul hUD)
  have hEq : E ∘ surfaceDirection φ true =
      fun z : Base × ℝ => W z.1 + z.2 • U z.1 := by
    funext z
    have hray : tangentRay true z.2 = (z.2) • (![1,0] : Base) + (![0,1] : Base) := by
      ext i
      fin_cases i <;> simp [tangentRay]
    simp only [Function.comp_apply,surfaceDirection,hray,map_add,map_smul]
    dsimp [W,U,transverseDerivative,coordinateDifferential,E]
    abel
  have hleft := E.hasFDerivAt.comp (p,(0:ℝ)) ((surfaceDirection_smooth hφ true).differentiable (by simp) _).hasFDerivAt
  change HasFDerivAt (fun z : Base × ℝ => W z.1 + z.2 • U z.1) _ (p,0) at hd
  have hfd := hleft.fderiv
  rw [hEq,hd.fderiv] at hfd
  rw [← hfd]
  apply ContinuousLinearMap.ext
  intro z
  simp [directionBlock_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,W,U]

lemma normalDefect_nondegenerate_of_direction {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (a : Fin 3 → ℝ) (p : Base)
    (hu : transverseDerivative φ p ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ p ≠ a)
    (hz : fderiv ℝ φ p (![0,1] : Base) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ true) (p,0))) :
    Function.Bijective (fderiv ℝ (normalDefect φ a) p) := by
  apply normalDefect_jet_bijective hφ a p hu ha hz
  rw [← surfaceDirection_true_block hφ p]
  exact (EuclideanSpace.equiv (Fin 3) ℝ).bijective.comp hreg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapSecondDerivative
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact second derivative of the standard crosscap and the chain
rule in a kernel direction. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma standardCrosscapDerivative_zero_apply (v : Base) :
    standardCrosscapDerivative 0 v = ((0:Base),v 0) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [standardCrosscapDerivative]
  · simp [standardCrosscapDerivative]

lemma standardCrosscap_second (p v w : Base) :
    fderiv ℝ (fderiv ℝ standardCrosscap) p v w =
      (![v 1*w 0+v 0*w 1,2*v 1*w 1],(0:ℝ)) := by
  have he : (fun x => fderiv ℝ standardCrosscap x w) =
      fun x : Base => (x 1*w 0+x 0*w 1) • ((![1,0],0) : Base × ℝ) +
        (2*x 1*w 1) • ((![0,1],0) : Base × ℝ) + ((0,w 0) : Base × ℝ) := by
    funext x
    rw [(standardCrosscap_hasFDerivAt x).fderiv]
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [standardCrosscapDerivative]
    · simp [standardCrosscapDerivative]
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0:Fin 2) p
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1:Fin 2) p
  have hd := ((((h1.mul_const (w 0)).add (h0.mul_const (w 1))).smul_const
    ((![1,0],0) : Base × ℝ)).add
      (((h1.const_mul 2).mul_const (w 1)).smul_const ((![0,1],0) : Base × ℝ))).add_const
        ((0,w 0) : Base × ℝ)
  change HasFDerivAt (fun x : Base => (x 1*w 0+x 0*w 1) • ((![1,0],0) : Base × ℝ) +
    (2*x 1*w 1) • ((![0,1],0) : Base × ℝ) + ((0,w 0) : Base × ℝ)) _ p at hd
  rw [← SphericalJets.secondDerivative_apply standardCrosscap_smooth.contDiffAt v w,he,hd.fderiv]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp <;> ring
  · simp

lemma kernel_secondDerivative_comp {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : E → H} {g : H → Z} (hf : ContDiff ℝ ∞ f) {U : Set H}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) {p : E} (hp : f p ∈ U)
    (v w : E) (hw : fderiv ℝ f p w = 0) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) p v w =
      fderiv ℝ g (f p) (fderiv ℝ (fderiv ℝ f) p v w) := by
  rw [SphericalJets.secondDerivative_comp hf hU hg hp v w,hw,map_zero,zero_add]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AxisDirectionJet
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The derivative-direction jet with the longitudinal vector in the kernel. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma axisDirectionJet_apply (f : Base → V) (p : Base) (z : Base × ℝ) :
    axisDirectionJet f p z = z.2 • fderiv ℝ f p (![1,0] : Base) +
      fderiv ℝ (fderiv ℝ f) p z.1 (![0,1] : Base) := by
  change fderiv ℝ f p (z.2 • (![1,0] : Base)) +
    fderiv ℝ (fderiv ℝ f) p z.1 (![0,1] : Base) = _
  rw [map_smul]

lemma axisDirectionJet_surfaceDirection {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base) :
    fderiv ℝ (surfaceDirection f true) (p,0) = axisDirectionJet f p := by
  rw [(surfaceDirection_hasFDerivAt hf true (p,0)).fderiv]
  apply ContinuousLinearMap.ext
  intro z
  simp [surfaceDirectionLinearization,axisDirectionJet,tangentRay,tangentRayVelocity]

lemma axisDirectionJet_postcompose {f : Base → V} {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {g : V → W} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : Base) (hz : fderiv ℝ f p (![0,1] : Base) = 0) :
    axisDirectionJet (g ∘ f) p = (fderiv ℝ g (f p)).comp (axisDirectionJet f p) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [axisDirectionJet_apply,ContinuousLinearMap.comp_apply,axisDirectionJet_apply,
    kernel_secondDerivative_comp hf isOpen_univ hg.contDiffOn (mem_univ _) _ _ hz,
    fderiv_comp p (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)]
  simp

lemma bijective_base_vertical_columns (L : Base →L[ℝ] Base)
    (hL : Function.Bijective L) (hz : L (![0,1] : Base) 0 = 0) :
    L (![0,1] : Base) 1 ≠ 0 ∧ L (![1,0] : Base) 0 ≠ 0 := by
  have hcol : ∀ x : Base, L x = (x 0) • L (![1,0] : Base) + (x 1) • L (![0,1] : Base) := by
    intro x
    have he : x = (x 0) • (![1,0] : Base) + (x 1) • (![0,1] : Base) := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [he]
    rw [map_add,map_smul,map_smul]
  constructor
  · intro hn
    have he : L (![0,1] : Base) = L 0 := by
      rw [map_zero]
      ext i
      fin_cases i
      · exact hz
      · exact hn
    have hh := congrFun (hL.1 he) 1
    norm_num at hh
  · intro hn
    obtain ⟨x,hx⟩ := hL.2 (![1,0] : Base)
    have h0 := congrFun hx 0
    rw [hcol] at h0
    simp [hn,hz] at h0

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapComposedDirection
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A source coordinate change preserves the regular direction zero of
the standard crosscap when the vertical direction is its kernel. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscap_composed_direction_bijective {g : Base → Base} (hg : ContDiff ℝ ∞ g)
    (p : Base) (hp : g p = 0) (hD : Function.Bijective (fderiv ℝ g p))
    (hy : fderiv ℝ g p (![0,1] : Base) 0 = 0) :
    Function.Bijective (axisDirectionJet (standardCrosscap ∘ g) p) := by
  have hc := bijective_base_vertical_columns (fderiv ℝ g p) hD hy
  have hfirst : ∀ v : Base, fderiv ℝ (standardCrosscap ∘ g) p v =
      standardCrosscapDerivative 0 (fderiv ℝ g p v) := by
    intro v
    rw [fderiv_comp p (standardCrosscap_smooth.differentiable (by simp) _)
      (hg.differentiable (by simp) p),hp,(standardCrosscap_hasFDerivAt 0).fderiv]
    rfl
  have hsecond : ∀ v w : Base,
      fderiv ℝ (fderiv ℝ (standardCrosscap ∘ g)) p v w =
        (![fderiv ℝ g p v 1 * fderiv ℝ g p w 0 + fderiv ℝ g p v 0 * fderiv ℝ g p w 1,
          2 * fderiv ℝ g p v 1 * fderiv ℝ g p w 1],(0:ℝ)) +
          standardCrosscapDerivative 0 (fderiv ℝ (fderiv ℝ g) p v w) := by
    intro v w
    rw [SphericalJets.secondDerivative_comp hg isOpen_univ standardCrosscap_smooth.contDiffOn
      (mem_univ _) v w,hp,standardCrosscap_second,(standardCrosscap_hasFDerivAt 0).fderiv]
  have hker : ∀ z : Base × ℝ, axisDirectionJet (standardCrosscap ∘ g) p z = 0 → z = 0 := by
    intro z hz
    rw [axisDirectionJet_apply,hfirst,hsecond] at hz
    simp only [standardCrosscapDerivative_zero_apply] at hz
    have hz0 := congrFun (congrArg Prod.fst hz) 0
    have hz1 := congrFun (congrArg Prod.fst hz) 1
    have hz2 := congrArg Prod.snd hz
    have hb0 : fderiv ℝ g p z.1 0 = 0 := by
      have hh : fderiv ℝ g p z.1 0 * fderiv ℝ g p (![0,1] : Base) 1 = 0 := by
        simpa [hy] using hz0
      exact (mul_eq_zero.mp hh).resolve_right hc.1
    have hb1 : fderiv ℝ g p z.1 1 = 0 := by
      have hh : 2 * fderiv ℝ g p z.1 1 * fderiv ℝ g p (![0,1] : Base) 1 = 0 := by
        simpa using hz1
      have hmul := (mul_eq_zero.mp hh).resolve_right hc.1
      exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
    have hzfirst : z.1 = 0 := by
      apply hD.1
      rw [map_zero]
      ext i
      fin_cases i
      · exact hb0
      · exact hb1
    have hzlast : z.2 = 0 := by
      have hh : z.2 * fderiv ℝ g p (![1,0] : Base) 0 = 0 := by
        simpa [hzfirst] using hz2
      exact (mul_eq_zero.mp hh).resolve_right hc.2
    exact Prod.ext hzfirst hzlast
  have hi : Function.Injective (axisDirectionJet (standardCrosscap ∘ g) p) := by
    intro z w he
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub,he,sub_self]
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalFormDirectionRegularity
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth source and target coordinates preserve the nondegenerate
derivative-direction zero of an actual standard crosscap. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma axisDirectionJet_congr_germ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : Base → V} {p : Base} (h : f =ᶠ[𝓝 p] g) :
    axisDirectionJet f p = axisDirectionJet g p := by
  simp only [axisDirectionJet,h.fderiv_eq,h.fderiv.fderiv_eq]

lemma normal_form_direction_regularity {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) {g : Base → Base} (hg : ContDiff ℝ ∞ g)
    {H : Base × ℝ → ProjectionTarget 3} (hH : ContDiff ℝ ∞ H) (p : Base)
    (hp : g p = 0) (hgD : Function.Bijective (fderiv ℝ g p))
    (hHD : Function.Bijective (fderiv ℝ H 0))
    (hEq : φ =ᶠ[𝓝 p] H ∘ (standardCrosscap ∘ g))
    (hv : fderiv ℝ φ p (![0,1] : Base) = 0) :
    Function.Bijective (fderiv ℝ (surfaceDirection φ true) (p,0)) := by
  let G := standardCrosscap ∘ g
  have hG : ContDiff ℝ ∞ G := standardCrosscap_smooth.comp hg
  have hstd0 : standardCrosscap (0:Base) = 0 := by
    apply Prod.ext
    · ext i; fin_cases i <;> simp [standardCrosscap]
    · simp [standardCrosscap]
  have hGp : G p = 0 := by change standardCrosscap (g p) = 0; rw [hp,hstd0]
  have hfirst : fderiv ℝ φ p (![0,1] : Base) = fderiv ℝ H 0
      (standardCrosscapDerivative 0 (fderiv ℝ g p (![0,1] : Base))) := by
    rw [hEq.fderiv_eq,fderiv_comp p (hH.differentiable (by simp) _) (hG.differentiable (by simp) p)]
    change fderiv ℝ H (G p) (fderiv ℝ (standardCrosscap ∘ g) p (![0,1] : Base)) = _
    rw [hGp,fderiv_comp p (standardCrosscap_smooth.differentiable (by simp) _) (hg.differentiable (by simp) p),
      hp,(standardCrosscap_hasFDerivAt 0).fderiv]
    rfl
  have hy : fderiv ℝ g p (![0,1] : Base) 0 = 0 := by
    have hh := hHD.1 (hfirst.symm.trans (hv.trans (map_zero _).symm))
    simpa [standardCrosscapDerivative] using congrArg Prod.snd hh
  have hGv : fderiv ℝ G p (![0,1] : Base) = 0 := by
    change fderiv ℝ (standardCrosscap ∘ g) p (![0,1] : Base) = 0
    rw [fderiv_comp p (standardCrosscap_smooth.differentiable (by simp) _) (hg.differentiable (by simp) p),
      hp,(standardCrosscap_hasFDerivAt 0).fderiv]
    apply Prod.ext
    · ext i; fin_cases i <;> simp [standardCrosscapDerivative]
    · simpa [standardCrosscapDerivative] using hy
  rw [axisDirectionJet_surfaceDirection hφ,axisDirectionJet_congr_germ hEq,
    axisDirectionJet_postcompose hG hH p hGv,hGp]
  exact hHD.comp (crosscap_composed_direction_bijective hg p hp hgD hy)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the actual smooth coordinate change from a strip chart to
an endpoint's standard crosscap chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

theorem crosscap_chart_transition (C : SurfaceCrosscapCoordinates f p)
    (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    (hp : p ∈ c.source) {φ : Base → ProjectionTarget 3}
    (hφ : φ =ᶠ[𝓝 (c p)] f ∘ c.symm) :
    ∃ g : Base → Base, ContDiff ℝ ∞ g ∧ g (c p) = 0 ∧
      Function.Bijective (fderiv ℝ g (c p)) ∧
      φ =ᶠ[𝓝 (c p)] C.target ∘ (standardCrosscap ∘ g) := by
  let V := c.target ∩ c.symm ⁻¹' C.source.source
  have hV : IsOpen V := c.symm.isOpen_inter_preimage C.source.open_source
  have hpV : c p ∈ V := by
    refine ⟨c.map_source hp,?_⟩
    change c.symm (c p) ∈ C.source.source
    rw [c.left_inv hp]
    exact C.source_mem
  have hlocal : ContDiffOn ℝ ∞ (C.source ∘ c.symm) V :=
    (C.source_smooth.comp (hci.mono inter_subset_left) (fun _ hx => hx.2)).contDiffOn
  obtain ⟨U,hU,h0U,hUV,g,hg,hEq⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := c p)) hV (singleton_subset_iff.mpr hpV) hlocal
  have hpU : c p ∈ U := h0U (mem_singleton _)
  have hEqg := hEq.eventuallyEq_of_mem (hU.mem_nhds hpU)
  have hg0 : g (c p) = 0 := by
    rw [hEqg.eq_of_nhds]
    change C.source (c.symm (c p)) = 0
    rw [c.left_inv hp,C.source_center]
  have hDc : c.symm.MDifferentiable 𝓘(ℝ,Base) planeModel :=
    ⟨hci.mdifferentiableOn (by simp),hcs.mdifferentiableOn (by simp)⟩
  have hDC : C.source.MDifferentiable planeModel 𝓘(ℝ,Base) :=
    ⟨C.source_smooth.mdifferentiableOn (by simp),C.source_inverse_smooth.mdifferentiableOn (by simp)⟩
  have hgD : Function.Bijective (fderiv ℝ g (c p)) := by
    rw [hEqg.fderiv_eq,← mfderiv_eq_fderiv,mfderiv_comp (c p)
      (hDC.mdifferentiableAt hpV.2) (hDc.mdifferentiableAt hpV.1)]
    exact (hDC.mfderiv_bijective hpV.2).comp (hDc.mfderiv_bijective hpV.1)
  refine ⟨g,hg,hg0,hgD,?_⟩
  filter_upwards [hφ,hEqg,hV.mem_nhds hpV] with x hφx hgx hx
  change φ x = C.target (standardCrosscap (g x))
  calc
    φ x = f (c.symm x) := hφx
    _ = C.target (standardCrosscap (C.source (c.symm x))) := C.model_eq _ hx.2
    _ = C.target (standardCrosscap (g x)) := by rw [hgx]; rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapCoordinateRegularity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nondegenerate direction zeros are retained in the actual full-arc
coordinates, at both singular endpoints. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p : M}

lemma crosscap_coordinate_direction_regularity (C : SurfaceCrosscapCoordinates f p)
    (c : OpenPartialHomeomorph M Base)
    (hcs : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ c.symm c.target)
    (hp : p ∈ c.source) {φ : Base → ProjectionTarget 3}
    (hφ : ContDiff ℝ ∞ φ) (hEq : φ =ᶠ[𝓝 (c p)] f ∘ c.symm)
    (hv : fderiv ℝ φ (c p) (![0,1] : Base) = 0) :
    Function.Bijective (fderiv ℝ (surfaceDirection φ true) (c p,0)) := by
  obtain ⟨g,hg,hgp,hgD,hgEq⟩ := crosscap_chart_transition C c hcs hci hp hEq
  have htD : C.target.MDifferentiable 𝓘(ℝ,Base × ℝ) 𝓘(ℝ,ProjectionTarget 3) :=
    ⟨C.target_smooth.contMDiff.contMDiffOn.mdifferentiableOn (by simp),
      C.target_inverse_smooth.contMDiffOn.mdifferentiableOn (by simp)⟩
  have htbij : Function.Bijective (fderiv ℝ C.target 0) := by
    rw [← mfderiv_eq_fderiv]
    exact htD.mfderiv_bijective C.target_mem
  exact normal_form_direction_regularity hφ hg C.target_smooth (c p) hgp hgD htbij hgEq hv

variable {q : M} {A : CrosscapConnectingArc f p q}

lemma CrosscapCoordinateStrip.endpoint_direction_regular (S : CrosscapCoordinateStrip A) :
    Function.Bijective (fderiv ℝ (surfaceDirection S.model true) (![0,A.arc.start],0)) ∧
      Function.Bijective (fderiv ℝ (surfaceDirection S.model true) (![0,A.arc.finish],0)) := by
  have hpsource : p ∈ S.chart.source :=
    (congrArg (fun y => y ∈ S.chart.source) A.source).mp
      (S.axis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)).1
  have hqsource : q ∈ S.chart.source :=
    (congrArg (fun y => y ∈ S.chart.source) A.target).mp
      (S.axis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)).1
  have hpchart : S.chart p = ![0,A.arc.start] :=
    (congrArg S.chart A.source).symm.trans
      (S.axis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)).2
  have hqchart : S.chart q = ![0,A.arc.finish] :=
    (congrArg S.chart A.target).symm.trans
      (S.axis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)).2
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ S.domain := by
    intro t ht
    apply S.rectangle 0 ⟨by linarith [S.width_pos],by linarith [S.width_pos]⟩ t
    constructor <;> linarith [S.width_pos,ht.1,ht.2]
  have hpdom : S.chart p ∈ S.domain := by rw [hpchart]; exact haxis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)
  have hqdom : S.chart q ∈ S.domain := by rw [hqchart]; exact haxis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)
  have hpV : fderiv ℝ S.model (S.chart p) (![0,1] : Base) = 0 := by rw [hpchart]; exact S.left_vertical
  have hqV : fderiv ℝ S.model (S.chart q) (![0,1] : Base) = 0 := by rw [hqchart]; exact S.right_vertical
  constructor
  · simpa only [hpchart] using crosscap_coordinate_direction_regularity A.left S.chart
      S.chart_smooth S.inverse_smooth hpsource S.model_smooth
        (S.model_eq.eventuallyEq_of_mem (S.domain_open.mem_nhds hpdom)) hpV
  · simpa only [hqchart] using crosscap_coordinate_direction_regularity A.right S.chart
      S.chart_smooth S.inverse_smooth hqsource S.model_smooth
        (S.model_eq.eventuallyEq_of_mem (S.domain_open.mem_nhds hqdom)) hqV

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapRegularLocus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine crosscap chart contains exactly one nonimmersed point. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {f : M → ProjectionTarget 3} {p : M}

lemma SurfaceCrosscapCoordinates.regular_iff (c : SurfaceCrosscapCoordinates f p)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {x : M} (hx : x ∈ c.source.source) :
    Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x) ↔ x ≠ p := by
  have hEq : EqOn (c.target ∘ standardCrosscap) (f ∘ c.source.symm) c.source.target := by
    intro y hy
    have hm := c.model_eq (c.source.symm y) (c.source.map_target hy)
    rw [c.source.right_inv hy] at hm
    exact hm.symm
  have hbridge := coordinate_representative_immersion_iff c.source c.source_smooth
    c.source_inverse_smooth hf c.source.open_target (subset_refl _) hEq (c.source.map_source hx)
  rw [c.source.left_inv hx] at hbridge
  rw [← hbridge]
  have htD : c.target.MDifferentiable 𝓘(ℝ,Base × ℝ) 𝓘(ℝ,ProjectionTarget 3) :=
    ⟨c.target_smooth.contMDiff.contMDiffOn.mdifferentiableOn (by simp),
      c.target_inverse_smooth.contMDiffOn.mdifferentiableOn (by simp)⟩
  have htI : Function.Injective (fderiv ℝ c.target (standardCrosscap (c.source x))) := by
    rw [← mfderiv_eq_fderiv]
    exact htD.mfderiv_injective (c.model_mem x hx)
  rw [fderiv_comp (c.source x) (c.target_smooth.differentiable (by simp) _)
    (standardCrosscap_hasFDerivAt _).differentiableAt]
  have hcomp : Function.Injective ((fderiv ℝ c.target (standardCrosscap (c.source x))).comp
      (fderiv ℝ standardCrosscap (c.source x))) ↔
      Function.Injective (fderiv ℝ standardCrosscap (c.source x)) := by
    constructor
    · intro h u v huv
      exact h (congrArg (fderiv ℝ c.target (standardCrosscap (c.source x))) huv)
    · intro h
      exact htI.comp h
  rw [hcomp,standardCrosscap_immersion_iff]
  constructor
  · intro hn he
    apply hn
    rw [he,c.source_center]
  · intro hn hz
    apply hn
    exact c.source.injOn hx c.source_mem (hz.trans c.source_center.symm)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapStripRegularNeighborhood
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A thin actual source rectangle has no singularities except the two
specified endpoint crosscaps. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.regular_neighborhood (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ U : Set Base, IsOpen U ∧ U ⊆ S.domain ∧
      (∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U) ∧
      ∀ x ∈ U, Function.Injective (fderiv ℝ S.model x) ↔
        x ≠ ![0,A.arc.start] ∧ x ≠ ![0,A.arc.finish] := by
  let R := {y | Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f y)}
  let O := A.left.source.source ∪ A.right.source.source ∪ R
  have hO : IsOpen O := (A.left.source.open_source.union A.right.source.open_source).union
    (surface_regular_locus_open hf)
  let U := S.domain ∩ (S.chart.target ∩ S.chart.symm ⁻¹' O)
  have hU : IsOpen U := S.domain_open.inter (S.chart.symm.isOpen_inter_preimage hO)
  have haxisU : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U := by
    intro t ht
    have hs := S.axis t ht
    have hx : (![0,t] : Base) ∈ S.domain := by
      apply S.rectangle 0 ⟨by linarith [S.width_pos],by linarith [S.width_pos]⟩ t
      constructor <;> linarith [S.width_pos,ht.1,ht.2]
    refine ⟨hx,S.domain_target hx,?_⟩
    change S.chart.symm (![0,t] : Base) ∈ O
    rw [← hs.2,S.chart.left_inv hs.1]
    by_cases hts : t = A.arc.start
    · rw [hts,A.source]
      exact Or.inl (Or.inl A.left.source_mem)
    · by_cases htf : t = A.arc.finish
      · rw [htf,A.target]
        exact Or.inl (Or.inr A.right.source_mem)
      · exact Or.inr (A.regular t ⟨lt_of_le_of_ne ht.1 (Ne.symm hts),lt_of_le_of_ne ht.2 htf⟩)
  have hpsource : p ∈ S.chart.source :=
    (congrArg (fun y => y ∈ S.chart.source) A.source).mp
      (S.axis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)).1
  have hqsource : q ∈ S.chart.source :=
    (congrArg (fun y => y ∈ S.chart.source) A.target).mp
      (S.axis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)).1
  have hpchart : S.chart p = ![0,A.arc.start] :=
    (congrArg S.chart A.source).symm.trans
      (S.axis _ (left_mem_Icc.mpr A.arc.start_lt_finish.le)).2
  have hqchart : S.chart q = ![0,A.arc.finish] :=
    (congrArg S.chart A.target).symm.trans
      (S.axis _ (right_mem_Icc.mpr A.arc.start_lt_finish.le)).2
  have hprecover : S.chart.symm (![0,A.arc.start] : Base) = p :=
    (congrArg S.chart.symm hpchart).symm.trans (S.chart.left_inv hpsource)
  have hqrecover : S.chart.symm (![0,A.arc.finish] : Base) = q :=
    (congrArg S.chart.symm hqchart).symm.trans (S.chart.left_inv hqsource)
  refine ⟨U,hU,inter_subset_left,haxisU,?_⟩
  intro x hx
  have hbridge := coordinate_representative_immersion_iff S.chart S.chart_smooth S.inverse_smooth hf
    S.domain_open S.domain_target S.model_eq hx.1
  rw [hbridge]
  constructor
  · intro h
    constructor
    · intro he
      rw [he,hprecover] at h
      exact ((A.left.regular_iff hf A.left.source_mem).mp h) rfl
    · intro he
      rw [he,hqrecover] at h
      exact ((A.right.regular_iff hf A.right.source_mem).mp h) rfl
  · rintro ⟨hxp,hxq⟩
    have hyp : S.chart.symm x ≠ p := by
      intro h
      apply hxp
      calc
        x = S.chart (S.chart.symm x) := (S.chart.right_inv hx.2.1).symm
        _ = S.chart p := congrArg S.chart h
        _ = ![0,A.arc.start] := hpchart
    have hyq : S.chart.symm x ≠ q := by
      intro h
      apply hxq
      calc
        x = S.chart (S.chart.symm x) := (S.chart.right_inv hx.2.1).symm
        _ = S.chart q := congrArg S.chart h
        _ = ![0,A.arc.finish] := hqchart
    rcases hx.2.2 with (hleft | hright) | hreg
    · exact (A.left.regular_iff hf hleft).mpr hyp
    · exact (A.right.regular_iff hf hright).mpr hyq
    · exact hreg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalAxisFactor
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalizing the actual two-zero defect along its connecting axis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem two_zero_axis_factor {N : Base → Base} {U : Set Base} (hU : IsOpen U)
    (hN : ContDiffOn ℝ ∞ N U) {p q : ℝ} (hpq : p < q)
    (haxis : ∀ t ∈ Icc p q, crosscapAxis t ∈ U)
    (hz : ∀ x ∈ U, N x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q)
    (hDp : Function.Bijective (fderiv ℝ N (crosscapAxis p)))
    (hDq : Function.Bijective (fderiv ℝ N (crosscapAxis q))) :
    ∃ (d : ℝ → Base) (W : Set ℝ), ContDiff ℝ ∞ d ∧ IsOpen W ∧ Icc p q ⊆ W ∧
      (∀ t ∈ Icc p q, d t ≠ 0) ∧
      ∀ t ∈ W, N (crosscapAxis t) = ((t-p)*(t-q)) • d t := by
  let V := crosscapAxis ⁻¹' U
  have hV : IsOpen V := hU.preimage crosscapAxis.continuous
  have hfV : ContDiffOn ℝ ∞ (N ∘ crosscapAxis) V :=
    hN.comp crosscapAxis.contDiff.contDiffOn (fun _ hx => hx)
  obtain ⟨W,hW,hKW,_hWV,g,hg,hge⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_Icc : IsCompact (Icc p q)) hV haxis hfV
  have hgevent (t : ℝ) (ht : t ∈ Icc p q) : g =ᶠ[𝓝 t] N ∘ crosscapAxis :=
    hge.eventuallyEq_of_mem (hW.mem_nhds (hKW ht))
  have hder (t : ℝ) (ht : t ∈ Icc p q) :
      deriv g t = fderiv ℝ N (crosscapAxis t) (![0,1] : Base) := by
    rw [(hgevent t ht).deriv_eq]
    have hd := ((hN.contDiffAt (hU.mem_nhds (haxis t ht))).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt t crosscapAxis.hasFDerivAt.hasDerivAt
    simpa only [crosscapAxis_apply] using hd.deriv
  have hp : g p = 0 := by
    rw [(hgevent p (left_mem_Icc.mpr hpq.le)).self_of_nhds]
    exact (hz _ (haxis p (left_mem_Icc.mpr hpq.le))).mpr (Or.inl rfl)
  have hq : g q = 0 := by
    rw [(hgevent q (right_mem_Icc.mpr hpq.le)).self_of_nhds]
    exact (hz _ (haxis q (right_mem_Icc.mpr hpq.le))).mpr (Or.inr rfl)
  have hdp : deriv g p ≠ 0 := by
    rw [hder p (left_mem_Icc.mpr hpq.le)]
    intro he
    have h := hDp.1 (he.trans (map_zero _).symm)
    have h1 := congrFun h 1
    norm_num at h1
  have hdq : deriv g q ≠ 0 := by
    rw [hder q (right_mem_Icc.mpr hpq.le)]
    intro he
    have h := hDq.1 (he.trans (map_zero _).symm)
    have h1 := congrFun h 1
    norm_num at h1
  have hzero : ∀ t ∈ Icc p q, g t = 0 → t = p ∨ t = q := by
    intro t ht he
    rw [(hgevent t ht).self_of_nhds] at he
    rcases (hz _ (haxis t ht)).mp he with h | h
    · exact Or.inl (congrFun h 1)
    · exact Or.inr (congrFun h 1)
  obtain ⟨d,hd,he,hn,_hdp,_hdq⟩ := nonzero_two_zero_factor hg hpq.ne hp hq hdp hdq hzero
  refine ⟨d,W,hd,hW,hKW,hn,?_⟩
  intro t ht
  exact (hge ht).symm.trans (he t)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AxisNormalizedDefect
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal coordinates adapted to the two simple zeros on the axis. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma axisNormalizedDefect_smoothAt {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {N : Base → Base} {x : Base} (hN : ContDiffAt ℝ ∞ N x) (hx : d (x 1) ≠ 0) :
    ContDiffAt ℝ ∞ (axisNormalizedDefect d N) x := by
  have hF : ContDiff ℝ ∞ (fun y : Base => planeComplexFrame (d (y 1))) :=
    planeComplexFrame_smooth.comp (hd.comp (contDiff_apply ℝ ℝ 1))
  exact ((planeComplexFrame_invertible hx).contDiffAt_map_inverse.comp x hF.contDiffAt).clm_apply hN

lemma axisNormalizedDefect_fderiv_zero {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {N : Base → Base} {x : Base} (hN : ContDiffAt ℝ ∞ N x)
    (hx : d (x 1) ≠ 0) (hz : N x = 0) :
    fderiv ℝ (axisNormalizedDefect d N) x =
      ((planeComplexFrame (d (x 1))).inverse).comp (fderiv ℝ N x) := by
  have hF : ContDiff ℝ ∞ (fun y : Base => planeComplexFrame (d (y 1))) :=
    planeComplexFrame_smooth.comp (hd.comp (contDiff_apply ℝ ℝ 1))
  have hJ := (planeComplexFrame_invertible hx).contDiffAt_map_inverse.comp x hF.contDiffAt
  have hD := (hJ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.clm_apply
    (hN.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  apply ContinuousLinearMap.ext
  intro v
  have he := congrArg (fun L => L v) hD.fderiv
  change (fderiv ℝ (fun y : Base => (planeComplexFrame (d (y 1))).inverse (N y)) x) v = _
  simpa [Function.comp_def,hz] using he

lemma axisNormalizedDefect_axis {d : ℝ → Base} {N : Base → Base} {p q t : ℝ}
    (hd : d t ≠ 0) (he : N (crosscapAxis t) = ((t-p)*(t-q)) • d t) :
    axisNormalizedDefect d N (crosscapAxis t) = ![(t-p)*(t-q),0] := by
  change (planeComplexFrame (d t)).inverse (N (crosscapAxis t)) = _
  rw [he,planeComplexFrame_inverse_axis hd]

lemma injective_second_column_nonzero (L : Base →L[ℝ] Base)
    (hL : Function.Surjective L) (haxis : (L (![0,1] : Base)) 1 = 0) :
    (L (![1,0] : Base)) 1 ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := hL (![0,1] : Base)
  have hsplit : v = v 0 • (![1,0] : Base)+v 1 • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  have he := congrFun hv 1
  rw [hsplit,map_add,map_smul,map_smul] at he
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,haxis,mul_zero,add_zero,
    Matrix.cons_val_one,Matrix.cons_val_zero] at he
  norm_num at he

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_AxisDefectJet
attribute [-simp] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized endpoint jets retain nonzero transverse normal components. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma axisNormalizedDefect_derivative_bijective {d : ℝ → Base} (hd : ContDiff ℝ ∞ d)
    {N : Base → Base} {x : Base} (hN : ContDiffAt ℝ ∞ N x)
    (hx : d (x 1) ≠ 0) (hz : N x = 0) (hD : Function.Bijective (fderiv ℝ N x)) :
    Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) x) := by
  rw [axisNormalizedDefect_fderiv_zero hd hN hx hz]
  exact (planeComplexFrame_invertible hx).inverse.bijective.comp hD

lemma normalized_axis_derivative {G : Base → Base} {p q t : ℝ}
    (hG : ContDiffAt ℝ ∞ G (crosscapAxis t)) {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0]) :
    fderiv ℝ G (crosscapAxis t) (![0,1] : Base) = ![(t-p)+(t-q),0] := by
  have he : G ∘ crosscapAxis =ᶠ[𝓝 t] fun s => (![(s-p)*(s-q),0] : Base) := by
    filter_upwards [hW.mem_nhds ht] with s hs
    exact haxis s hs
  have hd := (hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    crosscapAxis.hasFDerivAt.hasDerivAt
  have hp : HasDerivAt (fun s : ℝ => (![(s-p)*(s-q),0] : Base))
      (![(t-p)+(t-q),0] : Base) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert ((hasDerivAt_id t).sub_const p).mul ((hasDerivAt_id t).sub_const q) using 1 <;> first | (with_reducible_and_instances rfl) | (simp [add_comm])
      rfl
    · exact hasDerivAt_const t 0
  have hj := he.deriv_eq.trans hp.deriv
  exact (by simpa only [crosscapAxis_apply] using hd.deriv.symm.trans hj)

lemma normalized_axis_transverse_nonzero {G : Base → Base} {p q t : ℝ}
    (hG : ContDiffAt ℝ ∞ G (crosscapAxis t)) {W : Set ℝ} (hW : IsOpen W) (ht : t ∈ W)
    (haxis : ∀ s ∈ W, G (crosscapAxis s) = ![(s-p)*(s-q),0])
    (hD : Function.Bijective (fderiv ℝ G (crosscapAxis t))) :
    (fderiv ℝ G (crosscapAxis t) (![1,0] : Base)) 1 ≠ 0 := by
  apply injective_second_column_nonzero _ hD.2
  rw [normalized_axis_derivative hG hW ht haxis]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_FramedCrosscapDefect
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pair has exactly two nondegenerate normal-defect zeros
in a single rectangular coordinate neighborhood. -/
noncomputable section
open Set Filter Matrix Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.nondegenerate_normal_defect_framed (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (a : Fin 3 → ℝ) (δ : ℝ) (U : Set Base), 0 < δ ∧ IsOpen U ∧ U ⊆ S.domain ∧
      (∀ x ∈ Icc (-δ) δ, ∀ t ∈ Icc (A.arc.start-δ) (A.arc.finish+δ), (![x,t] : Base) ∈ U) ∧
      ContDiffOn ℝ ∞ (normalDefect S.model a) U ∧
      (∀ x ∈ U, normalDefect S.model a x = 0 ↔
        x = ![0,A.arc.start] ∨ x = ![0,A.arc.finish]) ∧
      Function.Bijective (fderiv ℝ (normalDefect S.model a) (![0,A.arc.start] : Base)) ∧
      Function.Bijective (fderiv ℝ (normalDefect S.model a) (![0,A.arc.finish] : Base)) ∧
      U ⊆ normalFrameDomain S.model a := by
  classical
  obtain ⟨a,ha⟩ := exists_curve_transverse_vector S.transverseVector S.transverseVector_smooth
  obtain ⟨V,hV,hVD,hVaxis,hVI⟩ := S.regular_neighborhood hf
  let U := V ∩ normalFrameDomain S.model a
  have hU : IsOpen U := hV.inter (normalFrameDomain_open S.model_smooth a)
  have hframe : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ normalFrameDomain S.model a := by
    intro t ht
    change transverseDerivative S.model (![0,t] : Base) ⨯₃ a ≠ 0
    rw [S.transverseDerivative_axis]
    exact curve_transverse_cross_ne_zero (S.transverseVector_ne_zero ht) (ha t)
  have hUaxis : ∀ t ∈ Icc A.arc.start A.arc.finish, (![0,t] : Base) ∈ U :=
    fun t ht => ⟨hVaxis t ht,hframe t ht⟩
  obtain ⟨δ,hδ,hrect⟩ := compact_axis_rectangle A.arc.start_lt_finish.le hU hUaxis
  have hl := hframe A.arc.start (left_mem_Icc.mpr A.arc.start_lt_finish.le)
  have hr := hframe A.arc.finish (right_mem_Icc.mpr A.arc.start_lt_finish.le)
  refine ⟨a,δ,U,hδ,hU,inter_subset_left.trans hVD,hrect,?_,?_,?_,?_,inter_subset_right⟩
  · exact normalDefect_smooth S.model_smooth (fun _ hx => normalFrameDomain_nonzero hx.2)
      (fun _ hx => normalFrameDomain_transverse hx.2)
  · intro x hx
    have hh : normalDefect S.model a x ≠ 0 ↔
        x ≠ ![0,A.arc.start] ∧ x ≠ ![0,A.arc.finish] :=
      (normalDefect_immersion_iff S.model a x (normalFrameDomain_nonzero hx.2)
        (normalFrameDomain_transverse hx.2)).symm.trans (hVI x hx.1)
    simpa only [not_not,not_and_or] using not_congr hh
  · exact normalDefect_nondegenerate_of_direction S.model_smooth a _
      (normalFrameDomain_nonzero hl) (normalFrameDomain_transverse hl) S.left_vertical
      S.endpoint_direction_regular.1
  · exact normalDefect_nondegenerate_of_direction S.model_smooth a _
      (normalFrameDomain_nonzero hr) (normalFrameDomain_transverse hr) S.right_vertical
      S.endpoint_direction_regular.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_NormalizedFramedAxis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common normal coordinate system for the two actual simple zeros. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem normalized_two_zero_axis_framed {N : Base → Base} {U : Set Base} (hU : IsOpen U)
    (hN : ContDiffOn ℝ ∞ N U) {p q : ℝ} (hpq : p < q)
    (haxis : ∀ t ∈ Icc p q, crosscapAxis t ∈ U)
    (hz : ∀ x ∈ U, N x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q)
    (hDp : Function.Bijective (fderiv ℝ N (crosscapAxis p)))
    (hDq : Function.Bijective (fderiv ℝ N (crosscapAxis q))) :
    ∃ (d : ℝ → Base) (O : Set Base) (W : Set ℝ), ContDiff ℝ ∞ d ∧
      IsOpen O ∧ O ⊆ U ∧ IsOpen W ∧ Icc p q ⊆ W ∧ (∀ t ∈ W, crosscapAxis t ∈ O) ∧
      ContDiffOn ℝ ∞ (axisNormalizedDefect d N) O ∧
      (∀ t ∈ W, axisNormalizedDefect d N (crosscapAxis t) = ![(t-p)*(t-q),0]) ∧
      (∀ x ∈ O, axisNormalizedDefect d N x = 0 ↔ x = crosscapAxis p ∨ x = crosscapAxis q) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis p)) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis q)) ∧
      (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis p) (![1,0] : Base)) 1 ≠ 0 ∧
      (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis q) (![1,0] : Base)) 1 ≠ 0 ∧
      (∀ x ∈ O, d (x 1) ≠ 0) := by
  obtain ⟨d,V,hd,hV,hKV,hn,he⟩ := two_zero_axis_factor hU hN hpq haxis hz hDp hDq
  let O := U ∩ {x : Base | d (x 1) ≠ 0}
  have hO : IsOpen O := hU.inter
    (isOpen_ne.preimage (hd.continuous.comp (continuous_apply 1)))
  let W := V ∩ crosscapAxis ⁻¹' O
  have hW : IsOpen W := hV.inter (hO.preimage crosscapAxis.continuous)
  have hKW : Icc p q ⊆ W := by
    intro t ht
    refine ⟨hKV ht,haxis t ht,?_⟩
    simpa only [mem_ofPred_eq,crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using hn t ht
  have hGO : ContDiffOn ℝ ∞ (axisNormalizedDefect d N) O := by
    intro x hx
    exact (axisNormalizedDefect_smoothAt hd (hN.contDiffAt (hU.mem_nhds hx.1)) hx.2).contDiffWithinAt
  have hGa : ∀ t ∈ W, axisNormalizedDefect d N (crosscapAxis t) = ![(t-p)*(t-q),0] := by
    intro t ht
    apply axisNormalizedDefect_axis
    · simpa only [mem_ofPred_eq,crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using ht.2.2
    · exact he t ht.1
  have hpW := hKW (left_mem_Icc.mpr hpq.le)
  have hqW := hKW (right_mem_Icc.mpr hpq.le)
  have hGp := hGO.contDiffAt (hO.mem_nhds hpW.2)
  have hGq := hGO.contDiffAt (hO.mem_nhds hqW.2)
  have hDpG : Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis p)) :=
    axisNormalizedDefect_derivative_bijective hd
      (hN.contDiffAt (hU.mem_nhds hpW.2.1)) hpW.2.2
      ((hz _ hpW.2.1).mpr (Or.inl rfl)) hDp
  have hDqG : Function.Bijective (fderiv ℝ (axisNormalizedDefect d N) (crosscapAxis q)) :=
    axisNormalizedDefect_derivative_bijective hd
      (hN.contDiffAt (hU.mem_nhds hqW.2.1)) hqW.2.2
      ((hz _ hqW.2.1).mpr (Or.inr rfl)) hDq
  refine ⟨d,O,W,hd,hO,inter_subset_left,hW,hKW,fun _ ht => ht.2,hGO,hGa,?_,hDpG,hDqG,
    normalized_axis_transverse_nonzero hGp hW hpW hGa hDpG,
    normalized_axis_transverse_nonzero hGq hW hqW hGa hDqG,fun _ hx => hx.2⟩
  intro x hx
  change (planeComplexFrame (d (x 1))).inverse (N x) = 0 ↔ _
  rw [←(map_zero (planeComplexFrame (d (x 1))).inverse)]
  exact (planeComplexFrame_invertible hx.2).inverse.injective.eq_iff.trans (hz x hx.1)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_CrosscapFramedRectangle
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized rectangle is constructed from the actual crosscap strip. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {f : M → ProjectionTarget 3} {p q : M} {A : CrosscapConnectingArc f p q}

theorem CrosscapCoordinateStrip.normalized_defect_rectangle_framed_oai (S : CrosscapCoordinateStrip A)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) :
    ∃ (a : Fin 3 → ℝ) (d : ℝ → Base) (r : ℝ) (O : Set Base),
      ContDiff ℝ ∞ d ∧ 0 < r ∧ IsOpen O ∧ O ⊆ S.domain ∧
      (∀ x ∈ Icc (-r) r, ∀ t ∈ Icc (A.arc.start-r) (A.arc.finish+r), (![x,t] : Base) ∈ O) ∧
      ContDiffOn ℝ ∞ (axisNormalizedDefect d (normalDefect S.model a)) O ∧
      (∀ t, crosscapAxis t ∈ O →
        axisNormalizedDefect d (normalDefect S.model a) (crosscapAxis t) =
          ![(t-A.arc.start)*(t-A.arc.finish),0]) ∧
      (∀ x ∈ O, axisNormalizedDefect d (normalDefect S.model a) x = 0 ↔
        x = crosscapAxis A.arc.start ∨ x = crosscapAxis A.arc.finish) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.start)) ∧
      Function.Bijective (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.finish)) ∧
      (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.start) (![1,0] : Base)) 1 ≠ 0 ∧
      (fderiv ℝ (axisNormalizedDefect d (normalDefect S.model a))
        (crosscapAxis A.arc.finish) (![1,0] : Base)) 1 ≠ 0 ∧
      (∀ x ∈ O, d (x 1) ≠ 0) ∧ O ⊆ normalFrameDomain S.model a := by
  obtain ⟨a,δ,U,hδ,hU,hUD,hrect,hN,hz,hDp,hDq,hUF⟩ := S.nondegenerate_normal_defect_framed hf
  have haxis : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ U := by
    intro t ht
    rw [crosscapAxis_apply]
    apply hrect 0 (by constructor <;> linarith) t
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨d,V,W,hd,hV,hVU,hW,hKW,hWa,hGV,hGa,hGz,hDpG,hDqG,hvp,hvq,hdn⟩ :=
    normalized_two_zero_axis_framed hU hN A.arc.start_lt_finish haxis
      (by simpa only [crosscapAxis_apply] using hz)
      (by simpa only [crosscapAxis_apply] using hDp)
      (by simpa only [crosscapAxis_apply] using hDq)
  let O := V ∩ {x : Base | x 1 ∈ W}
  have hO : IsOpen O := hV.inter (hW.preimage (continuous_apply 1))
  have hKO : ∀ t ∈ Icc A.arc.start A.arc.finish, crosscapAxis t ∈ O := by
    intro t ht
    refine ⟨hWa t (hKW ht),?_⟩
    simpa only [mem_ofPred_eq,crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using hKW ht
  obtain ⟨r,hr,hrrect⟩ := compact_axis_rectangle A.arc.start_lt_finish.le hO
    (by simpa only [crosscapAxis_apply] using hKO)
  refine ⟨a,d,r,O,hd,hr,hO,inter_subset_left.trans (hVU.trans hUD),hrrect,
    hGV.mono inter_subset_left,?_,fun x hx => hGz x hx.1,hDpG,hDqG,hvp,hvq,fun x hx => hdn x hx.1,
    inter_subset_left.trans (hVU.trans hUF)⟩
  intro t ht
  apply hGa t
  simpa only [mem_ofPred_eq,crosscapAxis_apply,Matrix.cons_val_one,Matrix.cons_val_zero] using ht.2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CrosscapCoordinateStrip.normalized_defect_rectangle_framed_oai.{u_1}
