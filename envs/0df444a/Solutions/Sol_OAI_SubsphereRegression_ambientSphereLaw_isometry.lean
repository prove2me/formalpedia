-- Prove2me | solution 1 for OAI.SubsphereRegression.ambientSphereLaw_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:03:57.696576+00:00
-- url     : https://prove2.me/submissions/2b802625-5e21-45cf-9bd2-c0ece464275e

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Spheres.lean:L223-L241
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereRegression.ambientSphereLaw_isometry. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Theorems.Thm_OAI_SubsphereRegression_sphereLaw_apply

-- ---- from OAI.Probability.Subsphere.Regression.Spheres ----
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SphereBounds

open scoped Pointwise
section MoreSphere
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma unitBallLaw_isometry_apply (e : E ≃ₗᵢ[ℝ] E) (s : Set E) :
    unitBallLaw (e ⁻¹' s) = unitBallLaw s := by
  have hb : e ⁻¹' Metric.closedBall (0 : E) 1 = Metric.closedBall 0 1 := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  have hset : e ⁻¹' s ∩ Metric.closedBall (0 : E) 1 =
      e ⁻¹' (s ∩ Metric.closedBall 0 1) := by rw [Set.preimage_inter, hb]
  rw [unitBallLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet,
    Measure.restrict_apply' Metric.isClosed_closedBall.measurableSet, hset]
  congr 1
  calc
    _ = (Measure.map e volume) (s ∩ Metric.closedBall 0 1) :=
      (e.toMeasurableEquiv.measurableEmbedding.map_apply _ _).symm
    _ = _ := by rw [e.measurePreserving.map_eq]

lemma ambientSphereLaw_apply [Nontrivial E] {s : Set E} (hs : MeasurableSet s) :
    ambientSphereLaw s = unitBallLaw (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
  rw [ambientSphereLaw, Measure.map_apply (by fun_prop) hs,
    sphereLaw_apply (measurable_subtype_coe hs)]
  congr 2
  ext x
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hs⟩
    exact ⟨⟨x,hx⟩,hs,rfl⟩

lemma ambientSphereLaw_isometry [Nontrivial E] (e : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving e (ambientSphereLaw (E := E)) (ambientSphereLaw (E := E)) := by
  refine ⟨e.continuous.measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply e.continuous.measurable hs,
    ambientSphereLaw_apply (e.continuous.measurable hs), ambientSphereLaw_apply hs]
  have hset : Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ e ⁻¹' s) =
      e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Metric.sphere 0 1 ∩ s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨hy, hys⟩, he⟩
      refine ⟨r,hr,e y,⟨?_,hys⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.norm_map] using hy
      · simpa only [map_smul] using congrArg e he
    · rintro ⟨r,hr,y,⟨hy,hys⟩,he⟩
      refine ⟨r,hr,e.symm y,⟨?_,?_⟩,?_⟩
      · simpa only [mem_sphere_zero_iff_norm, e.symm.norm_map] using hy
      · simpa using hys
      · simpa only [map_smul, e.symm_apply_apply] using congrArg e.symm he
  rw [hset, unitBallLaw_isometry_apply]

end MoreSphere

section FubiniAux
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
end FubiniAux

end SubsphereRegression
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open scoped Topology
open InnerProductSpace
open scoped Pointwise


theorem solution : type_of% @_root_.OAI.SubsphereRegression.ambientSphereLaw_isometry := @_root_.OAI.SubsphereRegression.ambientSphereLaw_isometry
