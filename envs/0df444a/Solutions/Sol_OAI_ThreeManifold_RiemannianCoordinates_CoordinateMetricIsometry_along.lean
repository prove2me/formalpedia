-- Prove2me | solution 1 for OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.along
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:40:38.794987+00:00
-- url     : https://prove2.me/submissions/5f212430-de20-455f-a3f1-4d95a761b5a8

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Coordinates.lean:L1180-L1199
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.along. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_connection

-- ---- from OAI.Geometry.ConjugatePoints.Coordinates ----
namespace OAI

noncomputable section

/-!
# Riemannian coordinates, connections, curvature, and Jacobi fields.
-/

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

section MatrixSmooth
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {n : Type*} [Fintype n] [DecidableEq n] {R : X → Matrix n n ℝ} {x : X}
end MatrixSmooth

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

namespace CoordinateMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N}
  {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3} {f : E3 → E3}
  (P : CoordinateMetricIsometry g h c d f)
lemma smoothAt {x : E3} (hx : x ∈ P.domain) : ContDiffAt ℝ ∞ f x :=
  P.smooth.contDiffAt (P.isOpen_domain.mem_nhds hx)
end CoordinateMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N}
  {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3} {f : E3 → E3}
  (P : CoordinateMetricIsometry g h c d f)
lemma along (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x F : ℝ → E3} {s : ℝ}
    (hx : DifferentiableAt ℝ x s) (hF : DifferentiableAt ℝ F s)
    (hxs : x s ∈ P.domain) :
    alongDerivative h d (f ∘ x) (fun r => fderiv ℝ f (x r) (F r)) s =
      fderiv ℝ f (x s) (alongDerivative g c x F s) := by
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  have hfs : ContDiffAt ℝ ∞ f (x s) := P.smoothAt hxs
  have hdf := (hfs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hx.hasDerivAt
  have hdA := ((hfs.fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt s hx.hasDerivAt
  have hdF : HasDerivAt (fun r => fderiv ℝ f (x r) (F r))
      (fderiv ℝ (fderiv ℝ f) (x s) (deriv x s) (F s) +
        fderiv ℝ f (x s) (deriv F s)) s := by
    convert hdA.clm_apply hF.hasDerivAt using 1 <;> rfl
  have he := P.connection hc hd hxs (deriv x s) (F s)
  rw [alongDerivative,hdF.deriv,hdf.deriv]
  change _ = fderiv ℝ f (x s) (deriv F s + connectionTerm g c (x s) (deriv x s) (F s))
  rw [map_add,← he]
  abel

end ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry

namespace ThreeManifold.RiemannianCoordinates

section
open MetricConstruction
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end LocalMetricIsometry
end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

section
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.RiemannianCoordinates
end

open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3_1
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3_1
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3_2
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3_2
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3_3
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3_3
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedAddCommGroupContinuousLinearMapRealIdE3_4
attribute [local instance] OAI.ThreeManifold.RiemannianCoordinates.instNormedSpaceRealContinuousLinearMapIdE3_4
end ThreeManifold.RiemannianCoordinates

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.along := @_root_.OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.along
