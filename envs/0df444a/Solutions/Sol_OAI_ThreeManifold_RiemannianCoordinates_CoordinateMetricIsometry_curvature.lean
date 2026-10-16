-- Prove2me | solution 1 for OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.curvature
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:38:47.273976+00:00
-- url     : https://prove2.me/submissions/8790b2ff-39d8-457f-bb0b-13e874c326cc

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Coordinates.lean:L1150-L1179
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.curvature. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_RiemannianCoordinates_CoordinateMetricIsometry_connection_derivative

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
lemma curvature (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.domain) (u v w : E3) :
    let A := fderiv ℝ f x
    curvatureTerm h d (f x) (A u) (A v) (A w) = A (curvatureTerm g c x u v w) := by
  intro A
  let H := fderiv ℝ (fderiv ℝ f) x
  let K := fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x
  let C := connectionBilin g c x
  let D := connectionBilin h d (f x)
  let dC := fderiv ℝ (connectionBilin g c) x
  let dD := fderiv ℝ (connectionBilin h d) (f x)
  have hH : H u v = H v u := ((P.smoothAt hx).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).eq u v
  have hK : K u v = K v u := (((P.smoothAt hx).fderiv_right (m := ∞)
    (by simp)).isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω); exact WithTop.coe_le_coe.mpr le_top)).eq u v
  have hconn (a b : E3) : A (C a b) = H a b + D (A a) (A b) := by
    simpa only [C,D,connectionBilin_apply] using (P.connection hc hd hx a b).symm
  have hdiff (a b e : E3) : A (dC a b e) =
      K a b e + dD (A a) (A b) (A e) + D (H a b) (A e) + D (A b) (H a e) - H a (C b e) := by
    apply (eq_sub_iff_add_eq).2
    simpa only [add_comm] using (P.connection_derivative hc hd hx a b e).symm
  rw [curvature_connection h hd (x := f x) (P.target hx),curvature_connection g hc (P.source hx)]
  change dD (A u) (A v) (A w) - dD (A v) (A u) (A w) +
    D (A u) (D (A v) (A w)) - D (A v) (D (A u) (A w)) =
    A (dC u v w - dC v u w + C u (C v w) - C v (C u w))
  simp only [map_sub,map_add]
  rw [hdiff,hdiff,hconn,hconn,hconn,hconn,hH,hK]
  simp only [map_add]
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


theorem solution : type_of% @_root_.OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.curvature := @_root_.OAI.ThreeManifold.RiemannianCoordinates.CoordinateMetricIsometry.curvature
