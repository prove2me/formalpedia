-- Prove2me | solution 1 for OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.coordinate_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:09:18.828988+00:00
-- url     : https://prove2.me/submissions/647010d1-3fc1-4e34-a0bc-b341cfd20c8c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Curvature.lean:L105-L135
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.coordinate_derivative. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature

-- ---- from OAI.Geometry.ConjugatePoints.Curvature ----
namespace OAI

noncomputable section

/-!
# Local isometries, warped curvature, and compact curvature estimates.
-/

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
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)

lemma coordinate_derivative {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {p : M}
    (hp : p ∈ P.domain) (hpc : p ∈ c.source) (hpd : f p ∈ d.source) (u : TangentSpace I3 p) :
    mfderiv I3 I3 d (f p) (mfderiv I3 I3 f p u) =
      fderiv ℝ (d ∘ f ∘ c.symm) (c p) (mfderiv I3 I3 c p u) := by
  have hcs := (mdifferentiable_of_mem_atlas (I := I3) hc).mdifferentiableAt_symm (c.map_source hpc)
  have hfs := (P.smoothAt hp).mdifferentiableAt (by simp)
  have hds := (mdifferentiable_of_mem_atlas (I := I3) hd).mdifferentiableAt hpd
  have he : mfderiv I3 I3 (d ∘ f ∘ c.symm) (c p) =
      (mfderiv I3 I3 d (f p)).comp ((mfderiv I3 I3 f p).comp (mfderiv I3 I3 c.symm (c p))) := by
    rw [mfderiv_comp _ (show MDifferentiableAt I3 I3 d ((f ∘ c.symm) (c p)) by
      simpa only [Function.comp_apply,c.left_inv hpc] using hds)
        ((show MDifferentiableAt I3 I3 f (c.symm (c p)) by
          rw [c.left_inv hpc]; exact hfs).comp _ hcs),
      mfderiv_comp _ (show MDifferentiableAt I3 I3 f (c.symm (c p)) by
          rw [c.left_inv hpc]; exact hfs) hcs]
    let A : M → E3 →L[ℝ] E3 := fun q => mfderiv I3 I3 f q
    let D : N → E3 →L[ℝ] E3 := fun q => mfderiv I3 I3 d q
    let C : E3 →L[ℝ] E3 := mfderiv I3 I3 c.symm (c p)
    change (D (f (c.symm (c p)))).comp ((A (c.symm (c p))).comp C) =
      (D (f p)).comp ((A p).comp C)
    rw [c.left_inv hpc]
  have hi := congrArg (fun L => L u) ((mdifferentiable_of_mem_atlas (I := I3) hc).symm_comp_deriv hpc)
  change mfderiv I3 I3 c.symm (c p) (mfderiv I3 I3 c p u) = u at hi
  have he' := congrArg (fun L => L (mfderiv I3 I3 c p u)) he
  rw [mfderiv_eq_fderiv] at he'
  change fderiv ℝ (d ∘ f ∘ c.symm) (c p) (mfderiv I3 I3 c p u) =
    mfderiv I3 I3 d (f p) (mfderiv I3 I3 f p
      (mfderiv I3 I3 c.symm (c p) (mfderiv I3 I3 c p u))) at he'
  rw [hi] at he'
  exact he'.symm

end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.WarpedCurvature
open Neck RiemannianCoordinates

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.WarpedCurvature
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart
open MetricConstruction RiemannianCoordinates
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
end ThreeManifold.Rechart

namespace ThreeManifold.CylinderConstruction
open MetricConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instChartedSpaceE3Cylinder
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instIsManifoldRealE3I3SomeENatTopCylinder
variable {r s c : ℝ → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ t, r t ≠ 0) (hs : ∀ t, s t ≠ 0)
end ThreeManifold.CylinderConstruction

namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.WarpedCurvature
open MetricConstruction CylinderConstruction RiemannianCoordinates
variable {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ} (hb : b ≠ 0) (hr : ∀ t, r t ≠ 0)
end ThreeManifold.WarpedCurvature

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart
open MetricConstruction RiemannianCoordinates
variable {E M X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
end ThreeManifold.Rechart
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff UpperHalfPlane RealInnerProductSpace
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature

attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise UpperHalfPlane
namespace ThreeManifold.WarpedCurvature
open RiemannianCoordinates Neck
end ThreeManifold.WarpedCurvature
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3UniversalPiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopUniversalPiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_1
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece
end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
variable {M N X : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]
namespace LocalMetricIsometry
variable {g : SmoothMetric M} {h : SmoothMetric N} {k : SmoothMetric X}
  {f : M → N} {w : N → X}
end LocalMetricIsometry
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder
end

open MetricConstruction CylinderConstruction RiemannianCoordinates

attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_1
variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3WholePiece_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopWholePiece_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Piece_1
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopPiece_1
end ThreeManifold.CompactMetric

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.RiemannianCoordinates OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise


theorem solution : type_of% @_root_.OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.coordinate_derivative := @_root_.OAI.ThreeManifold.RiemannianCoordinates.LocalMetricIsometry.coordinate_derivative
