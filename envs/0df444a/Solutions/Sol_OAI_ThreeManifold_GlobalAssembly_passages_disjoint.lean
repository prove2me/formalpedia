-- Prove2me | solution 1 for OAI.ThreeManifold.GlobalAssembly.passages_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:06:39.460368+00:00
-- url     : https://prove2.me/submissions/293f340a-551c-4cf4-9942-3c6d39c68a1c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Index.lean:L1274-L1286
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.GlobalAssembly.passages_disjoint. The node keeps its source
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

-- ---- from OAI.Geometry.ConjugatePoints.Index ----
namespace OAI

noncomputable section

/-!
# Index forms, cutoff fields, and assembly of local estimates.
-/

section

open Set Filter MeasureTheory Real
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

end ThreeManifold.IndexCutoff

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ThreeManifold.IndexForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end ThreeManifold.IndexForm

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace
namespace ThreeManifold.IndexForm

section
open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end

section
open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end

open IndexCutoff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

end ThreeManifold.IndexForm
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter MeasureTheory Real
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

end ThreeManifold.IndexCutoff
end

section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace ThreeManifold.IndexCutoff

end ThreeManifold.IndexCutoff
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
open IndexCutoff

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
open IndexCutoff

end ThreeManifold.RiemannianCoordinates
end

open Set MeasureTheory Topology Function

namespace ThreeManifold.GlobalAssembly

lemma passages_disjoint (U : Set ℝ) : Pairwise (Disjoint on (fun J : Passages U => J.val)) := by
  intro J K hJK
  apply disjoint_left.mpr
  intro x hxJ hxK
  change x ∈ J.val at hxJ
  change x ∈ K.val at hxK
  obtain ⟨j, _, hj⟩ := J.property
  obtain ⟨k, _, hk⟩ := K.property
  have he : J.val = K.val := by
    rw [hj, hk]
    exact (connectedComponentIn_eq (hj ▸ hxJ)).trans
      (connectedComponentIn_eq (hk ▸ hxK)).symm
  exact hJK (Subtype.ext he)

end ThreeManifold.GlobalAssembly

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.GlobalAssembly
open Set MeasureTheory Topology Function


theorem solution : type_of% @_root_.OAI.ThreeManifold.GlobalAssembly.passages_disjoint := @_root_.OAI.ThreeManifold.GlobalAssembly.passages_disjoint
