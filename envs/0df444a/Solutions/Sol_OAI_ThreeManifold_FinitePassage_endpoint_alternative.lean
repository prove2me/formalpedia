-- Prove2me | solution 1 for OAI.ThreeManifold.FinitePassage.endpoint_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:38:14.989682+00:00
-- url     : https://prove2.me/submissions/19b57c81-a2e8-497e-bf47-298213d238bf

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Passages.lean:L641-L665
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.FinitePassage.endpoint_alternative. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity
import Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
import Definitions.Def_OAI_Geometry_ConjugatePoints_Passages

-- ---- from OAI.Geometry.ConjugatePoints.Passages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

/-!
# Passage supports, extension, and compact metric estimates.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X Y : Type} [TopologicalSpace X] (O : TopologicalSpace.Opens X) (e : O ≃ₜ O)
end ThreeManifold.TwoGluing
namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction GluedConstruction
end

section
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_2
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_2
end

open MetricConstruction CylinderConstruction GluedConstruction
end ThreeManifold.CompactMetric

namespace ThreeManifold.CylinderConstruction

section
open QuotientConstruction

end

attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instChartedSpaceE3Cylinder_1
attribute [local instance] OAI.ThreeManifold.CylinderConstruction.instIsManifoldRealE3I3SomeENatTopCylinder_1
end ThreeManifold.CylinderConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates Cometric Neck

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_3
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_3
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.FinitePassage

lemma endpoint_alternative {M : Type*} [TopologicalSpace M] {O : Set M}
    {γ : ℝ → M} {A B a b : ℝ} (hab : a < b) (hAa : A ≤ a) (hbB : b ≤ B)
    (hr : ∀ s ∈ Ioo a b, γ s ∈ O)
    (hc : ContinuousOn γ (Icc A B))
    (ha : a ∉ Ioo A B ∩ γ ⁻¹' O) (hb : b ∉ Ioo A B ∩ γ ⁻¹' O) :
    (a = A ∨ γ a ∈ closure O \ O) ∧ (b = B ∨ γ b ∈ closure O \ O) := by
  have hcore : Icc a b ⊆ Icc A B := Icc_subset_Icc hAa hbB
  have hmem : ∀ s ∈ Icc a b, γ s ∈ closure O := by
    have hsc : ContinuousOn γ (closure (Ioo a b)) := by
      rw [closure_Ioo hab.ne]
      exact hc.mono hcore
    have hh := (show MapsTo γ (Ioo a b) O from hr).closure_of_continuousOn hsc
    rw [closure_Ioo hab.ne] at hh
    exact hh
  constructor
  · by_cases he : a = A
    · exact Or.inl he
    · right
      refine ⟨hmem a ⟨le_rfl,hab.le⟩,fun hao => ha ⟨?_,hao⟩⟩
      exact ⟨lt_of_le_of_ne hAa (Ne.symm he),hab.trans_le hbB⟩
  · by_cases he : b = B
    · exact Or.inl he
    · right
      refine ⟨hmem b ⟨hab.le,le_rfl⟩,fun hbo => hb ⟨?_,hbo⟩⟩
      exact ⟨hAa.trans_lt hab,lt_of_le_of_ne hbB he⟩
end ThreeManifold.FinitePassage
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_4
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.PassageDynamics

end ThreeManifold.PassageDynamics

namespace ThreeManifold.SupportExtension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end ThreeManifold.SupportExtension
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck
end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end

section
open RiemannianCoordinates MetricConstruction Cometric Neck LocalNeck ReturningPassage

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients
end ThreeManifold.CompactMetric

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.FinitePassage
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.ThreeManifold.FinitePassage.endpoint_alternative := @_root_.OAI.ThreeManifold.FinitePassage.endpoint_alternative
