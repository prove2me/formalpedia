-- Prove2me | solution 1 for OAI.ThreeManifold.CompactMetric.finite_neck_height_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:40:55.697155+00:00
-- url     : https://prove2.me/submissions/3c21519c-8e59-4316-9728-977293097563

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Passages.lean:L699-L725
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.CompactMetric.finite_neck_height_boundary. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_finite_neck_neighborhood
import Theorems.Thm_OAI_ThreeManifold_CompactMetric_neckPosition_mem_iff

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

end ThreeManifold.FinitePassage
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_4
lemma finite_neck_height_boundary {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ : ℝ → GluedConstruction.Manifold}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ U) (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck) :
    (∀ s ∈ Icc a b, (neckPosition δ (γ s)).1 ∈ Icc (0:ℝ) 1) ∧
    (γ a ∉ openNeck → (neckPosition δ (γ a)).1 = 0 ∨ (neckPosition δ (γ a)).1 = 1) ∧
    (γ b ∉ openNeck → (neckPosition δ (γ b)).1 = 0 ∨ (neckPosition δ (γ b)).1 = 1) := by
  obtain ⟨W,hW,_,hcc,hWU,hWe⟩ := finite_neck_neighborhood hδ hU hγ hab hsub hr
  have hpos : MapsTo (fun s => (neckPosition δ (γ s)).1) (Ioo a b) (Ioo (0:ℝ) 1) :=
    fun s hs => (neckPosition_mem_iff δ (hWe (hcc (Ioo_subset_Icc_self hs)))).mpr (hr s hs)
  have hcont : ContinuousOn (fun s => (neckPosition δ (γ s)).1) (closure (Ioo a b)) := by
    rw [closure_Ioo hab.ne]
    intro s hs
    exact ((continuous_fst.continuousAt.comp ((neckPosition_smooth δ
      (hWe (hcc hs))).continuousAt.comp (hγ.1.contMDiffAt (hU.mem_nhds (hsub hs))).continuousAt))).continuousWithinAt
  have hc := hpos.closure_of_continuousOn hcont
  rw [closure_Ioo hab.ne,closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hc
  have he (s : ℝ) (hs : s ∈ Icc a b) (hn : γ s ∉ openNeck) :
      (neckPosition δ (γ s)).1 = 0 ∨ (neckPosition δ (γ s)).1 = 1 := by
    have hn' : (neckPosition δ (γ s)).1 ∉ Ioo (0:ℝ) 1 :=
      fun hh => hn ((neckPosition_mem_iff δ (hWe (hcc hs))).mp hh)
    have hcs := hc hs
    simp only [mem_Ioo,not_and_or,not_lt] at hn'
    rcases hn' with hl | hr
    · exact Or.inl (le_antisymm hl hcs.1)
    · exact Or.inr (le_antisymm hcs.2 hr)
  exact ⟨fun s hs => hc hs,he a ⟨le_rfl,hab.le⟩,he b ⟨hab.le,le_rfl⟩⟩

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
open OAI OAI.ThreeManifold OAI.ThreeManifold.CompactMetric
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
attribute [local instance] OAI.ThreeManifold.CompactMetric.instChartedSpaceE3Cylinder_4
attribute [local instance] OAI.ThreeManifold.CompactMetric.instIsManifoldRealE3I3SomeENatTopCylinder_4


theorem solution : type_of% @_root_.OAI.ThreeManifold.CompactMetric.finite_neck_height_boundary := @_root_.OAI.ThreeManifold.CompactMetric.finite_neck_height_boundary
