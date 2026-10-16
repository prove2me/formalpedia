-- Prove2me | solution 1 for OAI.ThreeManifold.FinitePassage.bounded_component
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:36:55.005317+00:00
-- url     : https://prove2.me/submissions/c09a13b0-a186-4008-8148-fde2ac664d42

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Passages.lean:L607-L639
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.FinitePassage.bounded_component. The node keeps its source
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

lemma bounded_open_interval {S : Set ℝ} (hS : IsOpen S) (hc : IsConnected S)
    (hb : BddBelow S) (ha : BddAbove S) :
    S = Ioo (sInf S) (sSup S) := by
  apply Subset.antisymm _ (hc.Ioo_csInf_csSup_subset hb ha)
  intro x hx
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
  have hl : x-ε/2 ∈ S := by
    apply he
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  have hr : x+ε/2 ∈ S := by
    apply he
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  exact ⟨lt_of_le_of_lt (csInf_le hb hl) (by linarith),
    lt_of_lt_of_le (by linarith) (le_csSup ha hr)⟩

lemma closure_component_boundary {P : Set ℝ} (hP : IsOpen P) {x y : ℝ}
    (hy : y ∈ closure (connectedComponentIn P x))
    (hyn : y ∉ connectedComponentIn P x) : y ∉ P := by
  intro hyp
  have hn : connectedComponentIn P y ∈ nhds y :=
    hP.connectedComponentIn.mem_nhds (mem_connectedComponentIn hyp)
  obtain ⟨z,hzy,hzx⟩ := (mem_closure_iff_nhds.mp hy) _ hn
  have he : connectedComponentIn P x = connectedComponentIn P y :=
    (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm
  exact hyn (he ▸ mem_connectedComponentIn hyp)

theorem bounded_component {P : Set ℝ} (hP : IsOpen P) {A B x : ℝ}
    (hPB : P ⊆ Ioo A B) (hx : x ∈ P) :
    ∃ a b : ℝ, a < b ∧ A ≤ a ∧ b ≤ B ∧
      connectedComponentIn P x = Ioo a b ∧ a ∉ P ∧ b ∉ P := by
  let S := connectedComponentIn P x
  have hn : S.Nonempty := connectedComponentIn_nonempty_iff.mpr hx
  have hs : S ⊆ Ioo A B := (connectedComponentIn_subset P x).trans hPB
  have hb : BddBelow S := ⟨A,fun y hy => (hs hy).1.le⟩
  have ha : BddAbove S := ⟨B,fun y hy => (hs hy).2.le⟩
  have he : S = Ioo (sInf S) (sSup S) :=
    bounded_open_interval hP.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr hx) hb ha
  have hab : sInf S < sSup S := nonempty_Ioo.mp (he ▸ hn)
  have hcl : closure S = Icc (sInf S) (sSup S) := by
    conv_lhs => rw [he]
    rw [closure_Ioo hab.ne]
  refine ⟨sInf S,sSup S,hab,le_csInf hn (fun y hy => (hs hy).1.le),
    csSup_le hn (fun y hy => (hs hy).2.le),he,?_,?_⟩
  · apply closure_component_boundary hP
    · change sInf S ∈ closure S
      apply hcl.symm.subset
      exact ⟨le_rfl,hab.le⟩
    · change sInf S ∉ S
      intro hi
      have hi' := he.subset hi
      exact (lt_irrefl _) hi'.1
  · apply closure_component_boundary hP
    · change sSup S ∈ closure S
      apply hcl.symm.subset
      exact ⟨hab.le,le_rfl⟩
    · change sSup S ∉ S
      intro hi
      have hi' := he.subset hi
      exact (lt_irrefl _) hi'.2

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


theorem solution : type_of% @_root_.OAI.ThreeManifold.FinitePassage.bounded_component := @_root_.OAI.ThreeManifold.FinitePassage.bounded_component
