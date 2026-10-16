-- Prove2me | solution 1 for OAI.ThreeManifold.PassageDynamics.reflected_closed_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:45:44.970295+00:00
-- url     : https://prove2.me/submissions/3aa01c58-3647-46d8-9213-00722fb01f5b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Passages.lean:L874-L895
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.PassageDynamics.reflected_closed_smooth. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_scalar_reflection_germ

-- ---- from OAI.Geometry.ConjugatePoints.Passages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
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
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.PassageDynamics

lemma reflectEven_germ_center {f : ℝ → ℝ} {c : ℝ}
    (he : (fun s => f (2*c-s)) =ᶠ[nhds c] f) : reflectEven c f =ᶠ[nhds c] f := by
  filter_upwards [he] with s hs
  simp only [reflectEven]
  split_ifs <;> first | rfl | assumption
lemma reflectOdd_germ_center {f : ℝ → ℝ} {c : ℝ}
    (he : (fun s => -f (2*c-s)) =ᶠ[nhds c] f) : reflectOdd c f =ᶠ[nhds c] f := by
  filter_upwards [he] with s hs
  simp only [reflectOdd]
  split_ifs <;> first | rfl | assumption

lemma reflectEven_germ_left (f : ℝ → ℝ) {c s : ℝ} (hs : s < c) :
    reflectEven c f =ᶠ[nhds s] f := by
  filter_upwards [eventually_lt_nhds hs] with r hr
  exact ite_eq_left hr.le
lemma reflectOdd_germ_left (f : ℝ → ℝ) {c s : ℝ} (hs : s < c) :
    reflectOdd c f =ᶠ[nhds s] f := by
  filter_upwards [eventually_lt_nhds hs] with r hr
  exact ite_eq_left hr.le
lemma reflectEven_germ_right (f : ℝ → ℝ) {c s : ℝ} (hs : c < s) :
    reflectEven c f =ᶠ[nhds s] (fun r => f (2*c-r)) := by
  filter_upwards [eventually_gt_nhds hs] with r hr
  exact ite_eq_right (not_le.mpr hr)
lemma reflectOdd_germ_right (f : ℝ → ℝ) {c s : ℝ} (hs : c < s) :
    reflectOdd c f =ᶠ[nhds s] (fun r => -f (2*c-r)) := by
  filter_upwards [eventually_gt_nhds hs] with r hr
  exact ite_eq_right (not_le.mpr hr)

lemma reflected_closed_smooth {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (hta : ∀ s ∈ Icc a b, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc a b, ContDiffAt ℝ ∞ v s) :
    ∀ s ∈ Icc a (2*c-a), ContDiffAt ℝ ∞ (reflectEven c t) s ∧ ContDiffAt ℝ ∞ (reflectOdd c v) s := by
  have hcg := scalar_reflection_germ hF isOpen_Ioo hc
    (fun s hs => ht s (Ioo_subset_Icc_self hs)) (fun s hs => hv s (Ioo_subset_Icc_self hs)) hvc
  intro s hs
  rcases lt_trichotomy s c with hsc | hsc | hcs
  · have hsU : s ∈ Icc a b := ⟨hs.1,hsc.le.trans hc.2.le⟩
    exact ⟨(hta s hsU).congr_of_eventuallyEq (reflectEven_germ_left t hsc),
      (hva s hsU).congr_of_eventuallyEq (reflectOdd_germ_left v hsc)⟩
  · subst s
    exact ⟨(hta c (Ioo_subset_Icc_self hc)).congr_of_eventuallyEq (reflectEven_germ_center hcg.1),
      (hva c (Ioo_subset_Icc_self hc)).congr_of_eventuallyEq (reflectOdd_germ_center hcg.2)⟩
  · have hrU : 2*c-s ∈ Icc a b := ⟨by linarith [hs.2],by linarith [hc.2]⟩
    exact ⟨((hta _ hrU).comp s (contDiffAt_const.sub contDiffAt_id)).congr_of_eventuallyEq
      (reflectEven_germ_right t hcs),
      (((hva _ hrU).comp s (contDiffAt_const.sub contDiffAt_id)).neg).congr_of_eventuallyEq
      (reflectOdd_germ_right v hcs)⟩

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
open OAI OAI.ThreeManifold OAI.ThreeManifold.PassageDynamics
open Set Filter Topology
open scoped ContDiff


theorem solution : type_of% @_root_.OAI.ThreeManifold.PassageDynamics.reflected_closed_smooth := @_root_.OAI.ThreeManifold.PassageDynamics.reflected_closed_smooth
