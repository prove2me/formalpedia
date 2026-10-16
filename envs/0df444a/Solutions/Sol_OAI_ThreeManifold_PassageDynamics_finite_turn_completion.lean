-- Prove2me | solution 1 for OAI.ThreeManifold.PassageDynamics.finite_turn_completion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:47:19.78107+00:00
-- url     : https://prove2.me/submissions/eb0485b9-f357-43ba-82ee-d4e87c1f6308

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Passages.lean:L897-L932
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.PassageDynamics.finite_turn_completion. The node keeps its source
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
import Theorems.Thm_OAI_ThreeManifold_PassageDynamics_reflected_closed_equations

-- ---- from OAI.Geometry.ConjugatePoints.Returning ----
namespace OAI

noncomputable section

/-!
# Returning neck geodesics, passage dynamics, and index bounds.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Neck
open Matrix
open scoped Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.Turning

end ThreeManifold.Turning

namespace ThreeManifold.DirectTurning

section
open Set MeasureTheory Neck Matrix
open scoped Interval Topology

end

open Neck Matrix Set MeasureTheory Turning
open scoped Interval Topology Matrix.Norms.Elementwise

end ThreeManifold.DirectTurning

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningTime

end ThreeManifold.ReturningTime

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningCoefficients
open Neck Matrix

end ThreeManifold.ReturningCoefficients

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck Matrix

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

end ThreeManifold.ReturningCoefficients

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.PassageDynamics

lemma smooth_autonomous_unique {V : (ℝ × ℝ) → (ℝ × ℝ)}
    (hV : ContDiff ℝ ∞ V) {f g : ℝ → ℝ × ℝ} {a b c : ℝ}
    (hc : c ∈ Ioo a b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfd : ∀ s ∈ Ioo a b, HasDerivAt f (V (f s)) s)
    (hgd : ∀ s ∈ Ioo a b, HasDerivAt g (V (g s)) s)
    (heq : f c = g c) : EqOn f g (Icc a b) := by
  have hcomp := (isCompact_Icc.image_of_continuousOn hf).union (isCompact_Icc.image_of_continuousOn hg)
  obtain ⟨R, hR⟩ := hcomp.isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨K, hK⟩ := hV.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℝ × ℝ) R) (isCompact_closedBall (0 : ℝ × ℝ) R)
  exact ODE_solution_unique_of_mem_Icc (v := fun _ => V)
    (s := fun _ => Metric.closedBall (0 : ℝ × ℝ) R) (fun _ _ => hK) hc hf hfd
    (fun s hs => hR (Or.inl ⟨s, Ioo_subset_Icc_self hs, rfl⟩)) hg hgd
    (fun s hs => hR (Or.inr ⟨s, Ioo_subset_Icc_self hs, rfl⟩)) heq

lemma scalarVectorField_smooth {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁) :
    ContDiff ℝ ∞ (scalarVectorField F₁) :=
  contDiff_snd.prodMk ((hF.comp contDiff_fst).neg.div_const 2)

lemma scalar_equations_unique {F₁ : ℝ → ℝ} (hF : ContDiff ℝ ∞ F₁)
    {t v u w : ℝ → ℝ} {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F₁ (t s) / 2) s)
    (hu : ∀ s ∈ Icc a b, HasDerivAt u (w s) s)
    (hw : ∀ s ∈ Icc a b, HasDerivAt w (-F₁ (u s) / 2) s)
    (htc : t c = u c) (hvc : v c = w c) :
    EqOn t u (Icc a b) ∧ EqOn v w (Icc a b) := by
  have hh := smooth_autonomous_unique (scalarVectorField_smooth hF) hc
    ((HasDerivAt.continuousOn ht).prodMk (HasDerivAt.continuousOn hv))
    ((HasDerivAt.continuousOn hu).prodMk (HasDerivAt.continuousOn hw))
    (fun s hs => (ht s (Ioo_subset_Icc_self hs)).prodMk (hv s (Ioo_subset_Icc_self hs)))
    (fun s hs => (hu s (Ioo_subset_Icc_self hs)).prodMk (hw s (Ioo_subset_Icc_self hs)))
    (Prod.ext htc hvc)
  exact ⟨fun s hs => congrArg Prod.fst (hh hs), fun s hs => congrArg Prod.snd (hh hs)⟩

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix
open Neck Cometric ReturningCoefficients PassageDynamics Matrix

end

-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix DirectTurning Turning
open Neck Cometric ReturningCoefficients PassageDynamics Matrix DirectTurning Turning

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck

section
open Set Matrix MeasureTheory
open scoped ContDiff Interval Topology Matrix.Norms.Elementwise

end

section
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck
open Set Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

end

end OAI

-- ---- from OAI.Geometry.ConjugatePoints.Passages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem finite_turn_completion {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (ha : t a = 0) (hr : ∀ s ∈ Ioo a b, t s ∈ Ioo (0:ℝ) 1) :
    b ≤ 2*c-a ∧ EqOn (reflectEven c t) t (Icc a b) ∧ EqOn (reflectOdd c v) v (Icc a b) ∧
    reflectEven c t a = 0 ∧ reflectEven c t (2*c-a) = 0 ∧
    (∀ s ∈ Ioo a (2*c-a), reflectEven c t s ∈ Ioo (0:ℝ) 1) := by
  have hd := reflected_closed_equations hF hc ht hv hvc
  have ham : a < min b (2*c-a) := lt_min (hc.1.trans hc.2) (by linarith [hc.1])
  have hcm : c ∈ Ioo a (min b (2*c-a)) := ⟨hc.1,lt_min hc.2 (by linarith [hc.1])⟩
  have hsub : Icc a (min b (2*c-a)) ⊆ Icc a b := Icc_subset_Icc le_rfl (min_le_left _ _)
  have hrsub : Icc a (min b (2*c-a)) ⊆ Icc a (2*c-a) := Icc_subset_Icc le_rfl (min_le_right _ _)
  have he := scalar_equations_unique hF hcm
    (fun s hs => (hd s (hrsub hs)).1) (fun s hs => (hd s (hrsub hs)).2)
    (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs))
    (by simp [reflectEven]) (by simp [reflectOdd])
  have hend : reflectEven c t (2*c-a) = 0 := by
    rw [reflectEven,ite_eq_right (by linarith [hc.1]),show 2*c-(2*c-a) = a by ring,ha]
  have hbL : b ≤ 2*c-a := by
    by_contra hn
    have hLb : 2*c-a < b := lt_of_not_ge hn
    have hs : 2*c-a ∈ Icc a (min b (2*c-a)) := ⟨by linarith [hc.1],by simp [hLb.le]⟩
    have hzero : t (2*c-a) = 0 := (he.1 hs).symm.trans hend
    have hh := (hr (2*c-a) ⟨by linarith [hc.1],hLb⟩).1
    rw [hzero] at hh
    exact lt_irrefl _ hh
  refine ⟨hbL,?_,?_,?_,hend,?_⟩
  · simpa only [min_eq_left hbL] using he.1
  · simpa only [min_eq_left hbL] using he.2
  · simpa [reflectEven,hc.1.le] using ha
  · intro s hs
    unfold reflectEven
    split_ifs with hsc
    · exact hr s ⟨hs.1,hsc.trans_lt hc.2⟩
    · exact hr (2*c-s) ⟨by linarith [hs.2],by linarith [hc.2]⟩
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


theorem solution : type_of% @_root_.OAI.ThreeManifold.PassageDynamics.finite_turn_completion := @_root_.OAI.ThreeManifold.PassageDynamics.finite_turn_completion
