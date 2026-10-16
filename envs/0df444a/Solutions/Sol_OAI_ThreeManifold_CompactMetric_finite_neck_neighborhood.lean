-- Prove2me | solution 1 for OAI.ThreeManifold.CompactMetric.finite_neck_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:39:35.853307+00:00
-- url     : https://prove2.me/submissions/45dc3f82-6989-4c75-bc45-65e2e032d4e7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Passages.lean:L677-L697
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.CompactMetric.finite_neck_neighborhood. The node keeps its source
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
lemma interfaceBand_compact : IsCompact interfaceBand := by
  have hc : IsClosed {x : Piece | Real.log 2 ≤ HyperbolicCore.height x.1.1} :=
    isClosed_le continuous_const ((HyperbolicCore.height_continuous.comp continuous_subtype_val).comp continuous_fst)
  convert halfCore_compact.inter_right hc using 1
  ext x
  simp [interfaceBand,halfCore,and_comm]
lemma interfaceBand_subset_extended : interfaceBand ⊆ extendedPiece :=
  fun _ hx => RadialProfile.log_bounds.1.trans_le hx.1
lemma openNeck_subset_bands : openNeck ⊆
    inclusion false '' interfaceBand ∪ inclusion true '' interfaceBand := by
  rintro p ⟨x,hx,rfl⟩
  rcases halfCore_covers x with hl | ⟨ho,hr⟩
  · exact Or.inl ⟨x,⟨((HyperbolicCore.mem_cusp_iff_height (by norm_num : (1:ℝ)<2) x.1.1).mp hx).le,hl⟩,rfl⟩
  · exact Or.inr ⟨(gluingMap ⟨x,ho⟩).1,⟨((HyperbolicCore.mem_cusp_iff_height
      (by norm_num : (1:ℝ)<2) _).mp (gluingMap ⟨x,ho⟩).2).le,hr⟩,
      (TwoGluing.inclusion_transition collar gluingMap ⟨x,ho⟩).symm⟩
lemma closure_openNeck_subset_extended : closure openNeck ⊆ extendedNeck := by
  have hc : IsClosed (inclusion false '' interfaceBand ∪ inclusion true '' interfaceBand) :=
    ((interfaceBand_compact.image (TwoGluing.inclusion_openEmbedding collar gluingMap false).continuous).isClosed).union
      ((interfaceBand_compact.image (TwoGluing.inclusion_openEmbedding collar gluingMap true).continuous).isClosed)
  exact (closure_minimal openNeck_subset_bands hc).trans (by
    rintro p (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩)
    · exact Or.inl ⟨x,interfaceBand_subset_extended hx,rfl⟩
    · exact Or.inr ⟨x,interfaceBand_subset_extended hx,rfl⟩)

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
lemma finite_neck_neighborhood {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ : ℝ → GluedConstruction.Manifold}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ U) (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck) :
    ∃ W : Set ℝ, IsOpen W ∧ OrdConnected W ∧ Icc a b ⊆ W ∧ W ⊆ U ∧
      MapsTo γ W extendedNeck := by
  have hc : MapsTo γ (Icc a b) (closure openNeck) := by
    have hh := (show MapsTo γ (Ioo a b) openNeck from hr).closure_of_continuousOn (by
      rw [closure_Ioo hab.ne]
      exact hγ.1.continuousOn.mono hsub)
    rwa [closure_Ioo hab.ne] at hh
  let P := U ∩ γ ⁻¹' extendedNeck
  have hp : IsOpen P := hγ.1.continuousOn.isOpen_inter_preimage hU extendedNeck_isOpen
  have hcc : Icc a b ⊆ P := fun s hs => ⟨hsub hs,closure_openNeck_subset_extended (hc hs)⟩
  let W := connectedComponentIn P a
  have hW : IsOpen W := hp.connectedComponentIn
  have hcW : IsPreconnected W := isPreconnected_connectedComponentIn
  refine ⟨W,hW,hcW.ordConnected,?_,?_,?_⟩
  · exact isPreconnected_Icc.subset_connectedComponentIn ⟨le_rfl,hab.le⟩ hcc
  · exact (connectedComponentIn_subset P a).trans inter_subset_left
  · exact fun s hs => (connectedComponentIn_subset P a hs).2

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


theorem solution : type_of% @_root_.OAI.ThreeManifold.CompactMetric.finite_neck_neighborhood := @_root_.OAI.ThreeManifold.CompactMetric.finite_neck_neighborhood
