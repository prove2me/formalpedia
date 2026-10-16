-- Prove2me | solution 1 for OAI.ThreeManifold.QuotientConstruction.manifold_quotient_positive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:06:38.349656+00:00
-- url     : https://prove2.me/submissions/7e4f2933-195d-49bd-b97d-2685d4347bac

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Gluing.lean:L950-L986
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.QuotientConstruction.manifold_quotient_positive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing

-- ---- from OAI.Geometry.ConjugatePoints.Gluing ----
namespace OAI

noncomputable section

/-!
# Two-piece gluing, smooth charts, compactness, and orientation.
-/

open Set Manifold Bundle
open scoped ContDiff
open Set Filter Topology Manifold
open scoped ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Set Pointwise
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups

open Set Topology TopologicalSpace CategoryTheory
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]

end ThreeManifold.TwoGluing

open Set Topology TopologicalSpace
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

end ThreeManifold.GluedConstruction
open Set Topology Filter Manifold
open scoped ContDiff
namespace ThreeManifold.CircleConstruction
open QuotientConstruction
end ThreeManifold.CircleConstruction
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff UpperHalfPlane MatrixGroups
namespace ThreeManifold.HyperbolicCore
open QuotientConstruction

end ThreeManifold.HyperbolicCore

open Set Topology Filter TopologicalSpace Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
variable (O : Opens X) (e : O ≃ₜ O)

end ThreeManifold.TwoGluing
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff
namespace ThreeManifold.GluedConstruction
open HyperbolicCore
end ThreeManifold.GluedConstruction

open Set Topology Filter Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.AtlasOrientation

section
variable {E F M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace F N]

end

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
end ThreeManifold.AtlasOrientation

open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.QuotientConstruction
variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace Q]
  [Group G] [MulAction G M] {p : M → Q} (hp : IsQuotientCoveringMap p G)

lemma manifold_quotient_positive {σ : Q → M} (hσ : Function.RightInverse σ p)
    (hact : ∀ k : G, Continuous (fun x : M => k • x))
    (hpos : ∀ (k : G) (a b : M) (x : E), x ∈ (chartAt E a).target →
      k • (chartAt E a).symm x ∈ (chartAt E b).source →
      0 < LinearMap.det (fderiv ℝ
        (fun y => chartAt E b (k • (chartAt E a).symm y)) x).toLinearMap) :
    let := manifoldCharts (E := E) hp hσ
    AtlasOrientation.Positive (E := E) (M := Q) := by
  let := manifoldCharts (E := E) hp hσ
  change AtlasOrientation.Positive (E := E) (M := Q)
  intro c d hc hd x hx hy
  obtain ⟨a,rfl⟩ := hc
  obtain ⟨b,rfl⟩ := hd
  let ca := chartAt E (σ a)
  let cb := chartAt E (σ b)
  let la := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ a)
  let lb := hp.isCoveringMap.isLocalHomeomorph.localInverseAt (σ b)
  have ha : x ∈ ca.target := hx.1
  have hb : p (ca.symm x) ∈ lb.source := by
    simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.coe_trans_symm,
      hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm, Function.comp_def] using hy.1
  have hb' : lb (p (ca.symm x)) ∈ cb.source := by
    simpa only [OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.coe_trans_symm,
      hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm, Function.comp_def, mem_preimage] using hy.2
  obtain ⟨k,hk⟩ := cover_lift_eventuallyEq_action hp hact (σ b) hb
  have hks : k • ca.symm x ∈ cb.source := hk.eq_of_nhds ▸ hb'
  have he : ((lb.trans cb) ∘ (la.trans ca).symm) =ᶠ[nhds x]
      (fun y => cb (k • ca.symm y)) := by
    have hh := hk.comp_tendsto (ca.symm.continuousAt ha)
    filter_upwards [hh] with y hy
    simp only [la, lb, OpenPartialHomeomorph.coe_trans,OpenPartialHomeomorph.coe_trans_symm,
      hp.isCoveringMap.isLocalHomeomorph.localInverseAt_symm,Function.comp_def]
    exact congrArg cb hy
  rw [he.fderiv_eq]
  exact hpos k (σ a) (σ b) x ha hks

end ThreeManifold.QuotientConstruction
open Set Filter Topology Manifold Matrix
open scoped ContDiff UpperHalfPlane MatrixGroups
namespace ThreeManifold.HyperbolicCore
end ThreeManifold.HyperbolicCore
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CircleConstruction
end ThreeManifold.CircleConstruction
namespace ThreeManifold.GluedConstruction
end ThreeManifold.GluedConstruction

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.HyperbolicCore
end ThreeManifold.HyperbolicCore
namespace ThreeManifold.CircleConstruction
end ThreeManifold.CircleConstruction
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

end ThreeManifold.GluedConstruction

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore

end ThreeManifold.GluedConstruction

open Set Filter Topology
namespace ThreeManifold.Coordinates3

end ThreeManifold.Coordinates3

open Set Filter Topology Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore Coordinates3 TwoGluing

end ThreeManifold.GluedConstruction

open Set Topology Filter Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.Rechart

section
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [ChartedSpace E M]
variable (e : E ≃L[ℝ] F)

variable [IsManifold 𝓘(ℝ,E) ∞ M]

end

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
end ThreeManifold.Rechart

open Set Filter Topology TopologicalSpace Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X : Type} [TopologicalSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ChartedSpace E X] [IsManifold 𝓘(ℝ,E) ∞ X]
variable (O : Opens X) (e : O ≃ₜ O)
end ThreeManifold.TwoGluing
open Set Filter Topology Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.GluedConstruction
end ThreeManifold.GluedConstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.QuotientConstruction
open Set Manifold Bundle
open scoped ContDiff
open Set Filter Topology Manifold
open scoped ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Set Pointwise
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix
open scoped MatrixGroups UpperHalfPlane
open Matrix Set Manifold
open scoped MatrixGroups UpperHalfPlane ContDiff
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology Filter
open scoped UpperHalfPlane MatrixGroups
open Set Topology TopologicalSpace CategoryTheory
open Set Topology TopologicalSpace
open Set Topology Filter Manifold
open scoped ContDiff
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff UpperHalfPlane MatrixGroups
open Set Topology Filter TopologicalSpace Manifold IsManifold
open scoped ContDiff
open Set Topology Filter Manifold TopologicalSpace
open scoped ContDiff
open Set Topology Filter Manifold IsManifold
open scoped ContDiff
open Set Filter Topology Manifold IsManifold
open scoped ContDiff


theorem solution : type_of% @_root_.OAI.ThreeManifold.QuotientConstruction.manifold_quotient_positive := @_root_.OAI.ThreeManifold.QuotientConstruction.manifold_quotient_positive
