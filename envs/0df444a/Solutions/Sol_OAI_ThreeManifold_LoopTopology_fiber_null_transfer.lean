-- Prove2me | solution 1 for OAI.ThreeManifold.LoopTopology.fiber_null_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:30:55.438908+00:00
-- url     : https://prove2.me/submissions/5d8bc868-02ca-441b-adb2-81a1c57635fb

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/FundamentalGroup.lean:L344-L369
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.LoopTopology.fiber_null_transfer. The node keeps its source
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

-- ---- from OAI.Geometry.ConjugatePoints.FundamentalGroup ----
namespace OAI

noncomputable section

/-!
# Fundamental-group relations and nontrivial fiber classes.
-/

section

open Matrix Set Pointwise
open scoped MatrixGroups UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

end ThreeManifold.HyperbolicCore
end

section
open Set Filter Topology ModularGroup
open scoped UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

end ThreeManifold.HyperbolicCore
end

section
open Set Topology
namespace ThreeManifold.LoopTopology
open Path.Homotopic
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y}
lemma map_trans (F : C(X,Y)) {x₀ x₁ x₂ : X}
    (p : Path.Homotopic.Quotient x₀ x₁) (q : Path.Homotopic.Quotient x₁ x₂) :
    (p.trans q).map F = (p.map F).trans (q.map F) := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  induction q using Path.Homotopic.Quotient.ind with | mk q =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_trans q F.continuous)

lemma fiber_null_transfer (F : C(X×Y,Z)) {x₀ x₁ : X} (p : Path x₀ x₁)
    (b : FundamentalGroup Y y) :
    FundamentalGroup.map F (x₀,y) (pair 1 b) = 1 ↔
      FundamentalGroup.map F (x₁,y) (pair 1 b) = 1 := by
  let q : Path.Homotopic.Quotient (x₀,y) (x₁,y) := prod (Path.Homotopic.Quotient.mk p) (.refl y)
  have h : (pair (1 : FundamentalGroup X x₀) b).trans q =
      q.trans (pair (1 : FundamentalGroup X x₁) b) := by
    change (prod (.refl x₀) b).trans (prod (Path.Homotopic.Quotient.mk p) (.refl y)) =
      (prod (Path.Homotopic.Quotient.mk p) (.refl y)).trans (prod (.refl x₁) b)
    rw [comp_prod_eq_prod_comp,comp_prod_eq_prod_comp]
    simp
  have hm := congrArg (fun k : Path.Homotopic.Quotient (x₀,y) (x₁,y) => k.map F) h
  simp only [map_trans] at hm
  change (FundamentalGroup.map F (x₀,y) (pair 1 b)).trans (q.map F) =
    (q.map F).trans (FundamentalGroup.map F (x₁,y) (pair 1 b)) at hm
  constructor
  · intro h0
    rw [h0] at hm
    have he := congrArg (fun k => (q.map F).symm.trans k) hm
    simpa only [FundamentalGroup.one_def,Path.Homotopic.Quotient.refl_trans,← Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans] using he.symm
  · intro h1
    rw [h1] at hm
    have he := congrArg (fun k => k.trans (q.map F).symm) hm
    simpa only [FundamentalGroup.one_def,Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm,Path.Homotopic.Quotient.trans_refl] using he
end ThreeManifold.LoopTopology
end

section
open Set Filter Topology
open scoped UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore LoopTopology

end ThreeManifold.GluedConstruction
end

open Set Filter Topology
namespace ThreeManifold.GluedConstruction
open HyperbolicCore LoopTopology
end ThreeManifold.GluedConstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeManifold OAI.ThreeManifold.LoopTopology
open Set Topology
open Path.Homotopic


theorem solution : type_of% @_root_.OAI.ThreeManifold.LoopTopology.fiber_null_transfer := @_root_.OAI.ThreeManifold.LoopTopology.fiber_null_transfer
