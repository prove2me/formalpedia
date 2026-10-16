-- Prove2me | solution 1 for OAI.ThreeManifold.HyperbolicCore.action_orientation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:09:18.374957+00:00
-- url     : https://prove2.me/submissions/837a74ca-7443-414d-af66-011e5669d204

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Gluing.lean:L1019-L1047
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeManifold.HyperbolicCore.action_orientation. The node keeps its source
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

end ThreeManifold.QuotientConstruction
open Set Filter Topology Manifold Matrix
open scoped ContDiff UpperHalfPlane MatrixGroups
namespace ThreeManifold.HyperbolicCore
lemma action_orientation (g : SL(2,ℤ)) (a b : ℍ) (x : ℂ)
    (hx : x ∈ (chartAt ℂ a).target) :
    0 < LinearMap.det (fderiv ℝ
      (fun y => chartAt ℂ b (g • (chartAt ℂ a).symm y)) x).toLinearMap := by
  let z := (chartAt ℂ a).symm x
  have hz : (z : ℂ) = x := (chartAt ℂ a).right_inv hx
  have he : (fun y => chartAt ℂ b (g • (chartAt ℂ a).symm y)) =ᶠ[nhds x]
      (fun y => ((SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.ofComplex y : ℍ) : ℂ)) := by
    filter_upwards [(chartAt ℂ a).open_target.mem_nhds hx] with y hy
    have hy' : ((chartAt ℂ a).symm y : ℂ) = y := (chartAt ℂ a).right_inv hy
    have ho : UpperHalfPlane.ofComplex y = (chartAt ℂ a).symm y := by
      exact (congrArg UpperHalfPlane.ofComplex hy'.symm).trans
        (UpperHalfPlane.ofComplex_apply _)
    rw [ho]
    rfl
  rw [he.fderiv_eq]
  have hd := (UpperHalfPlane.hasStrictFDerivAt_smul (SpecialLinearGroup.mapGL ℝ g) z).hasFDerivAt
  rw [hz] at hd
  rw [hd.fderiv]
  change 0 < (UpperHalfPlane.smulFDeriv _ x).det
  rw [UpperHalfPlane.det_smulFDeriv]
  have hdet : (SpecialLinearGroup.mapGL ℝ g).det.val = 1 := by
    exact mapGL_det g
  have hn : 0 < ‖UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) x‖ := by
    rw [← hz]
    exact norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero _ z)
  simp only [hdet, one_pow, mul_one, sign_one]
  change (0 : ℝ) < 1 / ‖UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ g) x‖ ^ 4
  positivity

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
open OAI OAI.ThreeManifold OAI.ThreeManifold.HyperbolicCore
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
open Set Filter Topology Manifold Matrix
open scoped ContDiff UpperHalfPlane MatrixGroups


theorem solution : type_of% @_root_.OAI.ThreeManifold.HyperbolicCore.action_orientation := @_root_.OAI.ThreeManifold.HyperbolicCore.action_orientation
