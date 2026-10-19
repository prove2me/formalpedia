-- Prove2me | solution 2 for OAI.DiamondDistortion.Diamond.hasDistortion_iff_all_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:27:54.151871+00:00
-- url     : https://prove2.me/submissions/489ad5b7-bc40-4b89-999c-b99b28b0cf44

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Descent.lean:L85-L101
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Diamond.hasDistortion_iff_all_pairs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
import Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps
import Definitions.Def_OAI_Analysis_DiamondDistortion_EquivalentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_UpperFunction
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveBounds
import Definitions.Def_OAI_Analysis_DiamondDistortion_SignCube
import Definitions.Def_OAI_Analysis_DiamondDistortion_HeadProjections

-- ---- from OAI.Analysis.DiamondDistortion.DiamondGraph ----
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Diamond

lemma endpoint_ne (n : ℕ) (e : Edge n) : endpoint n e false ≠ endpoint n e true := by
  cases n with
  | zero => simp [endpoint]
  | succ n =>
    rcases e with ⟨e,i,b⟩
    cases b <;> simp [endpoint]

lemma adj_iff {n : ℕ} {u v : Vertex n} : (graph n).Adj u v ↔
    ∃ e : Edge n, (u=endpoint n e false ∧ v=endpoint n e true) ∨
      (u=endpoint n e true ∧ v=endpoint n e false) := by
  rw [graph,SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_,⟨e,hu,hv⟩ | ⟨e,hv,hu⟩⟩
    · exact ⟨e,Or.inl ⟨hu,hv⟩⟩
    · exact ⟨e,Or.inr ⟨hu,hv⟩⟩
  · rintro ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact ⟨endpoint_ne n e,Or.inl ⟨e,rfl,rfl⟩⟩
    · exact ⟨(endpoint_ne n e).symm,Or.inr ⟨e,rfl,rfl⟩⟩

lemma adj_endpoint (n : ℕ) (e : Edge n) :
    (graph n).Adj (endpoint n e false) (endpoint n e true) :=
  adj_iff.mpr ⟨e,Or.inl ⟨rfl,rfl⟩⟩

lemma distance_edge (n : ℕ) (e : Edge n) :
    distance n (endpoint n e false) (endpoint n e true)=1/(2:ℝ)^n := by
  rw [distance,SimpleGraph.dist_eq_one_iff_adj.mpr (adj_endpoint n e),Nat.cast_one,Nat.cast_ofNat]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

end Diamond

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Descent ----
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace PathModel
-- [generator] trimmed: open RecursiveModel DirectLayers SignCube
open RecursiveModel SignCube
end PathModel

namespace DirectSegmentApplications

end DirectSegmentApplications

namespace Diamond
variable {X : Type*} [NormedAddCommGroup X]
/-- The redundant conventional condition D≥1 follows from the
    all-pairs inequalities alone; thus HasDistortion adds no standing hypothesis. -/
lemma hasDistortion_iff_all_pairs {k : ℕ} (f : Vertex k → X) (D s : ℝ) :
    HasDistortion k f D s ↔ 0 < s ∧ ∀ u v,
      s*distance k u v ≤ ‖f u-f v‖ ∧ ‖f u-f v‖ ≤ D*s*distance k u v := by
  constructor
  · exact fun h => h.2
  · rintro ⟨hs,h⟩
    have hh := (h (endpoint k (baseEdge k) false) (endpoint k (baseEdge k) true)).1.trans
      (h (endpoint k (baseEdge k) false) (endpoint k (baseEdge k) true)).2
    rw [distance_edge] at hh
    have hp : 0 < s*(1/(2:ℝ)^k) := by positivity
    have hD : 1 ≤ D := (mul_le_mul_iff_left₀ hp).mp (by calc
      (1:ℝ)*(s*(1/(2:ℝ)^k)) = s*(1/(2:ℝ)^k) := one_mul _
      _ ≤ D*s*(1/(2:ℝ)^k) := hh
      _ = D*(s*(1/(2:ℝ)^k)) := by ring)
    exact ⟨hD,hs,h⟩
end Diamond

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
open scoped BigOperators Classical Topology
open Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Diamond.hasDistortion_iff_all_pairs := @_root_.OAI.DiamondDistortion.Diamond.hasDistortion_iff_all_pairs
