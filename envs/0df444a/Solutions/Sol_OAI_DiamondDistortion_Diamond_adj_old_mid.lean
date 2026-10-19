-- Prove2me | solution 1 for OAI.DiamondDistortion.Diamond.adj_old_mid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:21:18.542141+00:00
-- url     : https://prove2.me/submissions/d799d60d-cf2c-42bc-9615-0154009f03c8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean:L63-L78
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Diamond.adj_old_mid. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph

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

lemma adj_old_mid {n : ℕ} {u : Vertex n} {e : Edge n} {i : ℕ} :
    (graph (n+1)).Adj (Sum.inl u) (Sum.inr (e,i)) ↔
      u=endpoint n e false ∨ u=endpoint n e true := by
  rw [adj_iff]
  constructor
  · rintro ⟨⟨d,j,b⟩,h⟩
    cases b <;> simp [endpoint] at h
    · rcases h with ⟨hu,he,hj⟩
      subst d
      exact Or.inl hu
    · rcases h with ⟨hu,he,hj⟩
      subst d
      exact Or.inr hu
  · rintro (rfl | rfl)
    · exact ⟨(e,i,false),Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨(e,i,true),Or.inr ⟨rfl,rfl⟩⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

end Diamond

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Diamond.adj_old_mid := @_root_.OAI.DiamondDistortion.Diamond.adj_old_mid
