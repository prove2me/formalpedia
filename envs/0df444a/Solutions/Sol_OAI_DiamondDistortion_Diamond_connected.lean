-- Prove2me | solution 1 for OAI.DiamondDistortion.Diamond.connected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:22:47.843747+00:00
-- url     : https://prove2.me/submissions/8f129237-cf7c-4a8c-a7be-2b825ee3c6dc

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean:L111-L135
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Diamond.connected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Theorems.Thm_OAI_DiamondDistortion_Diamond_adj_old_mid

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

lemma replace_adj {n : ℕ} {u v : Vertex n} (h : (graph n).Adj u v) :
    ∃ p : (graph (n+1)).Walk (Sum.inl u) (Sum.inl v), p.length=2 := by
  obtain ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := adj_iff.mp h
  · exact ⟨.cons ((adj_old_mid (i := 0)).mpr (Or.inl rfl))
      (.cons (adj_old_mid.mpr (Or.inr rfl)).symm .nil),rfl⟩
  · exact ⟨.cons ((adj_old_mid (i := 0)).mpr (Or.inr rfl))
      (.cons (adj_old_mid.mpr (Or.inl rfl)).symm .nil),rfl⟩

lemma replace_walk {n : ℕ} {u v : Vertex n} (p : (graph n).Walk u v) :
    ∃ q : (graph (n+1)).Walk (Sum.inl u) (Sum.inl v),q.length=2*p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl⟩
  | cons h p ih =>
    obtain ⟨q,hq⟩ := ih
    obtain ⟨r,hr⟩ := replace_adj h
    refine ⟨r.append q,?_⟩
    rw [SimpleGraph.Walk.length_append,hr,hq,SimpleGraph.Walk.length_cons]
    omega

lemma connected (n : ℕ) : (graph n).Connected := by
  induction n with
  | zero =>
    have : Nonempty (Vertex 0) := ⟨false⟩
    refine ⟨?_⟩
    intro u v
    cases u <;> cases v
    · exact ⟨.nil⟩
    · exact (adj_endpoint 0 ()).reachable
    · exact (adj_endpoint 0 ()).symm.reachable
    · exact ⟨.nil⟩
  | succ n ih =>
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨Sum.inl (endpoint n (baseEdge n) false),?_⟩
    intro v
    cases v with
    | inl v =>
      obtain ⟨p⟩ := ih (endpoint n (baseEdge n) false) v
      obtain ⟨q,hq⟩ := replace_walk p
      exact ⟨q⟩
    | inr v =>
      obtain ⟨e,i⟩ := v
      obtain ⟨p⟩ := ih (endpoint n (baseEdge n) false) (endpoint n e false)
      obtain ⟨q,hq⟩ := replace_walk p
      exact ⟨q.append (adj_old_mid.mpr (Or.inl rfl)).toWalk⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

end Diamond

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Diamond.connected := @_root_.OAI.DiamondDistortion.Diamond.connected
