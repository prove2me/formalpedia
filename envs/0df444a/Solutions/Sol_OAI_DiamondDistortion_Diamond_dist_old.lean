-- Prove2me | solution 1 for OAI.DiamondDistortion.Diamond.dist_old
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:24:23.755895+00:00
-- url     : https://prove2.me/submissions/688d42e5-c7b3-4044-b3be-8f260ff016a6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean:L177-L190
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Diamond.dist_old. The node keeps its source
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
import Theorems.Thm_OAI_DiamondDistortion_Diamond_connected

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

lemma potential_walk {V : Type*} {G : SimpleGraph V} (φ : V → ℝ)
    (hφ : ∀ u v,G.Adj u v → |φ u-φ v| ≤ 1) {u v : V} (p : G.Walk u v) :
    |φ u-φ v| ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have ht : |φ u-φ w| ≤ |φ u-φ v|+|φ v-φ w| := abs_sub_le _ _ _
    have h := hφ u v h
    simp only [SimpleGraph.Walk.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

lemma distance_potential (n : ℕ) (a : Vertex n) :
    ∀ u v,(graph n).Adj u v →
      |((graph n).dist a u : ℝ)-(graph n).dist a v| ≤ 1 := by
  intro u v h
  have huv := (connected n).dist_triangle (u := a) (v := u) (w := v)
  have hvu := (connected n).dist_triangle (u := a) (v := v) (w := u)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at huv
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h.symm] at hvu
  have hu : ((graph n).dist a v : ℝ) ≤ (graph n).dist a u+1 := by exact_mod_cast huv
  have hv : ((graph n).dist a u : ℝ) ≤ (graph n).dist a v+1 := by exact_mod_cast hvu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma extendPotential_adj {n : ℕ} (φ : Vertex n → ℝ)
    (hφ : ∀ u v,(graph n).Adj u v → |φ u-φ v| ≤ 1) :
    ∀ u v,(graph (n+1)).Adj u v → |extendPotential φ u-extendPotential φ v| ≤ 1 := by
  intro u v h
  rcases adj_iff.mp h with ⟨⟨e,i,b⟩,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ <;>
    cases b <;> dsimp [endpoint,extendPotential]
  all_goals
    have h := hφ _ _ (adj_endpoint n e)
    have ha := (abs_le.mp h).1
    have hb := (abs_le.mp h).2
    apply abs_le.mpr
    constructor <;> linarith

/-- One subdivision doubles unweighted old-vertex distances. -/
lemma dist_old (n : ℕ) (u v : Vertex n) :
    (graph (n+1)).dist (Sum.inl u) (Sum.inl v)=2*(graph n).dist u v := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := (connected n).exists_walk_length_eq_dist u v
    obtain ⟨q,hq⟩ := replace_walk p
    exact (SimpleGraph.dist_le q).trans (by rw [hq,hp])
  · obtain ⟨p,hp⟩ := (connected (n+1)).exists_walk_length_eq_dist (Sum.inl u) (Sum.inl v)
    have h := potential_walk (extendPotential (fun w => ((graph n).dist u w : ℝ)))
      (extendPotential_adj _ (distance_potential n u)) p
    rw [hp] at h
    simp only [extendPotential,SimpleGraph.dist_self,Nat.cast_zero,mul_zero,zero_sub,abs_neg] at h
    rw [abs_of_nonneg (by positivity)] at h
    exact_mod_cast h

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

end Diamond

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Diamond.dist_old := @_root_.OAI.DiamondDistortion.Diamond.dist_old
