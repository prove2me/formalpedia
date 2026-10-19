-- Prove2me | solution 1 for OAI.DiamondDistortion.Diamond.squared_stretch_loss
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:26:04.384861+00:00
-- url     : https://prove2.me/submissions/4e1475fc-f0ac-4d65-8fe0-f6493624e83e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/DiamondGraph.lean:L275-L311
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Diamond.squared_stretch_loss. The node keeps its source
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
import Theorems.Thm_OAI_DiamondDistortion_Diamond_dist_old

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

lemma not_adj_new {n : ℕ} (u v : Edge n × ℕ) :
    ¬(graph (n+1)).Adj (Sum.inr u) (Sum.inr v) := by
  rintro h
  rcases adj_iff.mp h with ⟨⟨e,i,b⟩,h⟩
  cases b <;> simp [endpoint] at h

lemma dist_siblings (n : ℕ) (e : Edge n) {i j : ℕ} (hij : i ≠ j) :
    (graph (n+1)).dist (Sum.inr (e,i)) (Sum.inr (e,j))=2 := by
  apply le_antisymm
  · exact SimpleGraph.dist_le (.cons (adj_old_mid.mpr (Or.inl rfl)).symm
      (.cons (adj_old_mid.mpr (Or.inl rfl)) .nil))
  · apply Nat.succ_le_of_lt
    apply (connected (n+1)).one_lt_dist_of_ne_of_not_adj
    · intro h
      exact hij (Prod.mk.inj (Sum.inr.inj h)).2
    · exact not_adj_new _ _

lemma distance_old (n : ℕ) (u v : Vertex n) :
    distance (n+1) (Sum.inl u) (Sum.inl v)=distance n u v := by
  rw [distance,distance,dist_old,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  field_simp

lemma distance_edge (n : ℕ) (e : Edge n) :
    distance n (endpoint n e false) (endpoint n e true)=1/(2:ℝ)^n := by
  rw [distance,SimpleGraph.dist_eq_one_iff_adj.mpr (adj_endpoint n e),Nat.cast_one,Nat.cast_ofNat]

lemma distance_siblings (n : ℕ) (e : Edge n) {i j : ℕ} (hij : i ≠ j) :
    distance (n+1) (Sum.inr (e,i)) (Sum.inr (e,j))=2/(2:ℝ)^(n+1) := by
  rw [distance,dist_siblings n e hij,Nat.cast_ofNat]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma slope_plus_deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) :
    slope (fun v => f (Sum.inl v)) e+deviation f e i=slope f (e,i,false) := by
  dsimp [slope,deviation,endpoint]
  rw [pow_succ]
  module

lemma slope_minus_deviation {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i : ℕ) :
    slope (fun v => f (Sum.inl v)) e-deviation f e i=slope f (e,i,true) := by
  dsimp [slope,deviation,endpoint]
  rw [pow_succ]
  module

lemma deviation_sub {n : ℕ} (f : Vertex (n+1) → X) (e : Edge n) (i j : ℕ) :
    deviation f e i-deviation f e j=
      (2:ℝ)^(n+1) • (f (Sum.inr (e,i))-f (Sum.inr (e,j))) := by
  dsimp [deviation]
  rw [pow_succ]
  module

lemma deviation_separated {n : ℕ} (f : Vertex (n+1) → X) {s : ℝ}
    (hl : ∀ u v,s*distance (n+1) u v ≤ ‖f u-f v‖) (e : Edge n)
    {i j : ℕ} (hij : i ≠ j) : 2*s ≤ ‖deviation f e i-deviation f e j‖ := by
  rw [deviation_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(2:ℝ)^(n+1))]
  calc
    2*s = (2:ℝ)^(n+1)*(s*distance (n+1) (Sum.inr (e,i)) (Sum.inr (e,j))) := by
      rw [distance_siblings n e hij]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hl _ _) (by positivity)

/-- Supremum-free squared stretch-loss induction. The bound on all final-edge
    slopes loses s²/4 at each backward step. No maximum child is used. -/
lemma squared_stretch_loss (hX : QuadraticLens X) (k : ℕ) (f : Vertex k → X)
    {s B : ℝ} (hs : 0 < s)
    (hl : ∀ u v,s*distance k u v ≤ ‖f u-f v‖)
    (hb : ∀ e,‖slope f e‖^2 ≤ B) : s^2*(1+(k:ℝ)/4) ≤ B := by
  induction k generalizing B with
  | zero =>
    have h := hl (endpoint 0 () false) (endpoint 0 () true)
    rw [distance_edge] at h
    have h0 := hb ()
    simp only [slope,pow_zero,one_smul,norm_sub_rev] at h0
    norm_num at h ⊢
    nlinarith [sq_nonneg (s-‖f (endpoint 0 () false)-f (endpoint 0 () true)‖)]
  | succ n ih =>
    have hB : 0 ≤ B := (sq_nonneg _).trans (hb (baseEdge (n+1)))
    have hold : ∀ e,‖slope (fun v => f (Sum.inl v)) e‖^2 ≤ B-s^2/4 := by
      intro e
      have hp : ∀ i,‖slope (fun v => f (Sum.inl v)) e+deviation f e i‖ ≤ Real.sqrt B := by
        intro i
        rw [slope_plus_deviation]
        exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hb _)
      have hm : ∀ i,‖slope (fun v => f (Sum.inl v)) e-deviation f e i‖ ≤ Real.sqrt B := by
        intro i
        rw [slope_minus_deviation]
        exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hb _)
      have h := hX (slope (fun v => f (Sum.inl v)) e) (deviation f e)
        (Real.sqrt B) (2*s) (Real.sqrt_nonneg _) (by positivity) hp hm
        (fun _ _ hij => deviation_separated f hl e hij)
      rw [Real.sq_sqrt hB] at h
      nlinarith
    have hlo : ∀ u v,s*distance n u v ≤ ‖f (Sum.inl u)-f (Sum.inl v)‖ := by
      intro u v
      simpa only [distance_old] using hl (Sum.inl u) (Sum.inl v)
    have hind := ih (fun v => f (Sum.inl v)) hlo hold
    push_cast
    linarith

end Diamond

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Diamond
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Diamond.squared_stretch_loss := @_root_.OAI.DiamondDistortion.Diamond.squared_stretch_loss
