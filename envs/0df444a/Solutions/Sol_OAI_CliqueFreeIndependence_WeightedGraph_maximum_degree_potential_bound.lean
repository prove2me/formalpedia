-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:59:40.670037+00:00
-- url     : https://prove2.me/submissions/db41b72b-3b43-461f-a527-aff3bd6536ba

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/IndependentSet.lean:L118-L167
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_potential_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
import Definitions.Def_OAI_Combinatorics_CliqueFree_VertexSplitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Peeling
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_closedNeighbors
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_deletion_cost
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_edge_bound
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_stationary
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_potential_induce

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

lemma neighborMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ neighborMass G w u := mass_nonneg hw _

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Optimizer ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

lemma edgeForm_self (G : SimpleGraph V) (a : V → ℝ) : edgeForm G a a = 2 * edgeMass G a := by
  simp only [edgeForm,edgeMass,crossMass]
  ring

lemma edgeForm_neighbor (G : SimpleGraph V) (a b : V → ℝ) :
    edgeForm G a b = ∑ u, a u * neighborMass G b u := by
  simp only [edgeForm,neighborMass,mass,neighbors,sum_filter,mul_sum,mul_ite,mul_zero]

lemma edgeForm_mono (G : SimpleGraph V) {a b c d : V → ℝ}
    (ha : ∀ v, 0 ≤ a v) (hb : ∀ v, 0 ≤ b v) (hac : ∀ v, a v ≤ c v) (hbd : ∀ v, b v ≤ d v) :
    edgeForm G a b ≤ edgeForm G c d := by
  apply sum_le_sum
  intro u _
  apply sum_le_sum
  intro v _
  split_ifs
  · exact mul_le_mul (hac u) (hbd v) (hb v) ((ha u).trans (hac u))
  · rfl

lemma edgeMass_mono_weight (G : SimpleGraph V) {w q : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hwq : ∀ v, w v ≤ q v) : edgeMass G w ≤ edgeMass G q := by
  have h := edgeForm_mono G hw hw hwq hwq
  rw [edgeForm_self,edgeForm_self] at h
  linarith

lemma continuous_vertexPotential : Continuous vertexPotential := by
  have h := continuous_id.sub Real.continuous_mul_log
  convert h using 1
  ext x
  simp [vertexPotential]
  ring

lemma continuous_edgeMass (G : SimpleGraph V) : Continuous (edgeMass G) := by
  classical
  unfold edgeMass crossMass
  apply Continuous.div_const
  apply continuous_finsetSum
  intro u _
  apply continuous_finsetSum
  intro v _
  split_ifs <;> fun_prop

lemma continuous_potential (G : SimpleGraph V) : Continuous (potential G) := by
  unfold potential
  apply Continuous.sub _ (continuous_edgeMass G)
  exact continuous_finsetSum _ fun v _ ↦ continuous_vertexPotential.comp (continuous_apply v)

lemma vertexPotential_le_one {t : ℝ} (ht : 0 ≤ t) : vertexPotential t ≤ 1 := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [vertexPotential]
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ht) ht.le
  rw [mul_sub,mul_inv_cancel₀ ht.ne'] at h
  unfold vertexPotential
  nlinarith

lemma potential_clamp (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    potential G w ≤ potential G (fun v ↦ min (w v) 1) := by
  have hv (v : V) : vertexPotential (w v) ≤ vertexPotential (min (w v) 1) := by
    by_cases h : w v ≤ 1
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h)]
      simpa [vertexPotential] using vertexPotential_le_one (hw v)
  have hs := sum_le_sum (s := univ) (fun v _ ↦ hv v)
  have he := edgeMass_mono_weight G (fun v ↦ le_min (hw v) zero_le_one) (fun v ↦ min_le_left (w v) 1)
  unfold potential
  linarith

lemma exists_optimizer (G : SimpleGraph V) : ∃ w : V → ℝ, IsOptimizer G w := by
  let S : Set (V → ℝ) := Set.Icc 0 1
  have hS : IsCompact S := isCompact_Icc
  have hne : S.Nonempty := ⟨0,by simp [S]⟩
  obtain ⟨w,hw,hmax⟩ := hS.exists_isMaxOn hne (continuous_potential G).continuousOn
  refine ⟨w,hw.1,?_⟩
  intro q hq
  apply (potential_clamp G hq).trans
  apply hmax
  exact ⟨fun v ↦ le_min (hq v) zero_le_one,fun v ↦ min_le_right (q v) 1⟩

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Deletion ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma mass_closedNeighbors (G : SimpleGraph V) (w : V → ℝ) (v : V) :
    mass w (closedNeighbors G v) = w v + neighborMass G w v := by
  classical
  exact sum_insert (by simp) -- the two expressions are definitionally the sums

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.IndependentSet ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma exists_cheap_vertex {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    [Nonempty V] {Δ B : ℝ} (hΔ : 3 ≤ Δ) (hB : 0 ≤ B)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (htri : triangleMass G w ≤ B * edgeMass G w) :
    ∃ v, mass w (closedNeighbors G v) + edgeMass G (restrict (closedNeighbors G v) w) ≤
      (3+3*B/2) * Real.log Δ := by
  have hwpos (v : V) : 0 < w v := (optimizer_stationary hw v).1
  have hp (v : V) :
      w v * (mass w (closedNeighbors G v) + edgeMass G (restrict (closedNeighbors G v) w)) ≤
      w v + 2 * (w v * neighborMass G w v) + w v * triangleAt G w v / 2 := by
    rw [mass_closedNeighbors,edgeMass_closedNeighbors]
    have hv := (optimizer_stationary hw v).2.2
    have hN := neighborMass_nonneg G hw.1 v
    have hsq : w v * w v ≤ w v := by nlinarith [hw.1 v]
    have hmul := mul_le_mul_of_nonneg_right hsq hN
    nlinarith
  have hsum := sum_le_sum (s := univ) fun v _ ↦ hp v
  simp only [sum_add_distrib, ← mul_sum, ← sum_div] at hsum
  have he := edgeForm_self G w
  rw [edgeForm_neighbor] at he
  have ht : (∑ v, w v * triangleAt G w v) / 2 = 3*triangleMass G w := by
    unfold triangleMass
    ring
  rw [he,ht] at hsum
  have hedge := optimizer_edge_bound hw hΔ hdeg
  have hlog : 1 ≤ Real.log Δ := le_of_lt <| (Real.lt_log_iff_exp_lt (by linarith)).2
    (Real.exp_one_lt_three.trans_le hΔ)
  have hW : 0 ≤ ∑ v, w v := sum_nonneg (fun v _ ↦ hw.1 v)
  have htot : (∑ v, w v * (mass w (closedNeighbors G v) +
      edgeMass G (restrict (closedNeighbors G v) w))) ≤
        ((3+3*B/2)*Real.log Δ) * (∑ v, w v) := by
    have h1 := mul_le_mul_of_nonneg_right hlog hW
    have h2 := mul_le_mul_of_nonneg_left hedge (show 0 ≤ 2+3*B/2 by positivity)
    nlinarith
  by_contra h
  push Not at h
  have hlt (v : V) := mul_lt_mul_of_pos_left (h v) (hwpos v)
  have hh := sum_lt_sum (s := univ) (fun v _ ↦ (hlt v).le)
    ⟨Classical.arbitrary V, mem_univ _, hlt _⟩
  rw [← sum_mul] at hh
  linarith

lemma degree_induce_le (G : SimpleGraph V) (A : Finset V) (v : (A : Set V)) :
    (G.induce (A : Set V)).degree v ≤ G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective
    (fun u : (G.induce (A : Set V)).neighborSet v ↦
      (⟨u.val.val, u.property⟩ : G.neighborSet v))
    (fun u z h ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : G.neighborSet v ↦ (x : V)) h)

omit [Fintype V] in
lemma indepSet_image_induce (G : SimpleGraph V) (A : Finset V) (I : Finset (A : Set V))
    (hI : (G.induce (A : Set V)).IsIndepSet (I : Set (A : Set V))) :
    G.IsIndepSet (I.map ⟨Subtype.val, Subtype.val_injective⟩ : Set V) := by
  classical
  intro a ha b hb hab
  obtain ⟨a',ha',rfl⟩ := mem_map.1 ha
  obtain ⟨b',hb',rfl⟩ := mem_map.1 hb
  exact hI ha' hb' (fun h ↦ hab (congrArg Subtype.val h))

omit [Fintype V] in
lemma indepSet_insert_induce (G : SimpleGraph V) (A : Finset V) (v : V)
    (hA : ∀ b ∈ A, b ≠ v ∧ ¬G.Adj v b)
    (I : Finset (A : Set V))
    (hI : (G.induce (A : Set V)).IsIndepSet (I : Set _)) :
    G.IsIndepSet (↑(insert v (I.map ⟨Subtype.val, Subtype.val_injective⟩) : Finset V) : Set V) ∧
      (insert v (I.map ⟨Subtype.val, Subtype.val_injective⟩)).card = I.card + 1 := by
  classical
  have hnot (b : V) (hb : b ∈ I.map ⟨Subtype.val, Subtype.val_injective⟩) :
      b ≠ v ∧ ¬G.Adj v b := by
    obtain ⟨b',_,rfl⟩ := mem_map.1 hb
    exact hA b' b'.property
  have hi := indepSet_image_induce G A I hI
  constructor
  · intro a ha b hb hab
    change a ∈ insert v (I.map _) at ha
    change b ∈ insert v (I.map _) at hb
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact fun _ ↦ hab rfl
      · exact (hnot b hb).2
    · rcases hb with rfl | hb
      · exact fun h ↦ (hnot a ha).2 h.symm
      · exact hi ha hb hab
  · rw [card_insert_of_notMem (fun h ↦ (hnot v h).1 rfl), card_map]

/-- The maximum-degree induction controls the original variational functional,
not a surrogate objective or a conditional independence bound. -/
lemma maximum_degree_potential_bound (k : ℕ) {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 3 ≤ Δ)
    (htri : ∀ {U : Type u} [Fintype U] (H : SimpleGraph U) (w : U → ℝ),
      IsOptimizer H w → H.CliqueFree (k+2) → triangleMass H w ≤ B * edgeMass H w)
    (G : SimpleGraph V) (hf : G.CliqueFree (k+2)) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      ∀ q : V → ℝ, (∀ v, 0 ≤ q v) →
        potential G q ≤ ((3+3*B/2)*Real.log Δ) * (I.card : ℝ) := by
  classical
  have aux : ∀ n : ℕ, ∀ (U : Type u) [Fintype U], Fintype.card U = n →
      ∀ H : SimpleGraph U, H.CliqueFree (k+2) → (∀ v, (H.degree v : ℝ) ≤ Δ) →
        ∃ I : Finset U, H.IsIndepSet (I : Set U) ∧
          ∀ q : U → ℝ, (∀ v, 0 ≤ q v) →
            potential H q ≤ ((3+3*B/2)*Real.log Δ) * (I.card : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ hn H hfree hdegree
      rcases isEmpty_or_nonempty U with hU | hU
      · let _ := hU
        refine ⟨∅,by simp,?_⟩
        intro q _
        simp [potential,edgeMass,crossMass]
      · let _ := hU
        obtain ⟨w,hw⟩ := exists_optimizer H
        obtain ⟨v,hv⟩ := exists_cheap_vertex hw hΔ hB hdegree (htri H w hw hfree)
        let A : Finset U := (closedNeighbors H v)ᶜ
        have hA : ∀ b ∈ A, b ≠ v ∧ ¬H.Adj v b := by
          intro b hb
          simpa [A] using hb
        have hcard : Fintype.card (A : Set U) < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := v) (by simp [A])
        have hfreeA : (H.induce (A : Set U)).CliqueFree (k+2) :=
          (H.cliqueFree_induce_iff _ _).2 hfree.cliqueFreeOn
        have hdegA (a : (A : Set U)) : ((H.induce (A : Set U)).degree a : ℝ) ≤ Δ :=
          (Nat.cast_le.2 (degree_induce_le H A a)).trans (hdegree a)
        obtain ⟨I,hI,hIp⟩ := ih _ hcard (A : Set U) rfl (H.induce (A : Set U)) hfreeA hdegA
        obtain ⟨hJ,hJcard⟩ := indepSet_insert_induce H A v hA I hI
        refine ⟨insert v (I.map ⟨Subtype.val,Subtype.val_injective⟩),hJ,?_⟩
        intro q hq
        have hres := hIp (fun a ↦ w a) (fun a ↦ hw.1 a)
        rw [potential_induce] at hres
        have hcost := optimizer_deletion_cost hw (closedNeighbors H v)
        change potential H w - potential H (restrict A w) = _ at hcost
        rw [hJcard,Nat.cast_add,Nat.cast_one]
        have hmax := hw.2 q hq
        nlinarith
  exact aux _ V rfl G hf hdeg

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_potential_bound.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_potential_bound.{u}
