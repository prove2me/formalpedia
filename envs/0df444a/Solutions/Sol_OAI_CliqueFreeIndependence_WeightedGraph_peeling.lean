-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.peeling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:50:49.619849+00:00
-- url     : https://prove2.me/submissions/94b1a718-8ece-45a6-a0da-7df982493f45

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Peeling.lean:L135-L157
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.peeling. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_TriangleState_sum_eq

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
lemma crossMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : 0 ≤ crossMass G w A B := by
  classical
  exact sum_nonneg fun u _ ↦ sum_nonneg fun v _ ↦ by
    split_ifs
    · exact mul_nonneg (hw u) (hw v)
    · exact le_rfl

lemma commonMass_comm (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = commonMass G w v u := by
  classical
  simp [commonMass, inter_comm]

lemma edgeMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    0 ≤ edgeMass G w := div_nonneg (crossMass_nonneg G hw _ _) (by norm_num)

lemma triangleMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) :
    6 * triangleMass G w = ∑ u, w u * triangleAt G w u := by
  unfold triangleMass
  ring

lemma commonMass_eq_sum (G : SimpleGraph V) (w : V → ℝ) (u v : V) :
    commonMass G w u v = ∑ z ∈ neighbors G u, if G.Adj v z then w z else 0 := by
  classical
  unfold commonMass mass
  rw [← filter_mem_eq_inter, sum_filter]
  simp only [mem_neighbors]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.EdgeState ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance] OAI.CliqueFreeIndependence.WeightedGraph.edgeStateDecEq
namespace EdgeState
variable {G : SimpleGraph V}
lemma sum_eq (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst) = ∑ u, ∑ v ∈ neighbors G u, f u v := by
  classical
  change (∑ e : {e : V × V // G.Adj e.1 e.2}, f e.val.1 e.val.2) = _
  rw [← Finset.sum_subtype (univ.filter fun e : V × V ↦ G.Adj e.1 e.2)
    (by simp) (fun e : V × V ↦ f e.1 e.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]

end EdgeState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.TriangleState ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace TriangleState
variable {G : SimpleGraph V}
lemma sum_rotate (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (rotate t)) = ∑ t, weight w t * f t := by
  simpa only [rotateEquiv, Equiv.coe_fn_mk, weight_rotate] using rotateEquiv.sum_comp (fun t ↦ weight w t * f t)

lemma sum_weight (w : V → ℝ) : (∑ t : TriangleState G, weight w t) = 6 * triangleMass G w := by
  simp only [weight]
  rw [sum_eq (fun u v z ↦ w u * w v * w z), triangleMass_eq_sum]
  simp only [triangleAt, commonMass_eq_sum, mul_sum, mul_ite, mul_zero, mul_assoc]

lemma marginal (w : V → ℝ) (f : V → V → ℝ) :
    (∑ t : TriangleState G, weight w t * f t.first t.second) =
      ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst * f e.src e.dst := by
  simp only [weight]
  rw [sum_eq (fun u v z ↦ w u * w v * w z * f u v), EdgeState.sum_eq (fun u v ↦ w u * w v * commonMass G w u v * f u v)]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  rw [commonMass_eq_sum]
  simp only [mul_sum, sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}

lemma sum_flip (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (flip t)) = ∑ t, weight w t * f t := by
  simpa only [flipEquiv, Equiv.coe_fn_mk, weight_flip] using
    flipEquiv.sum_comp (fun t ↦ weight w t * f t)

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}
end TriangleState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Projection ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

variable {U : Type v} [Fintype U]

lemma sum_injective_le {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : J → ℝ) (hg : ∀ j, 0 ≤ g j) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    _ = ∑ j ∈ univ.image f, g j := (sum_image (fun _ _ _ _ h ↦ hf h)).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg hg

namespace EdgeProjection
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

end EdgeProjection

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Peeling ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

open FiniteCoupling
lemma triangle_subgraph_surviving_le {G H : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) :
    (∑ t : TriangleState G, if H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third
      then TriangleState.weight w t else 0) ≤ 6 * triangleMass H w := by
  classical
  let S := {t : TriangleState G // H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third}
  let f : S → TriangleState H := fun t ↦ ⟨t.val.val, t.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : TriangleState H ↦ t.val) hab
  calc
    _ = ∑ t : S, TriangleState.weight w t.val := by
      rw [← sum_filter]
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ t : S, TriangleState.weight w (f t) := rfl
    _ ≤ ∑ t : TriangleState H, TriangleState.weight w t :=
      sum_injective_le f hf _ (fun t ↦ mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _))
    _ = _ := TriangleState.sum_weight _

lemma triangle_deletion_bound {G H : SimpleGraph V} {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) :
    6 * triangleMass G w ≤ 6 * triangleMass H w +
      3 * ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst * bad (H.Adj e.src e.dst) := by
  have ht (t : TriangleState G) : TriangleState.weight w t ≤
      (if H.Adj t.first t.second ∧ H.Adj t.first t.third ∧ H.Adj t.second t.third
        then TriangleState.weight w t else 0) +
      TriangleState.weight w t * (bad (H.Adj t.first t.second) +
        bad (H.Adj t.first t.third) + bad (H.Adj t.second t.third)) := by
    have hn : 0 ≤ TriangleState.weight w t := mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)
    by_cases h1 : H.Adj t.first t.second <;> by_cases h2 : H.Adj t.first t.third <;>
      by_cases h3 : H.Adj t.second t.third <;> simp [bad,h1,h2,h3] <;> linarith
  have hs := sum_le_sum (s := univ) (fun t _ ↦ ht t)
  simp only [sum_add_distrib, mul_add] at hs
  rw [TriangleState.sum_weight] at hs
  have h13 : (∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.third)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.second) :=
    TriangleState.sum_flip w (fun t ↦ bad (H.Adj t.first t.second))
  have h23 : (∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.second t.third)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (H.Adj t.first t.second) :=
    TriangleState.sum_rotate w (fun t ↦ bad (H.Adj t.first t.second))
  rw [h13,h23,TriangleState.marginal w (fun u v ↦ bad (H.Adj u v))] at hs
  have hsurv := triangle_subgraph_surviving_le (G := G) (H := H) hw
  linarith

omit [Fintype V] in
lemma eraseEdge_le (G : SimpleGraph V) (u v : V) : eraseEdge G u v ≤ G := fun _ _ h ↦ h.1

lemma edgeMass_eraseEdge {G : SimpleGraph V} (w : V → ℝ) {u v : V} (huv : G.Adj u v) :
    edgeMass (eraseEdge G u v) w = edgeMass G w - w u * w v := by
  classical
  have hn : u ≠ v := huv.ne
  have heq (a b : V) : (if G.Adj a b then w a * w b else 0) =
      (if (eraseEdge G u v).Adj a b then w a * w b else 0) +
      (if a = u ∧ b = v then w u * w v else 0) +
      (if a = v ∧ b = u then w v * w u else 0) := by
    by_cases h1 : a = u ∧ b = v
    · obtain ⟨rfl,rfl⟩ := h1
      simp [eraseEdge,huv,hn,Ne.symm hn]
    by_cases h2 : a = v ∧ b = u
    · obtain ⟨rfl,rfl⟩ := h2
      simp [eraseEdge,huv.symm,hn,Ne.symm hn]
    simp only [eraseEdge, h1, h2, or_self, not_false_eq_true, and_true, ite_false, add_zero]
  have he : crossMass G w univ univ = crossMass (eraseEdge G u v) w univ univ + 2 * w u * w v := by
    unfold crossMass
    simp_rw [heq,sum_add_distrib]
    simp [ite_and]

    ring
  unfold edgeMass
  linarith

lemma sum_removed_directed {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst * bad ((eraseEdge G u v).Adj e.src e.dst)) =
      f u v + f v u := by
  classical
  have hn : u ≠ v := huv.ne
  have heq (a b : V) : (if G.Adj a b then f a b * bad ((eraseEdge G u v).Adj a b) else 0) =
      (if a = u ∧ b = v then f u v else 0) + (if a = v ∧ b = u then f v u else 0) := by
    by_cases h1 : a = u ∧ b = v
    · obtain ⟨rfl,rfl⟩ := h1
      simp [eraseEdge,huv,hn,Ne.symm hn,bad]
    by_cases h2 : a = v ∧ b = u
    · obtain ⟨rfl,rfl⟩ := h2
      simp [eraseEdge,huv.symm,hn,Ne.symm hn,bad]
    by_cases ha : G.Adj a b <;> simp [eraseEdge,h1,h2,bad,ha]
  rw [EdgeState.sum_eq (fun a b ↦ f a b * bad ((eraseEdge G u v).Adj a b))]
  simp only [neighbors,sum_filter]
  simp_rw [heq,sum_add_distrib,ite_and]
  simp

lemma triangleMass_eraseEdge {G : SimpleGraph V} {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {u v : V} (huv : G.Adj u v) :
    triangleMass G w - w u * w v * commonMass G w u v ≤ triangleMass (eraseEdge G u v) w := by
  have h := triangle_deletion_bound (G := G) (H := eraseEdge G u v) hw
  rw [sum_removed_directed huv (fun a b ↦ w a * w b * commonMass G w a b), commonMass_comm G w v u] at h
  nlinarith only [h]

lemma peeling (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 < w v)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ u v, H.Adj u v → τ ≤ commonMass H w u v) ∧
      triangleMass G w - τ * edgeMass G w ≤ triangleMass H w := by
  classical
  let S : Finset (SimpleGraph V) := univ.filter (fun H ↦ H ≤ G)
  obtain ⟨H,hHS,hmax⟩ := S.exists_max_image (fun H ↦ triangleMass H w - τ * edgeMass H w)
    ⟨G,by simp [S]⟩
  have hHG : H ≤ G := (mem_filter.1 hHS).2
  have hw0 := fun v ↦ (hw v).le
  refine ⟨H,hHG,?_,?_⟩
  · intro u v huv
    by_contra hn
    have hc : commonMass H w u v < τ := lt_of_not_ge hn
    have hle := hmax (eraseEdge H u v) (by simp [S]; exact (eraseEdge_le H u v).trans hHG)
    rw [edgeMass_eraseEdge w huv] at hle
    have ht := triangleMass_eraseEdge hw0 huv
    have hprod : 0 < w u * w v := mul_pos (hw u) (hw v)
    nlinarith [mul_lt_mul_of_pos_left hc hprod]
  · have hle := hmax G (by simp [S])
    have he := edgeMass_nonneg H hw0
    nlinarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq
open FiniteCoupling


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.peeling.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.peeling.{u}
