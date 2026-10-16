-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:25:47.208478+00:00
-- url     : https://prove2.me/submissions/38630283-648f-45e4-841c-7ec706aae591

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/LocalWalk.lean:L57-L75
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_stochastic. The node keeps its source
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

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

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

lemma sum_fiber (u : V) (f : V → ℝ) :
    (∑ e : EdgeState G, if e.src = u then f e.dst else 0) = ∑ v ∈ neighbors G u, f v := by
  classical
  rw [sum_eq (fun a b ↦ if a = u then f b else 0)]
  simp

lemma sum_fiber' (u : V) (f : V → ℝ) :
    (∑ e : EdgeState G, if u = e.src then f e.dst else 0) = ∑ v ∈ neighbors G u, f v := by
  classical
  simpa only [eq_comm] using sum_fiber u f

end EdgeState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.LocalWalk ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable (G : SimpleGraph V) (w : V → ℝ)

variable {G w}
lemma transition_stochastic (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : Stochastic (transition G w) := by
  classical
  intro e
  constructor
  · intro f
    dsimp [transition]
    split_ifs
    · exact (div_pos (hw _) (hc _ _ e.adj)).le
    all_goals exact le_rfl
  · change (∑ f : EdgeState G, if e.src = f.src then
        (if G.Adj e.dst f.dst then w f.dst / commonMass G w e.src e.dst else 0) else 0) = 1
    rw [EdgeState.sum_fiber' e.src (fun z ↦
      if G.Adj e.dst z then w z / commonMass G w e.src e.dst else 0)]
    have hid (z : V) : (if G.Adj e.dst z then w z / commonMass G w e.src e.dst else 0) =
        (if G.Adj e.dst z then w z else 0) / commonMass G w e.src e.dst := by
      split_ifs <;> simp
    simp_rw [hid]
    rw [← sum_div, ← commonMass_eq_sum, div_self (hc _ _ e.adj).ne']

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq
open FiniteEntropy FiniteKernel


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_stochastic.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_stochastic.{u}
