-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_closedNeighbors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:34:54.529776+00:00
-- url     : https://prove2.me/submissions/24ddd5a4-77bd-4e17-9187-6232d0d06257

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Deletion.lean:L33-L60
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_closedNeighbors. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_edgeMass_restrict

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma crossMass_factor (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = ∑ u ∈ A, w u * mass w (B ∩ neighbors G u) := by
  classical
  unfold crossMass mass
  apply sum_congr rfl
  intro u _
  rw [← filter_mem_eq_inter]
  simp only [sum_filter, mem_neighbors, mul_sum, mul_ite, mul_zero]

lemma crossMass_neighbors (G : SimpleGraph V) (w : V → ℝ)
    (A : Finset V) (v : V) :
    crossMass G w A (neighbors G v) = ∑ u ∈ A, w u * commonMass G w u v := by
  rw [crossMass_factor]
  simp only [commonMass, inter_comm]

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

 -- the two expressions are definitionally the sums

lemma edgeMass_closedNeighbors (G : SimpleGraph V) (w : V → ℝ) (v : V) :
    edgeMass G (restrict (closedNeighbors G v) w) =
      w v * neighborMass G w v + triangleAt G w v / 2 := by
  classical
  have hv : v ∉ neighbors G v := by simp
  have hs : (∑ u ∈ neighbors G v, if G.Adj v u then w v * w u else 0) =
      w v * neighborMass G w v := by
    rw [neighborMass, mass, mul_sum]
    apply sum_congr rfl
    intro u hu
    simp [(mem_neighbors G v u).1 hu]
  have hs' : (∑ u ∈ neighbors G v, if G.Adj u v then w u * w v else 0) =
      w v * neighborMass G w v := by
    simp_rw [G.adj_comm, mul_comm]
    exact hs
  have ht : crossMass G w (neighbors G v) (neighbors G v) = triangleAt G w v := by
    simpa [triangleAt, commonMass, inter_comm] using crossMass_neighbors G w (neighbors G v) v
  rw [edgeMass_restrict]
  have he : crossMass G w (closedNeighbors G v) (closedNeighbors G v) =
      2 * (w v * neighborMass G w v) + triangleAt G w v := by
    simp only [closedNeighbors, crossMass, sum_insert hv, G.irrefl, ite_false, zero_add,
      sum_add_distrib]
    rw [hs,hs']
    change _ + (_ + crossMass G w (neighbors G v) (neighbors G v)) = _
    rw [ht]
    ring
  rw [he]
  ring

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_closedNeighbors.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.edgeMass_closedNeighbors.{u}
