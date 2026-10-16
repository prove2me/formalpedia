-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.potential_induce
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:38:48.932839+00:00
-- url     : https://prove2.me/submissions/f057cb3a-72a6-4fc0-9790-719de50e8bfc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Deletion.lean:L91-L112
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.potential_induce. The node keeps its source
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

lemma potential_induce (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    potential (G.induce (A : Set V)) (fun v ↦ w v) = potential G (restrict A w) := by
  classical
  have he : edgeMass (G.induce (A : Set V)) (fun v ↦ w v) = edgeMass G (restrict A w) := by
    rw [edgeMass_restrict,edgeMass,crossMass]
    congr 1
    simp only [SimpleGraph.induce_adj]
    rw [← Finset.sum_subtype A (by simp)
      (fun u ↦ ∑ v : (A : Set V), if G.Adj u v then w u * w v else 0)]
    unfold crossMass
    apply sum_congr rfl
    intro u hu
    exact (Finset.sum_subtype A (by simp)
      (fun v ↦ if G.Adj u v then w u * w v else 0)).symm
  rw [potential, potential, he]
  congr 1
  rw [← Finset.sum_subtype A (by simp) (fun v ↦ vertexPotential (w v))]
  have hvertex (v : V) : vertexPotential (restrict A w v) =
      if v ∈ A then vertexPotential (w v) else 0 := by
    by_cases hv : v ∈ A <;> simp [restrict,hv,vertexPotential]
  simp_rw [hvertex]
  simp

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.potential_induce.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.potential_induce.{u}
