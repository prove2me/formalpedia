-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:05:37.458519+00:00
-- url     : https://prove2.me/submissions/ec366a43-8c94-49bb-8dea-bef7f1c8d32c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/TriangleState.lean:L82-L101
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.sum_eq. The node keeps its source
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
lemma sum_eq (f : V → V → V → ℝ) :
    (∑ t : TriangleState G, f t.first t.second t.third) =
      ∑ u, ∑ v ∈ neighbors G u, ∑ z ∈ neighbors G u,
        if G.Adj v z then f u v z else 0 := by
  classical
  change (∑ t : {t : V × V × V // _}, f t.val.1 t.val.2.1 t.val.2.2) = _
  rw [← Finset.sum_subtype (univ.filter fun t : V × V × V ↦
    G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2)
    (by simp) (fun t : V × V × V ↦ f t.1 t.2.1 t.2.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases huv : G.Adj u v
  · simp only [huv, true_and, ↓reduceIte]
    apply sum_congr rfl
    intro z _
    by_cases huz : G.Adj u z <;> simp [huz]
  · simp [huv]

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}
end TriangleState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.TriangleState
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.sum_eq.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.sum_eq.{u}
