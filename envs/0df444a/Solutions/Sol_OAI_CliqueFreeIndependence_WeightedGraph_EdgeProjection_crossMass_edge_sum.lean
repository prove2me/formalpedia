-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.EdgeProjection.crossMass_edge_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:08:38.54908+00:00
-- url     : https://prove2.me/submissions/5718d5df-145d-411c-9a25-4a09b1827ed4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Projection.lean:L55-L71
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.EdgeProjection.crossMass_edge_sum. The node keeps its source
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

namespace EdgeProjection
variable {H : SimpleGraph U} {G : SimpleGraph V} {π : U → V}

lemma crossMass_edge_sum (H : SimpleGraph U) (w : U → ℝ) (A B : Finset U) :
    crossMass H w A B =
      ∑ e : EdgeState H, if e.src ∈ A ∧ e.dst ∈ B then w e.src * w e.dst else 0 := by
  classical
  rw [EdgeState.sum_eq (fun a b ↦ if a ∈ A ∧ b ∈ B then w a * w b else 0)]
  have heq : (∑ a, ∑ b ∈ neighbors H a, if a ∈ A ∧ b ∈ B then w a * w b else 0) =
      ∑ a, if a ∈ A then (∑ b, if b ∈ B then if H.Adj a b then w a * w b else 0 else 0) else 0 := by
    apply sum_congr rfl
    intro a _
    by_cases ha : a ∈ A
    · simp only [ha, true_and, ↓reduceIte, neighbors, sum_filter]
      apply sum_congr rfl
      intro b _
      by_cases hb : b ∈ B <;> simp [hb]
    · simp [ha]
  rw [heq]
  simp [crossMass]

end EdgeProjection

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.EdgeProjection
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq


theorem solution.{v} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.EdgeProjection.crossMass_edge_sum.{v} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.EdgeProjection.crossMass_edge_sum.{v}
