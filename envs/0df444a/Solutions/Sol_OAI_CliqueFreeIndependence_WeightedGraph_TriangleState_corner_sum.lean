-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.corner_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:07:19.53863+00:00
-- url     : https://prove2.me/submissions/eb5182c9-e400-47c7-b7a6-c719165c1310

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/TriangleState.lean:L158-L173
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.corner_sum. The node keeps its source
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
end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}

lemma corner_sum (w : V → ℝ) (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, weight w t * f t.edge12 t.edge13) =
      ∑ e : EdgeState G, ∑ z : EdgeState G,
        if e.src = z.src ∧ G.Adj e.dst z.dst
          then w e.src * w e.dst * w z.dst * f e z else 0 := by
  classical
  calc
    _ = ∑ p : CornerPairs G, w p.val.1.src * w p.val.1.dst * w p.val.2.dst * f p.val.1 p.val.2 :=
      (cornerEquiv.sum_comp (fun p ↦ w p.val.1.src * w p.val.1.dst * w p.val.2.dst * f p.val.1 p.val.2))
    _ = ∑ p : EdgeState G × EdgeState G,
        if p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst
          then w p.1.src * w p.1.dst * w p.2.dst * f p.1 p.2 else 0 := by
      rw [← Finset.sum_subtype (univ.filter fun p : EdgeState G × EdgeState G ↦
          p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst) (by simp)
        (fun p ↦ w p.1.src * w p.1.dst * w p.2.dst * f p.1 p.2), sum_filter]
    _ = _ := Fintype.sum_prod_type _

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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.corner_sum.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.TriangleState.corner_sum.{u}
