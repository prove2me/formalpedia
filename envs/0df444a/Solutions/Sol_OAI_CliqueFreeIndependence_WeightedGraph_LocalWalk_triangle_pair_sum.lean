-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.triangle_pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:33:36.731886+00:00
-- url     : https://prove2.me/submissions/d0ecc3f2-402b-4dfa-bbfa-899b2860add2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/WalkCoupling.lean:L24-L43
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.triangle_pair_sum. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_TriangleState_corner_sum

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
lemma normalizer_pos [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) : 0 < normalizer G w := by
  exact sum_pos (fun e _ ↦ mul_pos (mul_pos (hw _) (hw _)) (hc _ _ e.adj)) univ_nonempty

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.WalkCoupling ----
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
variable {G : SimpleGraph V} {w : V → ℝ}
lemma triangle_pair_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12 t.edge13) =
      normalizer G w * ∑ e, law G w e * ∑ z, transition G w e z * f e z := by
  rw [TriangleState.corner_sum]
  simp only [mul_sum]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro z _
  have he := (hc _ _ e.adj).ne'
  have hZ := (normalizer_pos hw hc).ne'
  by_cases hs : e.src = z.src
  · by_cases ha : G.Adj e.dst z.dst
    · simp only [hs, ha, true_and, ↓reduceIte, transition, law]
      rw [hs] at he
      field_simp
    · simp [hs, ha, transition]
  · simp [hs, transition]

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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.triangle_pair_sum.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.triangle_pair_sum.{u}
