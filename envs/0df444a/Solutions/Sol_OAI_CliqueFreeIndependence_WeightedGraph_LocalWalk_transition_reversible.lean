-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_reversible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:27:06.587999+00:00
-- url     : https://prove2.me/submissions/024e5fce-0a1b-4321-8f78-4edee9c013cd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/LocalWalk.lean:L91-L104
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_reversible. The node keeps its source
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

lemma transition_reversible [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) :
    Reversible (law G w) (transition G w) := by
  classical
  intro e f
  by_cases hsrc : e.src = f.src
  · by_cases hadj : G.Adj e.dst f.dst
    · simp only [transition, hsrc, ite_true, hadj, hadj.symm, law]
      have he := (hc _ _ e.adj).ne'
      have hf := (hc _ _ f.adj).ne'
      rw [hsrc] at he
      field_simp [he, hf, (normalizer_pos hw hc).ne']
    · simp [transition, hsrc, hadj, G.adj_comm f.dst]
  · simp [transition, hsrc, Ne.symm hsrc]

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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_reversible.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.transition_reversible.{u}
