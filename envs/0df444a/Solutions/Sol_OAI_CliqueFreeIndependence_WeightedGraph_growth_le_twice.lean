-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.growth_le_twice
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:51:58.788744+00:00
-- url     : https://prove2.me/submissions/4605ef9e-b3be-48d0-b9a7-777192331160

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/EdgeState.lean:L110-L127
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.growth_le_twice. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_growth_mono

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
end EdgeState

lemma growth_le_twice {x s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) :
    growth x s ≤ 2 * x * (s + Real.exp (-x)) := by
  have hx0 : 0 ≤ x := by linarith
  have hexp := Real.exp_pos (-x)
  have hi (b : ℝ) (hb : Real.exp (-x) ≤ b) : growth x b ≤ 2 * x * b := by
    have hb0 := hexp.trans_le hb
    have hl : -Real.log b ≤ x := by
      have := Real.log_le_log hexp hb
      rw [Real.log_exp] at this
      linarith
    have hmax : max 0 (-Real.log b) ≤ x := max_le hx0 hl
    simp only [growth, one_div, Real.log_inv]
    nlinarith [mul_le_mul_of_nonneg_left hmax hb0.le]
  by_cases h : Real.exp (-x) ≤ s
  · have h' := hi s h
    nlinarith [mul_nonneg hx0 hexp.le]
  · have h' := (growth_mono hx hs hexp.le (le_of_not_ge h)).trans (hi _ le_rfl)
    nlinarith [mul_nonneg hx0 hs]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] OAI.CliqueFreeIndependence.WeightedGraph.edgeStateDecEq


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.growth_le_twice := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.growth_le_twice
