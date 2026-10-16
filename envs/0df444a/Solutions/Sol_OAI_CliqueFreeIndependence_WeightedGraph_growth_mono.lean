-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.growth_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:49:06.762773+00:00
-- url     : https://prove2.me/submissions/a0127db1-6d06-4799-a721-b899c09ee208

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/EdgeState.lean:L84-L108
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.growth_mono. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteEntropy_relTerm_nonneg

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

lemma growth_nonneg {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) : 0 ≤ growth x s :=
  mul_nonneg hs (add_nonneg hx (le_max_left _ _))

lemma growth_small {x s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    growth x s = s * (x - Real.log s) := by
  have hl : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
  simp [growth, Real.log_inv, max_eq_right (neg_nonneg.2 hl), sub_eq_add_neg]

lemma growth_large {x s : ℝ} (hs : 1 ≤ s) : growth x s = s * x := by
  have hl : 0 ≤ Real.log s := Real.log_nonneg hs
  simp [growth, Real.log_inv, max_eq_left (neg_nonpos.2 hl)]

lemma growth_mono {x : ℝ} (hx : 1 ≤ x) : MonotoneOn (growth x) (Set.Ici 0) := by
  intro a ha b hb hab
  change 0 ≤ a at ha
  change 0 ≤ b at hb
  rcases ha.eq_or_lt with ha | ha
  · rw [← ha, growth_zero]
    exact growth_nonneg (by linarith) hb
  have hb0 : 0 < b := ha.trans_le hab
  by_cases hb1 : b ≤ 1
  · rw [growth_small ha (hab.trans hb1), growth_small hb0 hb1]
    have hrel := FiniteEntropy.relTerm_nonneg ha.le hb0.le (fun _ ↦ hb0)
    rw [Real.log_div ha.ne' hb0.ne'] at hrel
    have hlog : Real.log b ≤ 0 := Real.log_nonpos hb0.le hb1
    have hmul := mul_nonneg (sub_nonneg.2 hab) (show 0 ≤ x - 1 - Real.log b by linarith)
    nlinarith
  by_cases ha1 : 1 ≤ a
  · rw [growth_large ha1, growth_large (le_of_not_ge hb1)]
    exact mul_le_mul_of_nonneg_right hab (by linarith)
  · rw [growth_small ha (le_of_not_ge ha1), growth_large (le_of_not_ge hb1)]
    have hrel := FiniteEntropy.relTerm_nonneg ha.le (by norm_num : (0:ℝ) ≤ 1)
      (fun _ ↦ by norm_num)
    simp only [div_one] at hrel
    have hamul := mul_nonneg (sub_nonneg.2 (le_of_not_ge ha1)) (show 0 ≤ x - 1 by linarith)
    have hbmul := mul_nonneg (sub_nonneg.2 (le_of_not_ge hb1)) (show 0 ≤ x by linarith)
    nlinarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] OAI.CliqueFreeIndependence.WeightedGraph.edgeStateDecEq


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.growth_mono := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.growth_mono
