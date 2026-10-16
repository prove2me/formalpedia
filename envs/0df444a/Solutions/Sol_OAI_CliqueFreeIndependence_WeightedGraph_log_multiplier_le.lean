-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.log_multiplier_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:59:54.915323+00:00
-- url     : https://prove2.me/submissions/1ecaa144-d73c-435e-81a9-5370d5030b0a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/DisjointCross.lean:L18-L48
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.log_multiplier_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.CliqueFree.SparseMultipliers ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

lemma multiplierBound_pos (k : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < multiplierBound k ε := by
  unfold multiplierBound
  positivity

lemma multiplierBound_ge_one (k : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ multiplierBound k ε := by
  unfold multiplierBound
  apply (le_div_iff₀ (pow_pos hε k)).2
  simpa using (pow_le_one₀ hε.le hε1 : ε^k ≤ 1).trans (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.DisjointCross ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

/-- A logarithm estimate with `log 2 ≤ 1` already applied. -/
lemma log_multiplier_le (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    Real.log (1 + Real.exp (4*x) * multiplierBound k (Real.exp (-8*x))) ≤
      (5 + 10*(k:ℝ) + (k:ℝ)^2)*x := by
  have hx0 : 0 ≤ x := by linarith
  have hε : Real.exp (-8*x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hb := multiplierBound_ge_one k (Real.exp_pos _) hε
  have he : 1 ≤ Real.exp (4*x) := Real.one_le_exp_iff.2 (by linarith)
  have hprod : 1 ≤ Real.exp (4*x) * multiplierBound k (Real.exp (-8*x)) :=
    one_le_mul_of_one_le_of_one_le he hb
  have hm := Real.log_le_log (by positivity : 0 < 1 + Real.exp (4*x) *
      multiplierBound k (Real.exp (-8*x)))
    (show 1 + Real.exp (4*x) * multiplierBound k (Real.exp (-8*x)) ≤
      2 * (Real.exp (4*x) * multiplierBound k (Real.exp (-8*x))) by linarith)
  have hbpos := multiplierBound_pos k (Real.exp_pos (-8*x))
  have hlogb : Real.log (multiplierBound k (Real.exp (-8*x))) =
      (((k:ℝ)+2)*k)*Real.log 2 + 8*(k:ℝ)*x := by
    unfold multiplierBound
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_exp]
    push_cast
    ring
  rw [Real.log_mul (by norm_num) (mul_pos (Real.exp_pos _) hbpos).ne',
    Real.log_mul (Real.exp_ne_zero _) hbpos.ne', Real.log_exp,hlogb] at hm
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ (1 + ((k:ℝ)+2)*k) := by positivity
  have haux := mul_le_mul_of_nonneg_left hlog2 hc
  have hxaux := mul_le_mul_of_nonneg_left hx hc
  nlinarith

end CliqueFreeIndependence.WeightedGraph

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open Lottery


theorem solution : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.log_multiplier_le := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.log_multiplier_le
