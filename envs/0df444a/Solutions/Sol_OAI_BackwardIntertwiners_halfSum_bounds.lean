-- Prove2me | solution 1 for OAI.BackwardIntertwiners.halfSum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:03:49.047352+00:00
-- url     : https://prove2.me/submissions/82c4c47a-fd37-4825-be79-936d6d5f68ba

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ExplicitWeights.lean:L118-L135
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.halfSum_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights

-- ---- from OAI.Analysis.BackwardIntertwiners.ExplicitWeights ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

lemma halfSum_linear (n : ℕ) :
    (∑ k ∈ Finset.range n, (10:ℝ)*((k:ℝ)+1)) = 5*(n:ℝ)*((n:ℝ)+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma halfSum_bounds {t : ℕ → ℕ} (ht : ResidueBounds t) (n : ℕ) :
    5*(n:ℝ)*((n:ℝ)+1) ≤ halfSum t n ∧
    halfSum t n ≤ 5*(n:ℝ)*((n:ℝ)+1) + 400*(n:ℝ)*Real.sqrt n := by
  have he : halfSum t n = 5*(n:ℝ)*((n:ℝ)+1) +
      ∑ k ∈ Finset.range n, residueCorrection t k := by
    simp only [halfSum, halfExponent, Finset.sum_add_distrib, halfSum_linear]
  rw [he]
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => residueCorrection_nonneg t k))
  · have hh : (∑ k ∈ Finset.range n, residueCorrection t k) ≤
        ∑ _k ∈ Finset.range n, 400*Real.sqrt n := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : (k:ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
      exact (residueCorrection_sqrt_bound ht k).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkn) (by norm_num))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
    nlinarith

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.halfSum_bounds := @_root_.OAI.BackwardIntertwiners.halfSum_bounds
