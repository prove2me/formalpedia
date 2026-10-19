-- Prove2me | solution 1 for OAI.BackwardIntertwiners.bilateralWeight_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:05:11.47199+00:00
-- url     : https://prove2.me/submissions/20cbeaa2-1adf-47d2-a917-769865ee6de2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/ExplicitWeights.lean:L200-L217
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.bilateralWeight_ratio. The node keeps its source
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

lemma bilateralWeight_ratio (t u : ℕ → ℕ) (j : ℤ) :
    bilateralWeight t u (j+1) / bilateralWeight t u j = bilateralBeta t u j := by
  cases j with
  | ofNat n =>
    change Real.exp (-halfSum t (n+1)) / Real.exp (-halfSum t n) = Real.exp (-halfExponent t n)
    rw [← Real.exp_sub, halfSum_succ]
    congr 1
    ring
  | negSucc n =>
    cases n with
    | zero =>
      change Real.exp (-halfSum t 0) / Real.exp (halfSum u 1) = Real.exp (-halfExponent u 0)
      simp [halfSum_succ, Real.exp_neg]
    | succ n =>
      change Real.exp (halfSum u (n+1)) / Real.exp (halfSum u (n+1+1)) = Real.exp (-halfExponent u (n+1))
      rw [← Real.exp_sub, halfSum_succ u (n+1)]
      congr 1
      ring

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.bilateralWeight_ratio := @_root_.OAI.BackwardIntertwiners.bilateralWeight_ratio
