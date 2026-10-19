-- Prove2me | solution 1 for OAI.DiamondDistortion.FiniteAverage.sqrt_pooled
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:18:49.063533+00:00
-- url     : https://prove2.me/submissions/aa28edd5-2268-44b3-b1ba-67f704eaddf2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/FiniteAverage.lean:L163-L177
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.FiniteAverage.sqrt_pooled. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion

-- ---- from OAI.Analysis.DiamondDistortion.FiniteAverage ----
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace FiniteAverage
variable {Ω : Type*} [Fintype Ω]

lemma sqrt_pooled {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 ≤ θ) :
    Real.sqrt η + Real.sqrt (η+2*θ) ≤ 2*Real.sqrt (η+θ) := by
  have h2 : 0 ≤ η+2*θ := by positivity
  have h1 : 0 ≤ η+θ := add_nonneg hη hθ
  have he0 := Real.sq_sqrt hη
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : Real.sqrt η * Real.sqrt (η+2*θ) ≤ η+θ := by
    have he : (Real.sqrt η * Real.sqrt (η+2*θ))^2 = η*(η+2*θ) := by
      rw [mul_pow, he0, he2]
    have hn := mul_nonneg (Real.sqrt_nonneg η) (Real.sqrt_nonneg (η+2*θ))
    nlinarith [sq_nonneg θ]
  apply (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  nlinarith

end FiniteAverage

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.FiniteAverage
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.FiniteAverage.sqrt_pooled := @_root_.OAI.DiamondDistortion.FiniteAverage.sqrt_pooled
