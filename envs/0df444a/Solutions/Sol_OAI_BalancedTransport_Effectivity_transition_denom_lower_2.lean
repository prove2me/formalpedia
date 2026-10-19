-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.transition_denom_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:04:01.081704+00:00
-- url     : https://prove2.me/submissions/a2c57241-b212-468e-ae4b-2ae89f92814f

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/FlatBounds.lean:L99-L116
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.transition_denom_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FlatBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

lemma transition_denom_lower (x : ℝ) :
    1 / 9 ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  have hb : (1 / 9 : ℝ) ≤ expNegInvGlue (1 / 2) := by
    have he : Real.exp (2 : ℝ) < 9 := by
      have hh := Real.exp_one_lt_three
      have hp := Real.exp_pos 1
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    norm_num [expNegInvGlue, Real.exp_neg]
    rw [← one_div]
    apply (le_div_iff₀ (Real.exp_pos (2 : ℝ))).mpr
    linarith
  by_cases hx : 1 / 2 ≤ x
  · exact hb.trans ((expNegInvGlue.monotone hx).trans
      (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  · have hh : 1 / 2 ≤ 1 - x := by linarith
    exact hb.trans ((expNegInvGlue.monotone hh).trans
      (le_add_of_nonneg_left (expNegInvGlue.nonneg _)))

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Polynomial


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.transition_denom_lower := @_root_.OAI.BalancedTransport.Effectivity.transition_denom_lower
