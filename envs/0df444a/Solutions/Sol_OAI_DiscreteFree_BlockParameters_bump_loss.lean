-- Prove2me | solution 1 for OAI.DiscreteFree.BlockParameters.bump_loss
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:23:25.899257+00:00
-- url     : https://prove2.me/submissions/582ae198-82e2-4d5a-9251-85e55804c56b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Parameters.lean:L59-L71
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.BlockParameters.bump_loss. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters

-- ---- from OAI.Analysis.LipschitzFree.Parameters ----
namespace OAI

/-!
# Quantitative block parameters and strict variation bounds
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.BlockParameters

theorem K_pos {p : ℕ} (hp : 1 ≤ p) : 0 < K p := by dsimp [K]; positivity

theorem bump_loss {p : ℕ} (hp : 1 ≤ p) :
    (L p : ℝ)/(K p : ℝ)*(2*(p : ℝ)*(R p : ℝ)+1) ≤ (L p : ℝ)/4 := by
  have hp' : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hR : 0 ≤ (R p : ℝ) := Nat.cast_nonneg _
  have hpR : 0 ≤ (p : ℝ)*(R p : ℝ) := mul_nonneg (by positivity) hR
  have hK : 0 < (K p : ℝ) := by exact_mod_cast K_pos hp
  have hKn : (K p : ℝ) = 10*(p : ℝ)*((R p : ℝ)+1) := by simp [K]
  have hnum : 4*(2*(p : ℝ)*(R p : ℝ)+1) ≤ (K p : ℝ) := by rw [hKn]; nlinarith
  have hL : 0 ≤ (L p : ℝ) := Nat.cast_nonneg _
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hK).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnum hL]

end DiscreteFree.BlockParameters

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.BlockParameters
open scoped BigOperators ENNReal


theorem solution : type_of% @_root_.OAI.DiscreteFree.BlockParameters.bump_loss := @_root_.OAI.DiscreteFree.BlockParameters.bump_loss
