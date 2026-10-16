-- Prove2me | solution 1 for OAI.RandomKSAT.killRatio_succ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T15:29:07.84807+00:00
-- url     : https://prove2.me/submissions/0a5d2ec5-6387-4565-a7fb-de2c1bdeff6a

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/FrozenReplacement.lean:L25-L38
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.killRatio_succ. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement

-- ---- from OAI.Probability.SATVariance.FrozenReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma killRatio_succ {u b s : ℕ} (hsu : s < u) (hsb : s ≤ b) :
    killRatio u b (s + 1) = killRatio u b s * ((b : ℝ) - s) / (2 * (u - s)) := by
  have hu : (0 : ℝ) < u.choose s := by exact_mod_cast Nat.choose_pos hsu.le
  have hu' : (0 : ℝ) < u.choose (s+1) := by exact_mod_cast Nat.choose_pos hsu
  have hus : (0 : ℝ) < (u : ℝ) - s := sub_pos.mpr (by exact_mod_cast hsu)
  have hb := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq b s)
  have hn := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq u s)
  push_cast [Nat.cast_sub hsb] at hb
  push_cast [Nat.cast_sub hsu.le] at hn
  unfold killRatio
  rw [pow_succ]
  apply (div_eq_iff (by positivity : (2 : ℝ)^s * 2 * u.choose (s+1) ≠ 0)).2
  field_simp
  nlinarith [mul_pos hu hus]

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.killRatio_succ := @_root_.OAI.RandomKSAT.killRatio_succ
