-- Prove2me | solution 1 for OAI.FixedClauseThreshold.killFraction_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:19:43.539983+00:00
-- url     : https://prove2.me/submissions/c4a5ac5b-38ae-4db4-8524-d1e7d8ab00d6

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Replacement.lean:L56-L76
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.killFraction_le_pow. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Theorems.Thm_OAI_FixedClauseThreshold_killFraction_succ

-- ---- from OAI.Probability.RandomSAT.Replacement ----
namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem sub_ratio_le {b n r : ℕ} (hbn : b ≤ n) (hrb : r ≤ b) (hrn : r < n) :
    ((b - r : ℕ) : ℝ) / ((n - r : ℕ) : ℝ) ≤ (b : ℝ) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr : (0 : ℝ) < (n - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hrn
  rw [div_le_div_iff₀ hnr hn, Nat.cast_sub hrb, Nat.cast_sub (Nat.le_of_lt hrn)]
  have hbn' : (b : ℝ) ≤ n := by exact_mod_cast hbn
  nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (sub_nonneg.mpr hbn')]

theorem killFraction_le_pow {b n r : ℕ} (hbn : b ≤ n) (hrn : r ≤ n)
    (hn : 0 < n) : killFraction b n r ≤ ((b : ℝ) / (2 * n)) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    by_cases hbr : b < r + 1
    · simp only [killFraction, Nat.choose_eq_zero_of_lt hbr, Nat.cast_zero, zero_div]
      positivity
    · have hrb : r ≤ b := by omega
      have ih' := ih (by omega)
      rw [killFraction_succ hrn, pow_succ]
      have hratio := sub_ratio_le hbn hrb (by omega : r < n)
      have hhalf : ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) ≤
          (b : ℝ) / (2 * n) := by
        simpa only [div_mul_eq_div_div_swap] using div_le_div_of_nonneg_right hratio
          (by norm_num : (0 : ℝ) ≤ 2)
      calc
        killFraction b n r * ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) =
            killFraction b n r * (((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ))) := by ring
        _ ≤ ((b : ℝ) / (2 * n)) ^ r * ((b : ℝ) / (2 * n)) :=
          mul_le_mul ih' hhalf (by positivity) (by positivity)

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.killFraction_le_pow := @_root_.OAI.FixedClauseThreshold.killFraction_le_pow
