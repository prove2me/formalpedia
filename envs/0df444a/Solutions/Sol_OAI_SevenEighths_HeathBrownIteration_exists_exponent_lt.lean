-- Prove2me | solution 1 for OAI.SevenEighths.HeathBrownIteration.exists_exponent_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:03:06.105193+00:00
-- url     : https://prove2.me/submissions/b8cb67a1-17be-4d91-9ebf-78e850179817

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_HeathBrownIteration
import Theorems.Thm_OAI_SevenEighths_HeathBrownIteration_exponent_error_le

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.HeathBrownIteration
noncomputable section
namespace OAI.SevenEighths.HeathBrownIteration
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, exponent n < 4 / 3 + ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (2 / 3 : ℝ) ^ (n + 1) ≤ (2 / 3 : ℝ) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have he := exponent_error_le n
  linarith
end OAI.SevenEighths.HeathBrownIteration
