-- Prove2me | solution 1 for MazurHuang.N19.short_model_two_adic_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:37:12.887977+00:00
-- url     : https://prove2.me/submissions/2b6d5dd6-47ed-410a-8229-bf85ef81f02f

/-
Two-adic congruences on the short conductor-nineteen model
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A finite two-adic certificate for the even-numerator branch of the
integral short model. -/
theorem solution :
    ∀ A : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 → ∀ B : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 → ∀ C : ZMod 32,
      C ^ 2 = A ^ 3 + 4 * A ^ 2 * B ^ 2 + 16 * A * B ^ 4 +
          16 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            2 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            2 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            4 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  decide
