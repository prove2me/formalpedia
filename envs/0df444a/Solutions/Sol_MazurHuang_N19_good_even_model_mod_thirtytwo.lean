-- Prove2me | solution 1 for MazurHuang.N19.good_even_model_mod_thirtytwo
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:13:42.287976+00:00
-- url     : https://prove2.me/submissions/f33b2af2-28f7-4b9d-b8c1-b6ccb2d111a8

/-
Two-adic normalization of the even good-model branch
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem solution :
    ∀ A B C : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 →
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 →
      C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 + 1216 * A * B ^ 4 +
          5776 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by
  have cert :     ∀ A : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) A = 0 → ∀ B : ZMod 32,
      ZMod.castHom (show 2 ∣ 32 by norm_num) (ZMod 2) B ≠ 0 → ∀ C : ZMod 32,
      C ^ 2 = A ^ 3 + 64 * A ^ 2 * B ^ 2 + 1216 * A * B ^ 4 +
          5776 * B ^ 6 →
      ZMod.castHom (show 4 ∣ 32 by norm_num) (ZMod 4) A = 0 ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C -
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B -
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) ∧
        (ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) C +
            8 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) A *
              ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B +
            76 * ZMod.castHom (show 8 ∣ 32 by norm_num) (ZMod 8) B ^ 3 = 0) := by decide
  intro A B C hA hB hC
  exact cert A hA B hB C hC
