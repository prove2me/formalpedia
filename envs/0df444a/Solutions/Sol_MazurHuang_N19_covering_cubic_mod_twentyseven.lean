-- Prove2me | solution 1 for MazurHuang.N19.covering_cubic_mod_twentyseven
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:15:22.350987+00:00
-- url     : https://prove2.me/submissions/d4c963b6-dec8-479d-a233-464831302711

/-
The cubic descent cover has no primitive zero modulo twenty-seven
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem solution :
    ∀ X Y Z : ZMod 27,
      X ^ 3 - 3 * Y ^ 3 + 24 * Z ^ 3 + 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 48 * X ^ 2 * Z + 144 * Y ^ 2 * Z = 0 →
        ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Y = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Z = 0 := by
  have cert :     ∀ X : ZMod 27, ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 → ∀ Y Z : ZMod 27,
      X ^ 3 - 3 * Y ^ 3 + 24 * Z ^ 3 + 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 48 * X ^ 2 * Z + 144 * Y ^ 2 * Z = 0 →
        ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Y = 0 ∧
          ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) Z = 0 := by decide
  intro X Y Z h
  have hm := congrArg (ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3)) h
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero] at hm
  have cert3 : ∀ a b c : ZMod 3,
      a ^ 3 - 3 * b ^ 3 + 24 * c ^ 3 + 3 * a ^ 2 * b -
        9 * a * b ^ 2 + 48 * a ^ 2 * c + 144 * b ^ 2 * c = 0 → a = 0 := by decide
  have hx : ZMod.castHom (show 3 ∣ 27 by norm_num) (ZMod 3) X = 0 :=
    cert3 _ _ _ hm
  exact cert X hx Y Z h
