-- Prove2me | solution 1 for MazurHuang.three_dvd_of_threeIsogeny35_cover_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:07:23.561513+00:00
-- url     : https://prove2.me/submissions/d8f47aad-8f61-4d82-9e6c-a4590d384fd0

/-
A ternary cubic form whose integer zeros are divisible by 3.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * a direct proof written for this bundle (glue): 3 | X from the equation, then an 81-case check
    modulo 9.  The source (FLT/Assumptions/MazurProof/RationalPointsX135Descent.lean, n35CoverRho_all_three_dvd) checks the same
    statement by one enumeration of 19683 cases modulo 27, which costs 11 s
  * the published statement
-/
import Mathlib

/-- Reduction modulo 9 of the cubic form after `X = 3 W` and division by 3 (81 cases, evaluated by
the kernel). -/
private theorem cover_mod_nine :
    ∀ Y Z : ZMod 9,
      -Y ^ 3 + 1000 * Z ^ 3 + 24 * Y ^ 2 * Z = 0 →
        ZMod.castHom (show 3 ∣ 9 by norm_num) (ZMod 3) Y = 0 ∧
          ZMod.castHom (show 3 ∣ 9 by norm_num) (ZMod 3) Z = 0 := by
  decide +kernel

theorem solution
    {X Y Z : ℤ}
    (h : X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
      9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z = 0) :
    3 ∣ X ∧ 3 ∣ Y ∧ 3 ∣ Z := by
  have hX : (3 : ℤ) ∣ X := by
    have h3 : (3 : ℤ) ∣ X ^ 3 :=
      ⟨Y ^ 3 - 1000 * Z ^ 3 - X ^ 2 * Y + 3 * X * Y ^ 2 - 8 * X ^ 2 * Z - 24 * Y ^ 2 * Z,
        by linear_combination h⟩
    exact (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow h3
  obtain ⟨W, rfl⟩ := hX
  have hmul : (3 : ℤ) * (9 * W ^ 3 - Y ^ 3 + 1000 * Z ^ 3 + 9 * W ^ 2 * Y - 9 * W * Y ^ 2 +
      72 * W ^ 2 * Z + 24 * Y ^ 2 * Z) = 0 := by
    linear_combination h
  have hred : 9 * W ^ 3 - Y ^ 3 + 1000 * Z ^ 3 + 9 * W ^ 2 * Y - 9 * W * Y ^ 2 +
      72 * W ^ 2 * Z + 24 * Y ^ 2 * Z = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  have hdvd : (9 : ℤ) ∣ -Y ^ 3 + 1000 * Z ^ 3 + 24 * Y ^ 2 * Z :=
    ⟨-(W ^ 3 + W ^ 2 * Y - W * Y ^ 2 + 8 * W ^ 2 * Z), by linear_combination hred⟩
  have h9 : ((-Y ^ 3 + 1000 * Z ^ 3 + 24 * Y ^ 2 * Z : ℤ) : ZMod 9) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr hdvd
  push_cast at h9
  have hc := cover_mod_nine (Y : ZMod 9) (Z : ZMod 9) h9
  refine ⟨dvd_mul_right 3 W, ?_, ?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Y 3).mp
    simpa [ZMod.castHom_apply] using hc.1
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd Z 3).mp
    simpa [ZMod.castHom_apply] using hc.2
