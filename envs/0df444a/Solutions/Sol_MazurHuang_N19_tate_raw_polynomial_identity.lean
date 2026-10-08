-- Prove2me | solution 1 for MazurHuang.N19.tate_raw_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:56:49.422127+00:00
-- url     : https://prove2.me/submissions/534bb70b-4a32-4260-8c8a-18d6117eb417

/-
The Tate-to-raw polynomial identity
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_MazurHuang_NineteenTatePolynomial
import Theorems.Thm_MazurHuang_N19_tate_radial_polynomial_identity
import Theorems.Thm_MazurHuang_N19_reduced_tate_raw_polynomial_identity

set_option maxHeartbeats 0
theorem solution (r s : ℚ) :
    _root_.MazurProof.TateNFDivision.F19 (r * s * (r - 1)) (s * (r - 1)) =
      s ^ 15 * (r - 1) ^ 24 * (fun (r s : ℚ) => r ^ 6
      - r ^ 5 * s ^ 7 + 11 * r ^ 5 * s ^ 6 - 48 * r ^ 5 * s ^ 5
      + 105 * r ^ 5 * s ^ 4 - 121 * r ^ 5 * s ^ 3
      + 69 * r ^ 5 * s ^ 2 - 20 * r ^ 5 * s - r ^ 5
      - 2 * r ^ 4 * s ^ 7 + 12 * r ^ 4 * s ^ 6 - 9 * r ^ 4 * s ^ 5
      - 60 * r ^ 4 * s ^ 4 + 144 * r ^ 4 * s ^ 3
      - 105 * r ^ 4 * s ^ 2 + 35 * r ^ 4 * s
      - 3 * r ^ 3 * s ^ 7 + 3 * r ^ 3 * s ^ 6 + 21 * r ^ 3 * s ^ 5
      - 30 * r ^ 3 * s ^ 4 - 41 * r ^ 3 * s ^ 3
      + 51 * r ^ 3 * s ^ 2 - 21 * r ^ 3 * s
      + r ^ 2 * s ^ 9 - 6 * r ^ 2 * s ^ 8 + 21 * r ^ 2 * s ^ 7
      - 50 * r ^ 2 * s ^ 6 + 66 * r ^ 2 * s ^ 5
      - 31 * r ^ 2 * s ^ 4 + 25 * r ^ 2 * s ^ 3
      - 18 * r ^ 2 * s ^ 2 + 7 * r ^ 2 * s
      + 3 * r * s ^ 6 - 15 * r * s ^ 5 + 10 * r * s ^ 4
      - 6 * r * s ^ 3 + 3 * r * s ^ 2 - r * s + s ^ 6) r s := by
  have h := MazurHuang.N19.tate_radial_polynomial_identity r (s*(r-1))
  have hq := MazurHuang.N19.reduced_tate_raw_polynomial_identity r s
  rw [hq] at h
  rw [show r*s*(r-1) = r*(s*(r-1)) by ring]
  rw [h]
  have factor (A : ℚ) : (s*(r-1))^15*((r-1)^9*A) = s^15*(r-1)^24*A := by ring
  exact factor _
