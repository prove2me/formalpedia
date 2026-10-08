-- Prove2me | solution 1 for MazurHuang.N19.reduced_tate_raw_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:44:57.151534+00:00
-- url     : https://prove2.me/submissions/3a46323d-4daf-4b3c-9c27-51fa49a3d3e8

/-
Raw chart after radial normalization
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib

set_option maxHeartbeats 0
theorem solution (r s : ℚ) : (fun (r c : ℚ) =>
      r^5*(r-1)^10
      - r*(r-1)^9*(20*r^3-15*r^2+6*r-1)*c
      + 3*r*(r-1)^8*(23*r^3-12*r^2+5*r-1)*c^2
      - r*(r-1)^6*(121*r^4-144*r^3+41*r^2-25*r+6)*c^3
      + r*(r-1)^5*(105*r^4-60*r^3-30*r^2-31*r+10)*c^4
      - 3*r*(r-1)^4*(16*r^4+3*r^3-7*r^2-22*r+5)*c^5
      + (r-1)^3*(11*r^5+12*r^4+3*r^3-50*r^2+3*r+1)*c^6
      - r^2*(r-1)^2*(r^3+2*r^2+3*r-21)*c^7
      - 6*r^2*(r-1)*c^8 + r^2*c^9) r (s*(r-1)) = (r-1)^9 * (fun (r s : ℚ) => r ^ 6
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
  ring
