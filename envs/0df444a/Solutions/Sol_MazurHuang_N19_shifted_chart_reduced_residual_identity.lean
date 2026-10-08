-- Prove2me | solution 1 for MazurHuang.N19.shifted_chart_reduced_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:51:17.130728+00:00
-- url     : https://prove2.me/submissions/e0ef5161-76ea-4e7b-b7d4-592ee6a1f1a0

/-
The reduced residual in shifted raw coordinates
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MazurProof.N19SutherlandModels
noncomputable section
def rawF19 (r s : ℚ) : ℚ :=
    r ^ 6
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
      - 6 * r * s ^ 3 + 3 * r * s ^ 2 - r * s + s ^ 6
def chartC7 (A T : ℚ) : ℚ := A^5+A^4*T^5+A^4*T^4-2*A^4*T^3-4*A^4*T^2+A^3*T^6+3*A^3*T^5+4*A^3*T^4+A^3*T^3+A^2*T^8-4*A^2*T^6-2*A^2*T^5+A^2*T^4+2*A*T^9+3*A*T^8-A*T^7-2*A*T^6+T^10+2*T^9+T^8
def chartC6 (A T : ℚ) : ℚ := -A*T*(A^5*T^3+A^5*T^2-2*A^5*T+A^5+A^4*T^5+4*A^4*T^4-8*A^4*T^2+2*A^4*T+4*A^3*T^6+6*A^3*T^5-2*A^3*T^3+3*A^3*T^2+8*A^2*T^7+4*A^2*T^6-10*A^2*T^5-4*A^2*T^4+8*A*T^8+8*A*T^7-A*T^6+2*T^9+2*T^8)
def chartK5 (A T : ℚ) : ℚ := A^4*T^3+4*A^4*T^2+A^4*T-A^4+5*A^3*T^4+7*A^3*T^3-6*A^3*T^2-3*A^3*T+10*A^2*T^5+9*A^2*T^4-3*A^2*T^3+8*A*T^6+5*A*T^5+T^7
def chartK4 (A T : ℚ) : ℚ := 3*A^3*T^3+3*A^3*T^2-3*A^3*T-A^3+9*A^2*T^4+2*A^2*T^3-5*A^2*T^2+11*A*T^5+3*A*T^4+3*T^6
def chartK3 (A T : ℚ) : ℚ := 3*A*T+2*A+3*T^2
def chartReduced (A T F : ℚ) : ℚ := chartC7 A T*F^3+(chartC6 A T+A^2*T*chartK5 A T)*F^2+(-A^4*T*chartK4 A T+A^6*T^2*chartK3 A T)*F-A^8*T^3

end
end MazurProof.N19SutherlandModels

open MazurProof.N19SutherlandModels
theorem solution (A T : ℚ) : chartReduced A T (A*T-A+T^2) = -(T^2-A)^2*rawF19 (A+T+1) (T+1) := by
  simp only [chartReduced,rawF19,chartC7,chartC6,chartK5,chartK4,chartK3]
  ring
