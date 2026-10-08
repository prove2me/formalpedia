-- Prove2me | solution 1 for MazurHuang.N19.raw_to_optimized_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T19:01:14.784136+00:00
-- url     : https://prove2.me/submissions/215d38a4-61f8-4511-81ee-e65da8306789

/-
Residual identity for the raw-to-optimized chart
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_MazurHuang_NineteenTatePolynomial
import Theorems.Thm_MazurHuang_N19_optimized_chart_homogenization
import Theorems.Thm_MazurHuang_N19_raw_chart_normalized_polynomial_identity

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

def optF19 (x y : ℚ) : ℚ :=
    y ^ 5
      - (x ^ 2 + 2) * y ^ 4
      - (2 * x ^ 3 + 2 * x ^ 2 + 2 * x - 1) * y ^ 3
      + (x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 2 * x) * y ^ 2
      - (x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 3 + x ^ 2

def rawDelta (r s : ℚ) : ℚ :=
  r * s ^ 2 - 3 * r * s + r + s ^ 2

def rawXFactor (r s : ℚ) : ℚ :=
  r * s - 2 * r + 1

def rawToOptX (r s : ℚ) : ℚ :=
  -(s - 1) * rawXFactor r s / rawDelta r s

def rawYNumerator (r s : ℚ) : ℚ :=
  r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1

def rawToOptY (r s : ℚ) : ℚ :=
  (s - 1) * rawYNumerator r s / ((r - s) * rawDelta r s)
def chartHomogeneous (T F N A D : ℚ) : ℚ := (fun (T F N A D : ℚ) =>
      T^3*N^5*D^2 - T^2*(T^2*F^2+2*D^2)*N^4*A*D
      + T*(2*T^3*F^3-2*T^2*F^2*D+2*T*F*D^2+D^3)*N^3*A^2*D
      + (-T^5*F^5+3*T^4*F^4*D-7*T^3*F^3*D^2+6*T^2*F^2*D^3-2*T*F*D^4)*N^2*A^3
      + (T^4*F^5-2*T^3*F^4*D+4*T^2*F^3*D^2-3*T*F^2*D^3)*N*A^4*D
      - T*F^3*A^5*D^4 + F^2*A^5*D^5) T F N A D

end
end MazurProof.N19SutherlandModels

open MazurProof.N19SutherlandModels
theorem solution {r s : ℚ}
    (hrs : r - s ≠ 0) (hdelta : rawDelta r s ≠ 0) :
    optF19 (rawToOptX r s) (rawToOptY r s) =
      (s - 1) ^ 2 * (s ^ 2 - r - s + 1) ^ 2 *
          rawXFactor r s ^ 4 /
        ((s - r) ^ 5 * rawDelta r s ^ 7) * rawF19 r s := by
  have hh := MazurHuang.N19.optimized_chart_homogenization (s-1) (rawXFactor r s) (rawYNumerator r s) (r-s) (rawDelta r s) hrs hdelta
  have hn := MazurHuang.N19.raw_chart_normalized_polynomial_identity r s
  change optF19 (rawToOptX r s) (rawToOptY r s) = (s-1)^2 * chartHomogeneous (s-1) (rawXFactor r s) (rawYNumerator r s) (r-s) (rawDelta r s) / ((r-s)^5 * rawDelta r s^7) at hh
  change chartHomogeneous (s-1) (rawXFactor r s) (rawYNumerator r s) (r-s) (rawDelta r s) = -(s^2-r-s+1)^2 * rawXFactor r s^4 * rawF19 r s at hn
  rw [hn] at hh
  rw [hh]
  rw [show (s-r)^5 = -(r-s)^5 by ring]
  field_simp [hrs,hdelta]
