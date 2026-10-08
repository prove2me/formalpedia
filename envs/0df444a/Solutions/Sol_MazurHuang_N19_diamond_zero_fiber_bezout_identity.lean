-- Prove2me | solution 1 for MazurHuang.N19.diamond_zero_fiber_bezout_identity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T19:05:29.243693+00:00
-- url     : https://prove2.me/submissions/15967b32-888f-45b8-aba7-a31110688953

/-
The zero-fibre Bézout identity
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_MazurHuang_NineteenTatePolynomial

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace MazurProof.N19SutherlandModels
noncomputable section
def optF19 (x y : ℚ) : ℚ :=
    y ^ 5
      - (x ^ 2 + 2) * y ^ 4
      - (2 * x ^ 3 + 2 * x ^ 2 + 2 * x - 1) * y ^ 3
      + (x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 2 * x) * y ^ 2
      - (x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 3 + x ^ 2

def diamondUNumerator (x y : ℚ) : ℚ :=
    y ^ 4
      - (x ^ 2 + 1) * y ^ 3
      - x * (2 * x ^ 2 + 3 * x + 1) * y ^ 2
      + x ^ 2 * (x ^ 3 + 3 * x ^ 2 + 5 * x + 4) * y
      - x ^ 2 * (x + 1)

def zeroFiberBezoutA (x y : ℚ) : ℚ :=
    (x ^ 2 - x - 1) * y ^ 3
      + (-x ^ 4 + x ^ 3 - x) * y ^ 2
      + (-2 * x ^ 5 - x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 7 + 2 * x ^ 6 + 2 * x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2

def zeroFiberBezoutB (x y : ℚ) : ℚ :=
    (-x ^ 2 + x + 1) * y ^ 4
      + (x ^ 4 - x ^ 3 + x ^ 2 - 1) * y ^ 3
      + (2 * x ^ 5 - 3 * x ^ 3 - 4 * x ^ 2 - 2 * x) * y ^ 2
      + (-x ^ 7 - 2 * x ^ 6 - 4 * x ^ 5 - x ^ 4 +
          4 * x ^ 3 + 2 * x ^ 2) * y
      + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2
end
end MazurProof.N19SutherlandModels

open MazurProof.N19SutherlandModels
/-- The optimized equation and the zero horizontal numerator force
`x⁷(x+1)²=0`. -/
theorem solution (x y : ℚ) :
    zeroFiberBezoutA x y * optF19 x y +
        zeroFiberBezoutB x y * diamondUNumerator x y =
      x ^ 7 * (x + 1) ^ 2 := by
  simp only [zeroFiberBezoutA, zeroFiberBezoutB, optF19,
    diamondUNumerator]
  ring
