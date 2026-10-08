-- Prove2me | solution 1 for MazurHuang.N19.optimized_to_diamond_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T19:03:27.59176+00:00
-- url     : https://prove2.me/submissions/52f0e4c2-825e-4be1-8619-64655be3f4b8

/-
Residual identity for the diamond quotient
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

def diamondVNumerator (x y : ℚ) : ℚ :=
    (x + 1) * y ^ 4
      - (x ^ 3 + x ^ 2 + x + 1) * y ^ 3
      - x * (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) * y ^ 2
      + x ^ 2 * (x ^ 4 + 4 * x ^ 3 + 8 * x ^ 2 + 9 * x + 5) * y
      - x ^ 2 * (x ^ 2 + 3 * x + 2)

def diamondU (x y : ℚ) : ℚ :=
  diamondUNumerator x y / x ^ 3

def diamondV (x y : ℚ) : ℚ :=
  diamondVNumerator x y / x ^ 3

def diamondResidual (u v : ℚ) : ℚ :=
  v ^ 2 + v - u ^ 3 - u ^ 2 - u

def diamondCertificate (x y : ℚ) : ℚ :=
    y ^ 7
      - (2 * x ^ 2 + 1) * y ^ 6
      + (x ^ 4 - 4 * x ^ 3 - 6 * x ^ 2 - x) * y ^ 5
      + (6 * x ^ 5 + 13 * x ^ 4 + 11 * x ^ 3 + 9 * x ^ 2) * y ^ 4
      + (-2 * x ^ 7 - 2 * x ^ 6 + 5 * x ^ 5 + 6 * x ^ 4 -
          2 * x ^ 2) * y ^ 3
      + (-4 * x ^ 8 - 19 * x ^ 7 - 38 * x ^ 6 - 41 * x ^ 5 -
          21 * x ^ 4 - x ^ 3) * y ^ 2
      + (x ^ 10 + 6 * x ^ 9 + 17 * x ^ 8 + 29 * x ^ 7 +
          32 * x ^ 6 + 23 * x ^ 5 + 9 * x ^ 4) * y
      - x ^ 8 - 4 * x ^ 7 - 7 * x ^ 6 - 5 * x ^ 5 - x ^ 4
end
end MazurProof.N19SutherlandModels

open MazurProof.N19SutherlandModels
set_option maxHeartbeats 0 in
/-- The explicit quotient coordinates satisfy the genus-one equation on the
optimized order-nineteen locus. -/
theorem solution {x y : ℚ} (hx : x ≠ 0) :
    diamondResidual (diamondU x y) (diamondV x y) =
      -diamondCertificate x y * optF19 x y / x ^ 9 := by
  simp only [diamondResidual, diamondU, diamondV, diamondUNumerator,
    diamondVNumerator, diamondCertificate, optF19]
  field_simp [hx]
  ring

