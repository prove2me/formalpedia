-- Prove2me | solution 1 for MazurHuang.N19.raw_chart_shifted_coordinate_relations
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:53:19.442974+00:00
-- url     : https://prove2.me/submissions/d583ea15-8695-4e15-ac01-864d9c2d4151

/-
Relations for the shifted raw-chart coordinates
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib

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

def rawDelta (r s : ℚ) : ℚ :=
  r * s ^ 2 - 3 * r * s + r + s ^ 2

def rawXFactor (r s : ℚ) : ℚ :=
  r * s - 2 * r + 1

def rawYNumerator (r s : ℚ) : ℚ :=
  r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1
end
end MazurProof.N19SutherlandModels

open MazurProof.N19SutherlandModels
theorem solution (r s : ℚ) : rawYNumerator r s = ((r-s)+(s-1))*rawXFactor r s-(r-s)^2 ∧ rawDelta r s = ((s-1)+1)*rawXFactor r s-(s-1)*(r-s) ∧ (r-s)*(s-1)-(r-s)+(s-1)^2 = rawXFactor r s ∧ (s-1)^2-(r-s) = s^2-r-s+1 := by
  simp only [rawYNumerator,rawDelta,rawXFactor]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring
