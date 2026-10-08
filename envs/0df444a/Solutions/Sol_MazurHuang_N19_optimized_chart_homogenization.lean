-- Prove2me | solution 1 for MazurHuang.N19.optimized_chart_homogenization
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:47:31.199248+00:00
-- url     : https://prove2.me/submissions/611c7074-6a7f-4a4a-b8a5-063100da9534

/-
Weighted homogenization of the optimized plane equation
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib

set_option maxHeartbeats 0
namespace MazurProof.N19SutherlandModels
noncomputable section
def optF19 (x y : ℚ) : ℚ :=
    y ^ 5
      - (x ^ 2 + 2) * y ^ 4
      - (2 * x ^ 3 + 2 * x ^ 2 + 2 * x - 1) * y ^ 3
      + (x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 2 * x) * y ^ 2
      - (x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 3 + x ^ 2
def chartHomogeneous (T F N A D : ℚ) : ℚ := (fun (T F N A D : ℚ) =>
      T^3*N^5*D^2 - T^2*(T^2*F^2+2*D^2)*N^4*A*D
      + T*(2*T^3*F^3-2*T^2*F^2*D+2*T*F*D^2+D^3)*N^3*A^2*D
      + (-T^5*F^5+3*T^4*F^4*D-7*T^3*F^3*D^2+6*T^2*F^2*D^3-2*T*F*D^4)*N^2*A^3
      + (T^4*F^5-2*T^3*F^4*D+4*T^2*F^3*D^2-3*T*F^2*D^3)*N*A^4*D
      - T*F^3*A^5*D^4 + F^2*A^5*D^5) T F N A D

end
end MazurProof.N19SutherlandModels

open MazurProof.N19SutherlandModels
theorem solution (T F N A D : ℚ) (hA : A ≠ 0) (hD : D ≠ 0) : optF19 (-T*F/D) (T*N/(A*D)) = T^2 * chartHomogeneous T F N A D / (A^5*D^7) := by
  simp only [optF19, chartHomogeneous]
  field_simp [hA,hD]
  ring
