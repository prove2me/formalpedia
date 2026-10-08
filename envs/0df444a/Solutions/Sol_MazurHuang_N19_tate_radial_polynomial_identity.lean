-- Prove2me | solution 1 for MazurHuang.N19.tate_radial_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:42:34.073254+00:00
-- url     : https://prove2.me/submissions/53984df9-9f40-42ba-83fd-02598ebb86b6

/-
Radial normalization of the Tate polynomial
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_MazurHuang_NineteenTatePolynomial

set_option maxHeartbeats 0
theorem solution (r c : ℚ) : MazurProof.TateNFDivision.F19 (r*c) c = c^15 * (fun (r c : ℚ) =>
      r^5*(r-1)^10
      - r*(r-1)^9*(20*r^3-15*r^2+6*r-1)*c
      + 3*r*(r-1)^8*(23*r^3-12*r^2+5*r-1)*c^2
      - r*(r-1)^6*(121*r^4-144*r^3+41*r^2-25*r+6)*c^3
      + r*(r-1)^5*(105*r^4-60*r^3-30*r^2-31*r+10)*c^4
      - 3*r*(r-1)^4*(16*r^4+3*r^3-7*r^2-22*r+5)*c^5
      + (r-1)^3*(11*r^5+12*r^4+3*r^3-50*r^2+3*r+1)*c^6
      - r^2*(r-1)^2*(r^3+2*r^2+3*r-21)*c^7
      - 6*r^2*(r-1)*c^8 + r^2*c^9) r c := by
  simp only [MazurProof.TateNFDivision.F19]
  ring
