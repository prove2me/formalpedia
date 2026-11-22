-- Prove2me | solution 1 for Lean4LPD.two_lt_cZero_of_m_zero_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:48.429962+00:00
-- url     : https://prove2.me/submissions/7000be8f-22db-4d62-9d16-5993b5281c1e

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real
namespace Lean4LPD
theorem _root_.solution {r G B : ℝ} (hr : 0 < r) (hG : 0 < G) (hB : 1 ≤ B) :
    2 < cZero r 0 G B := by
  have h01 : ((1 : ℝ) / (0 + 1)) = 1 := by norm_num
  have hfrac : 1 < (r + 1) / r := by rw [lt_div_iff₀ hr]; linarith
  have harg : (0 : ℝ) < 9 / 4 * ((0 : ℝ) + 1) / (r * G) := by positivity
  have hexp : 1 < exp (9 / 4 * ((0 : ℝ) + 1) / (r * G)) := by
    have h := Real.add_one_le_exp (9 / 4 * ((0 : ℝ) + 1) / (r * G))
    linarith
  -- the first two factors already exceed 1, and the root factor is the whole of `1 + B ≥ 2`
  have hab : 1 < (r + 1) / r * exp (9 / 4 * ((0 : ℝ) + 1) / (r * G)) := by
    nlinarith only [hfrac, hexp]
  have hc : (2 : ℝ) ≤ 1 + B := by linarith
  unfold cZero
  rw [h01, Real.rpow_one]
  nlinarith only [hab, hc, mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr hc)]
end Lean4LPD
