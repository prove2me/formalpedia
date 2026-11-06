-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.three_circles_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:40.803994+00:00
-- url     : https://prove2.me/submissions/e0eadcf4-f234-4eb1-b7ce-a4f70fa19f08

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl
import Theorems.Thm_OAI_SevenEighths_LogarithmicControl_three_circles

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex
open OAI.SevenEighths OAI.SevenEighths.LogarithmicControl
namespace OAI.SevenEighths.LogarithmicControl
theorem _root_.solution {g : ℂ → ℂ} {c z : ℂ} {r ρ R S A B T : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (hRS : R < S)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B * T)
    (hz : z ∈ closedBall c ρ) :
    ‖g z‖ ≤ A * B * T ^ ((Real.log ρ - Real.log r) /
      (Real.log R - Real.log r)) := by
  let θ := (Real.log ρ - Real.log r) / (Real.log R - Real.log r)
  have hlogR : 0 < Real.log R - Real.log r :=
    sub_pos.mpr (Real.log_lt_log hr (hrρ.trans hρR))
  have hθ0 : 0 ≤ θ := div_nonneg
    (sub_nonneg.mpr (Real.log_le_log hr hrρ.le)) hlogR.le
  have hθ1 : θ ≤ 1 := (div_le_one hlogR).mpr (by
    linarith [Real.log_le_log (hr.trans hrρ) hρR.le])
  have hzn : ‖z - c‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hBp : 0 ≤ B := zero_le_one.trans hB
  have hTp : 0 ≤ T := zero_le_one.trans hT
  have hp1 : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ0
  by_cases hzr : ‖z - c‖ ≤ r
  · have hgz := ha z (by simpa [mem_closedBall, dist_eq_norm] using hzr)
    exact hgz.trans (by nlinarith [mul_le_mul hB hp1 zero_le_one hBp])
  · have hzr' : r ≤ ‖z - c‖ := (lt_of_not_ge hzr).le
    have hzx : 0 < ‖z - c‖ := hr.trans_le hzr'
    let x := (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)
    have hx0 : 0 ≤ x := div_nonneg
      (sub_nonneg.mpr (Real.log_le_log hr hzr')) hlogR.le
    have hxθ : x ≤ θ := (div_le_div_iff_of_pos_right hlogR).mpr (by
      linarith [Real.log_le_log hzx hzn])
    have hx1 : x ≤ 1 := hxθ.trans hθ1
    have h := three_circles hr (hrρ.trans hρR) hRS hg ha hb hzr' (hzn.trans hρR.le)
    have hAa : A ^ (1 - x) ≤ A := by
      simpa using Real.rpow_le_rpow_of_exponent_le hA (show 1 - x ≤ 1 by linarith)
    have hBb : B ^ x ≤ B := by
      simpa using Real.rpow_le_rpow_of_exponent_le hB hx1
    have hTT : T ^ x ≤ T ^ θ := Real.rpow_le_rpow_of_exponent_le hT hxθ
    calc
      ‖g z‖ ≤ A ^ (1 - x) * (B * T) ^ x := h
      _ = A ^ (1 - x) * (B ^ x * T ^ x) := by rw [Real.mul_rpow hBp hTp]
      _ ≤ A * (B * T ^ θ) := mul_le_mul hAa
        (mul_le_mul hBb hTT (Real.rpow_nonneg hTp _) hBp)
        (by positivity) hAp
      _ = A * B * T ^ θ := by ring
end OAI.SevenEighths.LogarithmicControl
