-- Prove2me | solution 1 for GlobalTheory.ZeroBand.zeros_band
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:13:26.694569+00:00
-- url     : https://prove2.me/submissions/5a07c3cc-823f-4782-89e0-955644421adb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteBox
import Theorems.Thm_GlobalTheory_ZeroBand_finite_box
import Theorems.Thm_GlobalTheory_ZeroBand_band_le
import Theorems.Thm_GlobalTheory_ZeroWindow_count_zeros_window


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ZeroBand
namespace GlobalTheory.ZeroBand
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 → {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite ∧ ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)) - ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T) := by
  obtain ⟨C, hC, hcount⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨2 * C, by linarith, ?_⟩
  intro N _ χ hχ u T T' hT hu hT1 hT2
  have hw := hcount N χ hχ
  refine ⟨finite_box _ (fun t => (hw t).1) T, ?_⟩
  refine (band_le (LFunction χ) (fun ρ => analyticOrderNatAt (LFunction χ) ρ)
    (fun t => C * Real.log (N * (|t| + 2))) hw hT hu hT1 hT2).trans ?_
  have hT0 : 0 < T := by linarith
  rw [abs_neg, abs_of_pos hT0]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have huT : T + 2 ≤ u * T := by nlinarith
  have hx : (N : ℝ) * (T + 2) ≤ N * u * T := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left huT (by linarith)
  have hpos : 0 < (N : ℝ) * (T + 2) := by positivity
  have hL1 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) := Real.log_le_log hpos hx
  have h4 : (4 : ℝ) ≤ N * u * T := by nlinarith
  have hL : 1 ≤ Real.log (N * u * T) := by
    have he : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
    exact ((Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith)).le
  have hL2 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) ^ 2 := hL1.trans (by nlinarith)
  have hq : 0 ≤ u / T := div_nonneg (by linarith) hT0.le
  calc (C * Real.log (N * (T + 2)) + C * Real.log (N * (T + 2))) * (u / T)
      = 2 * C * Real.log (N * (T + 2)) * (u / T) := by ring
    _ ≤ 2 * C * Real.log (N * u * T) ^ 2 * (u / T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 (by linarith)) hq
    _ = 2 * C * (u * Real.log (N * u * T) ^ 2 / T) := by ring
end GlobalTheory.ZeroBand
