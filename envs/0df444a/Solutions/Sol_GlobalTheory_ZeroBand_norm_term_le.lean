-- Prove2me | solution 1 for GlobalTheory.ZeroBand.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:19.83877+00:00
-- url     : https://prove2.me/submissions/372a7c74-df20-4b37-8089-b5f71e1a90da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteBox

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
theorem _root_.solution (m : ℕ) {u T : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) {ρ : ℂ} (h1 : ρ.re < 1)
    (h2 : T ≤ |ρ.im|) : ‖(m : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (m : ℝ) * (u / T) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hρ : T ≤ ‖ρ‖ := h2.trans (Complex.abs_im_le_norm ρ)
  have hρ0 : 0 < ‖ρ‖ := hT0.trans_le hρ
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  have hup : u ^ ρ.re ≤ u := by
    calc u ^ ρ.re ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) h1.le
      _ = u := Real.rpow_one u
  calc u ^ ρ.re / ‖ρ‖ ≤ u / ‖ρ‖ := div_le_div_of_nonneg_right hup hρ0.le
    _ ≤ u / T := div_le_div_of_nonneg_left hu0.le hT0 hρ
end GlobalTheory.ZeroBand
