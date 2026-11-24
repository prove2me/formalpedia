-- Prove2me | solution 1 for GlobalTheory.tprod_inv_one_sub_pos_and_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:47.371038+00:00
-- url     : https://prove2.me/submissions/87826d26-8dee-40e7-b5b3-bdb2be26134f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsLogInvOneSubLeTwoMulAbs
import Theorems.Thm_GlobalTheory_abs_log_inv_one_sub_le_two_mul_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {ι : Type} (y : ι → ℝ) (B : ℝ), (∀ a, |y a| ≤ 1 / 2) → Summable (fun a => |y a|) →
      ∑' a, |y a| ≤ B →
      0 < ∏' a, (1 - y a)⁻¹ ∧ ∏' a, (1 - y a)⁻¹ ≤ Real.exp (2 * B) := by
  intro ι y B hy hs hB
  have hb : ∀ a, |Real.log (1 - y a)⁻¹| ≤ 2 * |y a| :=
    fun a => abs_log_inv_one_sub_le_two_mul_abs _ (hy a)
  have hs2 : Summable (fun a => 2 * |y a|) := hs.mul_left 2
  have hsl : Summable (fun a => Real.log (1 - y a)⁻¹) :=
    Summable.of_norm_bounded hs2 (fun a => by simpa only [Real.norm_eq_abs] using hb a)
  have hp := hsl.hasSum.rexp
  have he : (Real.exp ∘ fun a => Real.log (1 - y a)⁻¹) = fun a => (1 - y a)⁻¹ := by
    funext a
    have h1 := le_abs_self (y a)
    have h2 := hy a
    exact Real.exp_log (inv_pos.mpr (by linarith))
  rw [he] at hp
  rw [hp.tprod_eq]
  refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_⟩
  calc ∑' a, Real.log (1 - y a)⁻¹ ≤ ∑' a, 2 * |y a| :=
        hsl.tsum_le_tsum (fun a => (le_abs_self _).trans (hb a)) hs2
    _ = 2 * ∑' a, |y a| := tsum_mul_left
    _ ≤ 2 * B := by linarith
end GlobalTheory
