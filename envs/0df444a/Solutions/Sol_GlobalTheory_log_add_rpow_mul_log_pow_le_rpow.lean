-- Prove2me | solution 1 for GlobalTheory.log_add_rpow_mul_log_pow_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:47.650471+00:00
-- url     : https://prove2.me/submissions/f9c453f0-8dc8-42cb-9cc3-98e20dc657f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogAddRpowMulLogPowLeRpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open GlobalTheory
open Filter Asymptotics
namespace GlobalTheory
theorem _root_.solution :
    ∀ a b c C κ : ℝ, ∀ p : ℕ, 0 ≤ a → a < b → 0 < κ → ∃ x0 : ℝ, ∀ x ≥ x0,
      c * Real.log x + C * x ^ a * Real.log x ^ p + C ≤ κ * x ^ b := by
  intro a b c C κ p ha hab hκ
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have h1 : (fun x : ℝ => c * Real.log x) =o[atTop] fun x => x ^ b :=
    (isLittleO_log_rpow_atTop hb).const_mul_left c
  have h2 : (fun x : ℝ => C * x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
    have hl : (fun x : ℝ => Real.log x ^ p) =o[atTop] fun x => x ^ (b - a) := by
      have := isLittleO_log_rpow_rpow_atTop (p : ℝ) (sub_pos.2 hab)
      simpa [Real.rpow_natCast] using this
    have hm : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop]
        fun x => x ^ a * x ^ (b - a) :=
      (isBigO_refl (fun x : ℝ => x ^ a) atTop).mul_isLittleO hl
    have hm' : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
      refine hm.congr' (Eventually.of_forall fun _ => rfl) ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simpa [mul_assoc] using hm'.const_mul_left C
  have h3 : (fun _ : ℝ => C) =o[atTop] fun x => x ^ b := by
    rw [isLittleO_const_left]
    right
    exact tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hb)
  have h := (h1.add h2).add h3
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 ((h.bound hκ).and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨hbd, hxpos⟩ := hx0 x hx
  have hpos : 0 < x ^ b := Real.rpow_pos_of_pos hxpos b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hbd
  exact (le_abs_self _).trans hbd
end GlobalTheory
