-- Prove2me | solution 1 for GlobalTheory.PadicVal.exists_addValuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:08.765144+00:00
-- url     : https://prove2.me/submissions/f210cba3-ad18-4747-9dac-39dd3e8ce697

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddValuation
import Theorems.Thm_GlobalTheory_PadicVal_exists_rat_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PadicVal
variable {p : ℕ} [Fact p.Prime]
open Classical
namespace GlobalTheory.PadicVal
theorem _root_.solution (π : PadicAlgCl p) (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ x, x ≠ 0 →
      ∃ q : ℚ, v x = (q : WithTop ℚ) ∧ Real.log ‖x‖ = q * Real.log ‖π‖ := by
  have hL : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  have hex : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ q : ℚ, Real.log ‖x‖ = q * Real.log ‖π‖ := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_rat_log x hx
    obtain ⟨b, hb⟩ := exists_rat_log π (norm_pos_iff.1 h0)
    have hb0 : (b : ℝ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hb
      exact hL.ne hb
    have hlp : Real.log p ≠ 0 := by
      intro h
      rw [h, mul_zero] at hb
      exact hL.ne hb
    refine ⟨a / b, ?_⟩
    rw [ha, hb]
    push_cast
    field_simp
  let r : PadicAlgCl p → ℚ := fun x => if hx : x = 0 then 0 else Classical.choose (hex x hx)
  have hr : ∀ x, x ≠ 0 → Real.log ‖x‖ = r x * Real.log ‖π‖ := by
    intro x hx
    simp only [r, dif_neg hx]
    exact Classical.choose_spec (hex x hx)
  have hr' : ∀ x, x ≠ 0 → (r x : ℝ) = Real.log ‖x‖ / Real.log ‖π‖ := by
    intro x hx
    rw [hr x hx, mul_div_cancel_right₀ _ hL.ne]
  let f : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ)
  have f_ne : ∀ x, x ≠ 0 → f x = (r x : WithTop ℚ) := fun x hx => if_neg hx
  have f_zero : f 0 = ⊤ := if_pos rfl
  refine ⟨AddValuation.of f f_zero ?_ ?_ ?_, ?_⟩
  · have h : (r 1 : ℝ) = 0 := by
      rw [hr' 1 one_ne_zero, norm_one, Real.log_one, zero_div]
    rw [f_ne 1 one_ne_zero, Rat.cast_eq_zero.1 h]
    rfl
  · intro x y
    by_cases hx : x = 0
    · subst hx
      rw [f_zero, zero_add]
      exact min_le_right _ _
    by_cases hy : y = 0
    · subst hy
      rw [f_zero, add_zero]
      exact min_le_left _ _
    by_cases hxy : x + y = 0
    · rw [hxy, f_zero]
      exact le_top
    rw [f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_min, WithTop.coe_le_coe,
      ← Rat.cast_le (K := ℝ), Rat.cast_min, hr' x hx, hr' y hy, hr' _ hxy]
    have hle : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
    have hpos : 0 < ‖x + y‖ := norm_pos_iff.2 hxy
    rcases le_total ‖y‖ ‖x‖ with h | h
    · rw [max_eq_left h] at hle
      exact (min_le_left _ _).trans
        (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))
    · rw [max_eq_right h] at hle
      exact (min_le_right _ _).trans
        (div_le_div_of_nonpos_of_le hL.le (Real.log_le_log hpos hle))
  · intro x y
    by_cases hx : x = 0
    · subst hx
      rw [zero_mul, f_zero, top_add]
    by_cases hy : y = 0
    · subst hy
      rw [mul_zero, f_zero, add_top]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    rw [f_ne x hx, f_ne y hy, f_ne _ hxy, ← WithTop.coe_add, WithTop.coe_eq_coe]
    have h : (r (x * y) : ℝ) = r x + r y := by
      rw [hr' _ hxy, hr' x hx, hr' y hy, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), add_div]
    exact_mod_cast h
  · intro x hx
    exact ⟨r x, f_ne x hx, hr x hx⟩
end GlobalTheory.PadicVal
