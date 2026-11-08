-- Prove2me | solution 1 for LiquidWelfareFPA.lambda2_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:42:44.52533+00:00
-- url     : https://prove2.me/submissions/0ee592df-e0ae-4c67-9af6-a0bb65a44d5f

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam2

namespace Aux_LWFPA_l2
open LiquidWelfareFPA

theorem f_mono : MonotoneOn (fun y : ℝ => y * Real.exp y) (Set.Ici (-1)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (-1))
    (f' := fun y => 1 * Real.exp y + y * Real.exp y)
  · exact (continuous_id.mul Real.continuous_exp).continuousOn
  · intro y _
    exact ((hasDerivAt_id y).mul (Real.hasDerivAt_exp y)).hasDerivWithinAt
  · intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    have := Real.exp_pos y
    nlinarith

end Aux_LWFPA_l2

open LiquidWelfareFPA Aux_LWFPA_l2 in
theorem solution (γ : ℝ) (hγ : 1 ≤ γ) :
    -1 / γ < lambertW (-Real.exp (-2 / γ) / γ) ∧ lambertW (-Real.exp (-2 / γ) / γ) < 0 ∧
      0 < lam2 γ ∧ lam2 γ < 1 := by
  have hγ0 : 0 < γ := by linarith
  set x := -Real.exp (-2 / γ) / γ with hx
  have hxneg : x < 0 := by
    rw [hx, neg_div]; exact neg_neg_of_pos (div_pos (Real.exp_pos _) hγ0)
  -- x ≥ -1/e
  have hxlow : -1 * Real.exp (-1) ≤ x := by
    rw [hx]
    have h1 : Real.exp (-2 / γ) / γ ≤ Real.exp (-1) := by
      rw [div_le_iff₀ hγ0]
      have h2 : 2 / γ - 1 + 1 ≤ Real.exp (2 / γ - 1) := Real.add_one_le_exp _
      have h3 : Real.exp (-2 / γ) * Real.exp (2 / γ - 1) = Real.exp (-1) := by
        rw [← Real.exp_add]; congr 1; ring
      have h4 : 0 < Real.exp (-2 / γ) := Real.exp_pos _
      have h6 : Real.exp (-2 / γ) * (2 / γ) ≤ Real.exp (-1) := by
        rw [← h3]; exact mul_le_mul_of_nonneg_left (by linarith [h2]) h4.le
      have h7 : Real.exp (-2 / γ) * (2 / γ) * γ = 2 * Real.exp (-2 / γ) := by field_simp
      have h8 := mul_le_mul_of_nonneg_right h6 hγ0.le
      linarith
    rw [neg_div]
    linarith
  have hex : ∃ y : ℝ, -1 ≤ y ∧ y * Real.exp y = x := by
    have := intermediate_value_Icc (show (-1 : ℝ) ≤ 0 by norm_num)
      ((continuous_id.mul Real.continuous_exp).continuousOn (s := Set.Icc (-1) 0))
      (show x ∈ Set.Icc ((-1) * Real.exp (-1)) (0 * Real.exp 0) from ⟨hxlow, by simp; linarith⟩)
    obtain ⟨y, hy, hyx⟩ := this
    exact ⟨y, hy.1, hyx⟩
  have hW : -1 ≤ lambertW x ∧ lambertW x * Real.exp (lambertW x) = x := by
    unfold lambertW
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  have hWneg : lambertW x < 0 := by
    by_contra h
    push_neg at h
    have := mul_nonneg h (Real.exp_pos (lambertW x)).le
    linarith [hW.2]
  have hWlow : -1 / γ < lambertW x := by
    by_contra h
    push_neg at h
    have hm : -1 ≤ -1 / γ := by
      rw [le_div_iff₀ hγ0]; linarith
    have := f_mono hW.1 (show -1 / γ ∈ Set.Ici (-1 : ℝ) from hm) h
    simp only at this
    rw [hW.2] at this
    -- this : x ≤ -1/γ * exp(-1/γ); but x = -(1/γ) exp(-2/γ) > that
    have hlt : Real.exp (-2 / γ) < Real.exp (-1 / γ) := by
      apply Real.exp_lt_exp.mpr
      rw [div_lt_div_iff_of_pos_right hγ0]; norm_num
    have : -1 / γ * Real.exp (-1 / γ) < x := by
      rw [hx]
      have e1 : -1 / γ * Real.exp (-1 / γ) = -(Real.exp (-1 / γ) / γ) := by ring
      have e2 : -Real.exp (-2 / γ) / γ = -(Real.exp (-2 / γ) / γ) := by ring
      rw [e1, e2, neg_lt_neg_iff]
      exact div_lt_div_of_pos_right hlt hγ0
    linarith
  refine ⟨hWlow, hWneg, ?_, ?_⟩
  · unfold lam2
    rw [← hx]
    have := mul_lt_mul_of_pos_left hWlow hγ0
    rw [mul_div_cancel₀ _ hγ0.ne'] at this
    linarith
  · unfold lam2
    rw [← hx]
    have := mul_neg_of_pos_of_neg hγ0 hWneg
    linarith
