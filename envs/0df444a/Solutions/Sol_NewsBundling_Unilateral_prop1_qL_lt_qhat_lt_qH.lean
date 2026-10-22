-- Prove2me | solution 1 for NewsBundling.Unilateral.prop1_qL_lt_qhat_lt_qH
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:33:59.418178+00:00
-- url     : https://prove2.me/submissions/41d18371-41dc-45e4-89bf-619c1b352597

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

set_option autoImplicit false
open NewsBundling.Unilateral

theorem solution (β φ1 c Λ : ℝ)
    (hc : 0 < c) (hφ : φ1 < β) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1) :
    qL φ1 c < β / c ∧ β / c < qH β φ1 c Λ := by
  unfold qL qH
  constructor
  · exact div_lt_div_of_pos_right hφ hc
  · have h1 : 0 < 1 - Λ := by linarith
    rw [div_lt_div_iff₀ hc (by positivity)]
    nlinarith [mul_pos hΛ0 (sub_pos.2 hφ)]
