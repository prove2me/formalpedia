-- Prove2me | solution 1 for LinearPriceRule.Concave.linear_price
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:42:04.810239+00:00
-- url     : https://prove2.me/submissions/12c8f183-97b9-4f2f-b2ce-2927cb6826a1

import Mathlib
import Definitions.Def_LinearPriceRule_Concave_Model

set_option autoImplicit false

open LinearPriceRule.Concave

theorem solution (Pm b c : ℝ) (hb : 0 < b) (hc : c < Pm) :
    IsMaxOn (linProfitAt Pm b c) (Set.Ici 0) ((Pm - c) / (2 * b)) ∧
    (∀ Q ∈ Set.Ici (0 : ℝ), IsMaxOn (linProfitAt Pm b c) (Set.Ici 0) Q →
      Q = (Pm - c) / (2 * b)) ∧
    Pm - b * ((Pm - c) / (2 * b)) = (Pm + c) / 2 := by
  let q : ℝ := (Pm - c) / (2 * b)
  have hq : 0 ≤ q := le_of_lt (div_pos (sub_pos.mpr hc) (mul_pos (by norm_num) hb))
  have hdifference (Q : ℝ) :
      linProfitAt Pm b c q - linProfitAt Pm b c Q = b * (Q - q) ^ 2 := by
    dsimp [linProfitAt, q]
    field_simp
    ring
  have hmax (Q : ℝ) : linProfitAt Pm b c Q ≤ linProfitAt Pm b c q := by
    have hnonneg : 0 ≤ b * (Q - q) ^ 2 := mul_nonneg hb.le (sq_nonneg _)
    linarith [hdifference Q]
  refine ⟨fun Q _ => hmax Q, ?_, ?_⟩
  · intro Q _ hQ
    have hle : linProfitAt Pm b c q ≤ linProfitAt Pm b c Q := hQ hq
    have hs : b * (Q - q) ^ 2 = 0 := by
      nlinarith [hdifference Q, hmax Q]
    have hsq : (Q - q) ^ 2 = 0 := (mul_eq_zero.mp hs).resolve_left hb.ne'
    have heq : Q - q = 0 := sq_eq_zero_iff.mp hsq
    exact sub_eq_zero.mp heq
  · field_simp
    ring
