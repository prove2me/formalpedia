-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_scaled_cubic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:28:06.298709+00:00
-- url     : https://prove2.me/submissions/9d3f4a9a-d93f-4930-8997-74955c8a9807

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_unscaled_cubic
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (a z : ℝ) (ha : 0 < a) :
    |z^2/2-(1-Real.cos (a*z))/a^2| ≤ a*|z| * z^2/2 := by
  let r : ℝ := z^2/2-(1-Real.cos (a*z))/a^2
  have ha2 : 0 < a^2 := by positivity
  have heq : a^2*r = Real.cos (a*z)-1+(a*z)^2/2 := by
    dsimp [r]
    field_simp
    <;> ring
  have h := Kyprianou.Ch04.ito43_cosine_unscaled_cubic (a*z)
  rw [← heq,abs_mul,abs_of_pos ha2,abs_mul,abs_of_pos ha] at h
  apply le_of_mul_le_mul_left _ ha2
  change a^2*|r| ≤ a^2*(a*|z| * z^2/2)
  exact h.trans (by ring_nf; rfl)
