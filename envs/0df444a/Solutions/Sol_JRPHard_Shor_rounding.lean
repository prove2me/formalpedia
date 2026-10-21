-- Prove2me | solution 1 for JRPHard.Shor.rounding
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T08:34:58.057686+00:00
-- url     : https://prove2.me/submissions/4aaf2998-c338-4155-b425-1f11f92c5ec7

import Definitions.Def_JRPHard_Shor_DecisionProblems
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

private lemma inward_interval_bound (L U a b : ℝ) (hL : 0 < L)
    (hLa : L ≤ a) (hab : a ≤ b) (hbU : b ≤ U)
    (hrange : L + U < 2 * Real.sqrt (2 * L * U)) :
    a + b < 2 * Real.sqrt (2 * a * b) := by
  have ha : 0 < a := lt_of_lt_of_le hL hLa
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hU : 0 < U := lt_of_lt_of_le hb hbU
  have hLU : L ≤ U := hLa.trans (hab.trans hbU)
  have hgeom : 0 ≤ 2 * L * U := by positivity
  have hsqrt := Real.sq_sqrt hgeom
  have hsum : 0 < L + U := add_pos hL hU
  have hstrict : (L + U)^2 < 8 * L * U := by
    have h := mul_pos (sub_pos.mpr hrange)
      (show 0 < 2 * Real.sqrt (2 * L * U) + (L + U) by positivity)
    nlinarith
  have hcross1 : 0 ≤ U * a - L * b := by
    have h1 := mul_le_mul_of_nonneg_right hLa hb.le
    have h2 := mul_le_mul_of_nonneg_left hbU ha.le
    nlinarith
  have hcross2 : 0 ≤ U * b - L * a := by
    have h1 := mul_le_mul_of_nonneg_right hLU ha.le
    have h2 := mul_le_mul_of_nonneg_left hab hU.le
    nlinarith
  have hcross := mul_nonneg hcross1 hcross2
  have hscaled := mul_pos (sub_pos.mpr hstrict) (mul_pos ha hb)
  have hcombined : 0 < L * U * (8 * a * b - (a + b)^2) := by
    nlinarith
  have hdiff : 0 < 8 * a * b - (a + b)^2 :=
    pos_of_mul_pos_right hcombined (mul_pos hL hU).le
  have hsqrtab := Real.sq_sqrt (show 0 ≤ 2 * a * b by positivity)
  by_contra h
  have hrev : 2 * Real.sqrt (2 * a * b) ≤ a + b := le_of_not_gt h
  have hsquare := mul_self_le_mul_self
    (show 0 ≤ 2 * Real.sqrt (2 * a * b) by positivity) hrev
  nlinarith

theorem solution (M : ℕ) (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U)
    (hceil : ⌈L⌉₊ ≤ ⌊U⌋₊) (hbound : ⌊U⌋₊ ≤ M)
    (hrange : L + U < 2 * Real.sqrt (2 * L * U)) :
    (JRPHard.RangeDiv.HasDivisorIn M ⌈L⌉₊ ⌊U⌋₊ ↔
      ∃ d : ℕ, d ∣ M ∧ L ≤ (d : ℝ) ∧ (d : ℝ) ≤ U) ∧
    JRPHard.RangeDiv.IsRangeDivisorInstance M ⌈L⌉₊ ⌊U⌋₊ := by
  have hU : 0 < U := lt_of_lt_of_le hL hLU
  constructor
  · unfold JRPHard.RangeDiv.HasDivisorIn
    constructor
    · rintro ⟨d, hd, hlo, hhi⟩
      exact ⟨d, hd, Nat.ceil_le.mp hlo, (Nat.le_floor_iff hU.le).mp hhi⟩
    · rintro ⟨d, hd, hlo, hhi⟩
      exact ⟨d, hd, Nat.ceil_le.mpr hlo, (Nat.le_floor_iff hU.le).mpr hhi⟩
  · refine ⟨?_, hceil, hbound, ?_⟩
    · exact Nat.ceil_pos.mpr hL
    · apply inward_interval_bound L U (⌈L⌉₊ : ℝ) (⌊U⌋₊ : ℝ) hL
      · exact Nat.le_ceil L
      · exact_mod_cast hceil
      · exact Nat.floor_le hU.le
      · exact hrange

#print axioms solution
