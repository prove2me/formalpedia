-- Prove2me | solution 1 for Kyprianou.Ch04.nestedGridKernelSquareV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:55:45.967988+00:00
-- url     : https://prove2.me/submissions/8691d775-f04d-44d2-8983-3290243d1dbd

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem solution
    (a c K D x u v : ℝ) (hac : a ≤ c)
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hu : |u| ≤ K) (hd : |u-v| ≤ K*D) :
    (x * ((if a < |x| ∧ |x| < 1 then u else 0) -
      (if c < |x| ∧ |x| < 1 then v else 0)))^2 ≤
      K^2*D^2*(if c < |x| ∧ |x| < 1 then x^2 else 0) +
      K^2*(if a < |x| ∧ |x| ≤ c ∧ |x| < 1 then x^2 else 0) := by
  by_cases hc : c < |x| ∧ |x| < 1
  · have ha : a < |x| ∧ |x| < 1 := ⟨hac.trans_lt hc.1, hc.2⟩
    have hn : ¬ (a < |x| ∧ |x| ≤ c ∧ |x| < 1) :=
      fun h => (not_le_of_gt hc.1) h.2.1
    rw [if_pos ha, if_pos hc, if_pos hc, if_neg hn, mul_zero, add_zero]
    have hs : (u-v)^2 ≤ K^2*D^2 := by
      calc
        (u-v)^2 = |u-v|^2 := (sq_abs _).symm
        _ ≤ (K*D)^2 := by gcongr
        _ = _ := by ring
    calc
      _ = x^2*(u-v)^2 := by ring
      _ ≤ x^2*(K^2*D^2) := mul_le_mul_of_nonneg_left hs (sq_nonneg x)
      _ = _ := by ring
  · by_cases ha : a < |x| ∧ |x| < 1
    · have htail : a < |x| ∧ |x| ≤ c ∧ |x| < 1 :=
        ⟨ha.1, le_of_not_gt (fun h => hc ⟨h, ha.2⟩), ha.2⟩
      rw [if_pos ha, if_neg hc, if_neg hc, if_pos htail, sub_zero, mul_zero, zero_add]
      have hs : u^2 ≤ K^2 := by
        calc
          u^2 = |u|^2 := (sq_abs _).symm
          _ ≤ K^2 := by gcongr
      calc
        _ = x^2*u^2 := by ring
        _ ≤ x^2*K^2 := mul_le_mul_of_nonneg_left hs (sq_nonneg x)
        _ = _ := by ring
    · have hn : ¬ (a < |x| ∧ |x| ≤ c ∧ |x| < 1) :=
        fun h => ha ⟨h.1,h.2.2⟩
      simp [ha,hc,hn]
