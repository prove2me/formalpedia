-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StrictDyadicCrossingV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:23:21.755509+00:00
-- url     : https://prove2.me/submissions/756f1b6d-bd5a-484b-87de-aa605a5d224b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A strict crossing on a compact right-continuous path is detected on a countable grid. -/
theorem solution (f : NNReal → ℝ) (T : NNReal)
    (hr : ∀ t, ContinuousWithinAt f (Ici t) t) (δ : ℝ) :
    let q (j : ℕ) (k : Fin (2^j+1)) : NNReal :=
      (k.val : NNReal) / (2 : NNReal)^j * T
    (∀ j k, q j k ≤ T) ∧
      ((∃ t ≤ T, δ < |f t|) ↔ ∃ j k, δ < |f (q j k)|) := by
  intro q
  have hq (j : ℕ) (k : Fin (2^j+1)) : q j k ≤ T := by
    have hk : (k.val : NNReal) ≤ (2 : NNReal)^j := by
      exact_mod_cast Nat.lt_succ_iff.mp k.isLt
    have hdiv : (k.val : NNReal) / (2 : NNReal)^j ≤ 1 :=
      (div_le_iff₀ (by positivity)).2 (by simpa using hk)
    simpa [q] using mul_le_mul_of_nonneg_right hdiv (show 0 ≤ T from zero_le)
  refine ⟨hq,?_⟩
  constructor
  · rintro ⟨t,ht,hd⟩
    by_cases hT : 0 < T
    · have hc : ∀ s, ContinuousWithinAt (fun u => -|f u|) (Ici s) s :=
        fun s => (hr s).abs.neg
      obtain ⟨j,k,hk⟩ :=
        (AvramDividend.Classical.avram_ws01e_b_right_continuous_strict_dyadic_grid_event
          (fun u => -|f u|) T hT hc (-δ)).mp ⟨t,ht,by linarith⟩
      exact ⟨j,k,by change -|f (q j k)| < -δ at hk; linarith⟩
    · have hz : T = 0 := le_antisymm (le_of_not_gt hT) zero_le
      have ht0 : t = 0 := le_antisymm (hz ▸ ht) zero_le
      exact ⟨0,0,by simpa [q,hz,ht0] using hd⟩
  · rintro ⟨j,k,hk⟩
    exact ⟨q j k,hq j k,hk⟩
