-- Prove2me | solution 1 for Int.exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/99e38358-cd7f-5e25-9fc1-a02054701e51

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul

set_option autoImplicit false

namespace U1a_8

theorem exists_shift (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ k : ℤ, 0 < k * k - t * k + n ∧ ¬ IsSquare (k * k - t * k + n) ∧ (t - 2 * k) ^ 2 < 4 * (k * k - t * k + n) := by
  set D : ℤ := 4 * n - t ^ 2 with hD
  have hD0 : 0 < D := by omega
  refine ⟨D + |t|, ?_, ?_, ?_⟩
  · nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (2 * (D + |t|) - t)]
  · rintro ⟨s, hs⟩
    set m : ℤ := 2 * (D + |t|) - t with hm
    have hmD : D < m := by
      have := abs_nonneg t; have := le_abs_self t; have := neg_abs_le t; omega
    have h4 : 4 * (s * s) = m * m + D := by rw [← hs, hm, hD]; ring
    rcases le_or_gt (2 * |s|) m with h | h
    · nlinarith [sq_abs s, abs_nonneg s]
    · nlinarith [sq_abs s, abs_nonneg s]
  · nlinarith [abs_nonneg t, sq_abs t]

end U1a_8

theorem solution
    (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ k : ℤ, 0 < k ^ 2 - t * k + n ∧ ¬ IsSquare (k ^ 2 - t * k + n) := by
  obtain ⟨k, h1, h2, -⟩ := U1a_8.exists_shift t n htn
  exact ⟨k, by rw [sq]; exact h1, by rw [sq]; exact h2⟩

end S_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul
end P2MW
export P2MW.S_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul (solution)
