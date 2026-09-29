-- Prove2me | solution 1 for Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/32d83ac3-fc39-565e-a279-5b13174f0f79

import Mathlib
import Theorems.Thm_Nat_exists_squarefree_sq_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul

set_option autoImplicit false

theorem solution (t n : ℤ) (h : t ^ 2 < 4 * n) :
    ∃ a b : ℤ, b ≠ 0 ∧ Squarefree (a ^ 2 + t * a * b + n * b ^ 2).toNat ∧
      2 ≤ (a ^ 2 + t * a * b + n * b ^ 2).toNat := by
  set D : ℕ := (4 * n - t ^ 2).toNat with hD_def
  have hD1 : 1 ≤ D := by
    have : (1 : ℤ) ≤ 4 * n - t ^ 2 := by omega
    omega
  have hDcast : ((D : ℤ)) = 4 * n - t ^ 2 := by
    rw [hD_def]; exact Int.toNat_of_nonneg (by omega)
  obtain ⟨c, hc1, hsf⟩ := Nat.exists_squarefree_sq_add D hD1
  have hid : ((c : ℤ) - t) ^ 2 + t * ((c : ℤ) - t) * 2 + n * 2 ^ 2 = ((c ^ 2 + D : ℕ) : ℤ) := by
    push_cast [hDcast]; ring
  refine ⟨(c : ℤ) - t, 2, two_ne_zero, ?_, ?_⟩
  · rw [hid, Int.toNat_natCast]; exact hsf
  · rw [hid, Int.toNat_natCast]; nlinarith [sq_nonneg c]

end S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul
end P2MW
export P2MW.S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul (solution)
