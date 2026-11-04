-- Prove2me | solution 1 for Nat.eq_mul_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:56.978745+00:00
-- url     : https://prove2.me/submissions/63020645-0c3a-47e3-963d-37e673506dd0

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Theorems.Thm_Nat_mul_add_div_of_lt

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {n i t : ℕ} (hi : i < n) : t = i * (n + 1) ↔ t / n = i ∧ t % n = i := by
  constructor
  · rintro rfl
    rw [Nat.mul_succ]
    exact ⟨mul_add_div_of_lt hi, Nat.mul_add_mod_of_lt hi⟩
  · rintro ⟨hdiv, hmod⟩
    rw [Nat.mul_succ, ← Nat.div_add_mod' t n, hdiv, hmod]
end Nat
