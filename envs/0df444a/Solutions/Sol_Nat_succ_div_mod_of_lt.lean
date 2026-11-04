-- Prove2me | solution 1 for Nat.succ_div_mod_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:57.866837+00:00
-- url     : https://prove2.me/submissions/72640b28-86e0-4d04-a76e-67454a874380

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Theorems.Thm_Nat_mul_add_div_of_lt

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {n i : ℕ} (h : i % n + 1 < n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by
  have hsucc : i + 1 = i / n * n + (i % n + 1) := by rw [← Nat.add_assoc, Nat.div_add_mod']
  exact ⟨by rw [hsucc, mul_add_div_of_lt h], by rw [hsucc, Nat.mul_add_mod_of_lt h]⟩
end Nat
