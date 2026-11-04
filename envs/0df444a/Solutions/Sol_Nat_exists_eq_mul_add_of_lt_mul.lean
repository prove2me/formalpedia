-- Prove2me | solution 1 for Nat.exists_eq_mul_add_of_lt_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:56.057233+00:00
-- url     : https://prove2.me/submissions/63e7f1cb-9e7b-4b8f-9532-5027aa609f0d

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Theorems.Thm_P2M_Nat_div_lt_of_lt_mul__63b09184c268
public import Theorems.Thm_Nat_mod_lt_of_lt_mul

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {t m n : ℕ} (h : t < m * n) : ∃ a < m, ∃ b < n, t = a * n + b :=
  ⟨t / n, div_lt_of_lt_mul' h, t % n, mod_lt_of_lt_mul h, (Nat.div_add_mod' t n).symm⟩
end Nat
