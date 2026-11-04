-- Prove2me | solution 1 for Nat.succ_div_mod_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:37:56.914606+00:00
-- url     : https://prove2.me/submissions/1c73fcd8-b723-4518-9d27-46915933e20c

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index
public import Theorems.Thm_Nat_succ_div_mod_of_lt

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {n i : ℕ} (hn : 0 < n) (h : i % n + 1 ≠ n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 :=
  succ_div_mod_of_lt (lt_of_le_of_ne (Nat.mod_lt i hn) h)
end Nat
