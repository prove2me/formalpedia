-- Prove2me | solution 1 for Nat.mod_lt_of_lt_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:17.297753+00:00
-- url     : https://prove2.me/submissions/96376e8d-bc7d-4a7b-9106-9e936372b023

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {t m n : ℕ} (h : t < m * n) : t % n < n :=
  Nat.mod_lt t (Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt h))
end Nat
