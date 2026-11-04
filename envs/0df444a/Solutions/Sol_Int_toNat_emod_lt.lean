-- Prove2me | solution 1 for Int.toNat_emod_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:18.48135+00:00
-- url     : https://prove2.me/submissions/d142bd8a-7145-4a0e-b939-6bcb3892c2d6

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index

set_option autoImplicit false
public section
open Int
namespace Int
theorem _root_.solution {M : ℕ} (hM : 0 < M) (x : ℤ) : (x % (M : ℤ)).toNat < M := by
  have := Int.emod_lt_of_pos x (Int.natCast_pos.2 hM)
  omega
end Int
