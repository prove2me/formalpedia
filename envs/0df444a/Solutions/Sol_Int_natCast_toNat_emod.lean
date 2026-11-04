-- Prove2me | solution 1 for Int.natCast_toNat_emod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:19.427011+00:00
-- url     : https://prove2.me/submissions/57ff1661-1cb2-43e9-a709-a031a08c9ab5

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index

set_option autoImplicit false
public section
open Int
namespace Int
theorem _root_.solution {M : ℕ} (hM : 0 < M) (x : ℤ) : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (Int.natCast_ne_zero_iff_pos.2 hM))
end Int
