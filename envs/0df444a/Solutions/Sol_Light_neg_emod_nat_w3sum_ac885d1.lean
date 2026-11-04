-- Prove2me | solution 1 for Light.neg_emod_nat_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:06.733958+00:00
-- url     : https://prove2.me/submissions/dbbb6c02-3ef7-4e27-820b-9acf2baf6ba7

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution (a M : ℕ) (hM : 1 ≤ M) :
    (-(a : ℤ)) % (M : ℤ) = if a % M = 0 then 0 else (M : ℤ) - ((a % M : ℕ) : ℤ) := by
  have h : (a : ℤ) = (M : ℤ) * ((a / M : ℕ) : ℤ) + ((a % M : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod a M).symm
  have hlt : a % M < M := Nat.mod_lt _ (by omega)
  split_ifs with h0
  · rw [h0] at h
    rw [h, Nat.cast_zero, add_zero, ← mul_neg]
    exact Int.mul_emod_right _ _
  · have e : -(a : ℤ) = ((M : ℤ) - ((a % M : ℕ) : ℤ)) + (M : ℤ) * (-((a / M : ℕ) : ℤ) - 1) := by
      rw [h]
      push_cast
      ring
    rw [e, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
end Light
