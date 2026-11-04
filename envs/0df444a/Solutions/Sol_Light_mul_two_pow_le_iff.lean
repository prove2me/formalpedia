-- Prove2me | solution 1 for Light.mul_two_pow_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:04.698278+00:00
-- url     : https://prove2.me/submissions/a2b5dc34-1ee6-46b4-a18f-867c9f0240f7

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
theorem _root_.solution {a M i : ℕ} (hM : 1 ≤ M) : M * 2 ^ i ≤ a ↔ i < emodRounds a M := by
  rw [emodRounds, Nat.lt_size, Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
end Light
