-- Prove2me | solution 1 for Light.le_cbrtLeast_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:38:41.891026+00:00
-- url     : https://prove2.me/submissions/099f7422-3b5d-4556-a66b-51ecd43277fb

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Logs
namespace Light
theorem _root_.solution (n : ℕ) : n ≤ cbrtLeast n ^ 3 := Nat.find_spec (exists_le_cube n)
end Light
