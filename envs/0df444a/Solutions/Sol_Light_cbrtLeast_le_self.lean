-- Prove2me | solution 1 for Light.cbrtLeast_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:25.395362+00:00
-- url     : https://prove2.me/submissions/b134f749-924e-4816-8f05-9bd2c78c6e2a

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
public import Theorems.Thm_Light_cbrtLeast_le

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Logs
namespace Light
theorem _root_.solution (n : ℕ) : cbrtLeast n ≤ n :=
  cbrtLeast_le (Nat.le_self_pow (by norm_num) n)
end Light
