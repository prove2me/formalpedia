-- Prove2me | solution 1 for Light.pow_lt_of_lt_cbrtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:38:42.950873+00:00
-- url     : https://prove2.me/submissions/49e4cc04-aa32-42aa-a7ad-cf1f0555dff5

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
theorem _root_.solution {n s : ℕ} (h : s < cbrtLeast n) : s ^ 3 < n :=
  not_le.1 (Nat.find_min (exists_le_cube n) h)
end Light
