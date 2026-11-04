-- Prove2me | solution 1 for Light.cbrtLeast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:38:43.977393+00:00
-- url     : https://prove2.me/submissions/cefc34d7-52fa-417d-9139-0e7dc6db5eae

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
theorem _root_.solution {n s : ℕ} (h : n ≤ s ^ 3) : cbrtLeast n ≤ s :=
  Nat.find_min' (exists_le_cube n) h
end Light
