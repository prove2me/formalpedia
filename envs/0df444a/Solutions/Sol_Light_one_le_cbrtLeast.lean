-- Prove2me | solution 1 for Light.one_le_cbrtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:26.415016+00:00
-- url     : https://prove2.me/submissions/7162ad9a-afdb-4c9a-abb7-dcd0e8924165

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
public import Theorems.Thm_Light_le_cbrtLeast_pow

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Logs
namespace Light
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) : 1 ≤ cbrtLeast n := by
  by_contra h
  have hpow := le_cbrtLeast_pow n
  rw [show cbrtLeast n = 0 by omega] at hpow
  omega
end Light
