-- Prove2me | solution 1 for Light.polyBound_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:17:54.911896+00:00
-- url     : https://prove2.me/submissions/8886b7a7-9cec-4f02-8a99-6017171d3487

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize

set_option autoImplicit false
section
open Light
open ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution (s s' k : ℕ) (params : List ℕ) :
    2 ^ s' * polyBound s k params = polyBound (s' + s) k params := by
  simp only [polyBound, pow_add, mul_assoc]
end Light
