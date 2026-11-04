-- Prove2me | solution 1 for Light.polyBound_cons_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:50.444685+00:00
-- url     : https://prove2.me/submissions/b708d366-eef2-4c0a-913a-a4d6eaddf3cf

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
theorem _root_.solution {p p' : ℕ} (h : p ≤ p') (s k : ℕ) (params : List ℕ) :
    polyBound s k (p :: params) ≤ polyBound s k (p' :: params) := by
  simp only [polyBound, List.map_cons, List.prod_cons]
  gcongr
end Light
