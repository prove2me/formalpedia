-- Prove2me | solution 1 for Light.add_le_polyBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:53.433511+00:00
-- url     : https://prove2.me/submissions/b586a5f3-92b5-4737-a7fd-50c9da8b2d9d

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
import Theorems.Thm_Light_polyBound_mono
import Theorems.Thm_Light_polyBound_mul

set_option autoImplicit false
section
open Light
open ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution {a b s s' k k' : ℕ} {params : List ℕ} (ha : a ≤ polyBound s k params)
    (hb : b ≤ polyBound s' k' params) : a + b ≤ polyBound (1 + (s + s')) (k + k') params := by
  have ha' := ha.trans (polyBound_mono (Nat.le_add_right s s') (Nat.le_add_right k k') params)
  have hb' := hb.trans (polyBound_mono (Nat.le_add_left s' s) (Nat.le_add_left k' k) params)
  rw [← polyBound_mul]
  omega
end Light
