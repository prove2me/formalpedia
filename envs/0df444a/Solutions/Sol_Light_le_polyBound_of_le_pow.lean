-- Prove2me | solution 1 for Light.le_polyBound_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:52.847105+00:00
-- url     : https://prove2.me/submissions/9bef93b7-17e5-4601-b338-029cff8ec5ad

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
theorem _root_.solution {n A s m e k : ℕ} (he : e ≤ k) (h : m ≤ A * (n + 1) ^ e) :
    m ≤ polyBound (s + Nat.size A) k [n] := by
  have hA : A ≤ 2 ^ (s + Nat.size A) :=
    (Nat.lt_size_self A).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hn : (n + 1) ^ e ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) he
  have hbound : polyBound (s + Nat.size A) k [n] = 2 ^ (s + Nat.size A) * (n + 1) ^ k := by
    simp [polyBound]
  rw [hbound]
  exact h.trans (Nat.mul_le_mul hA hn)
end Light
