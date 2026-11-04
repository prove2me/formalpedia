-- Prove2me | solution 1 for Light.polyBound_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:50.428633+00:00
-- url     : https://prove2.me/submissions/d4795145-2c38-4ce9-a746-74a17012c38d

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
section
namespace Light
open ThreeSumApsp.WordRam
private theorem prod_succ_le (params : List ℕ) :
    (params.map (· + 1)).prod ≤ 2 ^ ((params.map Nat.log2).sum + params.length) := by
  induction params with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons]
    calc (p + 1) * (ps.map (· + 1)).prod
        ≤ 2 ^ (p.log2 + 1) * 2 ^ ((ps.map Nat.log2).sum + ps.length) :=
          Nat.mul_le_mul Nat.lt_log2_self ih
      _ = 2 ^ (p.log2 + (ps.map Nat.log2).sum + (ps.length + 1)) := by
          rw [← pow_add]
          congr 1
          omega
end Light
set_option autoImplicit false
section
open Light
open ThreeSumApsp.WordRam
namespace Light
theorem _root_.solution {b W s k r : ℕ} {params : List ℕ} (h : Admissible b params W)
    (hr : params.length ≤ r) (hb : s + k * r + k ≤ b) : polyBound s k params ≤ 2 ^ W := by
  set S := (params.map Nat.log2).sum
  have hexp : s + (S + params.length) * k ≤ W :=
    calc s + (S + params.length) * k ≤ s + (S + r) * k := by gcongr
      -- the difference is s S + k r S + k
      _ ≤ (s + k * r + k) * (S + 1) := Nat.le.intro (k := s * S + k * r * S + k) (by ring)
      _ ≤ b * (S + 1) := Nat.mul_le_mul_right _ hb
      _ ≤ W := h
  calc polyBound s k params ≤ 2 ^ s * (2 ^ (S + params.length)) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (prod_succ_le params) k)
    _ = 2 ^ (s + (S + params.length) * k) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hexp
end Light
