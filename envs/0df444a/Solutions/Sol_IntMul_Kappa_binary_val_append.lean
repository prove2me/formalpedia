-- Prove2me | solution 1 for IntMul.Kappa.binary_val_append
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-17T11:20:10.791709+00:00
-- url     : https://prove2.me/submissions/d27b8276-35cb-4091-b65e-707628792aa3

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

theorem solution(x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  have key : ∀ (y : List Bool) (a : ℕ),
      y.foldl (fun a b => 2 * a + b.toNat) a
        = 2 ^ y.length * a + y.foldl (fun a b => 2 * a + b.toNat) 0 := by
    intro y
    induction y with
    | nil => intro a; simp
    | cons b t ih =>
      intro a
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (2 * a + b.toNat), ih (2 * 0 + b.toNat)]
      ring
  unfold IntMul.val
  rw [List.foldl_append]
  exact key y _
