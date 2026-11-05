-- Prove2me | solution 1 for GraphProblems.stAdj
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:03:01.949214+00:00
-- url     : https://prove2.me/submissions/5398d045-0851-42e8-8b76-56ef6e94779b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
set_option autoImplicit false
section
section
open GraphProblems
open Read

private theorem getD_flatMap_mul_add {α β : Type} (d : β) (l : List α)
    (f : α → List β) (m : ℕ) (hf : ∀ a ∈ l, (f a).length = m)
    (i j : ℕ) (hi : i < l.length) (hj : j < m) :
    (l.flatMap f).getD (i * m + j) d = (f l[i]).getD j d := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getD_append _ _ _ _ (by simpa [hf a (by simp)] using hj)
    | succ i =>
      simp only [List.flatMap_cons]
      rw [List.getD_append_right _ _ _ _ (by
        rw [hf a (by simp), Nat.succ_mul]
        omega)]
      have hlength : (f a).length = m := hf a (by simp)
      rw [show i.succ * m + j - (f a).length = i * m + j by
        rw [hlength, Nat.succ_mul]
        omega]
      simp only [List.getElem_cons_succ]
      apply ih
      intro b hb
      exact hf b (by simp [hb])

theorem solution : StAdj := by
  classical
  intro n G u v
  unfold adjB matrix
  rw [getD_flatMap_mul_add false (List.finRange n)
    (fun u => (List.finRange n).map fun v => decide (G.Adj u v)) n (by simp)
    u v (by simpa using u.isLt) v.isLt]
  rw [List.getD_eq_getElem _ _ (by simpa using v.isLt)]
  simp
