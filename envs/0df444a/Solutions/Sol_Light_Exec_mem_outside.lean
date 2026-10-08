-- Prove2me | solution 1 for Light.Exec.mem_outside
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:03:57.937459+00:00
-- url     : https://prove2.me/submissions/5417eaf7-5a84-4e2e-8670-92586169903c

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



/-!
# Runs stay within their limits

Facts about the semantics of the light language; none of them mentions the compiler.  A state is
bounded if every variable and every cell holds a number of absolute value at most `lim.word`.

* The value of a safe expression in a bounded state is such a number (`Expr.abs_val_le`).
* A run that starts in a bounded state ends in one (`Exec.bounded`): induction on the run.  An
  assignment and a store write the value of a safe expression; a call starts in a frame that holds
  the values of safe expressions and zeros (`bounded_callFrame`, a case of `bounded_frame`).
* A run does not change the cells from `lim.space` on (`Exec.mem_outside`).

The compiler's proof needs the first two because a word of the machine stands for a number only as
long as the number is in the range of words, and the third because its end theorem speaks of all
cells of the memory, also of those that the run may not touch.
-/

public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}















































/-- A run does not change the cells from lim.space on. -/
theorem Exec.mem_outside_sourceProof {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (a : ℕ)
    (ha : lim.space ≤ a) : σ'.mem a = σ.mem a := by
  induction h with
  | skip => rfl
  | set _ => rfl
  | store _ _ haddr =>
    obtain ⟨h0, hlt⟩ := haddr
    exact Function.update_of_ne (by omega) _ _
  | seq _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | iteTrue _ _ _ ih => exact ih
  | iteFalse _ _ _ ih => exact ih
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | call _ _ _ _ ih => exact ih

end Light

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {s : Light.Stmt} {σ σ' : Light.State} {c : Nat},
  Light.Exec lim P d s σ σ' c → ∀ (a : Nat), @LE.le.{0} Nat instLENat lim.space a → @Eq.{1} Int (σ'.mem a) (σ.mem a) := by
  exact @Light.Exec.mem_outside_sourceProof

#print axioms solution
