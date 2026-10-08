-- Prove2me | solution 1 for Light.Exec.bounded
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-06T08:04:04.69968+00:00
-- url     : https://prove2.me/submissions/53c282b3-2c56-4a04-a222-6da1eacf98fa

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
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
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {l : List α} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getD_eq_getElem l d hi]
    exact h _ (List.getElem_mem hi)
  · rwa [List.getD_eq_default l d hi]























































/-! ## Blocks one after the other -/











































































/-! ## Sums -/









































section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]














end



































/-! ## A running minimum -/
























/-! ## Counting -/












































































/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]








































end Sorted

end List

namespace ThreeSumApsp

variable {α β : Type*}

/-! ## Lists of integers that are bounded in absolute value -/














/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i

/-! ## The entrywise sum of lists -/






















end ThreeSumApsp

end



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

/-- Writing a bounded number into a bounded function. -/
private theorem abs_update_le {f : ℕ → ℤ} {B v : ℤ} (hf : ∀ y, |f y| ≤ B) (hv : |v| ≤ B)
    (x y : ℕ) : |Function.update f x v y| ≤ B := by
  rw [Function.update_apply]
  split_ifs
  exacts [hv, hf y]

/-- The value of a safe expression in a bounded state fits in a word. -/
theorem Expr.abs_val_le {σ : State} (hσ : σ.Bounded lim) :
    ∀ e : Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  | .const n, h => by
    rw [Expr.val, abs_of_nonneg (Int.natCast_nonneg n)]
    exact h
  | .var x, _ => hσ.1 x
  | .op _ _ _, h => h.2.2
  | .load _, _ => hσ.2 _

/-- A frame that holds words, over a memory that holds words, is a bounded state. -/
theorem bounded_frame {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : State.Bounded lim ⟨frame args, μ⟩ :=
  ⟨ThreeSumApsp.AbsLe.abs_getD_le ((abs_nonneg _).trans (hμ 0)) hargs, hμ⟩

/-- The state in which a procedure starts is bounded, if the state of the caller is bounded and the
arguments of the call are safe. -/
theorem bounded_callFrame {σ : State} (hσ : σ.Bounded lim) (args : List Expr)
    (ha : ∀ e ∈ args, e.Safe lim σ) : State.Bounded lim ⟨frame (args.map (·.val σ)), σ.mem⟩ := by
  refine bounded_frame (fun v hv => ?_) hσ.2
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
  exact Expr.abs_val_le hσ e (ha e he)

/-- A run that starts with words in all variables and cells ends with words in all of them. -/
theorem Exec.bounded_sourceProof {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c)
    (hσ : σ.Bounded lim) : σ'.Bounded lim := by
  induction h with
  | skip => exact hσ
  | set hs => exact ⟨abs_update_le hσ.1 (Expr.abs_val_le hσ _ hs) _, hσ.2⟩
  | store _ he _ => exact ⟨hσ.1, abs_update_le hσ.2 (Expr.abs_val_le hσ _ he) _⟩
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | iteTrue _ _ _ ih => exact ih hσ
  | iteFalse _ _ _ ih => exact ih hσ
  | whileFalse _ _ => exact hσ
  | whileTrue _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | call ha _ _ _ ih =>
    have hbody := ih (bounded_callFrame hσ _ ha)
    exact ⟨abs_update_le hσ.1 (hbody.1 0) _, hbody.2⟩

















end Light

end


theorem solution : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {s : Light.Stmt} {σ σ' : Light.State} {c : Nat},
  Light.Exec lim P d s σ σ' c → Light.State.Bounded lim σ → Light.State.Bounded lim σ' := by
  exact @Light.Exec.bounded_sourceProof

#print axioms solution
