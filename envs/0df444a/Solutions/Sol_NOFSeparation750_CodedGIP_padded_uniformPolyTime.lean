-- Prove2me | solution 1 for NOFSeparation750.CodedGIP.padded_uniformPolyTime
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:27:03.605458+00:00
-- url     : https://prove2.me/submissions/9a1091da-3070-40b0-8bad-2abe13640caa

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.GetD
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Definitions.Def_NOFSeparation750_CodedGIP_Programs
import Mathlib
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Finite
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Fold
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Option
import Definitions.Def_NOFSeparation750_CodedGIP_EffectiveCodes

set_option linter.all false
set_option maxHeartbeats 4000000

/-!
Time-only adaptation of the Apache-2.0 Complexitylib reverse TM2 compiler by Erik Demaine.
Source: https://github.com/cslib-community/cslib-frontier/tree/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/TM2/Reverse
This file uses the archived Prove2Me native model and packaging lemmas. It drops the space
transfer, proves the needed auxiliary storage bound directly from the zipper steps, and
uses a Mathlib natural-coefficient polynomial for the final clock.
License: https://www.apache.org/licenses/LICENSE-2.0
-/


namespace Turing.TM2

/-- Execute one source step, keeping the last configuration after halting. -/
def stepTotal {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) (cfg : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  cfg.l.elim cfg (fun l => stepAux (M l) cfg.var cfg.stk)

end Turing.TM2
/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# A bounded input zipper for the TM2 compiler

The left stack is reversed and the right stack includes the symbol under the head. A separate
flag distinguishes the left boundary from the first input symbol. An empty right stack with
the flag unset represents the right boundary, including the initial position on empty input.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Input`: the two stacks and the left-boundary flag.
* `Turing.MultiTapeTM.ToTM2.Input.Represents`: agreement with a native input and head position.

## Main results

* `Turing.MultiTapeTM.ToTM2.Input.represents_init`: initialization represents native position one.
* `Turing.MultiTapeTM.ToTM2.Input.Represents.read_eq_inputSymbol`: reads agree with native reads.
* `Turing.MultiTapeTM.ToTM2.Input.Represents.move`: moves agree, including boundary clamping.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A read-only input tape represented by two stacks and a left-boundary flag. -/
@[ext]
structure Input (Symbol : Type) where
  /-- Input symbols strictly to the left of the head, in reverse order. -/
  left : List Symbol
  /-- Input symbols from the head onward, in input order. -/
  right : List Symbol
  /-- Whether the head is at the blank before the input. -/
  atLeft : Bool
deriving Inhabited

namespace Input

variable {Symbol : Type}

/-- Start at native position one, also when the input is empty. -/
def init (input : List Symbol) : Input Symbol := ⟨[], input, false⟩

/-- Read the current input symbol, or a blank at either boundary. -/
def read (z : Input Symbol) : Option Symbol :=
  if z.atLeft then none else z.right.head?

/-- Move left, stopping at the blank before the input. -/
def moveLeft (z : Input Symbol) : Input Symbol :=
  if z.atLeft then z else
    match z.left with
    | [] => { z with atLeft := true }
    | a :: l => ⟨l, a :: z.right, false⟩

/-- Move right, stopping at the blank after the input. -/
def moveRight (z : Input Symbol) : Input Symbol :=
  if z.atLeft then { z with atLeft := false } else
    match z.right with
    | [] => z
    | a :: r => ⟨a :: z.left, r, false⟩

/-- Move the input head in the indicated direction. -/
def move (z : Input Symbol) : SignType → Input Symbol
  | .neg => z.moveLeft
  | .zero => z
  | .pos => z.moveRight

/-- The stacks reconstruct the input and locate the head at the native bounded position. -/
structure Represents (z : Input Symbol) (input : List Symbol)
    (pos : Fin (input.length + 2)) : Prop where
  /-- The two stacks hold exactly the original input. -/
  contents : z.left.reverse ++ z.right = input
  /-- No symbols precede the left boundary. -/
  left_nil : z.atLeft = true → z.left = []
  /-- Native positions count the left boundary as zero. -/
  pos_eq : pos.val = if z.atLeft then 0 else z.left.length + 1

/-- Initialization agrees with the native initial head position, including on empty input. -/
theorem represents_init (input : List Symbol) :
    (init input).Represents input ⟨1, by omega⟩ := by
  constructor <;> simp [init]

namespace Represents

variable {z : Input Symbol} {input : List Symbol} {pos : Fin (input.length + 2)}

/-- The stacks retain exactly the number of input symbols. -/
theorem length_eq (h : z.Represents input pos) :
    z.left.length + z.right.length = input.length := by
  simpa only [List.length_append, List.length_reverse] using congrArg List.length h.contents

/-- A zipper read agrees with indexing the original input at the native head position. -/
theorem read_eq_getElem? (h : z.Represents input pos) :
    z.read = if pos.val = 0 then none else input[pos.val - 1]? := by
  rcases z with ⟨l, r, b⟩
  cases b with
  | false =>
    have hp : pos.val = l.length + 1 := h.pos_eq
    have hi : input = l.reverse ++ r := h.contents.symm
    simp [read, hp, hi, List.getElem?_append_right, List.head?_eq_getElem?]
  | true => simp [read, h.pos_eq]

/-- A zipper read agrees with the input symbol of any represented native configuration. -/
theorem read_eq_inputSymbol {k : ℕ} {State : Type*} {cfg : Cfg k Symbol State input}
    (h : z.Represents input cfg.inputPos) : z.read = cfg.inputSymbol := by
  rw [h.read_eq_getElem?]
  unfold Cfg.inputSymbol
  have := cfg.inputPos.isLt
  split_ifs <;> grind

/-- Moving left preserves the representation, with clamping at the left boundary. -/
theorem moveLeft (h : z.Represents input pos) :
    z.moveLeft.Represents input (moveInputPos pos .neg) := by
  have hm := val_moveInputPos_eq pos .neg
  simp only [SignType.cast] at hm
  rcases z with ⟨l, r, b⟩
  cases b with
  | true =>
    refine ⟨h.contents, h.left_nil, ?_⟩
    have hp : pos.val = 0 := h.pos_eq
    change (moveInputPos pos .neg).val = 0
    omega
  | false =>
    cases l with
    | nil =>
      refine ⟨h.contents, ?_, ?_⟩
      · simp [Input.moveLeft]
      · have hp : pos.val = 1 := h.pos_eq
        change (moveInputPos pos .neg).val = 0
        omega
    | cons a l =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [Input.moveLeft, List.reverse_cons, List.append_assoc] using h.contents
      · simp [Input.moveLeft]
      · have hp : pos.val = (a :: l).length + 1 := h.pos_eq
        simp only [List.length_cons] at hp
        change (moveInputPos pos .neg).val = l.length + 1
        omega

/-- Moving right preserves the representation, with clamping at the right boundary. -/
theorem moveRight (h : z.Represents input pos) :
    z.moveRight.Represents input (moveInputPos pos .pos) := by
  have hm := val_moveInputPos_eq pos .pos
  simp only [SignType.cast] at hm
  have hlen := h.length_eq
  rcases z with ⟨l, r, b⟩
  change l.length + r.length = input.length at hlen
  cases b with
  | true =>
    have hl : l = [] := h.left_nil rfl
    subst l
    refine ⟨h.contents, ?_, ?_⟩
    · simp [Input.moveRight]
    · have hp : pos.val = 0 := h.pos_eq
      change (moveInputPos pos .pos).val = 1
      omega
  | false =>
    cases r with
    | nil =>
      refine ⟨h.contents, h.left_nil, ?_⟩
      have hp : pos.val = l.length + 1 := h.pos_eq
      simp only [List.length_nil, Nat.add_zero] at hlen
      change (moveInputPos pos .pos).val = l.length + 1
      omega
    | cons a r =>
      refine ⟨?_, ?_, ?_⟩
      · simpa [Input.moveRight, List.reverse_cons, List.append_assoc] using h.contents
      · simp [Input.moveRight]
      · have hp : pos.val = l.length + 1 := h.pos_eq
        simp only [List.length_cons] at hlen
        change (moveInputPos pos .pos).val = l.length + 1 + 1
        omega

/-- Each zipper move simulates the corresponding native bounded head move. -/
theorem move (h : z.Represents input pos) (d : SignType) :
    (z.move d).Represents input (moveInputPos pos d) := by
  cases d with
  | neg => exact h.moveLeft
  | zero =>
    change z.Represents input (moveInputPos pos 0)
    rwa [moveInputPos_zero]
  | pos => exact h.moveRight

end Represents
end Input
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine, Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Bolton Bailey, Samuel Schlesinger
-/



/-!
# Raw two-stack work tapes

A work tape is stored as its current cell and two lists, nearest cell first. Blanks are retained:
moving beyond the stored interval extends it by one blank cell. Thus storage records the interval
visited by the head, independently of the number of times the machine revisits cells.
The relative read and representation proofs adapt the `BiTape` API of Bolton Bailey and
Samuel Schlesinger to raw lists.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.RawTape`: the current cell and the raw left and right stacks.
* `Turing.MultiTapeTM.ToTM2.RawTape.step`: native optional writing followed by head movement.
* `Turing.MultiTapeTM.ToTM2.RawTape.Represents`: correspondence with an integer-indexed native tape.

## Main results

* `Turing.MultiTapeTM.ToTM2.RawTape.Represents.step`: preservation of native tape semantics.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A work tape with raw stacks, ordered from the head outwards. Trailing blanks are retained. -/
@[ext] structure RawTape (Symbol : Type*) where
  /-- The cell under the head. -/
  head : Option Symbol
  /-- Cells strictly to the left, nearest first. -/
  left : List (Option Symbol)
  /-- Cells strictly to the right, nearest first. -/
  right : List (Option Symbol)
  deriving DecidableEq

namespace RawTape

variable {Symbol : Type*}

/-- A blank tape, initially storing just the cell at its head. -/
def init : RawTape Symbol := ⟨none, [], []⟩

instance : Inhabited (RawTape Symbol) := ⟨init⟩

/-- Perform an optional native write: `none` preserves the cell and `some none` erases it. -/
def write (t : RawTape Symbol) (w : Option (Option Symbol)) : RawTape Symbol :=
  { t with head := w.getD t.head }

@[simp] theorem write_none (t : RawTape Symbol) : t.write none = t := rfl

@[simp] theorem head_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).head = w.getD t.head := rfl

/-- Move left, extending the stored interval by a blank when the left stack is empty. -/
def moveLeft (t : RawTape Symbol) : RawTape Symbol :=
  ⟨t.left.headD none, t.left.tail, t.head :: t.right⟩

/-- Move right, extending the stored interval by a blank when the right stack is empty. -/
def moveRight (t : RawTape Symbol) : RawTape Symbol :=
  ⟨t.right.headD none, t.head :: t.left, t.right.tail⟩

/-- Apply a native work-tape action, writing before moving. -/
def step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) : RawTape Symbol :=
  match a.2 with
  | .neg => (t.write a.1).moveLeft
  | .zero => t.write a.1
  | .pos => (t.write a.1).moveRight

/-- Read at an integer offset relative to the head; unstored cells are blank. -/
def read (t : RawTape Symbol) : ℤ → Option Symbol
  | .ofNat 0 => t.head
  | .ofNat (n + 1) => t.right.getD n none
  | .negSucc n => t.left.getD n none

/-- The raw tape agrees with a native tape whose head is at `pos`. -/
def Represents (t : RawTape Symbol) (native : ℤ → Option Symbol) (pos : ℤ) : Prop :=
  ∀ z, t.read z = native (pos + z)

@[simp] theorem read_zero (t : RawTape Symbol) : t.read 0 = t.head := by simp [read]

@[simp] theorem read_init (z : ℤ) : (init : RawTape Symbol).read z = none := by
  cases z with
  | ofNat n => cases n <;> simp [read, init]
  | negSucc n => simp [read, init]

theorem read_write (t : RawTape Symbol) (w : Option (Option Symbol)) (z : ℤ) :
    (t.write w).read z = if z = 0 then w.getD t.head else t.read z := by
  cases z with
  | ofNat n => cases n <;> simp [read, write, add_eq_zero_iff_eq_neg]
  | negSucc n => simp [read, write]

theorem read_moveLeft (t : RawTape Symbol) (z : ℤ) :
    t.moveLeft.read z = t.read (z - 1) := by
  rcases t with ⟨h, l, r⟩
  cases z with
  | ofNat n =>
    cases n with
    | zero => cases l <;> rfl
    | succ n =>
      have he : (Int.ofNat (n + 1) : ℤ) - 1 = Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [he]
      cases n <;> rfl
  | negSucc n =>
    have he : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    rw [he]
    cases l <;> rfl

theorem read_moveRight (t : RawTape Symbol) (z : ℤ) :
    t.moveRight.read z = t.read (z + 1) := by
  rcases t with ⟨h, l, r⟩
  cases z with
  | ofNat n =>
    have he : (Int.ofNat n : ℤ) + 1 = Int.ofNat (n + 1) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [he]
    cases n <;> cases r <;> rfl
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n =>
      have he : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [he]
      rfl

theorem Represents.head {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.head = native pos := by
  simpa using h 0

theorem Represents.init : (init : RawTape Symbol).Represents (fun _ => none) 0 := by
  intro z
  exact read_init z

theorem Represents.write {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) (w : Option (Option Symbol)) :
    (t.write w).Represents (match w with
      | none => native
      | some s => Function.update native pos s) pos := by
  intro z
  rw [read_write]
  cases w with
  | none =>
    by_cases hz : z = 0
    · subst z; simpa using h 0
    · simpa [hz] using h z
  | some s =>
    by_cases hz : z = 0
    · subst z; simp
    · simpa [hz, show pos + z ≠ pos by omega] using h z

theorem Represents.moveLeft {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.moveLeft.Represents native (pos - 1) := by
  intro z
  rw [read_moveLeft, h]
  congr 1
  omega

theorem Represents.moveRight {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) : t.moveRight.Represents native (pos + 1) := by
  intro z
  rw [read_moveRight, h]
  congr 1
  omega

/-- Raw execution preserves a native optional-write-and-move action, including erasing cells. -/
theorem Represents.step {t : RawTape Symbol} {native : ℤ → Option Symbol} {pos : ℤ}
    (h : t.Represents native pos) (a : Option (Option Symbol) × SignType) :
    (t.step a).Represents (match a.1 with
      | none => native
      | some s => Function.update native pos s) (pos + a.2) := by
  rcases a with ⟨w, d⟩
  cases w <;> cases d
  · simpa only [RawTape.step, SignType.cast, add_zero] using h.write none
  · simpa only [RawTape.step, SignType.cast, sub_eq_add_neg] using (h.write none).moveLeft
  · simpa only [RawTape.step, SignType.cast] using (h.write none).moveRight
  · simpa only [RawTape.step, SignType.cast, add_zero] using h.write (some _)
  · simpa only [RawTape.step, SignType.cast, sub_eq_add_neg] using (h.write (some _)).moveLeft
  · simpa only [RawTape.step, SignType.cast] using (h.write (some _)).moveRight

@[simp] theorem left_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).left = t.left := rfl

@[simp] theorem right_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).right = t.right := rfl

@[simp] theorem length_left_moveLeft (t : RawTape Symbol) :
    t.moveLeft.left.length = t.left.length - 1 := by simp [moveLeft]

@[simp] theorem length_right_moveLeft (t : RawTape Symbol) :
    t.moveLeft.right.length = t.right.length + 1 := rfl

@[simp] theorem length_left_moveRight (t : RawTape Symbol) :
    t.moveRight.left.length = t.left.length + 1 := rfl

@[simp] theorem length_right_moveRight (t : RawTape Symbol) :
    t.moveRight.right.length = t.right.length - 1 := by simp [moveRight]

/-- The exact left-stack length after an action. -/
theorem length_left_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).left.length = match a.2 with
      | .neg => t.left.length - 1
      | .zero => t.left.length
      | .pos => t.left.length + 1 := by
  rcases a with ⟨w, d⟩
  cases d <;> simp only [step, length_left_moveLeft, length_left_moveRight, left_write]

/-- The exact right-stack length after an action. -/
theorem length_right_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).right.length = match a.2 with
      | .neg => t.right.length + 1
      | .zero => t.right.length
      | .pos => t.right.length - 1 := by
  rcases a with ⟨w, d⟩
  cases d <;> simp only [step, length_right_moveLeft, length_right_moveRight, right_write]

/-- The number of stored cells, including the current cell and stored blanks. -/
def span (t : RawTape Symbol) : ℕ := t.left.length + t.right.length + 1

@[simp] theorem span_init : (init : RawTape Symbol).span = 1 := rfl

@[simp] theorem span_write (t : RawTape Symbol) (w : Option (Option Symbol)) :
    (t.write w).span = t.span := rfl

/-- Storage grows only when the head moves beyond the previously stored interval. -/
theorem span_step (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).span = t.span +
      if (a.2 = .neg ∧ t.left = []) ∨ (a.2 = .pos ∧ t.right = []) then 1 else 0 := by
  rcases a with ⟨w, d⟩
  cases d <;> cases hl : t.left <;> cases hr : t.right <;>
    simp [span, length_left_step, length_right_step, hl, hr,
      Nat.add_comm, Nat.add_left_comm]

theorem span_step_le (t : RawTape Symbol) (a : Option (Option Symbol) × SignType) :
    (t.step a).span ≤ t.span + 1 := by
  rw [span_step]
  split_ifs <;> omega

end RawTape

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# A finite stack program for deterministic multi-tape machines

The input uses a pair of binary stacks and a flag for the left boundary. Each two-sided work
tape uses two stacks over `Option Bool`, with its current cell in finite control. Output is
accumulated in reverse order. A separate cleanup phase empties all auxiliary stacks before
reversing the output and resetting the control to Mathlib's canonical `haltList` convention.

## Main definitions

* `Turing.TM2.selectList`, `Turing.TM2.select`: finite case analysis in a TM2 statement.
* `Turing.MultiTapeTM.ToTM2.machine`: the finite-alphabet stack machine.
* `Turing.MultiTapeTM.ToTM2.program`: its running, cleanup and output-reversal phases.

## References

* [C. Papadimitriou, *Computational Complexity*, Chapter 2][Papadimitriou94]
-/


namespace Turing.TM2

open Stmt

variable {K : Type} {Γ : K → Type} {Λ State : Type}

/-- Finite case analysis compiles an arbitrary table on finite control to a fixed statement. -/
def selectList [DecidableEq State] (values : List State)
    (table : State → Stmt Γ Λ State) : Stmt Γ Λ State :=
  values.foldr (fun value rest => TM2.Stmt.branch (fun state => decide (state = value)) (table value) rest)
    halt

theorem stepAux_selectList [DecidableEq State] [DecidableEq K]
    (values : List State) (table : State → Stmt Γ Λ State)
    (state : State) (store : ∀ s, List (Γ s)) (h : state ∈ values) :
    stepAux (selectList values table) state store = stepAux (table state) state store := by
  induction values with
  | nil => simp at h
  | cons value values ih =>
    simp only [selectList, List.foldr_cons, stepAux]
    by_cases heq : state = value
    · subst value
      simp
    · simp only [heq, decide_false, Bool.cond_false]
      exact ih (List.mem_of_ne_of_mem heq h)

open scoped Classical in
/-- A table on a finite type uses only finitely many branches. -/
noncomputable def select [Fintype State] (table : State → Stmt Γ Λ State) : Stmt Γ Λ State :=
  selectList (Finset.univ.toList) table

theorem stepAux_select [Fintype State] [DecidableEq K]
    (table : State → Stmt Γ Λ State)
    (state : State) (store : ∀ s, List (Γ s)) :
    stepAux (select table) state store = stepAux (table state) state store := by
  classical
  exact stepAux_selectList _ _ _ _ (by simp)

end Turing.TM2

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- The four binary stacks and the two stacks for every work tape. -/
inductive Stack (k : ℕ) where
  | input | before | output | reversed
  | work (tape : Fin k) (right : Bool)
  deriving DecidableEq, Fintype

/-- Work stacks store blank cells explicitly; the input and output alphabets are binary. -/
abbrev Alphabet : Stack k → Type
  | .work _ _ => Option Bool
  | _ => Bool

instance (s : Stack k) : Fintype (Alphabet s) := by
  cases s <;> unfold Alphabet <;> infer_instance

/-- The three phases have no unbounded counters in their control. -/
inductive Label where
  | run | clean | reverse
  deriving DecidableEq

instance : Fintype Label := ⟨{.run, .clean, .reverse}, by intro l; cases l <;> simp⟩

/-- All unbounded data live on stacks. `symbol` and `busy` are scratch registers. -/
@[ext] structure Control (k : ℕ) (State : Type) where
  /-- The source state, or `none` when its final action has executed. -/
  state : Option State
  /-- Whether the bounded input head is at the blank before the word. -/
  atLeft : Bool
  /-- The current cell on each work tape. -/
  head : Fin k → Option Bool
  /-- A scratch register for input movement and output reversal. -/
  symbol : Option Bool
  /-- Whether the current cleanup round found a nonempty auxiliary stack. -/
  busy : Bool
  deriving Fintype

/-- Initial finite control, also restored before halting. -/
def initialControl (q : State) : Control k State :=
  ⟨some q, false, fun _ => none, none, false⟩

/-- A statement over the compiler's stack alphabets, phases and finite control. -/
abbrev Statement (k : ℕ) (State : Type) :=
  TM2.Stmt (Alphabet (k := k)) Label (Control k State)

open TM2.Stmt

/-- Write the current work cell, retaining the old value when no write is requested. -/
def writeWork (i : Fin k) (write : Option (Option Bool)) (next : Statement k State) :
    Statement k State :=
  load (fun v => { v with head := Function.update v.head i (write.getD (v.head i)) }) next

/-- Moving a work head transfers its old current cell to the opposite stack. -/
def moveWork (i : Fin k) (direction : SignType) (next : Statement k State) :
    Statement k State :=
  match direction with
  | .zero => next
  | .neg => push (.work i true) (fun v => v.head i)
      (pop (.work i false) (fun v a => { v with head := Function.update v.head i (a.getD none) })
        next)
  | .pos => push (.work i false) (fun v => v.head i)
      (pop (.work i true) (fun v a => { v with head := Function.update v.head i (a.getD none) })
        next)

/-- A fixed native work-tape action is a bounded straight-line stack statement. -/
def workAction (i : Fin k) (action : Option (Option Bool) × SignType)
    (next : Statement k State) : Statement k State :=
  writeWork i action.1 (moveWork i action.2 next)

/-- Move the bounded read-only input head. Empty stacks detect the two boundaries. -/
def moveInput (direction : SignType) (next : Statement k State) : Statement k State :=
  match direction with
  | .zero => next
  | .neg => TM2.Stmt.branch (fun v => v.atLeft) next
      (pop .before (fun v a => { v with symbol := a })
        (TM2.Stmt.branch (fun v => v.symbol.isSome)
          (push .input (fun v => v.symbol.getD false) next)
          (load (fun v => { v with atLeft := true }) next)))
  | .pos => TM2.Stmt.branch (fun v => v.atLeft) (load (fun v => { v with atLeft := false }) next)
      (pop .input (fun v a => { v with symbol := a })
        (TM2.Stmt.branch (fun v => v.symbol.isSome)
          (push .before (fun v => v.symbol.getD false) next) next))

/-- A source step updates every work tape, the input head, output and control. -/
def action (a : Turing.Action k Bool State) : Statement k State :=
  (List.finRange k).foldr (fun i next => workAction i (a.workTapes i) next)
    (moveInput a.inputTape
      (a.output.elim id (fun b => push .reversed (fun _ => b))
        (load (fun v => { v with state := a.state, symbol := none, busy := false })
          (goto (fun _ => .run)))))

/-- Stacks discarded before output reversal. -/
def auxiliaries (k : ℕ) : List (Stack k) :=
  [.input, .before] ++ (List.finRange k).flatMap (fun i => [.work i false, .work i true])

/-- Discard one cell from each auxiliary stack and remember whether any was nonempty. -/
def discard (s : Stack k) (next : Statement k State) : Statement k State :=
  pop s (fun v a => { v with busy := v.busy || a.isSome }) next

/-- A cleanup round either reduces auxiliary storage or advances to output reversal. -/
def clean : Statement k State :=
  load (fun v => { v with busy := false })
    ((auxiliaries k).foldr discard
      (TM2.Stmt.branch (fun v => v.busy) (goto (fun _ => .clean)) (goto (fun _ => .reverse))))

/-- The fixed program has finite control and a finite alphabet on every stack. -/
def program [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    Label → Statement k State
  | .run => peek .input (fun v a => { v with symbol := a })
      (TM2.select fun v => match v.state with
        | none => goto (fun _ => .clean)
        | some q => action (transition q (if v.atLeft then none else v.symbol) v.head))
  | .clean => clean
  | .reverse => pop .reversed (fun v a => { v with symbol := a })
      (TM2.Stmt.branch (fun v => v.symbol.isSome)
        (push .output (fun v => v.symbol.getD false) (goto (fun _ => .reverse)))
        (load (fun _ => initialControl q₀) halt))

/-- The actual Mathlib `FinTM2` produced by the reverse compiler. -/
abbrev machine [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    FinTM2 where
  K := Stack k
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .run
  σ := Control k State
  initialState := initialControl q₀
  m := program q₀ transition

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Raw configurations for the multi-tape to TM2 compiler

## Main definitions

* `Turing.MultiTapeTM.ToTM2.Data`: finite stacks representing a binary native configuration.
* `Turing.MultiTapeTM.ToTM2.Data.step`: apply one native action to the raw configuration.
* `Turing.MultiTapeTM.ToTM2.Data.run`: execute a native machine with raw stacks.
* `Turing.MultiTapeTM.ToTM2.Data.Represents`: agreement with a native configuration.

## Main results

* `Turing.MultiTapeTM.ToTM2.Data.represents_run`: raw execution agrees with native execution.
* `Turing.MultiTapeTM.ToTM2.Data.input_length_run`: input storage is exactly the input length.
* `Turing.MultiTapeTM.ToTM2.Data.output_prefix_run`: chronological output grows by extension.
-/


namespace Turing.MultiTapeTM.ToTM2

/-- A native binary configuration stored as finite stacks, with chronological output. -/
@[ext]
structure Data (k : ℕ) (State : Type) where
  /-- The current state, or `none` after halting. -/
  state : Option State
  /-- The bounded read-only input zipper. -/
  input : Input Bool
  /-- The work tapes, retaining all visited cells. -/
  work : Fin k → RawTape Bool
  /-- Symbols emitted so far, in chronological order. -/
  output : List Bool

namespace Data

variable {k : ℕ} {State : Type}

/-- Initialize the input zipper and blank work tapes. -/
def init (q₀ : State) (input : List Bool) : Data k State :=
  ⟨some q₀, Input.init input, fun _ => RawTape.init, []⟩

/-- Apply an action, including the output and movement of its final halting step. -/
def step (d : Data k State) (a : Action k Bool State) : Data k State where
  state := a.state
  input := d.input.move a.inputTape
  work i := (d.work i).step (a.workTapes i)
  output := d.output ++ a.output.toList

/-- Select and apply the native transition, staying put once halted. -/
noncomputable def totalStep (tm : MultiTapeTM k Bool State) (d : Data k State) : Data k State :=
  match d.state with
  | none => d
  | some q => d.step (tm.tr q d.input.read (fun i => (d.work i).head))

/-- Execute a fixed number of total steps from an arbitrary raw configuration. -/
noncomputable def runFrom (tm : MultiTapeTM k Bool State) (d : Data k State) (t : ℕ) :
    Data k State :=
  (totalStep tm)^[t] d

/-- Execute a fixed number of total steps from the initial raw configuration. -/
noncomputable def run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    Data k State :=
  runFrom tm (init tm.q₀ input) t

/-- Raw fields agree with the corresponding native state, heads, tapes and output. -/
structure Represents (d : Data k State) {sourceInput : List Bool}
    (cfg : Cfg k Bool State sourceInput) : Prop where
  /-- The control states agree. -/
  state : d.state = cfg.state
  /-- The input zipper represents the native bounded head. -/
  input : d.input.Represents sourceInput cfg.inputPos
  /-- Each work tape represents its native integer-indexed tape and head. -/
  work : ∀ i, (d.work i).Represents (cfg.workTapes i) (cfg.workTapePos i)
  /-- Output is chronological in both representations. -/
  output : d.output = cfg.output

@[simp]
theorem runFrom_zero (tm : MultiTapeTM k Bool State) (d : Data k State) :
    runFrom tm d 0 = d := by rfl

/-- The next raw configuration is one total step from the preceding configuration. -/
theorem runFrom_succ (tm : MultiTapeTM k Bool State) (d : Data k State) (t : ℕ) :
    runFrom tm d (t + 1) = totalStep tm (runFrom tm d t) := by
  exact Function.iterate_succ_apply' _ _ _

@[simp]
theorem run_zero (tm : MultiTapeTM k Bool State) (input : List Bool) :
    run tm input 0 = init tm.q₀ input := by rfl

/-- The next raw configuration on an input is obtained by one total step. -/
theorem run_succ (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    run tm input (t + 1) = totalStep tm (run tm input t) := by
  exact runFrom_succ _ _ _

/-- Halted raw configurations are fixed by the total step. -/
theorem totalStep_of_halt (tm : MultiTapeTM k Bool State) {d : Data k State}
    (h : d.state = none) : totalStep tm d = d := by
  rw [totalStep, h]

/-- A live raw configuration applies the transition selected from its current reads. -/
theorem totalStep_of_state (tm : MultiTapeTM k Bool State) {d : Data k State} {q : State}
    (h : d.state = some q) :
    totalStep tm d = d.step (tm.tr q d.input.read (fun i => (d.work i).head)) := by
  rw [totalStep, h]

namespace Represents

variable {d : Data k State} {sourceInput : List Bool} {cfg : Cfg k Bool State sourceInput}

/-- Initialization represents the native initial configuration. -/
theorem init (q₀ : State) (input : List Bool) :
    (Data.init (k := k) q₀ input).Represents (Cfg.init q₀ input) :=
  ⟨rfl, Input.represents_init input, fun _ => RawTape.Represents.init, rfl⟩

/-- Applying the same action preserves every field of the representation. -/
theorem step (h : d.Represents cfg) (a : Action k Bool State) :
    (d.step a).Represents (a.apply cfg) :=
  ⟨rfl, h.input.move a.inputTape, fun i => (h.work i).step (a.workTapes i),
    congrArg (· ++ a.output.toList) h.output⟩

/-- Raw and native configurations select the same action and take corresponding total steps. -/
theorem totalStep (h : d.Represents cfg) (tm : MultiTapeTM k Bool State) :
    (Data.totalStep tm d).Represents (tm.step cfg) := by
  cases hs : d.state with
  | none =>
    rw [Data.totalStep_of_halt tm hs, tm.step_of_halt (h.state.symm.trans hs)]
    exact h
  | some q =>
    rw [Data.totalStep_of_state tm hs, tm.step_of_state (h.state.symm.trans hs)]
    have hi : d.input.read = cfg.inputSymbol := h.input.read_eq_inputSymbol
    have hw : (fun i => (d.work i).head) = cfg.workTapeSymbols :=
      funext fun i => (h.work i).head
    rw [hi, hw]
    exact h.step _

/-- Any number of raw total steps represents the same number of native total steps. -/
theorem runFrom (h : d.Represents cfg) (tm : MultiTapeTM k Bool State) (t : ℕ) :
    (Data.runFrom tm d t).Represents (tm.runFrom cfg t) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Data.runFrom_succ, MultiTapeTM.runFrom, Function.iterate_succ_apply',
      ← MultiTapeTM.runFrom]
    exact ih.totalStep tm

end Represents

/-- Raw execution from initialization agrees with the native execution, even after halting. -/
theorem represents_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).Represents (tm.runFrom (tm.initCfg input) t) :=
  (Represents.init tm.q₀ input).runFrom tm t

/-- At every time, the raw input stacks retain exactly the original input length. -/
theorem input_length_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).input.left.length + (run tm input t).input.right.length = input.length :=
  (represents_run tm input t).input.length_eq

/-- The raw output is exactly the native chronological output. -/
theorem output_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).output = (tm.runFrom (tm.initCfg input) t).output :=
  (represents_run tm input t).output

/-- The raw control state agrees with the native state at every time. -/
theorem state_run (tm : MultiTapeTM k Bool State) (input : List Bool) (t : ℕ) :
    (run tm input t).state = (tm.runFrom (tm.initCfg input) t).state :=
  (represents_run tm input t).state

/-- Each action only appends to the output. -/
theorem output_prefix_step (d : Data k State) (a : Action k Bool State) :
    d.output <+: (d.step a).output :=
  ⟨a.output.toList, rfl⟩

/-- Total steps only append to the output, including a step which halts. -/
theorem output_prefix_totalStep (tm : MultiTapeTM k Bool State) (d : Data k State) :
    d.output <+: (totalStep tm d).output := by
  cases hs : d.state with
  | none => rw [totalStep_of_halt tm hs]
  | some q => rw [totalStep_of_state tm hs]; exact output_prefix_step _ _

/-- Earlier raw outputs are prefixes of all later raw outputs. -/
theorem output_prefix_run (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t u : ℕ} (h : t ≤ u) : (run tm input t).output <+: (run tm input u).output := by
  induction u, h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ u _ ih =>
    rw [run_succ]
    exact ih.trans (output_prefix_totalStep tm _)

/-- The amount of output never decreases. -/
theorem output_length_run_mono (tm : MultiTapeTM k Bool State) (input : List Bool) :
    Monotone (fun t => (run tm input t).output.length) :=
  fun _ _ h => (output_prefix_run tm input h).length_le

/-- Raw execution stays at its final configuration after halting. -/
theorem run_eq_of_halt (tm : MultiTapeTM k Bool State) (input : List Bool) {t u : ℕ}
    (hle : t ≤ u) (hhalt : (run tm input t).state = none) :
    run tm input u = run tm input t := by
  induction u, hle using Nat.le_induction with
  | base => rfl
  | succ u _ ih => rw [run_succ, ih, totalStep_of_halt tm hhalt]

/-- Every intermediate output is bounded by the output of a terminating run. -/
theorem output_length_run_le_of_halt (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t : ℕ} (hhalt : (run tm input t).state = none) (u : ℕ) :
    (run tm input u).output.length ≤ (run tm input t).output.length := by
  rcases le_total u t with h | h
  · exact output_length_run_mono tm input h
  · rw [run_eq_of_halt tm input h hhalt]

/-- Every raw output is a prefix of the complete output of a terminating native computation. -/
theorem output_prefix_run_of_computes {tm : MultiTapeTM k Bool State}
    {input output : List Bool} (h : tm.Computes input output) (t : ℕ) :
    (run tm input t).output <+: output := by
  obtain ⟨u, hhalt, hout⟩ := h
  have hraw : (run tm input u).output = output := (output_run tm input u).trans hout
  rcases le_total t u with h | h
  · exact hraw ▸ output_prefix_run tm input h
  · rw [run_eq_of_halt tm input h ((state_run tm input u).trans hhalt), hraw]

/-- A terminating native output bounds every intermediate raw output, without a time term. -/
theorem output_length_run_le_of_computes {tm : MultiTapeTM k Bool State}
    {input output : List Bool} (h : tm.Computes input output) (t : ℕ) :
    (run tm input t).output.length ≤ output.length :=
  (output_prefix_run_of_computes h t).length_le

end Data
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Stack representation for the reverse TM2 compiler

Each native transition compiles to one fixed Mathlib stack-machine statement. The finite control
holds the current work cells; raw stacks retain blank cells and preserve the two-sided geometry.

## Main definitions

* `Turing.MultiTapeTM.ToTM2.encode`: represent a raw configuration at a source-step boundary.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Finite control corresponding to raw simulation data, with arbitrary scratch registers. -/
def control (d : Data k State) (symbol : Option Bool := none) (busy : Bool := false) :
    Control k State := ⟨d.state, d.input.atLeft, fun i => (d.work i).head, symbol, busy⟩

/-- The stack representation keeps output in reverse order until cleanup. -/
def store (d : Data k State) : (s : Stack k) → List (Alphabet s)
  | .input => d.input.right
  | .before => d.input.left
  | .output => []
  | .reversed => d.output.reverse
  | .work i false => (d.work i).left
  | .work i true => (d.work i).right

/-- The TM2 configuration at a source-step boundary. -/
def encode (d : Data k State) : TM2.Cfg (Alphabet (k := k)) Label (Control k State) :=
  ⟨some .run, control d, store d⟩

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Compiled input movement and output emission

## Main definitions

* `Turing.MultiTapeTM.ToTM2.inputSymbol`: the scratch symbol after compiled input movement.

## Main results

* `Turing.MultiTapeTM.ToTM2.stepAux_moveInput`: compiled movement agrees with the raw input
  zipper, without a validity assumption.
* `Turing.MultiTapeTM.ToTM2.stepAux_finish`: emit an optional bit and restore boundary control.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Input movement retains scratch at the left boundary and otherwise remembers the popped bit. -/
def inputSymbol (d : Data k State) (direction : SignType) (scratch : Option Bool) : Option Bool :=
  if d.input.atLeft then scratch else
    match direction with
    | .zero => scratch
    | .neg => d.input.left.head?
    | .pos => d.input.right.head?

/-- The compiled input movement agrees with the zipper on every raw configuration. -/
theorem stepAux_moveInput (d : Data k State) (direction : SignType)
    (next : Statement k State) (scratch : Option Bool) (busy : Bool) :
    TM2.stepAux (moveInput direction next) (control d scratch busy) (store d) =
      TM2.stepAux next
        (control { d with input := d.input.move direction } (inputSymbol d direction scratch) busy)
        (store { d with input := d.input.move direction }) := by
  classical
  rcases d with ⟨state, ⟨left, right, atLeft⟩, work, output⟩
  cases direction <;> cases atLeft
  all_goals try rfl
  all_goals cases left <;> cases right
  all_goals
    simp only [moveInput, TM2.stepAux, control, store, inputSymbol, Input.move, Input.moveLeft,
      Input.moveRight]
  all_goals simp only [Alphabet, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
    Option.isSome_none, Option.isSome_some, Bool.cond_true, Bool.cond_false,
    Option.getD_some, Bool.false_eq_true, ↓reduceIte]
  all_goals
    congr 1
    funext s
    cases s with
    | work i side => cases side <;> simp [Function.update, store]
    | output => simp only [Function.update, store]; rfl
    | _ => simp [Function.update, store]

/-- Emitting an optional bit and loading the next source state restores a step boundary. -/
theorem stepAux_finish (d : Data k State) (state : Option State) (output : Option Bool)
    (scratch : Option Bool) (busy : Bool) :
    TM2.stepAux
      (output.elim id (fun b => TM2.Stmt.push .reversed (fun _ => b))
        (TM2.Stmt.load (fun v => { v with state := state, symbol := none, busy := false })
          (TM2.Stmt.goto (fun _ => .run))))
      (control d scratch busy) (store d) =
      encode { d with state := state, output := d.output ++ output.toList } := by
  classical
  cases output with
  | none =>
    simp only [Option.elim, encode, Option.toList_none, List.append_nil]
    congr 1
  | some b =>
    simp only [Option.elim, TM2.stepAux, encode, Option.toList_some]
    congr 1
    funext s
    cases s with
    | work i side => cases side <;> simp [Function.update, store]
    | output => simp only [Function.update, store]; rfl
    | _ => simp [Function.update, store]

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Execution correspondence for the reverse TM2 compiler

Each native transition compiles to one fixed Mathlib stack-machine statement. The finite control
holds the current work cells; raw stacks retain blank cells and preserve the two-sided geometry.

## Main results

* `Turing.MultiTapeTM.ToTM2.stepAux_action`: a compiled action realizes the raw tape update.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

private theorem control_write (d : Data k State) (i : Fin k) (w : Option (Option Bool))
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with
      head := (Function.update (control d symbol busy).head i
        (w.getD ((control d symbol busy).head i))) }
      = control { d with work := Function.update d.work i ((d.work i).write w) } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i <;> simp [Function.update, control, RawTape.write, h]

private theorem store_write (d : Data k State) (i : Fin k) (w : Option (Option Bool)) :
    store { d with work := Function.update d.work i ((d.work i).write w) } = store d := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i <;> cases side <;> simp [store, RawTape.write, h]
  | _ => rfl

private theorem stepAux_writeWork (d : Data k State) (i : Fin k) (w : Option (Option Bool))
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (writeWork i w next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).write w) } symbol busy)
        (store { d with work := Function.update d.work i ((d.work i).write w) }) := by
  simp only [writeWork, TM2.stepAux, control_write, store_write]

private theorem control_moveLeft (d : Data k State) (i : Fin k)
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with head := (Function.update (control d symbol busy).head i
      (((store d (.work i false)).head?).getD none)) } =
      control { d with work := Function.update d.work i (d.work i).moveLeft } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i
  · subst j
    simp only [control, store, RawTape.moveLeft, List.headD_eq_head?_getD, Function.update_self]
  · simp only [control, store, RawTape.moveLeft, List.headD_eq_head?_getD, Function.update_of_ne h]

private theorem store_moveLeft (d : Data k State) (i : Fin k) :
    Function.update
      (Function.update (store d) (.work i true) ((d.work i).head :: (d.work i).right))
      (.work i false) (d.work i).left.tail =
      store { d with work := Function.update d.work i (d.work i).moveLeft } := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i
    · subst j; cases side <;> simp [Function.update, store, RawTape.moveLeft]
    · cases side <;> simp [Function.update, store, h]
  | _ => rfl

private theorem control_moveRight (d : Data k State) (i : Fin k)
    (symbol : Option Bool) (busy : Bool) :
    { control d symbol busy with head := (Function.update (control d symbol busy).head i
      (((store d (.work i true)).head?).getD none)) } =
      control { d with work := Function.update d.work i (d.work i).moveRight } symbol busy := by
  apply Control.ext <;> try rfl
  funext j
  by_cases h : j = i
  · subst j
    simp only [control, store, RawTape.moveRight, List.headD_eq_head?_getD, Function.update_self]
  · simp only [control, store, RawTape.moveRight, List.headD_eq_head?_getD, Function.update_of_ne h]

private theorem store_moveRight (d : Data k State) (i : Fin k) :
    Function.update
      (Function.update (store d) (.work i false) ((d.work i).head :: (d.work i).left))
      (.work i true) (d.work i).right.tail =
      store { d with work := Function.update d.work i (d.work i).moveRight } := by
  funext s
  cases s with
  | work j side =>
    by_cases h : j = i
    · subst j; cases side <;> simp [Function.update, store, RawTape.moveRight]
    · cases side <;> simp [Function.update, store, h]
  | _ => rfl

private theorem stepAux_moveWork (d : Data k State) (i : Fin k) (direction : SignType)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (moveWork i direction next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).step (none, direction)) }
          symbol busy)
        (store
          { d with work := Function.update d.work i ((d.work i).step (none, direction)) }) := by
  cases direction with
  | zero => simp [moveWork, RawTape.step, RawTape.write, Function.update_eq_self]
  | neg =>
    simp only [moveWork, TM2.stepAux]
    rw [Function.update_of_ne (by simp : Stack.work i false ≠ Stack.work i true)]
    change TM2.stepAux next
      { control d symbol busy with head := (Function.update (control d symbol busy).head i
        (((store d (.work i false)).head?).getD none)) }
      (Function.update
        (Function.update (store d) (.work i true) ((d.work i).head :: (d.work i).right))
        (.work i false) (d.work i).left.tail) = _
    rw [control_moveLeft, store_moveLeft]
    rfl
  | pos =>
    simp only [moveWork, TM2.stepAux]
    rw [Function.update_of_ne (by simp : Stack.work i true ≠ Stack.work i false)]
    change TM2.stepAux next
      { control d symbol busy with head := (Function.update (control d symbol busy).head i
        (((store d (.work i true)).head?).getD none)) }
      (Function.update
        (Function.update (store d) (.work i false) ((d.work i).head :: (d.work i).left))
        (.work i true) (d.work i).right.tail) = _
    rw [control_moveRight, store_moveRight]
    rfl

private theorem stepAux_workAction (d : Data k State) (i : Fin k)
    (a : Option (Option Bool) × SignType) (next : Statement k State)
    (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (workAction i a next) (control d symbol busy) (store d) =
      TM2.stepAux next
        (control { d with work := Function.update d.work i ((d.work i).step a) } symbol busy)
        (store { d with work := Function.update d.work i ((d.work i).step a) }) := by
  rw [workAction, stepAux_writeWork, stepAux_moveWork]
  cases a with | mk w direction =>
    cases direction <;> simp [RawTape.step, RawTape.write, Function.update_idem]

private def applyWorks (d : Data k State)
    (a : Fin k → Option (Option Bool) × SignType) (indices : List (Fin k)) : Data k State :=
  indices.foldl (fun d i => { d with work := Function.update d.work i ((d.work i).step (a i)) }) d

private theorem stepAux_workActions (indices : List (Fin k))
    (a : Fin k → Option (Option Bool) × SignType) (d : Data k State)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (indices.foldr (fun i next => workAction i (a i) next) next)
      (control d symbol busy) (store d) =
      TM2.stepAux next (control (applyWorks d a indices) symbol busy)
        (store (applyWorks d a indices)) := by
  induction indices generalizing d with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldr_cons, stepAux_workAction, ih]
    rfl

private theorem applyWorks_eq (indices : List (Fin k)) (h : indices.Nodup)
    (a : Fin k → Option (Option Bool) × SignType) (d : Data k State) :
    applyWorks d a indices =
      { d with work := fun i => if i ∈ indices then (d.work i).step (a i) else d.work i } := by
  induction indices generalizing d with
  | nil => simp [applyWorks]
  | cons i indices ih =>
    rw [List.nodup_cons] at h
    change applyWorks { d with work := Function.update d.work i ((d.work i).step (a i)) }
      a indices = _
    rw [ih h.2]
    apply Data.ext <;> try rfl
    funext j
    by_cases hj : j = i
    · subst j
      simp [h.1]
    · by_cases hmem : j ∈ indices <;> simp [hj, hmem]

/-- Each work tape is updated once, in a fixed straight-line statement. -/
private theorem stepAux_allWork (a : Fin k → Option (Option Bool) × SignType) (d : Data k State)
    (next : Statement k State) (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux ((List.finRange k).foldr (fun i next => workAction i (a i) next) next)
      (control d symbol busy) (store d) =
      TM2.stepAux next (control { d with work := fun i => (d.work i).step (a i) } symbol busy)
        (store { d with work := fun i => (d.work i).step (a i) }) := by
  rw [stepAux_workActions, applyWorks_eq _ (List.nodup_finRange k)]
  simp only [List.mem_finRange, ↓reduceIte]

/-- One complete compiled action realizes the native update on finite tape data. -/
theorem stepAux_action (d : Data k State) (a : Turing.Action k Bool State)
    (symbol : Option Bool) (busy : Bool) :
    TM2.stepAux (action a) (control d symbol busy) (store d) = encode (d.step a) := by
  rw [action, stepAux_allWork, stepAux_moveInput, stepAux_finish]
  rfl

/-- One live source transition is exactly one Mathlib stack-machine transition. -/
theorem step_encode [Fintype State] (tm : MultiTapeTM k Bool State) (d : Data k State)
    {q : State} (hq : d.state = some q) :
    TM2.step (program tm.q₀ tm.tr) (encode d) = some (encode (Data.totalStep tm d)) := by
  simp only [encode, TM2.step, program, TM2.stepAux]
  rw [TM2.stepAux_select]
  change some (TM2.stepAux
    (match d.state with
    | none => TM2.Stmt.goto (fun _ => .clean)
    | some q => action (tm.tr q (if d.input.atLeft then none else d.input.right.head?)
        (fun i => (d.work i).head)))
    (control d d.input.right.head? false) (store d)) = _
  rw [hq, stepAux_action, Data.totalStep_of_state tm hq]
  rfl

/-- A halted source starts cleanup on the following target step. -/
theorem step_encode_halt [Fintype State] (tm : MultiTapeTM k Bool State) (d : Data k State)
    (hq : d.state = none) :
    TM2.step (program tm.q₀ tm.tr) (encode d) =
      some ⟨some .clean, control d d.input.right.head? false, store d⟩ := by
  simp only [encode, TM2.step, program, TM2.stepAux]
  rw [TM2.stepAux_select]
  simp only [control, hq, TM2.stepAux, store]

/-- Native initialization already has the stack layout required by the compiler. -/
theorem encode_init [Fintype State] (tm : MultiTapeTM k Bool State) (input : List Bool) :
    encode (Data.init tm.q₀ input) = initList (machine tm.q₀ tm.tr) input := by
  apply congrArg (fun s =>
    (⟨some .run, initialControl tm.q₀, s⟩ : TM2.Cfg (Alphabet (k := k)) Label (Control k State)))
  funext s
  cases s with
  | work i b => cases b <;> rfl
  | _ => rfl

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Whole-run correspondence before cleanup

The compiler executes exactly one source transition per TM2 transition until the first halting
source configuration. Its next transition enters cleanup. These statements include the final
source action, which may write, move heads and emit a bit while halting.

## Main results

* `Turing.MultiTapeTM.ToTM2.iterate_encode`: correspondence of every source execution prefix.
* `Turing.MultiTapeTM.ToTM2.prefixEvals`: the same correspondence with Mathlib's partial clock.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type} [Fintype State]

private theorem stepTotal_encode (tm : MultiTapeTM k Bool State) (d : Data k State)
    {q : State} (hq : d.state = some q) :
    TM2.stepTotal (program tm.q₀ tm.tr) (encode d) = encode (Data.totalStep tm d) :=
  Option.some.inj (step_encode tm d hq)

theorem stepTotal_encode_halt (tm : MultiTapeTM k Bool State) (d : Data k State)
    (hq : d.state = none) :
    TM2.stepTotal (program tm.q₀ tm.tr) (encode d) =
      ⟨some .clean, control d d.input.right.head? false, store d⟩ :=
  Option.some.inj (step_encode_halt tm d hq)

/-- Every source prefix through the first halted configuration is reproduced exactly. -/
theorem iterate_encode (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (TM2.stepTotal (program tm.q₀ tm.tr))^[i] (initList (machine tm.q₀ tm.tr) input) =
      encode (Data.run tm input i) := by
  induction i with
  | zero =>
    rw [Data.run_zero]
    exact (encode_init tm input).symm
  | succ i ih =>
    have hstep :
        (TM2.stepTotal (program tm.q₀ tm.tr))^[i + 1] (initList (machine tm.q₀ tm.tr) input) =
          TM2.stepTotal (program tm.q₀ tm.tr)
            ((TM2.stepTotal (program tm.q₀ tm.tr))^[i] (initList (machine tm.q₀ tm.tr) input)) :=
      Function.iterate_succ_apply' _ i _
    rw [hstep, ih (by omega)]
    have hn : (Data.run tm input i).state ≠ none := by
      rw [Data.state_run]
      exact ht.not_halted (by omega)
    cases hq : (Data.run tm input i).state with
    | none => exact False.elim (hn hq)
    | some q => rw [stepTotal_encode tm _ hq, Data.run_succ]

/-- The partial clock retains a successor throughout each source execution prefix. -/
private theorem partial_iterate_encode (tm : MultiTapeTM k Bool State) (input : List Bool)
    {t : ℕ} (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    (fun c => c.bind (machine tm.q₀ tm.tr).step)^[i]
      (some (initList (machine tm.q₀ tm.tr) input)) = some (encode (Data.run tm input i)) := by
  induction i with
  | zero =>
    rw [Data.run_zero]
    exact congrArg some (encode_init tm input).symm
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hn : (Data.run tm input i).state ≠ none := by
      rw [Data.state_run]
      exact ht.not_halted (by omega)
    cases hq : (Data.run tm input i).state with
    | none => exact False.elim (hn hq)
    | some q =>
      change TM2.step (program tm.q₀ tm.tr) (encode (Data.run tm input i)) = _
      rw [step_encode tm _ hq, Data.run_succ]

/-- Mathlib's partial execution reaches each source prefix in exactly that many transitions. -/
def prefixEvals (tm : MultiTapeTM k Bool State) (input : List Bool) {t : ℕ}
    (ht : tm.HaltsAt (tm.initCfg input) t) {i : ℕ} (hi : i ≤ t) :
    StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step
      (initList (machine tm.q₀ tm.tr) input) (some (encode (Data.run tm input i))) i :=
  ⟨⟨i, partial_iterate_encode tm input ht hi⟩, le_rfl⟩

end

end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Canonical cleanup for the multi-tape to TM2 compiler

Cleanup discards the input and work stacks, reverses the accumulated output onto the output
stack, and resets finite control. Existing output is retained as a suffix.

## Main definitions

* `StateTransition.EvalsToInTime.cons`, `.mono`: prepend one transition or enlarge the
  clock of a bounded partial execution.
* `Turing.MultiTapeTM.ToTM2.auxiliaryLength`: storage discarded by cleanup.
* `Turing.MultiTapeTM.ToTM2.totalStackLength`: storage on all stacks, including input and output.

## Main results

* `Turing.MultiTapeTM.ToTM2.cleanupEvals`: canonical halting with an explicit linear clock.

## References

* [C. Papadimitriou, *Computational Complexity*, Chapter 2][Papadimitriou94]
-/


namespace StateTransition.EvalsToInTime

/-- Prepend one transition to a bounded execution. -/
def cons {α : Type} {f : α → Option α} {a b c : α} {n : ℕ}
    (hs : f a = some b) (h : EvalsToInTime f b (some c) n) :
    EvalsToInTime f a (some c) (n + 1) where
  steps := h.steps + 1
  evals_in_steps := by
    rw [Function.iterate_succ_apply]
    change (flip bind f)^[h.steps] (f a) = some c
    rw [hs]
    exact h.evals_in_steps
  steps_le_m := Nat.add_le_add_right h.steps_le_m 1

/-- Increase the clock of a bounded execution. -/
def mono {α : Type} {f : α → Option α} {a c : α} {m n : ℕ}
    (h : EvalsToInTime f a (some c) m) (hmn : m ≤ n) :
    EvalsToInTime f a (some c) n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hmn⟩

end StateTransition.EvalsToInTime

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Exactly the stacks other than the two output stacks are discarded. -/
@[simp] theorem mem_auxiliaries (s : Stack k) :
    s ∈ auxiliaries k ↔ s ≠ .output ∧ s ≠ .reversed := by
  cases s with
  | work i b => cases b <;> simp [auxiliaries]
  | _ => simp [auxiliaries]

/-- Each auxiliary is popped exactly once in a cleanup round. -/
theorem auxiliaries_nodup (k : ℕ) : (auxiliaries k).Nodup := by
  have hp : List.Pairwise (Function.onFun List.Disjoint
      (fun i : Fin k => [Stack.work i false, Stack.work i true])) (List.finRange k) := by
    apply (List.nodup_finRange k).imp
    intro i j hij
    simp [Function.onFun, List.disjoint_left, hij]
  simpa [auxiliaries, List.nodup_append, List.nodup_flatMap, List.disjoint_left] using hp

/-- Pop each named stack once; the list is assumed duplicate-free when used operationally. -/
private def poppedStore (ss : List (Stack k)) (store : ∀ s : Stack k, List (Alphabet s)) :
    ∀ s : Stack k, List (Alphabet s) :=
  fun s => if s ∈ ss then (store s).tail else store s

private theorem poppedStore_cons (s : Stack k) (ss : List (Stack k))
    (store : ∀ s : Stack k, List (Alphabet s)) (h : s ∉ ss) :
    poppedStore ss (Function.update store s (store s).tail) = poppedStore (s :: ss) store := by
  funext t
  by_cases ht : t = s
  · subst t
    simp [poppedStore, h]
  · simp [poppedStore, ht]

private theorem any_update (s : Stack k) (ss : List (Stack k))
    (store : ∀ s : Stack k, List (Alphabet s)) (h : s ∉ ss) :
    ss.any (fun t => ((Function.update store s (store s).tail) t).head?.isSome) =
      ss.any (fun t => (store t).head?.isSome) := by
  induction ss with
  | nil => rfl
  | cons t ss ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.any_cons, Function.update_of_ne (Ne.symm h.1), ih h.2]

/-- The straight-line discard statement records whether a stack was nonempty before popping. -/
private theorem stepAux_discard (ss : List (Stack k)) (hss : ss.Nodup)
    (next : Statement k State) (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux (ss.foldr discard next) v store =
      TM2.stepAux next
        { v with busy := v.busy || ss.any (fun s => (store s).head?.isSome) }
        (poppedStore ss store) := by
  induction ss generalizing v store with
  | nil =>
    have hs : poppedStore [] store = store := by funext s; simp [poppedStore]
    simp only [List.foldr_nil, List.any_nil, Bool.or_false, hs]
  | cons s ss ih =>
    rw [List.nodup_cons] at hss
    simp only [List.foldr_cons, discard, TM2.stepAux]
    rw [ih hss.2, poppedStore_cons s ss store hss.1, any_update s ss store hss.1]
    simp [Bool.or_assoc]

/-- Total auxiliary storage before a cleanup round. -/
def auxiliaryLength (store : ∀ s : Stack k, List (Alphabet s)) : ℕ :=
  ∑ s : Stack k, if s ∈ auxiliaries k then (store s).length else 0

/-- Total stack storage, counting both output stacks and all auxiliary stacks. -/
def totalStackLength (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State)) : ℕ :=
  ∑ s : Stack k, (cfg.stk s).length

/-- Every stack contributes exactly once to the storage accounting. -/
theorem totalStackLength_eq (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State)) :
    totalStackLength cfg = auxiliaryLength cfg.stk +
      (cfg.stk .reversed).length + (cfg.stk .output).length := by
  classical
  calc
    _ = ∑ s : Stack k, ((if s ∈ auxiliaries k then (cfg.stk s).length else 0) +
        (if s = .reversed then (cfg.stk s).length else 0) +
        (if s = .output then (cfg.stk s).length else 0)) := by
      apply Finset.sum_congr rfl
      intro s hs
      cases s <;> simp
    _ = _ := by simp [auxiliaryLength, Finset.sum_add_distrib]

/-- Whether a cleanup round encounters a nonempty auxiliary stack. -/
private def auxiliaryBusy (store : ∀ s : Stack k, List (Alphabet s)) : Bool :=
  (auxiliaries k).any (fun s => (store s).head?.isSome)

/-- A round pops all auxiliaries, preserving both output stacks. -/
private theorem stepAux_clean (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux clean v store =
      ⟨some (if auxiliaryBusy store then .clean else .reverse),
        { v with busy := auxiliaryBusy store }, poppedStore (auxiliaries k) store⟩ := by
  simp only [clean, TM2.stepAux]
  rw [stepAux_discard _ (auxiliaries_nodup k)]
  simp only [Bool.false_or, TM2.stepAux]
  simp only [auxiliaryBusy]
  by_cases hb : (auxiliaries k).any (fun s => (store s).head?.isSome) = true
  · simp only [hb, Bool.cond_true, ↓reduceIte]
  · have hf := Bool.eq_false_iff.mpr hb
    simp only [hf, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]

/-- No auxiliary is busy precisely when all of them are empty. -/
private theorem auxiliaryBusy_eq_false_iff (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryBusy store = false ↔ ∀ s ∈ auxiliaries k, store s = [] := by
  simp [auxiliaryBusy, List.any_eq_false]

/-- Zero auxiliary storage is equivalent to emptiness of every auxiliary stack. -/
theorem auxiliaryLength_eq_zero_iff (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryLength store = 0 ↔ ∀ s ∈ auxiliaries k, store s = [] := by
  simp [auxiliaryLength, Finset.sum_eq_zero_iff]

/-- Popping auxiliary stacks cannot increase their total length. -/
private theorem auxiliaryLength_popped_le (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryLength (poppedStore (auxiliaries k) store) ≤ auxiliaryLength store := by
  apply Finset.sum_le_sum
  intro s hs
  by_cases h : s ∈ auxiliaries k
  · simp only [poppedStore, h, ↓reduceIte, List.length_tail]
    exact Nat.sub_le _ _
  · simp [h]

/-- A busy round strictly decreases auxiliary storage. -/
private theorem auxiliaryLength_popped_lt (store : ∀ s : Stack k, List (Alphabet s))
    (hb : auxiliaryBusy store = true) :
    auxiliaryLength (poppedStore (auxiliaries k) store) < auxiliaryLength store := by
  have hex : ∃ s, s ∈ auxiliaries k ∧ store s ≠ [] := by
    by_contra! h
    have := (auxiliaryBusy_eq_false_iff store).2 h
    simp [hb] at this
  obtain ⟨s, hs, hne⟩ := hex
  apply Finset.sum_lt_sum
  · intro t ht
    by_cases h : t ∈ auxiliaries k
    · simp only [poppedStore, h, ↓reduceIte, List.length_tail]
      exact Nat.sub_le _ _
    · simp [h]
  · refine ⟨s, Finset.mem_univ s, ?_⟩
    simp only [poppedStore, hs, ↓reduceIte, List.length_tail]
    have : 0 < (store s).length := List.length_pos_iff.mpr hne
    omega

/-- A quiet round leaves every stack unchanged. -/
private theorem poppedStore_eq_of_not_busy (store : ∀ s : Stack k, List (Alphabet s))
    (hb : auxiliaryBusy store = false) : poppedStore (auxiliaries k) store = store := by
  funext s
  by_cases h : s ∈ auxiliaries k
  · simp [poppedStore, h, (auxiliaryBusy_eq_false_iff store).mp hb s h]
  · simp [poppedStore, h]

variable [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)

/-- Reversal transfers one symbol, or resets finite control and halts on the empty stack. -/
private theorem stepAux_reverse (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux (program q₀ transition .reverse) v store =
      match store .reversed with
      | [] => ⟨none, initialControl q₀, Function.update store .reversed []⟩
      | b :: bs => ⟨some .reverse, { v with symbol := some b },
          Function.update (Function.update store .reversed bs) .output (b :: store .output)⟩ := by
  cases h : store .reversed with
  | nil => simp [program, TM2.stepAux, h, Option.isSome, Option.getD]
  | cons b bs =>
    simp only [program, TM2.stepAux, h, List.head?_cons, List.tail_cons,
      Option.isSome, Bool.cond_true]
    rfl

/-- When the auxiliaries are empty, the last reversal step has the canonical halting shape. -/
private theorem stepAux_reverse_nil (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s))
    (ha : ∀ s ∈ auxiliaries k, store s = []) (hr : store .reversed = []) :
    TM2.stepAux (program q₀ transition .reverse) v store =
      haltList (machine q₀ transition) (store .output) := by
  rw [stepAux_reverse, hr]
  change TM2.Cfg.mk none (initialControl q₀) _ = TM2.Cfg.mk none (initialControl q₀) _
  congr 1
  funext s
  cases s with
  | input => simp [machine, ha .input (by simp)]
  | before => simp [machine, ha .before (by simp)]
  | output => rfl
  | reversed => simp [machine]
  | work i b => simp [machine, ha (.work i b) (by simp)]

/-- Reversal preserves already populated output, which becomes a suffix of the final word. -/
private def reverseEvals (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s))
    (ha : ∀ s ∈ auxiliaries k, store s = []) :
    StateTransition.EvalsToInTime (TM2.step (program q₀ transition))
      ⟨some .reverse, v, store⟩
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (store .reversed).reverse (store .output))))
      ((store .reversed).length + 1) := by
  cases hr : store .reversed with
  | nil =>
    have hs : (TM2.step (program q₀ transition)) ⟨some .reverse, v, store⟩ =
        some (haltList (machine q₀ transition) (store .output)) := by
      change some (TM2.stepAux (program q₀ transition .reverse) v store) = _
      exact congrArg some (stepAux_reverse_nil q₀ transition v store ha hr)
    change StateTransition.EvalsToInTime _ _
      (some (haltList (machine q₀ transition) (store .output))) 1
    exact .cons hs (.refl _ _)
  | cons b bs =>
    let store' := Function.update (Function.update store .reversed bs) .output (b :: store .output)
    have ha' : ∀ s ∈ auxiliaries k, store' s = [] := by
      intro s hs
      have hne := (mem_auxiliaries s).mp hs
      simpa only [store', Function.update_of_ne hne.1, Function.update_of_ne hne.2] using ha s hs
    have hs : (TM2.step (program q₀ transition)) ⟨some .reverse, v, store⟩ =
        some ⟨some .reverse, { v with symbol := some b }, store'⟩ := by
      change some (TM2.stepAux (program q₀ transition .reverse) v store) = _
      rw [stepAux_reverse, hr]
    have hrec := reverseEvals { v with symbol := some b } store' ha'
    have hrev : store' .reversed = bs := by simp [store']
    have hout : store' .output = b :: store .output := by
      dsimp only [store']
      exact Function.update_self _ _ _
    rw [hrev, hout] at hrec
    rw [List.reverse_cons]
    have hw : List.append (α := Bool) (bs.reverse ++ [b]) (store .output) =
        List.append (α := Bool) bs.reverse (b :: store .output) :=
      List.append_assoc (α := Bool) bs.reverse [b] (store .output)
    rw [hw]
    change StateTransition.EvalsToInTime _ _ _ (bs.length + 1 + 1)
    exact .cons hs hrec
termination_by (store .reversed).length
decreasing_by simp_wf; rw [hr]; exact Nat.lt_succ_self _

/-- Cleanup reaches the canonical halting configuration within a linear number of TM2 steps. -/
private def cleanEvals (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    StateTransition.EvalsToInTime (TM2.step (program q₀ transition))
      ⟨some .clean, v, store⟩
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (store .reversed).reverse (store .output))))
      (auxiliaryLength store + (store .reversed).length + 2) := by
  cases hb : auxiliaryBusy store with
  | false =>
    have ha := (auxiliaryBusy_eq_false_iff store).mp hb
    have hs : (TM2.step (program q₀ transition)) ⟨some .clean, v, store⟩ =
        some ⟨some .reverse, { v with busy := false }, store⟩ := by
      change some (TM2.stepAux clean v store) = _
      rw [stepAux_clean, hb, poppedStore_eq_of_not_busy store hb]
      rfl
    exact (StateTransition.EvalsToInTime.cons hs (reverseEvals q₀ transition _ store ha)).mono
      (by omega)
  | true =>
    let store' := poppedStore (auxiliaries k) store
    have hrev : store' .reversed = store .reversed := by simp [store', poppedStore]
    have hout : store' .output = store .output := by simp [store', poppedStore]
    have hs : (TM2.step (program q₀ transition)) ⟨some .clean, v, store⟩ =
        some ⟨some .clean, { v with busy := true }, store'⟩ := by
      change some (TM2.stepAux clean v store) = _
      rw [stepAux_clean, hb]
      rfl
    have hrec := cleanEvals { v with busy := true } store'
    rw [hrev, hout] at hrec
    have hlt := auxiliaryLength_popped_lt store hb
    exact (StateTransition.EvalsToInTime.cons hs hrec).mono (by dsimp only [store'] at *; omega)
termination_by auxiliaryLength store
decreasing_by exact auxiliaryLength_popped_lt store hb

/-- Configuration form of `cleanEvals`, allowing arbitrary finite control and stack contents. -/
def cleanupEvals (cfg : (machine q₀ transition).Cfg) (hl : cfg.l = some .clean) :
    StateTransition.EvalsToInTime (machine q₀ transition).step cfg
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (cfg.stk .reversed).reverse (cfg.stk .output))))
      (auxiliaryLength cfg.stk + (cfg.stk .reversed).length + 2) := by
  cases cfg with | mk l v store =>
    cases hl
    exact cleanEvals q₀ transition v store

end
end Turing.MultiTapeTM.ToTM2

/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/



/-!
# Resource bounds for the reverse TM2 compiler

Input storage and the output buffer count toward the target clock. Each source step adds at most
one symbol to the work storage of each simulated tape.

## Main results

* `Turing.MultiTapeTM.ToTM2.outputsInTime`: output correspondence with a linear simulation clock.
-/


namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

private def stackEquiv (k : ℕ) : Stack k ≃ ((Bool ⊕ Bool) ⊕ Fin k × Bool) where
  toFun
    | .input => .inl (.inl false)
    | .before => .inl (.inl true)
    | .output => .inl (.inr false)
    | .reversed => .inl (.inr true)
    | .work i b => .inr (i, b)
  invFun
    | .inl (.inl false) => .input
    | .inl (.inl true) => .before
    | .inl (.inr false) => .output
    | .inl (.inr true) => .reversed
    | .inr (i, b) => .work i b
  left_inv s := by cases s with | work i b => cases b <;> rfl | _ => rfl
  right_inv s := by
    rcases s with ((b | b) | ⟨i, b⟩) <;> cases b <;> rfl

private theorem sum_stack (f : Stack k → ℕ) :
    ∑ s, f s = f .input + f .before + f .output + f .reversed +
      ∑ i, (f (.work i false) + f (.work i true)) := by
  rw [← (stackEquiv k).symm.sum_comp f]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, stackEquiv,
    Equiv.symm_mk, Equiv.coe_fn_mk]
  simp [add_comm, add_assoc]

/-- Stack storage at a source-step boundary, including the input and output. -/
private theorem totalStackLength_encode (d : Data k State) :
    totalStackLength (encode d) = d.input.left.length + d.input.right.length +
      (∑ i, ((d.work i).left.length + (d.work i).right.length)) + d.output.length := by
  rw [totalStackLength, sum_stack]
  simp only [encode, store, List.length_nil, List.length_reverse]
  omega

/-- Auxiliary storage excludes the accumulated output. -/
private theorem auxiliaryLength_store (d : Data k State) :
    auxiliaryLength (store d) = d.input.left.length + d.input.right.length +
      ∑ i, ((d.work i).left.length + (d.work i).right.length) := by
  have h := totalStackLength_encode d
  rw [totalStackLength_eq] at h
  simp only [encode, store, List.length_reverse, List.length_nil, Nat.add_zero] at h
  omega

private theorem auxiliaryLength_run_time_le (tm : MultiTapeTM k Bool State)
    (input : List Bool) (t : ℕ) :
    auxiliaryLength (store (Data.run tm input t)) ≤ input.length + k * (t + 1) := by
  rw [auxiliaryLength_store, Data.input_length_run]
  have hlocal (i : Fin k) : ((Data.run tm input t).work i).left.length +
      ((Data.run tm input t).work i).right.length ≤ t := by
    induction t with
    | zero => simp [Data.run_zero, Data.init, RawTape.init]
    | succ t ih =>
      rw [Data.run_succ]
      let q := Data.run tm input t
      change ((Data.totalStep tm q).work i).left.length +
        ((Data.totalStep tm q).work i).right.length ≤ t + 1
      cases hs : q.state with
      | none =>
        rw [Data.totalStep_of_halt tm hs]
        exact ih.trans (Nat.le_succ t)
      | some st =>
        rw [Data.totalStep_of_state tm hs]
        let a := tm.tr st q.input.read (fun i => (q.work i).head)
        have h := RawTape.span_step_le (q.work i) (a.workTapes i)
        change ((q.work i).step (a.workTapes i)).left.length +
          ((q.work i).step (a.workTapes i)).right.length ≤ t+1
        dsimp only [RawTape.span] at h
        change (q.work i).left.length + (q.work i).right.length ≤ t at ih
        omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  exact Nat.add_le_add_left (hsum.trans (Nat.mul_le_mul_left k (Nat.le_succ t))) _

/-- Once the source has halted, its raw output is the complete computed output. -/
private theorem output_run_of_halt (tm : MultiTapeTM k Bool State) {input output : List Bool}
    (hc : tm.Computes input output) {t : ℕ} (ht : (Data.run tm input t).state = none) :
    (Data.run tm input t).output = output := by
  obtain ⟨u, hu, hout⟩ := hc
  have hou : (Data.run tm input u).output = output := (Data.output_run tm input u).trans hout
  rcases le_total t u with htu | hut
  · rwa [Data.run_eq_of_halt tm input htu ht] at hou
  · rw [Data.run_eq_of_halt tm input hut ((Data.state_run tm input u).trans hu), hou]

/-- A native computation is simulated with a linear clock, including clearing every auxiliary
stack, reversing its output and restoring Mathlib's canonical halting control. -/
def outputsInTime [Fintype State] (tm : MultiTapeTM k Bool State)
    {input output : List Bool} {t : ℕ} (hc : tm.Computes input output)
    (ht : tm.RunsInTime input t) :
    TM2OutputsInTime (machine tm.q₀ tm.tr) input (some output)
      (input.length + (k + 1) * (t + 1) + output.length + 3) := by
  classical
  let hex := exists_haltsAt (runsInTime_iff_halted.mp ht)
  let u := hex.choose
  have hu := hex.choose_spec
  let d := Data.run tm input u
  have hd : d.state = none := (Data.state_run tm input u).trans hu.2.halted
  have ho : d.output = output := output_run_of_halt tm hc hd
  let cfg : (machine tm.q₀ tm.tr).Cfg :=
    ⟨some .clean, control d d.input.right.head? false, store d⟩
  have hstep : (machine tm.q₀ tm.tr).step (encode d) = some cfg := step_encode_halt tm d hd
  have hclean := cleanupEvals tm.q₀ tm.tr cfg rfl
  have htail := StateTransition.EvalsToInTime.cons hstep hclean
  change StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step (encode d)
    (some (haltList (machine tm.q₀ tm.tr) (d.output.reverse.reverse ++ [])))
    (auxiliaryLength (store d) + d.output.reverse.length + 2 + 1) at htail
  have htail' : StateTransition.EvalsToInTime (machine tm.q₀ tm.tr).step (encode d)
      (some (haltList (machine tm.q₀ tm.tr) output))
      (auxiliaryLength (store d) + d.output.length + 3) := by
    simpa only [cfg, store, List.reverse_reverse, List.append_nil, List.length_reverse,
      Nat.add_assoc, Nat.reduceAdd, ho] using htail
  have hresult := StateTransition.EvalsToInTime.trans (machine tm.q₀ tm.tr).step
    u (auxiliaryLength (store d) + d.output.length + 3) _ _ _
    (prefixEvals tm input hu.2 le_rfl) htail'
  refine hresult.mono ?_
  have ha := auxiliaryLength_run_time_le tm input u
  have hm : k * (u + 1) ≤ k * (t + 1) := Nat.mul_le_mul_left k (by omega)
  dsimp only [d] at *
  rw [ho]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

/-- Terminating native computation yields terminating canonical TM2 computation. -/
def outputs [Fintype State] (tm : MultiTapeTM k Bool State) {input output : List Bool}
    (hc : tm.Computes input output) : TM2Outputs (machine tm.q₀ tm.tr) input (some output) :=
  (outputsInTime tm hc (runsInTime_iff_halted.mpr hc.choose_spec.1)).toTM2Outputs

end

end Turing.MultiTapeTM.ToTM2

namespace Turing.MultiTapeTM

open Polynomial

end Turing.MultiTapeTM

open NOFSeparation750.CodedGIP in
theorem C1fp {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β}
    (h : Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut) :
    ∃ P : FiniteProgram, ∃ p : Polynomial ℕ, ∀ a,
      OutputsWithin P (encIn a) (encOut (f a)) (p.eval (encIn a).length) := by
  open Turing Turing.MultiTapeTM Polynomial in
  obtain ⟨t, s, ht, _, k, State, hfinite, tm, htm⟩ := h
  obtain ⟨c, d, ht⟩ := Cslib.polynomiallyBounded_iff_le.mp ht
  let : Fintype State := Fintype.ofFinite State
  let p : Polynomial ℕ := X + C (k+2) * (C c * (X + 1)^d + 1) + C 3
  refine ⟨⟨⟨ToTM2.machine tm.q₀ tm.tr, Equiv.refl Bool, Equiv.refl Bool⟩, fun i => by
    cases i <;> exact inferInstance⟩, p, fun a => ?_⟩
  let n := (encIn a).length
  have hOut : (encOut (f a)).length ≤ t n := (htm a).length_output_le
  have hrun := ToTM2.outputsInTime tm (htm a).1 (htm a).2.1
  have htime : n + (k+1) * (t n + 1) + (encOut (f a)).length + 3 ≤ p.eval n := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    have hlinear := Nat.mul_le_mul_left (k+2) (Nat.succ_le_succ (ht n))
    simp only [Nat.add_mul, Nat.succ_eq_add_one, Nat.one_mul] at hlinear ⊢
    omega
  unfold OutputsWithin
  refine ⟨?_⟩
  change TM2OutputsInTime (ToTM2.machine tm.q₀ tm.tr) (List.map id (encIn a))
    (some (List.map id (encOut (f a)))) (p.eval n)
  rw [List.map_id, List.map_id]
  exact (hrun.mono htime)






set_option autoImplicit true

open Turing

/-!
# Core of a general composition lemma for `Turing.TM2ComputableInPolyTime`

Given two machines `tm₁`, `tm₂` we build the stack/key/state packaging in which `tm₁` and `tm₂` can
run inside one machine:

* `Key := tm₁.K ⊕ (tm₂.K ⊕ Unit)` — the two machines' stacks plus one temporary stack (used to
  reverse the copied word, because stacks are LIFO);
* `Gam` — the corresponding (dependent) stack alphabets;
* `Lab := tm₁.Λ ⊕ (Unit ⊕ tm₂.Λ)` — the two label sets plus a copy-phase label;
* `Sta := tm₁.σ × (tm₂.σ × Option (tm₂.Γ tm₂.k₀))` — both internal states plus a one-symbol buffer.

`tr₁`/`tr₂` push each machine's statements through this packaging, and `stepAux_tr₁`/`stepAux_tr₂`
are the exact one-step commutation lemmas: one composite step simulates one step of the machine.
-/

namespace Turing

/-- Once a deterministic step function has halted, iterating it stays at `none`. -/
theorem iterate_none {α : Type*} (f : α → Option α) : ∀ m : ℕ,
    (flip bind f)^[m] (none : Option α) = none
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_none f m

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)

/-- Stack index type of the composite. -/
abbrev Key : Type := tm₁.K ⊕ (tm₂.K ⊕ Unit)

/-- Stack alphabets of the composite. -/
abbrev Gam : Key tm₁ tm₂ → Type
  | .inl a => tm₁.Γ a
  | .inr (.inl b) => tm₂.Γ b
  | .inr (.inr _) => tm₂.Γ tm₂.k₀

/-- Label type of the composite: machine 1's labels, machine 2's labels, and one copy-phase label
(stored as `Unit`). -/
abbrev Lab : Type := tm₁.Λ ⊕ (Fin 2 ⊕ tm₂.Λ)

/-- Internal state of the composite: both machines' states plus a one-symbol buffer. -/
abbrev Sta : Type := tm₁.σ × (tm₂.σ × Option (tm₂.Γ tm₂.k₀))

/-- The stack contents of the composite as a dependent function. -/
def pack (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) : (k : Key tm₁ tm₂) → List (Gam tm₁ tm₂ k)
  | .inl a => S₁ a
  | .inr (.inl b) => S₂ b
  | .inr (.inr _) => T

theorem pack_update_left (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (k : tm₁.K) (x : List (tm₁.Γ k)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inl k) x
      = pack tm₁ tm₂ (Function.update S₁ k x) S₂ T := by
  funext j
  rcases j with a | (b | u)
  · by_cases h : a = k
    · subst h; simp [pack]
    · simp only [pack, Function.update_of_ne (by simp [h] : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inl k),
        Function.update_of_ne h]
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ Sum.inl k)]
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ Sum.inl k)]

theorem pack_update_right (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (k : tm₂.K) (x : List (tm₂.Γ k)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inr (Sum.inl k)) x
      = pack tm₁ tm₂ S₁ (Function.update S₂ k x) T := by
  funext j
  rcases j with a | (b | u)
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inr (Sum.inl k))]
  · by_cases h : b = k
    · subst h; simp [pack]
    · have hne : ¬ ((Sum.inr (Sum.inl b) : Key tm₁ tm₂) = Sum.inr (Sum.inl k)) :=
        fun hh => h (by simpa using hh)
      rw [Function.update_of_ne (a := Sum.inr (Sum.inl b)) (a' := Sum.inr (Sum.inl k))
            (v := x) (f := pack tm₁ tm₂ S₁ S₂ T) hne]
      simp only [pack, Function.update_of_ne (a := b) (a' := k) (v := x) (f := S₂) h]
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ Sum.inr (Sum.inl k))]

theorem pack_update_tmp (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : List (tm₂.Γ tm₂.k₀)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inr (Sum.inr ())) x
      = pack tm₁ tm₂ S₁ S₂ x := by
  funext j
  rcases j with a | (b | u)
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inr (Sum.inr ()))]
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ Sum.inr (Sum.inr ()))]
  · simp only [pack]
    congr 1
    cases u
    rfl

/-- Label translation for machine 1: its own labels, and its halting label is turned into a jump to
the copy phase. -/
def lab₁ : Option tm₁.Λ → Option (Lab tm₁ tm₂)
  | none => some (Sum.inr (Sum.inl 0))
  | some l => some (Sum.inl l)

/-- Label translation for machine 2: its halting label stays a halting label. -/
def lab₂ : Option tm₂.Λ → Option (Lab tm₁ tm₂)
  | none => none
  | some l => some (Sum.inr (Sum.inr l))

/-- Reindex machine 1's statements into the composite. -/
def tr₁ : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .push k g q => .push (Sum.inl k) (fun s => g s.1) (tr₁ q)
  | .peek k g q => .peek (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr₁ q)
  | .pop k g q => .pop (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr₁ q)
  | .load g q => .load (fun s => (g s.1, s.2)) (tr₁ q)
  | .branch g q r => .branch (fun s => g s.1) (tr₁ q) (tr₁ r)
  | .goto g => .goto (fun s => Sum.inl (g s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inl 0))

/-- Reindex machine 2's statements into the composite. -/
def tr₂ : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .push k g q => .push (Sum.inr (Sum.inl k)) (fun s => g s.2.1) (tr₂ q)
  | .peek k g q => .peek (Sum.inr (Sum.inl k)) (fun s o => (s.1, (g s.2.1 o, s.2.2))) (tr₂ q)
  | .pop k g q => .pop (Sum.inr (Sum.inl k)) (fun s o => (s.1, (g s.2.1 o, s.2.2))) (tr₂ q)
  | .load g q => .load (fun s => (s.1, (g s.2.1, s.2.2))) (tr₂ q)
  | .branch g q r => .branch (fun s => g s.2.1) (tr₂ q) (tr₂ r)
  | .goto g => .goto (fun s => Sum.inr (Sum.inr (g s.2.1)))
  | .halt => .halt

theorem stepAux_tr₁ (q : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v₁ : tm₁.σ) (v₂ : tm₂.σ)
    (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (tr₁ tm₁ tm₂ q) (v₁, v₂, b) (pack tm₁ tm₂ S₁ S₂ T)
      = ⟨lab₁ tm₁ tm₂ (TM2.stepAux q v₁ S₁).l,
          ((TM2.stepAux q v₁ S₁).var, v₂, b),
          pack tm₁ tm₂ (TM2.stepAux q v₁ S₁).stk S₂ T⟩ := by
  induction q generalizing v₁ S₁ with
  | push k g q ih =>
      simp only [tr₁, TM2.stepAux, pack_update_left tm₁ tm₂]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr₁, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr₁, TM2.stepAux, pack_update_left tm₁ tm₂]
      exact ih _ _
  | load g q ih =>
      simp only [tr₁, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v₁
      · simp only [tr₁, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr₁, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr₁, TM2.stepAux, lab₁]
  | halt => simp only [tr₁, TM2.stepAux, lab₁]

theorem stepAux_tr₂ (q : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (v₂ : tm₂.σ)
    (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (tr₂ tm₁ tm₂ q) (v₁, v₂, b) (pack tm₁ tm₂ S₁ S₂ T)
      = ⟨lab₂ tm₁ tm₂ (TM2.stepAux q v₂ S₂).l,
          (v₁, ((TM2.stepAux q v₂ S₂).var, b)),
          pack tm₁ tm₂ S₁ (TM2.stepAux q v₂ S₂).stk T⟩ := by
  induction q generalizing v₂ S₂ with
  | push k g q ih =>
      simp only [tr₂, TM2.stepAux, pack_update_right tm₁ tm₂]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr₂, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr₂, TM2.stepAux, pack_update_right tm₁ tm₂]
      exact ih _ _
  | load g q ih =>
      simp only [tr₂, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v₂
      · simp only [tr₂, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr₂, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr₂, TM2.stepAux, lab₂]
  | halt => simp only [tr₂, TM2.stepAux, lab₂]
end CompCore

end Turing


namespace Turing

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)

/-- Program of the composite: machine 1's code, the copy phase, then machine 2's code. -/
def compCode (copy : TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :
    Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .inl l => tr₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl _) => copy
  | .inr (.inr l) => tr₂ tm₁ tm₂ (tm₂.m l)

/-- The composite step function. -/
def compStep (copy : TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) →
      Option (TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :=
  TM2.step (compCode tm₁ tm₂ copy)

/-- Embed machine 1's configuration into the composite. -/
def cfg₁ (c : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  ⟨lab₁ tm₁ tm₂ c.l, (c.var, v₂, b), pack tm₁ tm₂ c.stk S₂ T⟩

theorem step_cfg₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) {c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ}
    (h : tm₁.step c = some c') :
    TM2.step M (cfg₁ tm₁ tm₂ c v₂ b S₂ T) = some (cfg₁ tm₁ tm₂ c' v₂ b S₂ T) := by
  obtain ⟨l, v₁, S₁⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm₁.m l) v₁ S₁ := (Option.some.inj h).symm
      subst hh
      simp only [cfg₁, lab₁, hM, TM2.step.eq_2, FinTM2.step, stepAux_tr₁]

/-- Run lifting for machine 1: any `m`-step run of `tm₁` is an `m`-step run of the composite. -/
theorem iterate_cfg₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ),
      (flip bind tm₁.step)^[m] (some c) = some c' →
      (flip bind (TM2.step M))^[m] (some (cfg₁ tm₁ tm₂ c v₂ b S₂ T))
        = some (cfg₁ tm₁ tm₂ c' v₂ b S₂ T)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm₁.step) (some c) = tm₁.step c from rfl] at h
      cases hstep : tm₁.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step M)) (some (cfg₁ tm₁ tm₂ c v₂ b S₂ T))
                = TM2.step M (cfg₁ tm₁ tm₂ c v₂ b S₂ T) from rfl,
              step_cfg₁ tm₁ tm₂ M hM v₂ b S₂ T hstep]
          exact iterate_cfg₁ M hM v₂ b S₂ T m d c' h

/-- Embed machine 2's configuration into the composite. -/
def cfg₂ (c : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀))
    (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  ⟨lab₂ tm₁ tm₂ c.l, (v₁, (c.var, b)), pack tm₁ tm₂ S₁ c.stk T⟩

theorem step_cfg₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) {c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ}
    (h : tm₂.step c = some c') :
    TM2.step M (cfg₂ tm₁ tm₂ c v₁ b S₁ T) = some (cfg₂ tm₁ tm₂ c' v₁ b S₁ T) := by
  obtain ⟨l, v₂, S₂⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm₂.m l) v₂ S₂ := (Option.some.inj h).symm
      subst hh
      simp only [cfg₂, lab₂, hM, TM2.step.eq_2, FinTM2.step, stepAux_tr₂]

/-- Run lifting for machine 2. -/
theorem iterate_cfg₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ),
      (flip bind tm₂.step)^[m] (some c) = some c' →
      (flip bind (TM2.step M))^[m] (some (cfg₂ tm₁ tm₂ c v₁ b S₁ T))
        = some (cfg₂ tm₁ tm₂ c' v₁ b S₁ T)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm₂.step) (some c) = tm₂.step c from rfl] at h
      cases hstep : tm₂.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step M)) (some (cfg₂ tm₁ tm₂ c v₁ b S₁ T))
                = TM2.step M (cfg₂ tm₁ tm₂ c v₁ b S₁ T) from rfl,
              step_cfg₂ tm₁ tm₂ M hM v₁ b S₁ T hstep]
          exact iterate_cfg₂ M hM v₁ b S₁ T m d c' h

end CompCore

end Turing


namespace Turing

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)
variable {βΓ : Type} [Inhabited βΓ]

/-- Copy pass 1: move `tm₁`'s output stack onto the temporary stack, through the two alphabets'
equivalences (this pass reverses the word, since stacks are LIFO). -/
def copyStmt₁ (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  .pop (Sum.inl tm₁.k₁) (fun v o => (v.1, (v.2.1, o.map (fun x => ia₂.invFun (oa₁ x)))))
    (.branch (fun v => v.2.2.isSome)
      (.push (Sum.inr (Sum.inr ()))
        (fun v => (v.2.2).getD (ia₂.invFun default))
        (.goto (fun _ => Sum.inr (Sum.inl 0))))
      (.goto (fun _ => Sum.inr (Sum.inl 1))))

/-- Copy pass 2: move the temporary stack onto `tm₂`'s input stack, restoring the order. -/
def copyStmt₂ (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  .pop (Sum.inr (Sum.inr ())) (fun v o => (v.1, (v.2.1, o)))
    (.branch (fun v => v.2.2.isSome)
      (.push (Sum.inr (Sum.inl tm₂.k₀))
        (fun v => (v.2.2).getD (ia₂.invFun default))
        (.goto (fun _ => Sum.inr (Sum.inl 1))))
      (.goto (fun _ => Sum.inr (Sum.inr tm₂.main))))

/-- The composite program: `tm₁`'s code, the two copy passes, `tm₂`'s code. -/
def compProg (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .inl l => tr₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl 0) => copyStmt₁ tm₁ tm₂ oa₁ ia₂
  | .inr (.inl 1) => copyStmt₂ tm₁ tm₂ ia₂
  | .inr (.inr l) => tr₂ tm₁ tm₂ (tm₂.m l)

theorem compProg_inl (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) (l : tm₁.Λ) :
    compProg tm₁ tm₂ oa₁ ia₂ (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l) := rfl

theorem compProg_inr_inr (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (l : tm₂.Λ) :
    compProg tm₁ tm₂ oa₁ ia₂ (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l) := rfl

/-- One step of copy pass 1 on a nonempty source stack. -/
theorem step_copy₁_some (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : tm₁.Γ tm₁.k₁) (xs : List (tm₁.Γ tm₁.k₁)) (hS₁ : S₁ tm₁.k₁ = x :: xs) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 0)), (v.1, (v.2.1, some (ia₂.invFun (oa₁ x)))),
          pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ xs) S₂
            (ia₂.invFun (oa₁ x) :: T)⟩ := by
  simp only [compProg, copyStmt₁, TM2.step, TM2.stepAux, hS₁, Option.map_some,
    Option.isSome_some, Option.getD_some, cond_true, List.head?_cons, List.tail_cons,
    pack, pack_update_left, pack_update_tmp, pack_update_right]

/-- One step of copy pass 1 on an empty source stack. -/
theorem step_copy₁_nil (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (hS₁ : S₁ tm₁.k₁ = []) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ S₂ T⟩ := by
  have hupd : Function.update S₁ tm₁.k₁ ([] : List (tm₁.Γ tm₁.k₁)) = S₁ := by
    rw [← hS₁]; exact Function.update_eq_self _ _
  rw [← hupd]
  simp [compProg, copyStmt₁, TM2.step, TM2.stepAux, pack, pack_update_tmp, pack_update_right,
    pack_update_left]

/-- One step of copy pass 2 on a nonempty temporary stack. -/
theorem step_copy₂_some (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : tm₂.Γ tm₂.k₀) (xs : List (tm₂.Γ tm₂.k₀)) (hT : T = x :: xs) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, some x)),
          pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀)) xs⟩ := by
  subst hT
  simp [compProg, copyStmt₂, TM2.step, TM2.stepAux, pack, pack_update_tmp, pack_update_right,
    pack_update_left]

/-- One step of copy pass 2 on an empty temporary stack: the composite enters `tm₂`. -/
theorem step_copy₂_nil (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) (hT : T = []) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inr tm₂.main)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ S₂ T⟩ := by
  subst hT
  simp only [compProg, copyStmt₂, TM2.step, TM2.stepAux, List.head?_nil, Option.map_none,
    Option.isSome_none, Bool.false_eq_true, cond_false, pack]
  rw [show ([] : List (tm₂.Γ tm₂.k₀)).tail = [] from rfl, pack_update_tmp]

end CompCore

end Turing

namespace Turing

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)
variable {βΓ : Type} [Inhabited βΓ]



end CompCore

end Turing




/-! ## Exit stage (ported verbatim from the swarm's ExitStage.lean) -/

open StateTransition

namespace QMCExit

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ : Type*} {σ : Type*}

open Turing.TM2.Stmt

/-! ### Utilities on `EvalsToInTime` -/

/-- Chaining `EvalsToInTime` steps when the intermediate configuration is given explicitly. -/
def EvalsToInTime.trans' {α : Type*} {f : α → Option α} {a b : α} {c : Option α} {m₁ m₂ : ℕ}
    (h₁ : EvalsToInTime f a (some b) m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  EvalsToInTime.trans f m₁ m₂ a b c h₁ h₂

/-- Weakening the step bound. -/
def EvalsToInTime.mono {α : Type*} {f : α → Option α} {a : α} {b : Option α} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

/-- `flip bind` of the step function of a TM2 machine is the step function itself. -/
theorem flip_bind_step (M : Λ → Turing.TM2.Stmt Γ Λ σ) (c : Turing.TM2.Cfg Γ Λ σ) :
    (flip bind (Turing.TM2.step M)) c = Turing.TM2.step M c := by
  rcases c with ⟨l, v, S⟩
  cases l <;> rfl

/-! ### The drain loop -/

/-- Statement at the *detection* label of the drain loop for stack `k`: peek at the stack; if it is
empty continue at `N`, otherwise continue at `C`.  The flag is stored in the machine state by
`mark`. -/
def drainDetect (k : K) (A C N : Λ) (flag : σ → Bool) (mark : σ → Bool → σ) :
    Turing.TM2.Stmt Γ Λ σ :=
  peek k (fun v o => mark v o.isNone)
    (branch flag (goto fun _ => N) (goto fun _ => C))

/-- Statement at the *pop* label of the drain loop for stack `k`: throw away the top symbol and go
back to the detection label `A`. -/
def drainPop (k : K) (A : Λ) : Turing.TM2.Stmt Γ Λ σ :=
  pop k (fun v _ => v) (goto fun _ => A)

variable {M : Λ → Turing.TM2.Stmt Γ Λ σ} {k : K} {A C N : Λ} {flag : σ → Bool}
  {mark : σ → Bool → σ}

/-- One detection step on an empty stack. -/
theorem step_drain_nil (hA : M A = drainDetect (Γ := Γ) k A C N flag mark)
    (hft : ∀ v, flag (mark v true) = true) (v : σ) (S : ∀ j, List (Γ j)) (hS : S k = []) :
    Turing.TM2.step M ⟨some A, v, S⟩ = some ⟨some N, mark v true, S⟩ := by
  show some (Turing.TM2.stepAux (M A) v S) = _
  rw [hA, drainDetect]
  simp [hS, hft]

/-- One detection step on a nonempty stack. -/
theorem step_drain_cons (hA : M A = drainDetect (Γ := Γ) k A C N flag mark)
    (hff : ∀ v, flag (mark v false) = false) (v : σ) (S : ∀ j, List (Γ j))
    (x : Γ k) (xs : List (Γ k)) (hS : S k = x :: xs) :
    Turing.TM2.step M ⟨some A, v, S⟩ = some ⟨some C, mark v false, S⟩ := by
  show some (Turing.TM2.stepAux (M A) v S) = _
  rw [hA, drainDetect]
  simp [hS, hff]

/-- One pop step: the top symbol is thrown away, the state is unchanged. -/
theorem step_drain_pop (hC : M C = drainPop (Γ := Γ) (σ := σ) k A) (v : σ)
    (S : ∀ j, List (Γ j)) (xs : List (Γ k)) (hS : S k = x :: xs) :
    Turing.TM2.step M ⟨some C, v, S⟩ = some ⟨some A, v, Function.update S k xs⟩ := by
  show some (Turing.TM2.stepAux (M C) v S) = _
  rw [hC, drainPop]
  simp [hS]

/-- **The drain loop.**  Starting at the detection label `A` with stack `k` holding `L`, the
machine reaches the exit label `N` with stack `k` empty and no other stack changed, in exactly
`2 * L.length + 1` steps.  The state runs through `mark · false` once per removed symbol and ends
with the "empty" flag set. -/
def drain_stack (hA : M A = drainDetect (Γ := Γ) k A C N flag mark)
    (hC : M C = drainPop (Γ := Γ) (σ := σ) k A)
    (hft : ∀ v, flag (mark v true) = true) (hff : ∀ v, flag (mark v false) = false)
    (L : List (Γ k)) (v : σ) (S : ∀ j, List (Γ j)) (hS : S k = L) :
    EvalsToInTime (Turing.TM2.step M) ⟨some A, v, S⟩
      (some ⟨some N, mark ((fun w => mark w false)^[L.length] v) true,
        Function.update S k []⟩) (2 * L.length + 1) := by
  induction L generalizing v S with
  | nil =>
    have hstep := step_drain_nil hA hft v S hS
    have hupd : Function.update S k ([] : List (Γ k)) = S := by
      rw [← hS]; exact Function.update_eq_self k S
    refine ⟨⟨1, ?_⟩, by simp⟩
    rw [Function.iterate_one, flip_bind_step M, hstep]
    simp only [List.length_nil, Function.iterate_zero_apply]
    rw [hupd]
  | cons x xs ih =>
    have hstep1 := step_drain_cons hA hff v S x xs hS
    have hstep2 := step_drain_pop hC (mark v false) (S := S) xs (x := x) hS
    have hS' : Function.update S k xs k = xs := by simp
    have ih' := ih (mark v false) (Function.update S k xs) hS'
    have e1 : EvalsToInTime (Turing.TM2.step M) ⟨some A, v, S⟩
        (some ⟨some C, mark v false, S⟩) 1 :=
      ⟨⟨1, by rw [Function.iterate_one, flip_bind_step M, hstep1]⟩, by simp⟩
    have e2 : EvalsToInTime (Turing.TM2.step M) ⟨some C, mark v false, S⟩
        (some ⟨some A, mark v false, Function.update S k xs⟩) 1 :=
      ⟨⟨1, by rw [Function.iterate_one, flip_bind_step M, hstep2]⟩, by simp⟩
    have hfin : EvalsToInTime (Turing.TM2.step M) ⟨some A, v, S⟩
        (some ⟨some N, mark ((fun w => mark w false)^[xs.length] (mark v false)) true,
          Function.update (Function.update S k xs) k []⟩) (2 * xs.length + 1 + 2) :=
      EvalsToInTime.trans' (EvalsToInTime.trans' e1 e2) ih'
    have hiter : ((fun w => mark w false)^[xs.length] (mark v false))
        = (fun w => mark w false)^[(x :: xs).length] v := by
      rw [List.length_cons, Function.iterate_succ_apply]
    have hupd2 : Function.update (Function.update S k xs) k ([] : List (Γ k))
        = Function.update S k [] := by simp
    rw [hiter, hupd2] at hfin
    have hb : 2 * (x :: xs).length + 1 = 2 * xs.length + 1 + 2 := by
      simp only [List.length_cons]
      omega
    refine ⟨hfin.toEvalsTo, ?_⟩
    rw [hb]
    exact hfin.steps_le_m

/-- Convenience form of `drain_stack` with the stack contents `S k` in place of `L`. -/
def drain_stack' (hA : M A = drainDetect (Γ := Γ) k A C N flag mark)
    (hC : M C = drainPop (Γ := Γ) (σ := σ) k A)
    (hft : ∀ v, flag (mark v true) = true) (hff : ∀ v, flag (mark v false) = false)
    (v : σ) (S : ∀ j, List (Γ j)) :
    EvalsToInTime (Turing.TM2.step M) ⟨some A, v, S⟩
      (some ⟨some N, mark ((fun w => mark w false)^[(S k).length] v) true,
        Function.update S k []⟩) (2 * (S k).length + 1) :=
  drain_stack hA hC hft hff (S k) v S rfl

/-! ### Rewriting the endpoints of an `EvalsToInTime` -/

/-- Transport an `EvalsToInTime` statement along equalities of its endpoints. -/
def EvalsToInTime.congr_cfg {α : Type*} {f : α → Option α} {a a' : α} {b b' : Option α} {m : ℕ}
    (ha : a = a') (hb : b = b') (h : EvalsToInTime f a b m) : EvalsToInTime f a' b' m := by
  subst ha; subst hb; exact h

/-! ### Bridge to `TM2OutputsInTime` -/

/-- A configuration-level run that ends in the (exact) halting configuration gives
`TM2OutputsInTime`. -/
def tm2OutputsInTime_of_cfg {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {out : List (tm.Γ tm.k₁)} {n : ℕ} {c : tm.Cfg}
    (h : EvalsToInTime (Turing.TM2.step tm.m) (Turing.initList tm l) (some c) n)
    (hc : c = Turing.haltList tm out) : Turing.TM2OutputsInTime tm l (some out) n := by
  subst c
  unfold Turing.TM2OutputsInTime
  exact h

/-- Conversely, `TM2OutputsInTime` is a configuration-level run into `haltList`. -/
def cfg_of_tm2OutputsInTime {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {out : List (tm.Γ tm.k₁)} {n : ℕ} (h : Turing.TM2OutputsInTime tm l (some out) n) :
    EvalsToInTime (Turing.TM2.step tm.m) (Turing.initList tm l) (some (Turing.haltList tm out)) n := by
  unfold Turing.TM2OutputsInTime at h
  exact h

/-- The stack family of the *initial* configuration, written exactly as `initList` writes it. -/
def initStacks (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀)) : ∀ k, List (tm.Γ k) :=
  fun k => @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀)
    (fun h => by rw [h]; exact l) fun _ => []

/-- A configuration with the main label, the initial state and the initial stack family *is*
`initList`. -/
theorem mk_initList {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)} {v : tm.σ}
    {S : ∀ k, List (tm.Γ k)} (hv : v = tm.initialState) (hS : S = initStacks tm l) :
    (⟨some tm.main, v, S⟩ : tm.Cfg) = Turing.initList tm l := by
  subst hv
  subst hS
  rfl

/-- A program step that is a bare `goto`: one step, everything unchanged. -/
def goto_step {M : Λ → Turing.TM2.Stmt Γ Λ σ} {A B : Λ} (h : M A = goto (fun _ => B))
    (v : σ) (S : ∀ j, List (Γ j)) :
    EvalsToInTime (Turing.TM2.step M) ⟨some A, v, S⟩ (some ⟨some B, v, S⟩) 1 := by
  have hstep : Turing.TM2.step M ⟨some A, v, S⟩ = some ⟨some B, v, S⟩ := by
    show some (Turing.TM2.stepAux (M A) v S) = _
    rw [h]
    rfl
  exact ⟨⟨1, by rw [Function.iterate_one, flip_bind_step M, hstep]⟩, by simp⟩

/-- The stack family of the halting configuration, written with an explicit `if` and cast. -/
def haltStacks (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁)) : ∀ k, List (tm.Γ k) :=
  fun k => @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁)
    (fun h => by rw [h]; exact out) fun _ => []

/-- A configuration with the halting label, the initial state and the halting stack family *is*
`haltList`. -/
theorem mk_haltList {tm : Turing.FinTM2} {out : List (tm.Γ tm.k₁)} {v : tm.σ}
    {S : ∀ k, List (tm.Γ k)} (hv : v = tm.initialState) (hS : S = haltStacks tm out) :
    (⟨none, v, S⟩ : tm.Cfg) = Turing.haltList tm out := by
  subst hv
  subst hS
  rfl

/-! ### The final halt step -/

/-- A single `load (fun _ => v₀) halt` step halts with the state reset to `v₀`. -/
def halt_at (hN : M N = load (fun _ : σ => v₀) halt) (v : σ) (S : ∀ j, List (Γ j)) :
    EvalsToInTime (Turing.TM2.step M) ⟨some N, v, S⟩ (some ⟨none, v₀, S⟩) 1 := by
  have hstep : Turing.TM2.step M ⟨some N, v, S⟩ = some ⟨none, v₀, S⟩ := by
    show some (Turing.TM2.stepAux (M N) v S) = _
    rw [hN]
    rfl
  exact ⟨⟨1, by rw [Function.iterate_one, flip_bind_step M, hstep]⟩, by simp⟩

/-- **Exit stage for one stack.**  Drain stack `k`, then halt with the state reset to `v₀`. -/
def drain_then_halt (hA : M A = drainDetect (Γ := Γ) k A C N flag mark)
    (hC : M C = drainPop (Γ := Γ) (σ := σ) k A)
    (hft : ∀ v, flag (mark v true) = true) (hff : ∀ v, flag (mark v false) = false)
    (hN : M N = load (fun _ : σ => v₀) halt)
    (L : List (Γ k)) (v : σ) (S : ∀ j, List (Γ j)) (hS : S k = L) :
    EvalsToInTime (Turing.TM2.step M) ⟨some A, v, S⟩
      (some ⟨none, v₀, Function.update S k []⟩) (1 + (2 * L.length + 1)) := by
  exact EvalsToInTime.trans' (drain_stack hA hC hft hff L v S hS) (halt_at hN _ _)

/-! ### End-to-end exit stage for a bundled machine -/

/-- **Exit stage, packaged.**  For a bundled machine whose program at `A`, `C`, `N` is the drain
loop and the final `load … halt`, starting at `⟨some A, v, S⟩` where every stack other than `k` is
already in its halting shape, the machine reaches the exact halting configuration
`haltList tm out` — i.e. `TM2OutputsInTime` — in `2 * (S k).length + 2` steps. -/
def exit_stage_one {tm : Turing.FinTM2} {out : List (tm.Γ tm.k₁)} {k : tm.K} {A C N : tm.Λ}
    {flag : tm.σ → Bool} {mark : tm.σ → Bool → tm.σ}
    (hA : tm.m A = drainDetect (Γ := tm.Γ) k A C N flag mark)
    (hC : tm.m C = drainPop (Γ := tm.Γ) (σ := tm.σ) k A)
    (hft : ∀ v, flag (mark v true) = true) (hff : ∀ v, flag (mark v false) = false)
    (hN : tm.m N = load (fun _ : tm.σ => tm.initialState) halt)
    (hk : k ≠ tm.k₁) (v : tm.σ) (S : ∀ j, List (tm.Γ j))
    (hS : ∀ j, j ≠ k → S j = haltStacks tm out j) :
    EvalsToInTime (Turing.TM2.step tm.m) ⟨some A, v, S⟩
      (some (Turing.haltList tm out)) (1 + (2 * (S k).length + 1)) := by
  have h1 := drain_stack' (M := tm.m) hA hC hft hff (v := v) (S := S)
  have h2 := halt_at (M := tm.m) (N := N) (v₀ := tm.initialState) hN
    (mark ((fun w => mark w false)^[(S k).length] v) true) (Function.update S k [])
  have h3 := EvalsToInTime.trans' h1 h2
  have hcfg : (⟨none, tm.initialState, Function.update S k []⟩ : tm.Cfg) =
      Turing.haltList tm out := by
    refine mk_haltList (hv := rfl) ?_
    funext j
    by_cases hj : j = k
    · subst hj
      rw [Function.update_self]
      simp [haltStacks, hk]
    · rw [Function.update_of_ne hj, hS j hj]
  have hcfg' : (some ⟨none, tm.initialState, Function.update S k []⟩ : Option tm.Cfg)
      = some (Turing.haltList tm out) := by rw [hcfg]
  exact EvalsToInTime.congr_cfg rfl hcfg' h3

@[simp] theorem initStacks_k0 (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀)) :
    initStacks tm l tm.k₀ = l := by
  simp [initStacks]

@[simp] theorem haltStacks_k1 (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁)) :
    haltStacks tm out tm.k₁ = out := by
  simp [haltStacks]

@[simp] theorem initList_stk (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀)) (k : tm.K) :
    (Turing.initList tm l).stk k = initStacks tm l k := rfl

@[simp] theorem haltList_stk (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁)) (k : tm.K) :
    (Turing.haltList tm out).stk k = haltStacks tm out k := rfl

/-- `TM2OutputsInTime` is monotone in the step bound (useful for polynomial slack). -/
def tm2OutputsInTime_mono {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {out : Option (List (tm.Γ tm.k₁))} {m m' : ℕ} (h : Turing.TM2OutputsInTime tm l out m)
    (hm : m ≤ m') : Turing.TM2OutputsInTime tm l out m' :=
  EvalsToInTime.mono h hm

end QMCExit



namespace Turing

namespace CompCore

variable {tm₁ : FinTM2} {tm₂ : FinTM2}
variable {βΓ : Type} [Inhabited βΓ]
/-- **Copy pass 1, whole word** (`EvalsToInTime` form): moves `L` from `tm₁`'s output stack onto the
temporary stack through the two alphabets' equivalences (reversing it) in `|L| + 1` steps. -/
noncomputable def copy₁_trace (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    ∀ (L : List (tm₁.Γ tm₁.k₁)) (v : Sta tm₁ tm₂)
      (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
      (T : List (tm₂.Γ tm₂.k₀)), S₁ tm₁.k₁ = L →
      EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
        ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
        (some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ []) S₂
            ((L.map (fun x => ia₂.invFun (oa₁ x))).reverse ++ T)⟩) (L.length + 1)
  | [], v, S₁, S₂, T, hL => by
      have hupd : Function.update S₁ tm₁.k₁ ([] : List (tm₁.Γ tm₁.k₁)) = S₁ := by
        rw [← hL]; exact Function.update_eq_self _ _
      rw [hupd]
      have hstep := step_copy₁_nil tm₁ tm₂ oa₁ ia₂ v S₁ S₂ T hL
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      refine ⟨⟨1, ?_⟩, by simp⟩
      rw [Function.iterate_one, this]
      exact hstep
  | x :: xs, v, S₁, S₂, T, hL => by
      have hstep := step_copy₁_some tm₁ tm₂ oa₁ ia₂ v S₁ S₂ T x xs hL
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have e1 : EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
          ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
          (some ⟨some (Sum.inr (Sum.inl 0)), (v.1, (v.2.1, some (ia₂.invFun (oa₁ x)))),
            pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ xs) S₂ (ia₂.invFun (oa₁ x) :: T)⟩) 1 := by
        refine ⟨⟨1, ?_⟩, by simp⟩
        rw [Function.iterate_one, this]
        exact hstep
      refine (QMCExit.EvalsToInTime.trans' e1 (copy₁_trace oa₁ ia₂ xs (v.1, (v.2.1, some (ia₂.invFun (oa₁ x))))
        (Function.update S₁ tm₁.k₁ xs) S₂ (ia₂.invFun (oa₁ x) :: T) (by simp)))
        |> QMCExit.EvalsToInTime.congr_cfg rfl (by
            simp only [List.map_cons, List.reverse_cons, List.map_append, List.append_assoc,
              List.singleton_append, List.append_nil, List.nil_append, Function.update_idem])
        |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

/-- **Copy pass 2, whole word** (`EvalsToInTime` form). -/
noncomputable def copy₂_trace (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    ∀ (L : List (tm₂.Γ tm₂.k₀)) (v : Sta tm₁ tm₂)
      (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k)),
      EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
        ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ L⟩
        (some ⟨some (Sum.inr (Sum.inr tm₂.main)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (L.reverse ++ S₂ tm₂.k₀)) []⟩) (L.length + 1)
  | [], v, S₁, S₂ => by
      have hstep := step_copy₂_nil tm₁ tm₂ oa₁ ia₂ v S₁ S₂ [] rfl
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ []⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have hupd : Function.update S₂ tm₂.k₀ (([] : List (tm₂.Γ tm₂.k₀)).reverse ++ S₂ tm₂.k₀)
          = S₂ := by simp
      rw [hupd]
      refine ⟨⟨1, ?_⟩, by simp⟩
      rw [Function.iterate_one, this]
      exact hstep
  | x :: xs, v, S₁, S₂ => by
      have hstep := step_copy₂_some tm₁ tm₂ oa₁ ia₂ v S₁ S₂ (x :: xs) x xs rfl
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ (x :: xs)⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have e1 : EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
          ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ (x :: xs)⟩
          (some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, some x)),
            pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀)) xs⟩) 1 := by
        refine ⟨⟨1, ?_⟩, by simp⟩
        rw [Function.iterate_one, this]
        exact hstep
      refine (QMCExit.EvalsToInTime.trans' e1 (copy₂_trace oa₁ ia₂ xs (v.1, (v.2.1, some x)) S₁
        (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀))))
        |> QMCExit.EvalsToInTime.congr_cfg rfl (by
            simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
              Function.update_idem, Function.update_self])
        |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

end CompCore

end Turing


/-! ### Growth and size bounds (from the swarm's `Growth.lean`) -/

attribute [instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin Turing.FinTM2.ΛFin
  Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

namespace Turing

namespace TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- The number of `push` statements executed inside a single statement chain.

A single `TM2.step` runs a whole chain (`push`/`peek`/`pop`/`load`/`branch` continue within the
same step), ending at `goto` or `halt`; `pushes` therefore bounds the number of symbols that a step
can add to the stacks. -/
def pushes : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

variable [Fintype K] [DecidableEq K]

/-- Total number of symbols stored on all stacks. -/
def volume (s : (k : K) → List (Γ k)) : ℕ := ∑ k, (s k).length

theorem length_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
  funext j
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem volume_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (Function.update s k v) + (s k).length = volume s + v.length := by
  classical
  unfold volume
  rw [length_update, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s + pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have hv := volume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      have hq := ih v (Function.update s k (g v :: s k))
      simp only [TM2.stepAux, pushes]
      omega
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      have hq := ih (g v (s k).head?) (Function.update s k (s k).tail)
      simp only [TM2.stepAux, pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [TM2.stepAux, hg, Bool.cond_false, pushes]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simp only [TM2.stepAux, hg, Bool.cond_true, pushes]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _
  | halt => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _

end TM2

open TM2 in
/-- Number of symbols a machine can add to all of its stacks in one step, summed over its program. -/
noncomputable def FinTM2.growth (tm : FinTM2) : ℕ := ∑ l, TM2.pushes (tm.m l)

namespace FinTM2

variable (tm : FinTM2)

theorem flip_bind_none : (flip bind tm.step) (none : Option tm.Cfg) = none := rfl

theorem flip_bind_some (c : tm.Cfg) : (flip bind tm.step) (some c) = tm.step c := rfl

theorem step_volume {a b : tm.Cfg} (h : tm.step a = some b) :
    TM2.volume b.stk ≤ TM2.volume a.stk + tm.growth := by
  classical
  obtain ⟨l, v, s⟩ := a
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
      have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
      rw [hb, FinTM2.growth]
      refine (TM2.stepAux_volume _ _ _).trans (Nat.add_le_add_left ?_ _)
      exact Finset.single_le_sum (f := fun x => TM2.pushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem iterate_volume (tm : FinTM2) : ∀ (m : ℕ) (a b : tm.Cfg),
    (flip bind tm.step)^[m] (some a) = some b →
      TM2.volume b.stk ≤ TM2.volume a.stk + m * tm.growth
  | 0, a, b, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h; simp
  | m + 1, a, b, h => by
      rw [Function.iterate_succ_apply'] at h
      cases hprev : (flip bind tm.step)^[m] (some a) with
      | none => rw [hprev, tm.flip_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hprev, tm.flip_bind_some] at h
          have ih := iterate_volume tm m a c hprev
          have hs := tm.step_volume h
          have hmul : (m + 1) * tm.growth = m * tm.growth + tm.growth := Nat.succ_mul _ _
          rw [hmul]
          omega

theorem volume_initList (s : List (tm.Γ tm.k₀)) : TM2.volume (initList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk
    simp only [initList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem volume_haltList (s : List (tm.Γ tm.k₁)) : TM2.volume (haltList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk
    simp only [haltList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

end FinTM2

end Turing



namespace Turing

/-- **Output length bound for an arbitrary `FinTM2`.** If `tm` outputs `t` on input `s` within `n`
steps, then `t` has at most `s.length + n * growth` symbols. -/
theorem TM2OutputsInTime.output_length_le {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) : t.length ≤ s.length + n * tm.growth := by
  have hvol := tm.iterate_volume h.steps (initList tm s) (haltList tm t) h.evals_in_steps
  rw [tm.volume_initList, tm.volume_haltList] at hvol
  exact hvol.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Turing

namespace Turing

open Polynomial in
/-- General-`Γ` analogue of `OAI.MetricKMedian.Binary.PolyProgram.sizeBound`: the polynomial that
bounds the *length* of a machine's output, given a polynomial bound `p` on its number of steps. -/
noncomputable def FinTM2.sizeBound (tm : FinTM2) (p : Polynomial ℕ) : Polynomial ℕ :=
  X + p * C tm.growth

namespace FinTM2

theorem eval_sizeBound (tm : FinTM2) (p : Polynomial ℕ) (n : ℕ) :
    (tm.sizeBound p).eval n = n + p.eval n * tm.growth := by
  simp [sizeBound]

/-- The identity a composite needs: evaluating a time polynomial at the *output length* of a first
machine is the same as evaluating its composition with `sizeBound` at the input length. -/
theorem eval_comp_sizeBound (tm : FinTM2) (q p : Polynomial ℕ) (n : ℕ) :
    (q.comp (tm.sizeBound p)).eval n = q.eval (n + p.eval n * tm.growth) := by
  rw [Polynomial.eval_comp, tm.eval_sizeBound]

end FinTM2

/-- **Output length bound, polynomial form** (general-`Γ` analogue of
`PolyProgram.length_bound`). If `tm` outputs `t` on input `s` within `p.eval s.length` steps, then
`t.length ≤ (tm.sizeBound p).eval s.length`. This is what lets a composite bound the length of the
string it feeds into the next machine. -/
theorem TM2OutputsInTime.length_le_sizeBound {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {p : Polynomial ℕ}
    (h : TM2OutputsInTime tm s (some t) (p.eval s.length)) :
    t.length ≤ (tm.sizeBound p).eval s.length := by
  rw [tm.eval_sizeBound]
  exact TM2OutputsInTime.output_length_le h

end Turing


/-! ## Assembling the composite run

Now the pieces: machine 1's run (`phase₁`), the two copy passes, machine 2's run (`phase₂`).
Note that no exit stage is needed: copy pass 1 *empties* `tm₁`'s output stack, copy pass 2 empties
the temporary stack, and `tm₂`'s halting configuration has every stack but its output stack empty.
So the composite already ends in the exact halting configuration of `compTM`.
-/

namespace Turing

namespace CompCore

open Polynomial

/-- `initStacks` is "put `l` on the input stack, nothing elsewhere". -/
theorem initStacks_eq_update (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    QMCExit.initStacks tm l = Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ l := by
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp [QMCExit.initStacks]
  · simp [QMCExit.initStacks, Function.update, h]

/-- Internal initial state of the composite. -/
def compInit (tm₁ tm₂ : FinTM2) : Sta tm₁ tm₂ :=
  (tm₁.initialState, (tm₂.initialState, none))

variable {tm₁ : FinTM2} {tm₂ : FinTM2}
variable {βΓ : Type} [Inhabited βΓ]

/-- **The composite machine**: run `tm₁`, copy its output onto `tm₂`'s input, run `tm₂`.
(An `abbrev`, so that its stack indices reduce definitionally.) -/
noncomputable abbrev compTM (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) : FinTM2 where
  K := Key tm₁ tm₂
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := Sum.inl tm₁.k₀
  k₁ := Sum.inr (Sum.inl tm₂.k₁)
  Γ := Gam tm₁ tm₂
  Λ := Lab tm₁ tm₂
  main := Sum.inl tm₁.main
  ΛFin := inferInstance
  σ := Sta tm₁ tm₂
  initialState := compInit tm₁ tm₂
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := compProg tm₁ tm₂ oa₁ ia₂

/-- The composite's input stack family is `pack` of `tm₁`'s. -/
theorem pack_initStacks (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (l : List (tm₁.Γ tm₁.k₀)) :
    pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []
      = QMCExit.initStacks (compTM oa₁ ia₂) l := by
  funext k
  rcases k with a | (b | u)
  · show QMCExit.initStacks tm₁ l a = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inl a)
    unfold QMCExit.initStacks
    by_cases h : a = tm₁.k₀
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (by simpa using h)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inl b))))
        = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inr (Sum.inl b))
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₀ from
      by intro e; cases e)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inr u))))
        = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inr (Sum.inr u))
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₀ from
      by intro e; cases e)]

/-- The composite's halting stack family is `pack` of `tm₂`'s. -/
theorem pack_haltStacks (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (u : List (tm₂.Γ tm₂.k₁)) :
    pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []
      = QMCExit.haltStacks (compTM oa₁ ia₂) u := by
  funext k
  rcases k with a | (b | uu)
  · show ([] : List (Gam tm₁ tm₂ (Sum.inl a)))
        = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inl a)
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inl a : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₁ from
      by intro e; cases e)]
  · show QMCExit.haltStacks tm₂ u b = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inr (Sum.inl b))
    unfold QMCExit.haltStacks
    by_cases h : b = tm₂.k₁
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (by simpa using h)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inr uu))))
        = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inr (Sum.inr uu))
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inr (Sum.inr uu) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₁ from
      by intro e; cases e)]

/-- The stack that copy pass 1 leaves behind is empty. -/
theorem update_haltStacks_self (t : List (tm₁.Γ tm₁.k₁)) :
    Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = tm₁.k₁
  · subst h; simp
  · rw [Function.update_of_ne h]
    simp [QMCExit.haltStacks, h]

/-- **Phase 1**: machine 1's run, lifted into the composite. -/
noncomputable def phase₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {N : ℕ}
    (h : TM2OutputsInTime tm₁ l (some t) N) :
    EvalsToInTime (TM2.step M)
      ⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩
      (some ⟨some (Sum.inr (Sum.inl 0)), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.haltStacks tm₁ t) (fun _ => []) []⟩) N := by
  have h1 := iterate_cfg₁ (tm₁ := tm₁) (tm₂ := tm₂) (M := M) hM tm₂.initialState
    (none : Option (tm₂.Γ tm₂.k₀)) (fun _ => []) [] h.steps
    (Turing.initList tm₁ l) (Turing.haltList tm₁ t) h.evals_in_steps
  exact ⟨⟨h.steps, h1⟩, h.steps_le_m⟩

/-- **Phase 2**: machine 2's run, lifted into the composite. -/
noncomputable def phase₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    {S₁ : (k : tm₁.K) → List (tm₁.Γ k)}
    {l : List (tm₂.Γ tm₂.k₀)} {u : List (tm₂.Γ tm₂.k₁)} {M' : ℕ}
    (h : TM2OutputsInTime tm₂ l (some u) M') :
    EvalsToInTime (TM2.step M)
      ⟨some (Sum.inr (Sum.inr tm₂.main)), compInit tm₁ tm₂,
        pack tm₁ tm₂ S₁ (QMCExit.initStacks tm₂ l) []⟩
      (some ⟨none, compInit tm₁ tm₂, pack tm₁ tm₂ S₁ (QMCExit.haltStacks tm₂ u) []⟩) M' := by
  have h1 := iterate_cfg₂ (tm₁ := tm₁) (tm₂ := tm₂) (M := M) hM tm₁.initialState
    (none : Option (tm₂.Γ tm₂.k₀)) S₁ [] h.steps
    (Turing.initList tm₂ l) (Turing.haltList tm₂ u) h.evals_in_steps
  exact ⟨⟨h.steps, h1⟩, h.steps_le_m⟩

/-- **The composite run**: machine 1, the two copy passes, machine 2. -/
noncomputable def comp_run (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {u : List (tm₂.Γ tm₂.k₁)}
    {N M' : ℕ} (h₁ : TM2OutputsInTime tm₁ l (some t) N)
    (h₂ : TM2OutputsInTime tm₂ (t.map (fun x => ia₂.invFun (oa₁ x))) (some u) M') :
    EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
      ⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩
      (some ⟨none, compInit tm₁ tm₂,
        pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []⟩)
      (M' + ((t.length + 1) + ((t.length + 1) + N))) := by
  have hP1 := phase₁ (tm₁ := tm₁) (tm₂ := tm₂) (compProg tm₁ tm₂ oa₁ ia₂) (fun _ => rfl) h₁
  have hC1 := copy₁_trace (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂ t (compInit tm₁ tm₂)
    (QMCExit.haltStacks tm₁ t) (fun _ => []) [] (QMCExit.haltStacks_k1 tm₁ t)
  have hC2 := copy₂_trace (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂
    ((t.map (fun x => ia₂.invFun (oa₁ x))).reverse) (compInit tm₁ tm₂)
    (Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ []) (fun _ => [])
  have hP2 := phase₂ (tm₁ := tm₁) (tm₂ := tm₂) (compProg tm₁ tm₂ oa₁ ia₂) (fun _ => rfl)
    (S₁ := Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ []) h₂
  -- copy pass 1, with its endpoint written for copy pass 2
  have hC1' := hC1
  simp only [compInit, List.append_nil] at hC1'
  -- copy pass 2, with its endpoint written for machine 2
  have hC2' := hC2
  simp only [compInit, ← initStacks_eq_update, List.reverse_reverse, List.append_nil] at hC2'
  have hchain := QMCExit.EvalsToInTime.trans'
    (QMCExit.EvalsToInTime.trans' (QMCExit.EvalsToInTime.trans' hP1 hC1') hC2') hP2
  simpa only [update_haltStacks_self, List.length_reverse, List.length_map] using hchain

/-- The composite run, packaged as `TM2OutputsInTime` for `compTM`. -/
noncomputable def tm2OutputsInTime_comp (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ)
    (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {u : List (tm₂.Γ tm₂.k₁)}
    {N M' : ℕ} (h₁ : TM2OutputsInTime tm₁ l (some t) N)
    (h₂ : TM2OutputsInTime tm₂ (t.map (fun x => ia₂.invFun (oa₁ x))) (some u) M') :
    TM2OutputsInTime (compTM oa₁ ia₂) l (some u)
      (M' + ((t.length + 1) + ((t.length + 1) + N))) := by
  have hrun := comp_run (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂ h₁ h₂
  have hstart : Turing.initList (compTM oa₁ ia₂) l =
      (⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩ :
        TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := by
    have h1 : Turing.initList (compTM oa₁ ia₂) l =
        (⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
          QMCExit.initStacks (compTM oa₁ ia₂) l⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := rfl
    rw [h1, ← pack_initStacks]
  have hend : (⟨none, compInit tm₁ tm₂,
        pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []⟩ :
        TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      = Turing.haltList (compTM oa₁ ia₂) u := by
    have h1 : Turing.haltList (compTM oa₁ ia₂) u =
        (⟨none, compInit tm₁ tm₂, QMCExit.haltStacks (compTM oa₁ ia₂) u⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := rfl
    rw [h1, ← pack_haltStacks]
  have h := hrun
  rw [← hstart, hend] at h
  exact QMCExit.tm2OutputsInTime_of_cfg h rfl

/-- Polynomial evaluation on `ℕ` is monotone. -/
theorem poly_eval_mono (q : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : q.eval a ≤ q.eval b := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval_add, Polynomial.eval_add]; exact add_le_add hp hq
  | monomial n c =>
      rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

/-- The arithmetic of the composite's time bound. -/
theorem comp_time_le (tm : FinTM2) (p q : Polynomial ℕ) (n Lt N M' : ℕ)
    (hN : N ≤ p.eval n) (hLt : Lt ≤ (tm.sizeBound p).eval n) (hM : M' ≤ q.eval Lt) :
    M' + ((Lt + 1) + ((Lt + 1) + N)) ≤
      (p + C 2 * (tm.sizeBound p + 1) + q.comp (tm.sizeBound p)).eval n := by
  have hSB : (tm.sizeBound p).eval n = n + p.eval n * tm.growth := tm.eval_sizeBound p n
  have h1 : (p + C 2 * (tm.sizeBound p + 1) + q.comp (tm.sizeBound p)).eval n
      = p.eval n + 2 * ((tm.sizeBound p).eval n + 1) + q.eval ((tm.sizeBound p).eval n) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one,
      Polynomial.eval_X, Polynomial.eval_comp]
  rw [h1, hSB]
  have hmono : q.eval Lt ≤ q.eval (n + p.eval n * tm.growth) := by
    rw [hSB] at hLt
    exact poly_eval_mono q hLt
  omega

end CompCore

end Turing

/-! ## The composition theorem -/

namespace Turing

open Polynomial

/-- **Composition of polynomial-time TM2 machines.** This is the statement of Mathlib's
`proof_wanted TM2ComputableInPolyTime.comp`, proved here for an inhabited middle alphabet
(the general case is reduced to this one plus the empty-alphabet variant). -/
theorem TM2ComputableInPolyTime.comp_of_inhabited
    {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
    {f : α → β} {g : β → γ} [Inhabited βΓ]
    (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  classical
  have hmap : ∀ s : List βΓ,
      List.map (fun x => h2.inputAlphabet.invFun (h1.outputAlphabet x))
        (List.map h1.outputAlphabet.invFun s) = List.map h2.inputAlphabet.invFun s := by
    intro s
    rw [List.map_map]
    simp only [Function.comp_def]
    rw [show (fun y => h2.inputAlphabet.invFun (h1.outputAlphabet (h1.outputAlphabet.invFun y)))
        = h2.inputAlphabet.invFun from by
      funext y
      rw [show h1.outputAlphabet (h1.outputAlphabet.invFun y) = y from
        Equiv.apply_symm_apply h1.outputAlphabet y]]
  refine ⟨⟨⟨CompCore.compTM h1.outputAlphabet h2.inputAlphabet, h1.inputAlphabet,
      h2.outputAlphabet⟩,
    h1.time + C 2 * (h1.tm.sizeBound h1.time + 1) + h2.time.comp (h1.tm.sizeBound h1.time), ?_⟩⟩
  intro a
  have h1a := h1.outputsFun a
  have h1a' : TM2OutputsInTime h1.tm
      (List.map h1.inputAlphabet.invFun (eα a))
      (some (List.map h1.outputAlphabet.invFun (eβ (f a))))
      (h1.time.eval (List.map h1.inputAlphabet.invFun (eα a)).length) := by
    rw [List.length_map]; exact h1a
  have h2a := h2.outputsFun (f a)
  have h2a' : TM2OutputsInTime h2.tm
      (List.map (fun x => h2.inputAlphabet.invFun (h1.outputAlphabet x))
        (List.map h1.outputAlphabet.invFun (eβ (f a))))
      (some (List.map h2.outputAlphabet.invFun (eγ (g (f a)))))
      (h2.time.eval (eβ (f a)).length) := by
    rw [hmap]; exact h2a
  have hrun := CompCore.tm2OutputsInTime_comp (tm₁ := h1.tm) (tm₂ := h2.tm)
    h1.outputAlphabet h2.inputAlphabet h1a h2a'
  refine QMCExit.tm2OutputsInTime_mono hrun (CompCore.comp_time_le h1.tm h1.time h2.time
    (eα a).length (List.length (List.map h1.outputAlphabet.invFun (eβ (f a))))
    (h1.time.eval (eα a).length) (h2.time.eval (eβ (f a)).length) le_rfl ?_ ?_)
  · have h := TM2OutputsInTime.length_le_sizeBound h1a'
    simp only [List.length_map] at h ⊢
    exact h
  · rw [List.length_map]

end Turing

/-! ### Axiom audit -/

/-! ## The empty-middle-alphabet case

If the middle alphabet `βΓ` is empty, then every `eβ b` is `[]`: machine 1 outputs the empty word and
machine 2's input stack is already empty, so the copy phase is replaced by a single jump.
-/

namespace Turing

namespace CompCore

variable {tm₁ : FinTM2} {tm₂ : FinTM2}

theorem haltStacks_eq_update (tm : FinTM2) (u : List (tm.Γ tm.k₁)) :
    QMCExit.haltStacks tm u = Function.update (fun k => ([] : List (tm.Γ k))) tm.k₁ u := by
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp [QMCExit.haltStacks]
  · simp [QMCExit.haltStacks, Function.update, h]

theorem initStacks_nil (tm : FinTM2) :
    QMCExit.initStacks tm ([] : List (tm.Γ tm.k₀)) = fun _ => [] := by
  rw [initStacks_eq_update]
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · rw [Function.update_of_ne h]

theorem haltStacks_nil (tm : FinTM2) :
    QMCExit.haltStacks tm ([] : List (tm.Γ tm.k₁)) = fun _ => [] := by
  rw [haltStacks_eq_update]
  funext k
  by_cases h : k = tm.k₁
  · subst h; simp
  · rw [Function.update_of_ne h]

/-- Program of the degenerate composite (empty middle alphabet): machine 1, then a jump into
machine 2's main label. -/
def compProgE : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .inl l => tr₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl 0) => .goto (fun _ => Sum.inr (Sum.inr tm₂.main))
  | .inr (.inl 1) => .goto (fun _ => Sum.inr (Sum.inr tm₂.main))
  | .inr (.inr l) => tr₂ tm₁ tm₂ (tm₂.m l)

/-- The degenerate composite machine. -/
noncomputable abbrev compTME : FinTM2 where
  K := Key tm₁ tm₂
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := Sum.inl tm₁.k₀
  k₁ := Sum.inr (Sum.inl tm₂.k₁)
  Γ := Gam tm₁ tm₂
  Λ := Lab tm₁ tm₂
  main := Sum.inl tm₁.main
  ΛFin := inferInstance
  σ := Sta tm₁ tm₂
  initialState := compInit tm₁ tm₂
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := compProgE

/-- The composite's input stack family, for the degenerate machine. -/
theorem pack_initStacksE (l : List (tm₁.Γ tm₁.k₀)) :
    pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []
      = QMCExit.initStacks compTME l := by
  funext k
  rcases k with a | (b | u)
  · show QMCExit.initStacks tm₁ l a = QMCExit.initStacks compTME l (Sum.inl a)
    unfold QMCExit.initStacks
    by_cases h : a = tm₁.k₀
    · subst h; rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (by simpa using h)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inl b))))
        = QMCExit.initStacks compTME l (Sum.inr (Sum.inl b))
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ compTME.k₀ from by intro e; cases e)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inr u))))
        = QMCExit.initStacks compTME l (Sum.inr (Sum.inr u))
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ compTME.k₀ from by intro e; cases e)]

/-- The composite's halting stack family, for the degenerate machine. -/
theorem pack_haltStacksE (u : List (tm₂.Γ tm₂.k₁)) :
    pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []
      = QMCExit.haltStacks compTME u := by
  funext k
  rcases k with a | (b | uu)
  · show ([] : List (Gam tm₁ tm₂ (Sum.inl a))) = QMCExit.haltStacks compTME u (Sum.inl a)
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inl a : Key tm₁ tm₂) ≠ compTME.k₁ from by intro e; cases e)]
  · show QMCExit.haltStacks tm₂ u b = QMCExit.haltStacks compTME u (Sum.inr (Sum.inl b))
    unfold QMCExit.haltStacks
    by_cases h : b = tm₂.k₁
    · subst h; rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (by simpa using h)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inr uu))))
        = QMCExit.haltStacks compTME u (Sum.inr (Sum.inr uu))
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inr (Sum.inr uu) : Key tm₁ tm₂) ≠ compTME.k₁ from by intro e; cases e)]

/-- **The degenerate composite run**: machine 1, one jump, machine 2. -/
noncomputable def comp_runE {l : List (tm₁.Γ tm₁.k₀)} {N : ℕ}
    (h₁ : TM2OutputsInTime tm₁ l (some ([] : List (tm₁.Γ tm₁.k₁))) N)
    {u : List (tm₂.Γ tm₂.k₁)} {M' : ℕ} (h₂ : TM2OutputsInTime tm₂ [] (some u) M') :
    EvalsToInTime (TM2.step compProgE)
      ⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩
      (some ⟨none, compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.haltStacks tm₁ []) (QMCExit.haltStacks tm₂ u) []⟩)
      (M' + (1 + N)) := by
  have hP1 := phase₁ (tm₁ := tm₁) (tm₂ := tm₂) compProgE (fun _ => rfl) h₁
  have hG := QMCExit.goto_step (M := compProgE)
    (A := Sum.inr (Sum.inl 0)) (B := Sum.inr (Sum.inr tm₂.main)) rfl (compInit tm₁ tm₂)
    (pack tm₁ tm₂ (QMCExit.haltStacks tm₁ []) (fun _ => []) [])
  have hP2 := phase₂ (tm₁ := tm₁) (tm₂ := tm₂) compProgE (fun _ => rfl)
    (S₁ := QMCExit.haltStacks tm₁ []) (l := []) h₂
  rw [initStacks_nil] at hP2
  exact QMCExit.EvalsToInTime.mono
    (QMCExit.EvalsToInTime.trans' (QMCExit.EvalsToInTime.trans' hP1 hG) hP2) (by omega)

/-- The degenerate composite run, packaged as `TM2OutputsInTime`. -/
noncomputable def tm2OutputsInTime_compE
    {l : List (tm₁.Γ tm₁.k₀)} {N : ℕ}
    (h₁ : TM2OutputsInTime tm₁ l (some ([] : List (tm₁.Γ tm₁.k₁))) N)
    {u : List (tm₂.Γ tm₂.k₁)} {M' : ℕ} (h₂ : TM2OutputsInTime tm₂ [] (some u) M') :
    TM2OutputsInTime compTME l (some u) (M' + (1 + N)) := by
  have hrun := comp_runE (tm₁ := tm₁) (tm₂ := tm₂) h₁ h₂
  have hstart : Turing.initList compTME l =
      (⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩ :
        TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := by
    have h1 : Turing.initList compTME l =
        (⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂, QMCExit.initStacks compTME l⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := rfl
    rw [h1, ← pack_initStacksE]
  have hend : (⟨none, compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.haltStacks tm₁ []) (QMCExit.haltStacks tm₂ u) []⟩ :
        TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      = Turing.haltList compTME u := by
    have h1 : Turing.haltList compTME u =
        (⟨none, compInit tm₁ tm₂, QMCExit.haltStacks compTME u⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := rfl
    rw [h1, ← pack_haltStacksE, haltStacks_nil]
  have h := hrun
  rw [← hstart, hend] at h
  exact h

end CompCore

end Turing

namespace Turing

open Polynomial

/-- **Composition of polynomial-time TM2 machines, empty middle alphabet.** -/
theorem TM2ComputableInPolyTime.comp_of_empty
    {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
    {f : α → β} {g : β → γ} (hβ : ¬ Nonempty βΓ)
    (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  classical
  have hnil : ∀ s : List βΓ, s = [] := fun s => by
    rcases s with _ | ⟨b, _⟩
    · rfl
    · exact absurd ⟨b⟩ hβ
  refine ⟨⟨⟨CompCore.compTME (tm₁ := h1.tm) (tm₂ := h2.tm), h1.inputAlphabet,
      h2.outputAlphabet⟩,
    h1.time + C 2 * (h1.tm.sizeBound h1.time + 1) + h2.time.comp (h1.tm.sizeBound h1.time), ?_⟩⟩
  intro a
  have h1a := h1.outputsFun a
  rw [hnil (eβ (f a))] at h1a
  simp only [List.map_nil] at h1a
  have h2a := h2.outputsFun (f a)
  rw [hnil (eβ (f a))] at h2a
  simp only [List.map_nil, List.length_nil] at h2a
  have hrun := CompCore.tm2OutputsInTime_compE (tm₁ := h1.tm) (tm₂ := h2.tm) h1a h2a
  refine QMCExit.tm2OutputsInTime_mono hrun ?_
  refine le_trans (by omega) (CompCore.comp_time_le h1.tm h1.time h2.time (eα a).length 0
    (h1.time.eval (eα a).length) (h2.time.eval 0) le_rfl (Nat.zero_le _) le_rfl)

/-- **Composition of polynomial-time TM2 machines.**  This is the statement of Mathlib's
`proof_wanted TM2ComputableInPolyTime.comp`, with no hypothesis on the middle alphabet. -/
theorem TM2ComputableInPolyTime.comp'
    {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (h1 : TM2ComputableInPolyTime eα eβ f) (h2 : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) := by
  classical
  by_cases h : Nonempty βΓ
  · haveI : Inhabited βΓ := Classical.inhabited_of_nonempty h
    exact TM2ComputableInPolyTime.comp_of_inhabited h1 h2
  · exact TM2ComputableInPolyTime.comp_of_empty h h1 h2


end Turing


namespace KeepCore
open Turing

variable (Q : FinTM2)

abbrev KKey : Type := Q.K ⊕ Bool

abbrev KGam : KKey Q → Type
  | .inl k => Q.Γ k
  | .inr _ => Bool

abbrev KLab : Type := Q.Λ ⊕ Fin 3

abbrev KSta : Type := Q.σ × Option Bool

def kpack (S : (k : Q.K) → List (Q.Γ k)) (A B : List Bool) : (k : KKey Q) → List (KGam Q k)
  | .inl k => S k
  | .inr false => A
  | .inr true => B

theorem kpack_update_left (S : (k : Q.K) → List (Q.Γ k)) (A B : List Bool)
    (k : Q.K) (x : List (Q.Γ k)) :
    Function.update (kpack Q S A B) (Sum.inl k) x = kpack Q (Function.update S k x) A B := by
  funext j
  rcases j with a | (_ | _)
  · by_cases h : a = k
    · subst h; simp [kpack]
    · simp only [kpack, Function.update_of_ne (by simp [h] : (Sum.inl a : KKey Q) ≠ Sum.inl k),
        Function.update_of_ne h]
  · simp only [kpack, Function.update_of_ne (by simp : (Sum.inr false : KKey Q) ≠ Sum.inl k)]
  · simp only [kpack, Function.update_of_ne (by simp : (Sum.inr true : KKey Q) ≠ Sum.inl k)]

theorem kpack_update_side (S : (k : Q.K) → List (Q.Γ k)) (A B : List Bool) (x : List Bool) :
    Function.update (kpack Q S A B) (Sum.inr false) x = kpack Q S x B := by
  funext j
  rcases j with a | (_ | _)
  · simp only [kpack, Function.update_of_ne (by simp : (Sum.inl a : KKey Q) ≠ Sum.inr false)]
  · simp [kpack]
  · simp only [kpack, Function.update_of_ne (by simp : (Sum.inr true : KKey Q) ≠ Sum.inr false)]

theorem kpack_update_tmp (S : (k : Q.K) → List (Q.Γ k)) (A B : List Bool) (x : List Bool) :
    Function.update (kpack Q S A B) (Sum.inr true) x = kpack Q S A x := by
  funext j
  rcases j with a | (_ | _)
  · simp only [kpack, Function.update_of_ne (by simp : (Sum.inl a : KKey Q) ≠ Sum.inr true)]
  · simp only [kpack, Function.update_of_ne (by simp : (Sum.inr false : KKey Q) ≠ Sum.inr true)]
  · simp [kpack]

def labQ : Option Q.Λ → Option (KLab Q)
  | none => some (Sum.inr 2)
  | some l => some (Sum.inl l)

def trQ : TM2.Stmt Q.Γ Q.Λ Q.σ → TM2.Stmt (KGam Q) (KLab Q) (KSta Q)
  | .push k g q => .push (Sum.inl k) (fun s => g s.1) (trQ q)
  | .peek k g q => .peek (Sum.inl k) (fun s o => (g s.1 o, s.2)) (trQ q)
  | .pop k g q => .pop (Sum.inl k) (fun s o => (g s.1 o, s.2)) (trQ q)
  | .load g q => .load (fun s => (g s.1, s.2)) (trQ q)
  | .branch g q r => .branch (fun s => g s.1) (trQ q) (trQ r)
  | .goto g => .goto (fun s => Sum.inl (g s.1))
  | .halt => .goto (fun _ => Sum.inr 2)

theorem stepAux_trQ (q : TM2.Stmt Q.Γ Q.Λ Q.σ) (v : Q.σ) (b : Option Bool)
    (S : (k : Q.K) → List (Q.Γ k)) (A B : List Bool) :
    TM2.stepAux (trQ Q q) (v, b) (kpack Q S A B)
      = ⟨labQ Q (TM2.stepAux q v S).l, ((TM2.stepAux q v S).var, b),
          kpack Q (TM2.stepAux q v S).stk A B⟩ := by
  induction q generalizing v S with
  | push k g q ih =>
      simp only [trQ, TM2.stepAux, kpack_update_left Q]
      exact ih _ _
  | peek k g q ih =>
      simp only [trQ, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [trQ, TM2.stepAux, kpack_update_left Q]
      exact ih _ _
  | load g q ih =>
      simp only [trQ, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [trQ, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [trQ, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [trQ, TM2.stepAux, labQ]
  | halt => simp only [trQ, TM2.stepAux, labQ]

variable (ia : Q.Γ Q.k₀ ≃ Bool) (oa : Q.Γ Q.k₁ ≃ Bool)

def copy1 : TM2.Stmt (KGam Q) (KLab Q) (KSta Q) :=
  .pop (Sum.inl Q.k₀) (fun v o => (v.1, o.map ia))
    (.branch (fun v => v.2.isSome)
      (.push (Sum.inr false) (fun v => v.2.getD false)
        (.push (Sum.inr true) (fun v => v.2.getD false) (.goto (fun _ => Sum.inr 0))))
      (.goto (fun _ => Sum.inr 1)))

def copy2 : TM2.Stmt (KGam Q) (KLab Q) (KSta Q) :=
  .pop (Sum.inr true) (fun v o => (v.1, o))
    (.branch (fun v => v.2.isSome)
      (.push (Sum.inl Q.k₀) (fun v => ia.symm (v.2.getD false)) (.goto (fun _ => Sum.inr 1)))
      (.goto (fun _ => Sum.inl Q.main)))

def app : TM2.Stmt (KGam Q) (KLab Q) (KSta Q) :=
  .pop (Sum.inr false) (fun v o => (v.1, o))
    (.branch (fun v => v.2.isSome)
      (.push (Sum.inl Q.k₁) (fun v => oa.symm (v.2.getD false)) (.goto (fun _ => Sum.inr 2)))
      .halt)

def kprog : KLab Q → TM2.Stmt (KGam Q) (KLab Q) (KSta Q)
  | .inl l => trQ Q (Q.m l)
  | .inr 0 => copy1 Q ia
  | .inr 1 => copy2 Q ia
  | .inr 2 => app Q oa

end KeepCore

namespace KeepCore
open Turing
variable (Q : FinTM2) (ia : Q.Γ Q.k₀ ≃ Bool) (oa : Q.Γ Q.k₁ ≃ Bool)

theorem step_copy1_cons (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k)) (A B : List Bool)
    (x : Q.Γ Q.k₀) (xs : List (Q.Γ Q.k₀)) (hS : S Q.k₀ = x :: xs) :
    TM2.step (kprog Q ia oa) ⟨some (Sum.inr 0), v, kpack Q S A B⟩
      = some ⟨some (Sum.inr 0), (v.1, some (ia x)),
          kpack Q (Function.update S Q.k₀ xs) (ia x :: A) (ia x :: B)⟩ := by
  simp only [kprog, copy1, TM2.step, TM2.stepAux, kpack, hS, Option.map_some,
    Option.isSome_some, Option.getD_some, cond_true, List.head?_cons, List.tail_cons,
    kpack_update_left, kpack_update_side, kpack_update_tmp]

theorem step_copy1_nil (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k)) (A B : List Bool)
    (hS : S Q.k₀ = []) :
    TM2.step (kprog Q ia oa) ⟨some (Sum.inr 0), v, kpack Q S A B⟩
      = some ⟨some (Sum.inr 1), (v.1, none), kpack Q S A B⟩ := by
  have hupd : Function.update S Q.k₀ ([] : List (Q.Γ Q.k₀)) = S := by
    rw [← hS]; exact Function.update_eq_self _ _
  conv_rhs => rw [← hupd]
  simp [kprog, copy1, TM2.step, TM2.stepAux, kpack, hS, kpack_update_left]

theorem step_copy2_cons (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k)) (A : List Bool)
    (y : Bool) (ys : List Bool) :
    TM2.step (kprog Q ia oa) ⟨some (Sum.inr 1), v, kpack Q S A (y :: ys)⟩
      = some ⟨some (Sum.inr 1), (v.1, some y),
          kpack Q (Function.update S Q.k₀ (ia.symm y :: S Q.k₀)) A ys⟩ := by
  simp only [kprog, copy2, TM2.step, TM2.stepAux, kpack, Option.isSome_some,
    Option.getD_some, cond_true, List.head?_cons, List.tail_cons,
    kpack_update_left, kpack_update_side, kpack_update_tmp]

theorem step_copy2_nil (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k)) (A : List Bool) :
    TM2.step (kprog Q ia oa) ⟨some (Sum.inr 1), v, kpack Q S A []⟩
      = some ⟨some (Sum.inl Q.main), (v.1, none), kpack Q S A []⟩ := by
  simp only [kprog, copy2, TM2.step, TM2.stepAux, kpack, List.head?_nil, Option.isSome_none,
    Bool.false_eq_true, cond_false]
  rw [show ([] : List Bool).tail = [] from rfl, kpack_update_tmp]

theorem step_app_cons (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k)) (B : List Bool)
    (z : Bool) (zs : List Bool) :
    TM2.step (kprog Q ia oa) ⟨some (Sum.inr 2), v, kpack Q S (z :: zs) B⟩
      = some ⟨some (Sum.inr 2), (v.1, some z),
          kpack Q (Function.update S Q.k₁ (oa.symm z :: S Q.k₁)) zs B⟩ := by
  simp only [kprog, app, TM2.step, TM2.stepAux, kpack, Option.isSome_some,
    Option.getD_some, cond_true, List.head?_cons, List.tail_cons,
    kpack_update_left, kpack_update_side, kpack_update_tmp]

theorem step_app_nil (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k)) (B : List Bool) :
    TM2.step (kprog Q ia oa) ⟨some (Sum.inr 2), v, kpack Q S [] B⟩
      = some ⟨none, (v.1, none), kpack Q S [] B⟩ := by
  simp only [kprog, app, TM2.step, TM2.stepAux, kpack, List.head?_nil, Option.isSome_none,
    Bool.false_eq_true, cond_false]
  rw [show ([] : List Bool).tail = [] from rfl, kpack_update_side]

end KeepCore

namespace KeepCore
open Turing
variable {Q : FinTM2} (ia : Q.Γ Q.k₀ ≃ Bool) (oa : Q.Γ Q.k₁ ≃ Bool)

def oneStep {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
    {M : Λ → TM2.Stmt Γ Λ σ} {c c' : TM2.Cfg Γ Λ σ}
    (h : TM2.step M c = some c') : EvalsToInTime (TM2.step M) c (some c') 1 :=
  ⟨⟨1, by rw [Function.iterate_one, QMCExit.flip_bind_step]; exact h⟩, le_rfl⟩

def copy1_trace : ∀ (xs : List (Q.Γ Q.k₀)) (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k))
    (A B : List Bool), S Q.k₀ = xs →
    EvalsToInTime (TM2.step (kprog Q ia oa)) ⟨some (Sum.inr 0), v, kpack Q S A B⟩
      (some ⟨some (Sum.inr 1), (v.1, none), kpack Q (Function.update S Q.k₀ [])
        ((xs.map ia).reverse ++ A) ((xs.map ia).reverse ++ B)⟩) (xs.length + 1)
  | [], v, S, A, B, hS => by
      have hupd : Function.update S Q.k₀ ([] : List (Q.Γ Q.k₀)) = S := by
        rw [← hS]; exact Function.update_eq_self _ _
      rw [hupd]
      exact oneStep (step_copy1_nil Q ia oa v S A B hS)
  | x :: xs, v, S, A, B, hS =>
      (QMCExit.EvalsToInTime.trans' (oneStep (step_copy1_cons Q ia oa v S A B x xs hS))
        (copy1_trace xs (v.1, some (ia x)) (Function.update S Q.k₀ xs) (ia x :: A) (ia x :: B)
          (by simp)))
      |> QMCExit.EvalsToInTime.congr_cfg rfl (by
          simp only [List.map_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append, Function.update_idem])
      |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

def copy2_trace : ∀ (ys : List Bool) (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k))
    (A : List Bool),
    EvalsToInTime (TM2.step (kprog Q ia oa)) ⟨some (Sum.inr 1), v, kpack Q S A ys⟩
      (some ⟨some (Sum.inl Q.main), (v.1, none),
        kpack Q (Function.update S Q.k₀ ((ys.map ia.symm).reverse ++ S Q.k₀)) A []⟩)
      (ys.length + 1)
  | [], v, S, A => by
      have hupd : Function.update S Q.k₀
          ((([] : List Bool).map ia.symm).reverse ++ S Q.k₀) = S := by simp
      rw [hupd]
      exact oneStep (step_copy2_nil Q ia oa v S A)
  | y :: ys, v, S, A =>
      (QMCExit.EvalsToInTime.trans' (oneStep (step_copy2_cons Q ia oa v S A y ys))
        (copy2_trace ys (v.1, some y) (Function.update S Q.k₀ (ia.symm y :: S Q.k₀)) A))
      |> QMCExit.EvalsToInTime.congr_cfg rfl (by
          simp only [List.map_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append, Function.update_idem, Function.update_self])
      |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

def app_trace : ∀ (zs : List Bool) (v : KSta Q) (S : (k : Q.K) → List (Q.Γ k))
    (B : List Bool),
    EvalsToInTime (TM2.step (kprog Q ia oa)) ⟨some (Sum.inr 2), v, kpack Q S zs B⟩
      (some ⟨none, (v.1, none),
        kpack Q (Function.update S Q.k₁ ((zs.map oa.symm).reverse ++ S Q.k₁)) [] B⟩)
      (zs.length + 1)
  | [], v, S, B => by
      have hupd : Function.update S Q.k₁
          ((([] : List Bool).map oa.symm).reverse ++ S Q.k₁) = S := by simp
      rw [hupd]
      exact oneStep (step_app_nil Q ia oa v S B)
  | z :: zs, v, S, B =>
      (QMCExit.EvalsToInTime.trans' (oneStep (step_app_cons Q ia oa v S B z zs))
        (app_trace zs (v.1, some z) (Function.update S Q.k₁ (oa.symm z :: S Q.k₁)) B))
      |> QMCExit.EvalsToInTime.congr_cfg rfl (by
          simp only [List.map_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append, Function.update_idem, Function.update_self])
      |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

def cfgQ (c : TM2.Cfg Q.Γ Q.Λ Q.σ) (b : Option Bool) (A B : List Bool) :
    TM2.Cfg (KGam Q) (KLab Q) (KSta Q) :=
  ⟨labQ Q c.l, (c.var, b), kpack Q c.stk A B⟩

theorem step_cfgQ (b : Option Bool) (A B : List Bool) {c c' : TM2.Cfg Q.Γ Q.Λ Q.σ}
    (h : Q.step c = some c') :
    TM2.step (kprog Q ia oa) (cfgQ c b A B) = some (cfgQ c' b A B) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (Q.m l) v S := (Option.some.inj h).symm
      subst hh
      simp only [cfgQ, labQ, kprog, TM2.step.eq_2, stepAux_trQ]

theorem iterate_cfgQ (b : Option Bool) (A B : List Bool) :
    ∀ (m : ℕ) (c c' : TM2.Cfg Q.Γ Q.Λ Q.σ),
      (flip bind Q.step)^[m] (some c) = some c' →
      (flip bind (TM2.step (kprog Q ia oa)))^[m] (some (cfgQ c b A B))
        = some (cfgQ c' b A B)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind Q.step) (some c) = Q.step c from rfl] at h
      cases hstep : Q.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step (kprog Q ia oa))) (some (cfgQ c b A B))
                = TM2.step (kprog Q ia oa) (cfgQ c b A B) from rfl,
              step_cfgQ ia oa b A B hstep]
          exact iterate_cfgQ b A B m d c' h

def phaseQ (A : List Bool) {l : List (Q.Γ Q.k₀)} {out : List (Q.Γ Q.k₁)} {N : ℕ}
    (h : TM2OutputsInTime Q l (some out) N) :
    EvalsToInTime (TM2.step (kprog Q ia oa))
      ⟨some (Sum.inl Q.main), (Q.initialState, none), kpack Q (QMCExit.initStacks Q l) A []⟩
      (some ⟨some (Sum.inr 2), (Q.initialState, none),
        kpack Q (QMCExit.haltStacks Q out) A []⟩) N := by
  have h1 := iterate_cfgQ ia oa (none : Option Bool) A [] h.steps
    (Turing.initList Q l) (Turing.haltList Q out) h.evals_in_steps
  exact ⟨⟨h.steps, h1⟩, h.steps_le_m⟩

end KeepCore

namespace KeepCore
open Turing
variable {Q : FinTM2}

noncomputable abbrev keepTM (Q : FinTM2) (ia : Q.Γ Q.k₀ ≃ Bool) (oa : Q.Γ Q.k₁ ≃ Bool) :
    FinTM2 where
  K := KKey Q
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := Sum.inl Q.k₀
  k₁ := Sum.inl Q.k₁
  Γ := KGam Q
  Λ := KLab Q
  main := Sum.inr 0
  ΛFin := inferInstance
  σ := KSta Q
  initialState := (Q.initialState, none)
  σFin := inferInstance
  Γk₀Fin := Q.Γk₀Fin
  m := kprog Q ia oa

variable (ia : Q.Γ Q.k₀ ≃ Bool) (oa : Q.Γ Q.k₁ ≃ Bool)

theorem kpack_initStacks (l : List (Q.Γ Q.k₀)) :
    kpack Q (QMCExit.initStacks Q l) [] [] = QMCExit.initStacks (keepTM Q ia oa) l := by
  funext k
  rcases k with a | (_ | _)
  · show QMCExit.initStacks Q l a = QMCExit.initStacks (keepTM Q ia oa) l (Sum.inl a)
    unfold QMCExit.initStacks
    by_cases h : a = Q.k₀
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (show (Sum.inl a : KKey Q) ≠ (keepTM Q ia oa).k₀ from
        fun e => h (Sum.inl.inj e))]
  · show ([] : List Bool) = QMCExit.initStacks (keepTM Q ia oa) l (Sum.inr false)
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr false : KKey Q) ≠ (keepTM Q ia oa).k₀ from by intro e; cases e)]
  · show ([] : List Bool) = QMCExit.initStacks (keepTM Q ia oa) l (Sum.inr true)
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr true : KKey Q) ≠ (keepTM Q ia oa).k₀ from by intro e; cases e)]

theorem kpack_haltStacks (u : List (Q.Γ Q.k₁)) :
    kpack Q (QMCExit.haltStacks Q u) [] [] = QMCExit.haltStacks (keepTM Q ia oa) u := by
  funext k
  rcases k with a | (_ | _)
  · show QMCExit.haltStacks Q u a = QMCExit.haltStacks (keepTM Q ia oa) u (Sum.inl a)
    unfold QMCExit.haltStacks
    by_cases h : a = Q.k₁
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (show (Sum.inl a : KKey Q) ≠ (keepTM Q ia oa).k₁ from
        fun e => h (Sum.inl.inj e))]
  · show ([] : List Bool) = QMCExit.haltStacks (keepTM Q ia oa) u (Sum.inr false)
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inr false : KKey Q) ≠ (keepTM Q ia oa).k₁ from by intro e; cases e)]
  · show ([] : List Bool) = QMCExit.haltStacks (keepTM Q ia oa) u (Sum.inr true)
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inr true : KKey Q) ≠ (keepTM Q ia oa).k₁ from by intro e; cases e)]

theorem update_initStacks_nil (l : List (Q.Γ Q.k₀)) :
    Function.update (QMCExit.initStacks Q l) Q.k₀ [] = fun _ => [] := by
  rw [CompCore.initStacks_eq_update, Function.update_idem]
  funext k
  by_cases h : k = Q.k₀
  · subst h; simp
  · rw [Function.update_of_ne h]

theorem update_haltStacks (u v : List (Q.Γ Q.k₁)) :
    Function.update (QMCExit.haltStacks Q u) Q.k₁ v = QMCExit.haltStacks Q v := by
  rw [CompCore.haltStacks_eq_update, CompCore.haltStacks_eq_update, Function.update_idem]

noncomputable def keep_run {l : List (Q.Γ Q.k₀)} {out : List (Q.Γ Q.k₁)} {N : ℕ}
    (h : TM2OutputsInTime Q l (some out) N) :
    TM2OutputsInTime (keepTM Q ia oa) l
      (some (l.map (fun x => oa.symm (ia x)) ++ out))
      ((l.length + 1) + (N + ((l.length + 1) + (l.length + 1)))) := by
  set R := (l.map ia).reverse with hR
  have hS0 : QMCExit.initStacks Q l Q.k₀ = l := by simp [QMCExit.initStacks]
  have h1 := copy1_trace ia oa l (Q.initialState, none) (QMCExit.initStacks Q l) [] [] hS0
  simp only [List.append_nil, update_initStacks_nil] at h1
  have h2 := copy2_trace ia oa R (Q.initialState, none) (fun _ => []) R
  have e2 : Function.update (fun k => ([] : List (Q.Γ k))) Q.k₀
      ((R.map ia.symm).reverse ++ ([] : List (Q.Γ Q.k₀))) = QMCExit.initStacks Q l := by
    rw [CompCore.initStacks_eq_update, hR]
    simp [List.map_reverse, List.map_map, Function.comp_def]
  rw [e2] at h2
  have h3 := phaseQ ia oa R h
  have h4 := app_trace ia oa R (Q.initialState, none) (QMCExit.haltStacks Q out) []
  have e4 : Function.update (QMCExit.haltStacks Q out) Q.k₁
      ((R.map oa.symm).reverse ++ QMCExit.haltStacks Q out Q.k₁) =
      QMCExit.haltStacks Q (l.map (fun x => oa.symm (ia x)) ++ out) := by
    rw [update_haltStacks, QMCExit.haltStacks_k1, hR]
    simp [List.map_reverse, List.map_map, Function.comp_def]
  rw [e4] at h4
  have hchain := QMCExit.EvalsToInTime.trans'
    (QMCExit.EvalsToInTime.trans' (QMCExit.EvalsToInTime.trans' h1 h2) h3) h4
  have hstart : Turing.initList (keepTM Q ia oa) l =
      (⟨some (Sum.inr 0), (Q.initialState, none), kpack Q (QMCExit.initStacks Q l) [] []⟩ :
        TM2.Cfg (KGam Q) (KLab Q) (KSta Q)) := by
    rw [kpack_initStacks]; rfl
  have hend : (⟨none, (Q.initialState, none),
      kpack Q (QMCExit.haltStacks Q (l.map (fun x => oa.symm (ia x)) ++ out)) [] []⟩ :
        TM2.Cfg (KGam Q) (KLab Q) (KSta Q)) =
      Turing.haltList (keepTM Q ia oa) (l.map (fun x => oa.symm (ia x)) ++ out) := by
    rw [kpack_haltStacks]; rfl
  rw [← hstart, hend, hR, List.length_reverse, List.length_map] at hchain
  exact QMCExit.tm2OutputsInTime_of_cfg hchain rfl

end KeepCore

namespace FPAux
open Turing NOFSeparation750.CodedGIP

theorem outputsWithin_mono {P : FiniteProgram} {i o : List Bool} {t t' : ℕ}
    (h : OutputsWithin P i o t) (ht : t ≤ t') : OutputsWithin P i o t' :=
  let ⟨h⟩ := h; ⟨QMCExit.tm2OutputsInTime_mono h ht⟩

theorem fp_comp (A B : FiniteProgram) (f g : List Bool → List Bool) (tA tB : List Bool → ℕ)
    (hA : ∀ L, OutputsWithin A L (f L) (tA L))
    (hB : ∀ L, OutputsWithin B (f L) (g L) (tB L)) :
    ∃ P : FiniteProgram, ∀ L,
      OutputsWithin P L (g L) (tB L + ((f L).length + 1 + ((f L).length + 1 + tA L))) := by
  classical
  let oa := A.machine.outputAlphabet
  let ia := B.machine.inputAlphabet
  refine ⟨⟨⟨CompCore.compTM (tm₁ := A.machine.tm) (tm₂ := B.machine.tm) oa ia,
    A.machine.inputAlphabet, B.machine.outputAlphabet⟩, ?_⟩, ?_⟩
  · intro k
    rcases k with a | (b | u)
    · exact A.finiteAlphabet a
    · exact B.finiteAlphabet b
    · exact B.finiteAlphabet _
  · intro L
    obtain ⟨h1⟩ := hA L
    obtain ⟨h2⟩ := hB L
    have h2' : TM2OutputsInTime B.machine.tm
        (((f L).map oa.symm).map (fun x => ia.invFun (oa x))) (some ((g L).map B.machine.outputAlphabet.symm)) (tB L) := by
      have : ((f L).map oa.symm).map (fun x => ia.invFun (oa x)) = (f L).map ia.symm := by
        simp [List.map_map, Function.comp_def]
      rw [this]; exact h2
    have := CompCore.tm2OutputsInTime_comp (tm₁ := A.machine.tm) (tm₂ := B.machine.tm) oa ia h1 h2'
    refine ⟨?_⟩
    simpa [List.length_map] using this


theorem fp_keep (Qp : FiniteProgram) (h : List Bool → List Bool) (t : List Bool → ℕ)
    (hQ : ∀ L, OutputsWithin Qp L (h L) (t L)) :
    ∃ P : FiniteProgram, ∀ L, OutputsWithin P L (L ++ h L) (t L + 3 * (L.length + 1)) := by
  classical
  let ia := Qp.machine.inputAlphabet
  let oa := Qp.machine.outputAlphabet
  refine ⟨⟨⟨KeepCore.keepTM Qp.machine.tm ia oa, ia, oa⟩, ?_⟩, ?_⟩
  · intro k
    rcases k with a | b
    · exact Qp.finiteAlphabet a
    · exact (inferInstance : Finite Bool)
  · intro L
    obtain ⟨hq⟩ := hQ L
    have := KeepCore.keep_run ia oa hq
    refine ⟨?_⟩
    have e : (L.map ia.symm).map (fun x => oa.symm (ia x)) ++ (h L).map oa.symm
        = (L ++ h L).map oa.symm := by
      simp [List.map_map, Function.comp_def]
    rw [e] at this
    refine QMCExit.tm2OutputsInTime_mono this ?_
    simp only [List.length_map]; omega

/-- The sandwich used for the coded-GIP evaluator. -/
theorem fp_sandwich (A G B : FiniteProgram) (f1 g f2 : List Bool → List Bool)
    (tA tG tB : List Bool → ℕ)
    (hA : ∀ L, OutputsWithin A L (f1 L) (tA L))
    (hG : ∀ L, OutputsWithin G (f1 L) (g L) (tG L))
    (hB : ∀ L, OutputsWithin B (L ++ g L) (f2 (L ++ g L)) (tB L)) :
    ∃ P : FiniteProgram, ∀ L, OutputsWithin P L (f2 (L ++ g L))
      (tA L + tG L + tB L + 7 * (L.length + (f1 L).length + (g L).length + 1)) := by
  obtain ⟨P1, hP1⟩ := fp_comp A G f1 g tA tG hA hG
  obtain ⟨P2, hP2⟩ := fp_keep P1 g _ hP1
  obtain ⟨P3, hP3⟩ := fp_comp P2 B (fun L => L ++ g L) (fun L => f2 (L ++ g L)) _ tB hP2 hB
  refine ⟨P3, fun L => outputsWithin_mono (hP3 L) ?_⟩
  simp only [List.length_append]
  omega
end FPAux



open Turing.MultiTapeTM

set_option linter.unusedSectionVars false
namespace UPTAux
open NOFSeparation750.CodedGIP

/-- capped powers: `min (s^j) (n+1)` with `s = 2^a`. -/
def powCap (a n j : ℕ) : ℕ := (fun st => min (st * 2 ^ a) (n + 1))^[j] 1

theorem powCap_poly (a : ℕ) :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => powCap a p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
  unfold powCap
  refine ComputableTidilyInPolyTime.iterateWithInput_of_bounded_growth
    (step := fun (p : ℕ × ℕ) (st : ℕ) => min (st * 2 ^ a) (p.1 + 1))
    (count := fun p => p.2) (init := fun _ => 1) (by fun_prop) (by fun_prop) (by fun_prop)
    (growth := fun p => p.1 + 1) ⟨?_, ?_⟩
  · exact PolyBounded.of_forall_le 1 1 (fun p => by
      have := length_le_encPair_left encUnary encUnary p
      simp only [encUnary_apply, List.length_replicate] at this ⊢
      nlinarith)
  · intro p st
    simp only [encUnary_apply, List.length_replicate]
    omega

def lvl (k a n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter (fun j => decide (envelope k a 0 * powCap a n j ≤ n))).length - 1

theorem lvl_poly (k a : ℕ) : ComputableTidilyInPolyTime (lvl k a) encUnary encUnary := by
  unfold lvl
  have hp := powCap_poly a
  have htest : ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => decide (envelope k a 0 * powCap a p.1 p.2 ≤ p.1))
      (encPair encUnary encUnary) encBool := by
    apply ComputableTidilyInPolyTime.unary_le'
    · exact ComputableTidilyInPolyTime.unary_mul.comp ((ComputableTidilyInPolyTime.const _).prod hp)
    · exact ComputableTidilyInPolyTime.fst _ _
  have hf := ComputableTidilyInPolyTime.filterWithInput
    (test := fun (n j : ℕ) => decide (envelope k a 0 * powCap a n j ≤ n))
    (list := fun n => List.range (n + 1)) (by fun_prop) htest
  have hl := (ComputableTidilyInPolyTime.length_list encUnary).comp hf
  exact ComputableTidilyInPolyTime.unary_sub.comp (hl.prod (ComputableTidilyInPolyTime.const 1))

theorem powCap_eq (a n : ℕ) : ∀ j, powCap a n j = min ((2 ^ a) ^ j) (n + 1)
  | 0 => by simp [powCap]
  | j + 1 => by
      have ih := powCap_eq a n j
      unfold powCap at ih ⊢
      rw [Function.iterate_succ_apply', ih, pow_succ]
      have hs : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      rcases le_total ((2 ^ a) ^ j) (n + 1) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]
        have : n + 1 ≤ (2 ^ a) ^ j * 2 ^ a := h.trans (Nat.le_mul_of_pos_right _ hs)
        rw [min_eq_right this, min_eq_right (le_trans le_rfl (Nat.le_mul_of_pos_right _ hs))]

theorem envelope_eq (k a j : ℕ) : envelope k a j = envelope k a 0 * (2 ^ a) ^ j := by
  unfold envelope codeLength; ring

theorem envelope_mono (k a : ℕ) : Monotone (envelope k a) := by
  intro i j hij
  rw [envelope_eq k a i, envelope_eq k a j]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Nat.one_le_two_pow hij)

theorem envelope0_pos (k a : ℕ) (ha : 1 ≤ a) : 1 ≤ envelope k a 0 := by
  unfold envelope codeLength copies
  have h1 : 2 ^ a < 4 ^ a := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have : 1 ≤ 4 ^ a - 2 ^ a := by omega
  have h2 : 1 ≤ 2 * a := by omega
  simp only [pow_zero, mul_one]
  exact Nat.one_le_iff_ne_zero.mpr (by positivity)

theorem lvl_eq (k a n : ℕ) (ha : 1 ≤ a) : lvl k a n = paddingLevel k a n := by
  classical
  have hE := envelope0_pos k a ha
  have htest : ∀ j, decide (envelope k a 0 * powCap a n j ≤ n) = decide (envelope k a j ≤ n) := by
    intro j
    rw [powCap_eq, envelope_eq k a j]
    congr 1
    apply propext
    rcases le_total ((2 ^ a) ^ j) (n + 1) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h]
      constructor
      · intro h'; nlinarith
      · intro h'; nlinarith
  unfold lvl paddingLevel
  simp_rw [htest]
  set S := (Finset.range (n + 1)).filter (fun j => envelope k a j ≤ n) with hS
  have hlen : ((List.range (n + 1)).filter (fun j => decide (envelope k a j ≤ n))).length = S.card := by
    have hnd : ((List.range (n + 1)).filter (fun j => decide (envelope k a j ≤ n))).Nodup :=
      (List.nodup_range).filter _
    rw [← List.toFinset_card_of_nodup hnd, hS]
    congr 1
    ext j; simp
  rw [hlen]
  by_cases hne : S.Nonempty
  · obtain ⟨M, hM⟩ : ∃ M : ℕ, S.max = (M : WithBot ℕ) := ⟨S.max' hne, (Finset.coe_max' hne).symm⟩
    have hMmem : M ∈ S := Finset.mem_of_max hM
    have hSeq : S = Finset.range (M + 1) := by
      ext j
      simp only [Finset.mem_range]
      constructor
      · intro hj; exact Nat.lt_succ_of_le (Finset.le_max_of_eq hj hM)
      · intro hj
        rw [hS, Finset.mem_filter] at hMmem ⊢
        rw [Finset.mem_range] at hMmem ⊢
        exact ⟨by omega, (envelope_mono k a (by omega : j ≤ M)).trans hMmem.2⟩
    rw [hM, hSeq, Finset.card_range]
    rfl
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; rfl


section field
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {b : ℕ} (codec : (Fin b → Bool) ≃ F)

def encF : F ↪ List Bool := ⟨fun f => List.ofFn (codec.symm f), by
  intro x y h
  exact codec.symm.injective (List.ofFn_injective h)⟩

theorem encF_length (f : F) : (encF codec f).length = b := by
  show (List.ofFn (codec.symm f)).length = b; simp

def dot (u v : List F) : F := ((u.zip v).map (fun p => p.1 * p.2)).foldl (· + ·) 0

theorem dot_poly : ComputableTidilyInPolyTime (fun p : List F × List F => dot p.1 p.2)
    (encPair (encList (encF codec)) (encList (encF codec))) (encF codec) := by
  unfold dot
  have hz := ComputableTidilyInPolyTime.zip (encF codec) (encF codec)
  have hm : ComputableTidilyInPolyTime (fun q : F × F => q.1 * q.2)
      (encPair (encF codec) (encF codec)) (encF codec) := ComputableTidilyInPolyTime.of_finite _
  have hmap := (ComputableTidilyInPolyTime.map hm).comp hz
  refine ComputableTidilyInPolyTime.foldl_of_bounded_growth (encA := encF codec)
    (encL := encList (encF codec)) hmap
    (ComputableTidilyInPolyTime.const 0) (ComputableTidilyInPolyTime.of_finite _) (growth := 0) ?_
  intro st v; simp [encF_length]

def col (M : List (List F)) (t : ℕ) : List F := M.map (fun row => row.getD t 0)

theorem col_poly : ComputableTidilyInPolyTime (fun p : List (List F) × ℕ => col p.1 p.2)
    (encPair (encList (encList (encF codec))) encUnary) (encList (encF codec)) := by
  unfold col
  refine ComputableTidilyInPolyTime.mapWithInput (f := fun (p : List (List F) × ℕ) (row : List F) => row.getD p.2 0)
    (ComputableTidilyInPolyTime.fst _ _) ?_
  have := ComputableTidilyInPolyTime.listGetD (encA := encF codec) (encL := encList (encF codec)) (0 : F)
  exact this.comp (((ComputableTidilyInPolyTime.snd _ _)).prod
    ((ComputableTidilyInPolyTime.snd _ _).comp (ComputableTidilyInPolyTime.fst _ _)))

theorem foldlF_poly {γ : Type} {encIn : γ ↪ List Bool} (op : F → F → F) (init : F)
    {list : γ → List F} (h : ComputableTidilyInPolyTime list encIn (encList (encF codec))) :
    ComputableTidilyInPolyTime (fun x => (list x).foldl op init) encIn (encF codec) := by
  refine ComputableTidilyInPolyTime.foldl_of_bounded_growth (encA := encF codec)
    (encL := encList (encF codec)) h (ComputableTidilyInPolyTime.const init)
    (ComputableTidilyInPolyTime.of_finite _) (growth := 0) ?_
  intro st v; simp [encF_length]

abbrev Data (F : Type) := ℕ × (List (List F) × (List (List F) × (List (List (List F)) × List (List F))))

def encData : Data F ↪ List Bool :=
  encPair encUnary (encPair (encList (encList (encF codec)))
    (encPair (encList (encList (encF codec)))
      (encPair (encList (encList (encList (encF codec)))) (encList (encList (encF codec))))))

def inner (d : Data F) (t h i : ℕ) : F := dot ((d.2.2.2.1.getD i []).getD h []) (col d.2.1 t)

def lhs (k ℓ : ℕ) (d : Data F) (t : ℕ) : F :=
  ((List.range ℓ).map (fun h => ((List.range k).map (fun i => inner d t h i)).foldl (· * ·) 1)).foldl
    (· + ·) 0

def rhs (k : ℕ) (d : Data F) (t : ℕ) : F :=
  ((List.range k).map (fun i => dot (d.2.2.2.2.getD i []) (col d.2.2.1 t))).foldl (· + ·) 0

def check (k ℓ : ℕ) (d : Data F) : Bool := (List.range d.1).all (fun t => lhs k ℓ d t == rhs k d t)

theorem check_poly (k ℓ : ℕ) :
    ComputableTidilyInPolyTime (check (F := F) k ℓ) (encData codec) encBool := by
  have hd := dot_poly codec
  have hc := col_poly codec
  -- projections from Data × ℕ
  let eD := encData codec
  have hG : ComputableTidilyInPolyTime (fun p : Data F × ℕ => p.1.2.1) (encPair eD encUnary)
      (encList (encList (encF codec))) := by
    unfold eD encData; fun_prop
  have hH : ComputableTidilyInPolyTime (fun p : Data F × ℕ => p.1.2.2.1) (encPair eD encUnary)
      (encList (encList (encF codec))) := by
    unfold eD encData; fun_prop
  have hU : ComputableTidilyInPolyTime (fun p : Data F × ℕ => p.1.2.2.2.1) (encPair eD encUnary)
      (encList (encList (encList (encF codec)))) := by
    unfold eD encData; fun_prop
  have hV : ComputableTidilyInPolyTime (fun p : Data F × ℕ => p.1.2.2.2.2) (encPair eD encUnary)
      (encList (encList (encF codec))) := by
    unfold eD encData; fun_prop
  have hT : ComputableTidilyInPolyTime (fun p : Data F × ℕ => p.2) (encPair eD encUnary) encUnary :=
    ComputableTidilyInPolyTime.snd _ _
  have hcolG : ComputableTidilyInPolyTime (fun p : Data F × ℕ => col p.1.2.1 p.2)
      (encPair eD encUnary) (encList (encF codec)) := hc.comp (hG.prod hT)
  have hcolH : ComputableTidilyInPolyTime (fun p : Data F × ℕ => col p.1.2.2.1 p.2)
      (encPair eD encUnary) (encList (encF codec)) := hc.comp (hH.prod hT)
  have hgetU : ∀ i h : ℕ, ComputableTidilyInPolyTime (fun p : Data F × ℕ => (p.1.2.2.2.1.getD i []).getD h [])
      (encPair eD encUnary) (encList (encF codec)) := by
    intro i h
    have g1 := (ComputableTidilyInPolyTime.listGetD (encA := encList (encList (encF codec)))
      (encL := encList (encList (encList (encF codec)))) ([] : List (List F))).comp
      (hU.prod (ComputableTidilyInPolyTime.const i))
    exact (ComputableTidilyInPolyTime.listGetD (encA := encList (encF codec))
      (encL := encList (encList (encF codec))) ([] : List F)).comp
      (g1.prod (ComputableTidilyInPolyTime.const h))
  have hgetV : ∀ i : ℕ, ComputableTidilyInPolyTime (fun p : Data F × ℕ => p.1.2.2.2.2.getD i [])
      (encPair eD encUnary) (encList (encF codec)) := by
    intro i
    exact (ComputableTidilyInPolyTime.listGetD (encA := encList (encF codec))
      (encL := encList (encList (encF codec))) ([] : List F)).comp
      (hV.prod (ComputableTidilyInPolyTime.const i))
  have hinner : ∀ h i : ℕ, ComputableTidilyInPolyTime (fun p : Data F × ℕ => inner p.1 p.2 h i)
      (encPair eD encUnary) (encF codec) := fun h i => hd.comp ((hgetU i h).prod hcolG)
  have hprodh : ∀ h : ℕ, ComputableTidilyInPolyTime
      (fun p : Data F × ℕ => ((List.range k).map (fun i => inner p.1 p.2 h i)).foldl (· * ·) 1)
      (encPair eD encUnary) (encF codec) := fun h =>
    foldlF_poly codec _ _ (ComputableTidilyInPolyTime.mapConst (List.range k)
      (f := fun (p : Data F × ℕ) (i : ℕ) => inner p.1 p.2 h i) (fun i _ => hinner h i))
  have hlhs : ComputableTidilyInPolyTime (fun p : Data F × ℕ => lhs k ℓ p.1 p.2)
      (encPair eD encUnary) (encF codec) :=
    foldlF_poly codec _ _ (ComputableTidilyInPolyTime.mapConst (List.range ℓ)
      (f := fun (p : Data F × ℕ) (h : ℕ) => ((List.range k).map (fun i => inner p.1 p.2 h i)).foldl (· * ·) 1)
      (fun h _ => hprodh h))
  have hrhs : ComputableTidilyInPolyTime (fun p : Data F × ℕ => rhs k p.1 p.2)
      (encPair eD encUnary) (encF codec) :=
    foldlF_poly codec _ _ (ComputableTidilyInPolyTime.mapConst (List.range k)
      (f := fun (p : Data F × ℕ) (i : ℕ) => dot (p.1.2.2.2.2.getD i []) (col p.1.2.2.1 p.2))
      (fun i _ => hd.comp ((hgetV i).prod hcolH)))
  have htest : ComputableTidilyInPolyTime (fun p : Data F × ℕ => lhs k ℓ p.1 p.2 == rhs k p.1 p.2)
      (encPair eD encUnary) encBool := ComputableTidilyInPolyTime.beq hlhs hrhs
  have hr : ComputableTidilyInPolyTime (fun d : Data F => List.range d.1) eD (encList encUnary) := by
    unfold eD encData; fun_prop
  exact ComputableTidilyInPolyTime.allWithInput (test := fun (d : Data F) (t : ℕ) => lhs k ℓ d t == rhs k d t) hr htest

noncomputable def decF (w : List Bool) : F :=
  ((Finset.univ.toList : List F).find?
    (fun f => List.ofFn (codec.symm f) == (w ++ List.replicate b false).take b)).getD 0

theorem decF_eq (w : List Bool) : decF codec w = codec (fun t => w.getD t false) := by
  unfold decF
  have hpad : (w ++ List.replicate b false).take b = List.ofFn (fun t : Fin b => w.getD t false) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_take, List.getElem_ofFn]
      rw [List.getD_eq_getElem?_getD]
      by_cases hi : i < w.length
      · rw [List.getElem_append_left hi, List.getElem?_eq_getElem hi]; rfl
      · rw [List.getElem_append_right (by omega), List.getElem?_eq_none (by omega)]
        simp
  rw [hpad]
  have hfind : (Finset.univ.toList : List F).find?
      (fun f => List.ofFn (codec.symm f) == List.ofFn (fun t : Fin b => w.getD t false)) =
      some (codec (fun t => w.getD t false)) := by
    set g : Fin b → Bool := fun t => w.getD t false
    have hp : ∀ f : F, (List.ofFn (codec.symm f) == List.ofFn g) = true ↔ f = codec g := by
      intro f
      rw [beq_iff_eq]
      constructor
      · intro h; have := List.ofFn_injective h; rw [← this]; simp
      · intro h; rw [h]; simp
    rw [List.find?_eq_some_iff_append]
    refine ⟨(hp _).mpr rfl, ?_⟩
    obtain ⟨as, bs, hab⟩ := List.append_of_mem (Finset.mem_toList.mpr (Finset.mem_univ (codec g)))
    refine ⟨as, bs, hab, fun a ha => ?_⟩
    rw [Bool.not_eq_true']
    by_contra hpa
    have := (hp a).mp (by simpa using hpa)
    subst this
    have hnd := Finset.nodup_toList (Finset.univ : Finset F)
    rw [hab] at hnd
    exact (List.nodup_append.mp hnd).2.2 _ ha _ (List.mem_cons_self) rfl
  rw [hfind]; rfl

theorem decF_poly : ComputableTidilyInPolyTime (decF codec) encBits (encF codec) := by
  unfold decF
  have h1 : ComputableTidilyInPolyTime (fun f : F => List.ofFn (codec.symm f)) (encF codec) encBits :=
    ComputableTidilyInPolyTime.of_finite _
  have hpad : ComputableTidilyInPolyTime (fun w : List Bool => (w ++ List.replicate b false).take b)
      encBits encBits := by fun_prop
  have hlist : ComputableTidilyInPolyTime (fun _ : List Bool => (Finset.univ.toList : List F))
      encBits (encList (encF codec)) := ComputableTidilyInPolyTime.const _
  have htest : ComputableTidilyInPolyTime
      (fun p : List Bool × F => List.ofFn (codec.symm p.2) == (p.1 ++ List.replicate b false).take b)
      (encPair encBits (encF codec)) encBool :=
    ComputableTidilyInPolyTime.beq (h1.comp (ComputableTidilyInPolyTime.snd _ _))
      (hpad.comp (ComputableTidilyInPolyTime.fst _ _))
  have hfind := ComputableTidilyInPolyTime.findWithInput
    (test := fun (w : List Bool) (f : F) => List.ofFn (codec.symm f) == (w ++ List.replicate b false).take b)
    hlist htest
  exact ComputableTidilyInPolyTime.optionGetDWithInput hfind (ComputableTidilyInPolyTime.const _)

end field


/-- the generator input: unary padding level of the leading unary length. -/
def f1 (k a : ℕ) (L : List Bool) : List Bool := List.replicate (lvl k a (L.idxOf false)) true ++ [false]

theorem f1_poly (k a : ℕ) : ComputableTidilyInPolyTime (f1 k a) encBits encBits := by
  unfold f1
  have hl := lvl_poly k a
  have hn : ComputableTidilyInPolyTime (fun L : List Bool => L.idxOf false) encBits encUnary := by fun_prop
  have h2 := hl.comp hn
  fun_prop

section parse
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] (k a : ℕ) (codec : (Fin (2 * a) → Bool) ≃ F)

noncomputable def fieldRow (w : List Bool) (cnt : ℕ) : List F :=
  (List.range cnt).map (fun t => decF codec ((w.drop (t * (2 * a))).take (2 * a)))

theorem fieldRow_poly : ComputableTidilyInPolyTime (fun p : List Bool × ℕ => fieldRow a codec p.1 p.2)
    (encPair encBits encUnary) (encList (encF codec)) := by
  unfold fieldRow
  have hdec := decF_poly codec
  refine ComputableTidilyInPolyTime.mapWithInput
    (f := fun (p : List Bool × ℕ) (t : ℕ) => decF codec ((p.1.drop (t * (2 * a))).take (2 * a)))
    (by fun_prop) ?_
  have : ComputableTidilyInPolyTime (fun q : (List Bool × ℕ) × ℕ => (q.1.1.drop (q.2 * (2 * a))).take (2 * a))
      (encPair (encPair encBits encUnary) encUnary) encBits := by fun_prop
  exact hdec.comp this

def nOf (L : List Bool) : ℕ := L.idxOf false
def rOf (L : List Bool) : ℕ := (4 ^ a - 2 ^ a) * powCap a (nOf L) (lvl k a (nOf L))
def bodyOf (L : List Bool) : List Bool := L.drop (nOf L + 1)
def genOf (L : List Bool) : List Bool := (bodyOf L).drop (k * nOf L)
def blkOf (L : List Bool) (i : ℕ) : List Bool := ((bodyOf L).drop (i * nOf L)).take (nOf L)
def mOf (L : List Bool) : ℕ := (genOf k L).idxOf false
def gROf (L : List Bool) : List Bool := (genOf k L).drop (mOf k L + 1)
def g2Of (L : List Bool) : List Bool := (gROf k L).drop (mOf k L * (rOf k a L * (2 * a)))
def mtOf (L : List Bool) : ℕ := (g2Of k a L).idxOf false
def hROf (L : List Bool) : List Bool := (g2Of k a L).drop (mtOf k a L + 1)

noncomputable def parse (L : List Bool) : Data F :=
  (rOf k a L,
   (List.range (mOf k L)).map (fun s => fieldRow a codec ((gROf k L).drop (s * (rOf k a L * (2 * a)))) (rOf k a L)),
   (List.range (mtOf k a L)).map (fun s => fieldRow a codec ((hROf k a L).drop (s * (rOf k a L * (2 * a)))) (rOf k a L)),
   (List.range k).map (fun i => (List.range (copies k)).map (fun h =>
      fieldRow a codec ((blkOf L i).drop (h * mOf k L * (2 * a))) (mOf k L))),
   (List.range k).map (fun i => fieldRow a codec ((blkOf L i).drop (copies k * mOf k L * (2 * a))) (mtOf k a L)))

noncomputable def f2 (L : List Bool) : List Bool :=
  [decide (envelope k a 0 ≤ nOf L) && check k (copies k) (parse k a codec L)]

section polys
variable {k a}
local notation "PT" => ComputableTidilyInPolyTime

theorem nOf_poly : PT (fun L : List Bool => nOf L) encBits encUnary := by unfold nOf; fun_prop

theorem rOf_poly : PT (fun L : List Bool => rOf k a L) encBits encUnary := by
  unfold rOf
  have h1 := (lvl_poly k a).comp nOf_poly
  have h2 := (powCap_poly a).comp (nOf_poly.prod h1)
  exact ComputableTidilyInPolyTime.unary_mul.comp ((ComputableTidilyInPolyTime.const _).prod h2)

theorem bodyOf_poly : PT (fun L : List Bool => bodyOf L) encBits encBits := by
  unfold bodyOf; have := nOf_poly; fun_prop

theorem genOf_poly : PT (fun L : List Bool => genOf k L) encBits encBits := by
  unfold genOf; have := nOf_poly; have := bodyOf_poly; fun_prop

theorem blkOf_poly (i : ℕ) : PT (fun L : List Bool => blkOf L i) encBits encBits := by
  unfold blkOf; have := nOf_poly; have := bodyOf_poly; fun_prop

theorem mOf_poly : PT (fun L : List Bool => mOf k L) encBits encUnary := by
  unfold mOf; have := genOf_poly (k := k); fun_prop

theorem gROf_poly : PT (fun L : List Bool => gROf k L) encBits encBits := by
  unfold gROf; have := genOf_poly (k := k); have := mOf_poly (k := k); fun_prop

theorem g2Of_poly : PT (fun L : List Bool => g2Of k a L) encBits encBits := by
  unfold g2Of; have := gROf_poly (k := k); have := mOf_poly (k := k); have := rOf_poly (k := k) (a := a)
  fun_prop

theorem mtOf_poly : PT (fun L : List Bool => mtOf k a L) encBits encUnary := by
  unfold mtOf; have := g2Of_poly (k := k) (a := a); fun_prop

theorem hROf_poly : PT (fun L : List Bool => hROf k a L) encBits encBits := by
  unfold hROf; have := g2Of_poly (k := k) (a := a); have := mtOf_poly (k := k) (a := a); fun_prop

theorem compPT {α β γ : Type} {eα : α ↪ List Bool} {eβ : β ↪ List Bool} {eγ : γ ↪ List Bool}
    {f : β → γ} {g : α → β} (hf : PT f eβ eγ) (hg : PT g eα eβ) : PT (fun x => f (g x)) eα eγ :=
  hf.comp hg

attribute [local irreducible] fieldRow decF in
theorem parse_poly : PT (parse k a codec) encBits (encData codec) := by
  unfold parse encData
  have hfr := fieldRow_poly a codec
  have hr := rOf_poly (k := k) (a := a)
  have hm := mOf_poly (k := k)
  have hmt := mtOf_poly (k := k) (a := a)
  have hgR := gROf_poly (k := k)
  have hhR := hROf_poly (k := k) (a := a)
  -- G
  have hGf : PT (fun p : List Bool × ℕ =>
      fieldRow a codec ((gROf k p.1).drop (p.2 * (rOf k a p.1 * (2 * a)))) (rOf k a p.1))
      (encPair encBits encUnary) (encList (encF codec)) := by
    have h1 : PT (fun p : List Bool × ℕ => (gROf k p.1).drop (p.2 * (rOf k a p.1 * (2 * a))))
        (encPair encBits encUnary) encBits := by
      have := hgR.comp (ComputableTidilyInPolyTime.fst encBits encUnary)
      have := hr.comp (ComputableTidilyInPolyTime.fst encBits encUnary)
      fun_prop
    exact compPT (f := fun p : List Bool × ℕ => fieldRow a codec p.1 p.2) hfr
      (h1.prod (hr.comp (ComputableTidilyInPolyTime.fst _ _)))
  have hG := ComputableTidilyInPolyTime.mapWithInput
    (f := fun (L : List Bool) (s : ℕ) =>
      fieldRow a codec ((gROf k L).drop (s * (rOf k a L * (2 * a)))) (rOf k a L))
    (ComputableTidilyInPolyTime.range.comp hm) hGf
  -- H
  have hHf : PT (fun p : List Bool × ℕ =>
      fieldRow a codec ((hROf k a p.1).drop (p.2 * (rOf k a p.1 * (2 * a)))) (rOf k a p.1))
      (encPair encBits encUnary) (encList (encF codec)) := by
    have h1 : PT (fun p : List Bool × ℕ => (hROf k a p.1).drop (p.2 * (rOf k a p.1 * (2 * a))))
        (encPair encBits encUnary) encBits := by
      have := hhR.comp (ComputableTidilyInPolyTime.fst encBits encUnary)
      have := hr.comp (ComputableTidilyInPolyTime.fst encBits encUnary)
      fun_prop
    exact compPT (f := fun p : List Bool × ℕ => fieldRow a codec p.1 p.2) hfr
      (h1.prod (hr.comp (ComputableTidilyInPolyTime.fst _ _)))
  have hH := ComputableTidilyInPolyTime.mapWithInput
    (f := fun (L : List Bool) (s : ℕ) =>
      fieldRow a codec ((hROf k a L).drop (s * (rOf k a L * (2 * a)))) (rOf k a L))
    (ComputableTidilyInPolyTime.range.comp hmt) hHf
  -- Us
  have hUih : ∀ i h : ℕ, PT (fun L : List Bool =>
      fieldRow a codec ((blkOf L i).drop (h * mOf k L * (2 * a))) (mOf k L))
      encBits (encList (encF codec)) := by
    intro i h
    have hb := blkOf_poly i
    have h1 : PT (fun L : List Bool => (blkOf L i).drop (h * mOf k L * (2 * a))) encBits encBits := by
      fun_prop
    exact compPT (f := fun p : List Bool × ℕ => fieldRow a codec p.1 p.2) hfr (h1.prod hm)
  have hU := ComputableTidilyInPolyTime.mapConst (List.range k)
    (f := fun (L : List Bool) (i : ℕ) => (List.range (copies k)).map (fun h =>
      fieldRow a codec ((blkOf L i).drop (h * mOf k L * (2 * a))) (mOf k L)))
    (fun i _ => ComputableTidilyInPolyTime.mapConst (List.range (copies k))
      (f := fun (L : List Bool) (h : ℕ) => fieldRow a codec ((blkOf L i).drop (h * mOf k L * (2 * a))) (mOf k L))
      (fun h _ => hUih i h))
  -- Vs
  have hVi : ∀ i : ℕ, PT (fun L : List Bool =>
      fieldRow a codec ((blkOf L i).drop (copies k * mOf k L * (2 * a))) (mtOf k a L))
      encBits (encList (encF codec)) := by
    intro i
    have hb := blkOf_poly i
    have h1 : PT (fun L : List Bool => (blkOf L i).drop (copies k * mOf k L * (2 * a))) encBits encBits := by
      fun_prop
    exact compPT (f := fun p : List Bool × ℕ => fieldRow a codec p.1 p.2) hfr (h1.prod hmt)
  have hV := ComputableTidilyInPolyTime.mapConst (List.range k)
    (f := fun (L : List Bool) (i : ℕ) =>
      fieldRow a codec ((blkOf L i).drop (copies k * mOf k L * (2 * a))) (mtOf k a L))
    (fun i _ => hVi i)
  exact hr.prod (hG.prod (hH.prod (hU.prod hV)))

theorem f2_poly : PT (f2 k a codec) encBits encBits := by
  unfold f2
  have hc := (check_poly codec k (copies k)).comp (parse_poly (k := k) (a := a) (codec := codec))
  have hn := nOf_poly
  have hle : PT (fun L : List Bool => decide (envelope k a 0 ≤ nOf L)) encBits encBool :=
    ComputableTidilyInPolyTime.unary_le' (ComputableTidilyInPolyTime.const _) hn
  have hand : PT (fun L : List Bool => decide (envelope k a 0 ≤ nOf L) && check k (copies k) (parse k a codec L))
      encBits encBool := ComputableTidilyInPolyTime.bool_and' hle hc
  fun_prop

end polys

end parse

end UPTAux

namespace UPTCorr

theorem chunk_drop {α : Type} : ∀ (m : ℕ) (f : Fin m → List α) (c : ℕ) (hf : ∀ s, (f s).length = c)
    (T : List α) (s : Fin m), ∃ R, ((List.ofFn f).flatten ++ T).drop (s.val * c) = f s ++ R
  | 0, _, _, _, _, s => s.elim0
  | m + 1, f, c, hf, T, s => by
      rw [List.ofFn_succ, List.flatten_cons, List.append_assoc]
      refine Fin.cases ?_ (fun s => ?_) s
      · exact ⟨(List.ofFn fun i => f i.succ).flatten ++ T, by simp⟩
      · obtain ⟨R, hR⟩ := chunk_drop m (fun i => f i.succ) c (fun i => hf _) T s
        refine ⟨R, ?_⟩
        rw [Fin.val_succ, Nat.succ_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' (hf 0)]
        exact hR

theorem chunk_take {α : Type} (m : ℕ) (f : Fin m → List α) (c : ℕ) (hf : ∀ s, (f s).length = c)
    (T : List α) (s : Fin m) : (((List.ofFn f).flatten ++ T).drop (s.val * c)).take c = f s := by
  obtain ⟨R, hR⟩ := chunk_drop m f c hf T s
  rw [hR, List.take_left' (hf s)]

theorem flat_drop_all {α : Type} : ∀ (m : ℕ) (f : Fin m → List α) (c : ℕ) (hf : ∀ s, (f s).length = c)
    (T : List α), ((List.ofFn f).flatten ++ T).drop (m * c) = T
  | 0, _, _, _, T => by simp
  | m + 1, f, c, hf, T => by
      rw [List.ofFn_succ, List.flatten_cons, List.append_assoc, Nat.succ_mul, Nat.add_comm,
        ← List.drop_drop, List.drop_left' (hf 0)]
      exact flat_drop_all m (fun i => f i.succ) c (fun i => hf _) T

theorem flat_length {α : Type} : ∀ (m : ℕ) (f : Fin m → List α) (c : ℕ)
    (hf : ∀ s, (f s).length = c), (List.ofFn f).flatten.length = m * c
  | 0, _, _, _ => by simp
  | m + 1, f, c, hf => by
      rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0,
        flat_length m (fun i => f i.succ) c (fun i => hf _)]
      ring

theorem foldl_add {M : Type} [AddCommMonoid M] : ∀ (l : List M) (init : M),
    l.foldl (· + ·) init = init + l.sum
  | [], init => by simp
  | x :: l, init => by rw [List.foldl_cons, foldl_add l, List.sum_cons]; abel

theorem foldl_mul {M : Type} [CommMonoid M] : ∀ (l : List M) (init : M),
    l.foldl (· * ·) init = init * l.prod
  | [], init => by simp
  | x :: l, init => by rw [List.foldl_cons, foldl_mul l, List.prod_cons, mul_assoc]

theorem sum_map_range {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem prod_map_range {M : Type} [CommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).prod = ∏ i : Fin n, f i := by
  rw [Fin.prod_univ_eq_prod_range]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]; simp

end UPTCorr

namespace UPTCorr
open NOFSeparation750.CodedGIP UPTAux

theorem idxOf_unary (n : ℕ) (rest : List Bool) :
    (List.replicate n true ++ false :: rest).idxOf false = n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, List.idxOf_cons_ne _ (by simp), ih]

theorem getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (d : α) {i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp

theorem drop_unary (m : ℕ) (X : List Bool) :
    (List.replicate m true ++ false :: X).drop (m + 1) = X := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.cons_append, List.drop_succ_cons]; exact ih

theorem getD_take_drop (l : List Bool) (p b t : ℕ) (ht : t < b) :
    ((l.drop p).take b).getD t false = l.getD (p + t) false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht,
    List.getElem?_drop]

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp


section core
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] (k a : ℕ) (codec : (Fin (2 * a) → Bool) ≃ F)

theorem fvb_length {r : ℕ} (v : Fin r → F) : (fieldVectorBits codec v).length = r * (2 * a) := by
  unfold fieldVectorBits
  exact flat_length r _ (2 * a) (fun t => by simp)

theorem genBits_eq {r : ℕ} (P : CodePresentation F r) :
    generatorBits codec P = List.replicate P.dimension true ++ false ::
      (List.ofFn fun i => fieldVectorBits codec (P.basis i).val).flatten := by
  simp [generatorBits, unary]

/-- a row of a generator matrix, read back. -/
theorem fieldRow_row {r : ℕ} (P : CodePresentation F r) (T : List Bool) (s : Fin P.dimension) :
    fieldRow a codec (((List.ofFn fun i => fieldVectorBits codec (P.basis i).val).flatten ++ T).drop
      (s.val * (r * (2 * a)))) r = List.ofFn (fun t => (P.basis s).val t) := by
  obtain ⟨R, hR⟩ := chunk_drop P.dimension (fun i => fieldVectorBits codec (P.basis i).val)
    (r * (2 * a)) (fun i => fvb_length a codec _) T s
  rw [hR]
  unfold fieldRow
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have ht : t < r := by simpa using h1
    have := chunk_take r (fun u => List.ofFn (codec.symm ((P.basis s).val u))) (2 * a)
      (fun u => by simp) R ⟨t, ht⟩
    simp only [fieldVectorBits] at this ⊢
    rw [this, decF_eq]
    have : (fun u : Fin (2 * a) => (List.ofFn (codec.symm ((P.basis s).val ⟨t, ht⟩))).getD u false)
        = codec.symm ((P.basis s).val ⟨t, ht⟩) := by
      funext u; rw [getD_ofFn _ _ u.2]
    rw [this, Equiv.apply_symm_apply]

section parsefacts
variable {r : ℕ} (P : CodePair F r) {n : ℕ} (x : Fin k → Fin n → Bool)

noncomputable abbrev GBits : List Bool := generatorBits codec P.small ++ generatorBits codec P.large
noncomputable abbrev Lin : List Bool := evaluationInput x ++ GBits a codec P

theorem Lin_eq : Lin k a codec P x = List.replicate n true ++ false ::
    ((List.ofFn fun i => List.ofFn (x i)).flatten ++ GBits a codec P) := by
  simp [Lin, evaluationInput, unary]

theorem nOf_Lin : nOf (Lin k a codec P x) = n := by
  rw [Lin_eq]; exact idxOf_unary _ _

theorem bodyOf_Lin : bodyOf (Lin k a codec P x) =
    (List.ofFn fun i => List.ofFn (x i)).flatten ++ GBits a codec P := by
  unfold bodyOf; rw [nOf_Lin, Lin_eq]; exact drop_unary _ _

theorem blkOf_Lin (i : Fin k) : blkOf (Lin k a codec P x) i.val = List.ofFn (x i) := by
  unfold blkOf; rw [bodyOf_Lin, nOf_Lin]
  exact chunk_take k (fun i => List.ofFn (x i)) n (fun _ => by simp) _ i

theorem genOf_Lin : genOf k (Lin k a codec P x) = GBits a codec P := by
  unfold genOf; rw [bodyOf_Lin, nOf_Lin]
  exact flat_drop_all k (fun i => List.ofFn (x i)) n (fun _ => by simp) _

theorem mOf_Lin : mOf k (Lin k a codec P x) = P.small.dimension := by
  unfold mOf; rw [genOf_Lin, GBits, genBits_eq, List.append_assoc, List.cons_append]
  exact idxOf_unary _ _

theorem gROf_Lin : gROf k (Lin k a codec P x) =
    (List.ofFn fun i => fieldVectorBits codec (P.small.basis i).val).flatten ++
      generatorBits codec P.large := by
  unfold gROf; rw [mOf_Lin, genOf_Lin, GBits, genBits_eq, List.append_assoc, List.cons_append]
  exact drop_unary _ _

theorem g2Of_Lin (hr : rOf k a (Lin k a codec P x) = r) :
    g2Of k a (Lin k a codec P x) = generatorBits codec P.large := by
  unfold g2Of; rw [gROf_Lin, mOf_Lin, hr]
  exact flat_drop_all _ _ (r * (2 * a)) (fun _ => fvb_length a codec _) _

theorem mtOf_Lin (hr : rOf k a (Lin k a codec P x) = r) :
    mtOf k a (Lin k a codec P x) = P.large.dimension := by
  unfold mtOf; rw [g2Of_Lin k a codec P x hr, genBits_eq]; exact idxOf_unary _ _

theorem hROf_Lin (hr : rOf k a (Lin k a codec P x) = r) :
    hROf k a (Lin k a codec P x) =
      (List.ofFn fun i => fieldVectorBits codec (P.large.basis i).val).flatten := by
  unfold hROf; rw [mtOf_Lin k a codec P x hr, g2Of_Lin k a codec P x hr, genBits_eq]
  have := drop_unary P.large.dimension ((List.ofFn fun i => fieldVectorBits codec (P.large.basis i).val).flatten)
  exact this

/-- dot product of two range-indexed lists. -/
theorem dot_range (m : ℕ) (f g : ℕ → F) :
    dot ((List.range m).map f) ((List.range m).map g) = ∑ i : Fin m, f i * g i := by
  unfold dot
  rw [List.zip_map', foldl_add, zero_add, List.map_map]
  exact sum_map_range m _

def cU (i : Fin k) (h a' : ℕ) : F :=
  codec (fun u => (List.ofFn (x i)).getD ((h * P.small.dimension + a') * (2 * a) + u) false)

def cV (i : Fin k) (a' : ℕ) : F :=
  codec (fun u => (List.ofFn (x i)).getD
    ((copies k * P.small.dimension + a') * (2 * a) + u) false)

theorem fieldRow_coef (l : List Bool) (p cnt : ℕ) :
    fieldRow a codec (l.drop p) cnt =
      (List.range cnt).map (fun a' => codec (fun u => l.getD (p + a' * (2 * a) + u) false)) := by
  unfold fieldRow
  refine List.map_congr_left (fun a' _ => ?_)
  rw [decF_eq, List.drop_drop]
  congr 1; funext u
  rw [getD_take_drop _ _ _ _ u.2]

theorem parse_U (hr : rOf k a (Lin k a codec P x) = r) (i : Fin k) (h : ℕ) (hh : h < copies k) :
    (((parse k a codec (Lin k a codec P x)).2.2.2.1).getD i.val []).getD h [] =
      (List.range P.small.dimension).map (fun a' => cU k a codec P x i h a') := by
  unfold parse
  simp only
  rw [getD_map_range _ _ _ i.2, getD_map_range _ _ _ hh, blkOf_Lin, mOf_Lin, fieldRow_coef]
  refine List.map_congr_left (fun a' _ => ?_)
  unfold cU; congr 2; ring

theorem parse_V (hr : rOf k a (Lin k a codec P x) = r) (i : Fin k) :
    ((parse k a codec (Lin k a codec P x)).2.2.2.2).getD i.val [] =
      (List.range P.large.dimension).map (fun a' => cV k a codec P x i a') := by
  unfold parse
  simp only
  rw [getD_map_range _ _ _ i.2, blkOf_Lin, mOf_Lin, mtOf_Lin k a codec P x hr, fieldRow_coef]
  refine List.map_congr_left (fun a' _ => ?_)
  unfold cV; congr 2; ring

theorem parse_colG (hr : rOf k a (Lin k a codec P x) = r) (t : Fin r) :
    col (parse k a codec (Lin k a codec P x)).2.1 t.val =
      (List.range P.small.dimension).map (fun s =>
        if hs : s < P.small.dimension then (P.small.basis ⟨s, hs⟩).val t else 0) := by
  unfold parse col
  simp only [List.map_map]
  rw [mOf_Lin]
  refine List.map_congr_left (fun s hs => ?_)
  have hs' : s < P.small.dimension := by simpa using hs
  simp only [Function.comp_apply, dif_pos hs']
  rw [gROf_Lin, hr, fieldRow_row a codec P.small _ ⟨s, hs'⟩,
    List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem parse_colH (hr : rOf k a (Lin k a codec P x) = r) (t : Fin r) :
    col (parse k a codec (Lin k a codec P x)).2.2.1 t.val =
      (List.range P.large.dimension).map (fun s =>
        if hs : s < P.large.dimension then (P.large.basis ⟨s, hs⟩).val t else 0) := by
  unfold parse col
  simp only [List.map_map]
  rw [mtOf_Lin k a codec P x hr]
  refine List.map_congr_left (fun s hs => ?_)
  have hs' : s < P.large.dimension := by simpa using hs
  simp only [Function.comp_apply, dif_pos hs']
  have := fieldRow_row a codec P.large [] ⟨s, hs'⟩
  rw [List.append_nil] at this
  rw [hROf_Lin k a codec P x hr, hr, this, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem lhs_val (hr : rOf k a (Lin k a codec P x) = r) (t : Fin r) :
    lhs k (copies k) (parse k a codec (Lin k a codec P x)) t.val =
      ∑ h : Fin (copies k), ∏ i : Fin k, ∑ a' : Fin P.small.dimension,
        cU k a codec P x i h a' * (P.small.basis a').val t := by
  unfold lhs
  rw [foldl_add, zero_add, sum_map_range]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [foldl_mul, one_mul, prod_map_range]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  unfold UPTAux.inner
  rw [parse_U k a codec P x hr i h h.2, parse_colG k a codec P x hr t, dot_range]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [dif_pos a'.2]

theorem rhs_val (hr : rOf k a (Lin k a codec P x) = r) (t : Fin r) :
    rhs k (parse k a codec (Lin k a codec P x)) t.val =
      ∑ i : Fin k, ∑ a' : Fin P.large.dimension,
        cV k a codec P x i a' * (P.large.basis a').val t := by
  unfold rhs
  rw [foldl_add, zero_add, sum_map_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [parse_V k a codec P x hr i, parse_colH k a codec P x hr t, dot_range]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [dif_pos a'.2]

theorem encode_apply {r : ℕ} (Q : CodePresentation F r) (u : Fin Q.dimension → F) (t : Fin r) :
    (Q.encode u).val t = ∑ i, u i * (Q.basis i).val t := by
  unfold CodePresentation.encode
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp [smul_eq_mul]

theorem check_correct (hr : rOf k a (Lin k a codec P x) = r) :
    check k (copies k) (parse k a codec (Lin k a codec P x)) =
      nativeFunction P codec (copies k) k (fun i t => (List.ofFn (x i)).getD t.val false) := by
  have h1 : (parse k a codec (Lin k a codec P x)).1 = r := hr
  unfold check nativeFunction codedGIP
  rw [Bool.eq_iff_iff, List.all_eq_true, h1]
  simp only [decide_eq_true_eq]
  rw [funext_iff]
  have hbitsU : ∀ (i : Fin k) (h : Fin (copies k)) (a' : Fin P.small.dimension),
      (codec fun u : Fin (2 * a) =>
        (List.ofFn fun t : Fin (nativeLength P (copies k) (2 * a)) => (List.ofFn (x i)).getD t.val false).getD
        ((h.val * P.small.dimension + a'.val) * (2 * a) + u.val) false) = cU k a codec P x i h a' := by
    intro i h a'
    unfold cU; congr 1; funext u
    have hidx : (h.val * P.small.dimension + a'.val) * (2 * a) + u.val <
        nativeLength P (copies k) (2 * a) := by
      have hh := h.2; have ha := a'.2; have hu := u.2
      have : (h.val * P.small.dimension + a'.val + 1) * (2 * a) ≤
          (copies k * P.small.dimension + P.large.dimension) * (2 * a) :=
        Nat.mul_le_mul_right _ (by nlinarith)
      show _ < (copies k * P.small.dimension + P.large.dimension) * (2 * a)
      nlinarith
    rw [getD_ofFn _ _ hidx]
  have hbitsV : ∀ (i : Fin k) (a' : Fin P.large.dimension),
      (codec fun u : Fin (2 * a) =>
        (List.ofFn fun t : Fin (nativeLength P (copies k) (2 * a)) => (List.ofFn (x i)).getD t.val false).getD
        ((copies k * P.small.dimension + a'.val) * (2 * a) + u.val) false) = cV k a codec P x i a' := by
    intro i a'
    unfold cV; congr 1; funext u
    have hidx : (copies k * P.small.dimension + a'.val) * (2 * a) + u.val <
        nativeLength P (copies k) (2 * a) := by
      have ha := a'.2; have hu := u.2
      have : (copies k * P.small.dimension + a'.val + 1) * (2 * a) ≤
          (copies k * P.small.dimension + P.large.dimension) * (2 * a) :=
        Nat.mul_le_mul_right _ (by omega)
      show _ < (copies k * P.small.dimension + P.large.dimension) * (2 * a)
      nlinarith
    rw [getD_ofFn _ _ hidx]
  constructor
  · intro hall t
    have := hall t.val (List.mem_range.mpr t.2)
    rw [beq_iff_eq, lhs_val k a codec P x hr t, rhs_val k a codec P x hr t] at this
    simp only [Finset.sum_apply]
    unfold decodeForehead
    simp only [encode_apply]
    simp only [hbitsU, hbitsV]
    exact this
  · intro hfun t ht
    have := hfun ⟨t, List.mem_range.mp ht⟩
    rw [beq_iff_eq]
    rw [show t = (⟨t, List.mem_range.mp ht⟩ : Fin r).val from rfl,
      lhs_val k a codec P x hr, rhs_val k a codec P x hr]
    simp only [Finset.sum_apply] at this
    unfold decodeForehead at this
    simp only [encode_apply] at this
    simp only [hbitsU, hbitsV] at this
    exact this

end parsefacts

theorem envelope_paddingLevel_le (k a n : ℕ) (hn : envelope k a 0 ≤ n) :
    envelope k a (paddingLevel k a n) ≤ n := by
  classical
  set S := (Finset.range (n + 1)).filter (fun j => envelope k a j ≤ n) with hS
  have h0 : 0 ∈ S := by simp [hS, hn]
  have hne : S.Nonempty := ⟨0, h0⟩
  have hpl : paddingLevel k a n = S.max' hne := by
    unfold paddingLevel
    rw [← hS, ← Finset.coe_max' hne]; rfl
  have hmem := S.max'_mem hne
  rw [← hpl] at hmem
  simp only [hS, Finset.mem_filter] at hmem
  exact hmem.2

theorem f2_correct (ha : 1 ≤ a) (D : PairFamily F a) {n : ℕ} (x : Fin k → Fin n → Bool) :
    f2 k a codec (Lin k a codec (D (paddingLevel k a n)) x) = [paddedFamily D codec k n x] := by
  unfold f2 paddedFamily
  rw [nOf_Lin]
  by_cases hn : n < envelope k a 0
  · rw [if_pos hn]
    simp [Nat.not_le.mpr hn]
  · rw [if_neg hn]
    have hn' : envelope k a 0 ≤ n := Nat.le_of_not_lt hn
    have hr : rOf k a (Lin k a codec (D (paddingLevel k a n)) x) = codeLength a (paddingLevel k a n) := by
      unfold rOf
      rw [nOf_Lin, lvl_eq k a n ha, powCap_eq]
      have h1 := envelope_paddingLevel_le k a n hn'
      rw [envelope_eq] at h1
      have hE := envelope0_pos k a ha
      have : (2 ^ a) ^ paddingLevel k a n ≤ n + 1 := by nlinarith
      rw [min_eq_left this]
      unfold codeLength; ring
    rw [check_correct k a codec (D (paddingLevel k a n)) x hr]
    simp [hn']

end core

end UPTCorr


namespace UPTFinal
open NOFSeparation750.CodedGIP

theorem evalInput_length {k n : ℕ} (x : Fin k → Fin n → Bool) :
    (evaluationInput x).length = k * n + n + 1 := by
  unfold evaluationInput unary
  rw [List.length_append, UPTCorr.flat_length k _ n (fun _ => by simp)]
  simp; ring

theorem paddingLevel_le (k a n : ℕ) : paddingLevel k a n ≤ n := by
  classical
  unfold paddingLevel
  set S := (Finset.range (n + 1)).filter (fun j => envelope k a j ≤ n)
  by_cases hne : S.Nonempty
  · rw [← Finset.coe_max' hne]
    have := (Finset.mem_filter.mp (S.max'_mem hne)).1
    rw [Finset.mem_range] at this
    show S.max' hne ≤ n
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Nat.zero_le _

theorem paddingLevel_zero (k a n : ℕ) (hn : n < envelope k a 0) : paddingLevel k a n = 0 := by
  classical
  unfold paddingLevel
  have : (Finset.range (n + 1)).filter (fun j => envelope k a j ≤ n) = ∅ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and,
      Nat.not_le]
    intro _
    exact lt_of_lt_of_le hn (UPTAux.envelope_mono k a (Nat.zero_le j))
  rw [this]; rfl

theorem codeLength_le_envelope (k a j : ℕ) (ha : 1 ≤ a) : codeLength a j ≤ envelope k a j := by
  unfold envelope
  have h1 : 1 ≤ copies k + 1 := by omega
  have h2 : 1 ≤ 2 * a := by omega
  calc codeLength a j ≤ (copies k + 1) * codeLength a j := Nat.le_mul_of_pos_left _ h1
    _ ≤ (copies k + 1) * codeLength a j * (2 * a) := Nat.le_mul_of_pos_right _ h2

theorem dim_le {F : Type} [Field F] {r : ℕ} (Q : CodePresentation F r) : Q.dimension ≤ r := by
  have := Submodule.finrank_le Q.code
  rwa [Module.finrank_eq_card_basis Q.basis, Fintype.card_fin, Module.finrank_fin_fun] at this

theorem genBits_length {F : Type} [Field F] [Fintype F] [DecidableEq F] {a r : ℕ} (codec : (Fin (2 * a) → Bool) ≃ F)
    (Q : CodePresentation F r) :
    (generatorBits codec Q).length ≤ r + 1 + r * (r * (2 * a)) := by
  unfold generatorBits unary
  rw [List.length_append, UPTCorr.flat_length _ _ (r * (2 * a)) (fun _ => UPTCorr.fvb_length a codec _)]
  have h1 := dim_le Q
  have h2 := Nat.mul_le_mul_right (r * (2 * a)) h1
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  omega

end UPTFinal

open NOFSeparation750.CodedGIP Polynomial in
theorem solution (k a : ℕ) (hk : 2 ≤ k) (ha : Allowed k a)
    (F : Type) [Field F] [Fintype F] (D : PairFamily F a)
    (codec : (Fin (2 * a) → Bool) ≃ F) (heff : EffectivePairFamily D codec) :
    UniformPolyTime (paddedFamily D codec k) := by
  classical
  have ha1 := ha.1
  obtain ⟨A, pA, hA⟩ := C1fp (Turing.MultiTapeTM.ComputableInPolyTime.of_tidy (UPTAux.f1_poly k a))
  obtain ⟨B, pB, hB⟩ := C1fp (Turing.MultiTapeTM.ComputableInPolyTime.of_tidy (UPTAux.f2_poly (k := k) (a := a) codec))
  obtain ⟨gen, _, p, hgen⟩ := heff
  let J : List Bool → ℕ := fun L => UPTAux.lvl k a (UPTAux.nOf L)
  let g : List Bool → List Bool := fun L =>
    generatorBits codec (D (J L)).small ++ generatorBits codec (D (J L)).large
  have hG : ∀ L, OutputsWithin gen (UPTAux.f1 k a L) (g L) (p.eval (codeLength a (J L))) :=
    fun L => (hgen (J L)).1
  obtain ⟨P, hP⟩ := FPAux.fp_sandwich A gen B (UPTAux.f1 k a) g (UPTAux.f2 k a codec)
    (fun L => pA.eval L.length) (fun L => p.eval (codeLength a (J L)))
    (fun L => pB.eval (L ++ g L).length) (fun L => hA L) hG (fun L => hB (L ++ g L))
  set c0 := codeLength a 0
  let R : Polynomial ℕ := X + C c0
  let Gp : Polynomial ℕ := C 2 * (R + 1) + C 2 * (R * (R * C (2 * a)))
  let q : Polynomial ℕ := pA + p.comp R + pB.comp (X + Gp) + C 7 * (X + X + Gp + 1)
  refine ⟨P, q, fun n x => ?_⟩
  have hmain := hP (evaluationInput x)
  have hnOf : UPTAux.nOf (evaluationInput x) = n := by
    unfold UPTAux.nOf evaluationInput unary
    rw [List.append_assoc, List.singleton_append]
    exact UPTCorr.idxOf_unary _ _
  have hJ : J (evaluationInput x) = paddingLevel k a n := by
    show UPTAux.lvl k a (UPTAux.nOf (evaluationInput x)) = _
    rw [hnOf, UPTAux.lvl_eq k a n ha1]
  have hout : UPTAux.f2 k a codec (evaluationInput x ++ g (evaluationInput x)) =
      [paddedFamily D codec k n x] := by
    have : g (evaluationInput x) = UPTCorr.GBits a codec (D (paddingLevel k a n)) := by
      show generatorBits codec (D (J (evaluationInput x))).small ++
        generatorBits codec (D (J (evaluationInput x))).large = _
      rw [hJ]
    rw [this]
    exact UPTCorr.f2_correct k a codec ha1 D x
  rw [hout] at hmain
  refine FPAux.outputsWithin_mono hmain ?_
  -- time bound
  set ℓL := (evaluationInput x).length with hℓL
  have hlen : ℓL = k * n + n + 1 := UPTFinal.evalInput_length x
  rw [← hlen]
  set j := J (evaluationInput x)
  have hjn : j ≤ n := by rw [hJ]; exact UPTFinal.paddingLevel_le k a n
  have hcl : codeLength a j ≤ ℓL + c0 := by
    rw [hJ]
    by_cases hn : n < envelope k a 0
    · rw [UPTFinal.paddingLevel_zero k a n hn]; omega
    · have h1 := UPTCorr.envelope_paddingLevel_le k a n (Nat.le_of_not_lt hn)
      have h2 := UPTFinal.codeLength_le_envelope k a (paddingLevel k a n) ha1
      omega
  have hg : (g (evaluationInput x)).length ≤ Gp.eval ℓL := by
    show (generatorBits codec (D j).small ++ generatorBits codec (D j).large).length ≤ _
    rw [List.length_append]
    have h1 := UPTFinal.genBits_length codec (D j).small
    have h2 := UPTFinal.genBits_length codec (D j).large
    have hR : codeLength a j ≤ R.eval ℓL := by simp [R]; exact hcl
    simp only [Gp, eval_add, eval_mul, eval_C, eval_one]
    have hR2 := Nat.mul_le_mul hR (Nat.mul_le_mul_right (2 * a) hR)
    nlinarith
  have hf1 : (UPTAux.f1 k a (evaluationInput x)).length ≤ ℓL := by
    show (List.replicate (UPTAux.lvl k a ((evaluationInput x).idxOf false)) true ++ [false]).length ≤ _
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    have : UPTAux.lvl k a ((evaluationInput x).idxOf false) = j := rfl
    rw [this]; omega
  have hpG : p.eval (codeLength a j) ≤ (p.comp R).eval ℓL := by
    rw [eval_comp]; exact Turing.CompCore.poly_eval_mono p (by simp [R]; exact hcl)
  have hpB : pB.eval (evaluationInput x ++ g (evaluationInput x)).length ≤ (pB.comp (X + Gp)).eval ℓL := by
    rw [eval_comp]; refine Turing.CompCore.poly_eval_mono pB ?_
    rw [List.length_append]; simp only [eval_add, eval_X]; omega
  simp only [q, eval_add, eval_mul, eval_C, eval_X, eval_one]
  omega
