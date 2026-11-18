-- Prove2me | solution 1 for HILL.PRG.batch_calls_polytime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-18T02:24:08.793224+00:00
-- url     : https://prove2.me/submissions/0ea56da9-56ab-45f2-ab8c-2435f93a5a4c

import Definitions.Def_HILL_PRG_Model
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
import Mathlib.Tactic.DeriveFintype

open HILL.PRG

/-!
A verified call to a TM2 subroutine leaves the caller's stacks and state intact.
The Mathlib output certificate also guarantees the callee's own scratch stacks
are empty at return.
-/

namespace Turing.BatchSubmissionCall

open StateTransition

variable (tm : FinTM2) {K L σ : Type} (Γ : K → Type)

abbrev Alphabet : tm.K ⊕ K → Type := Sum.elim tm.Γ Γ

abbrev Stmt (L σ : Type) :=
  TM2.Stmt (Alphabet tm Γ) (tm.Λ ⊕ L) (tm.σ × σ)

abbrev Cfg (L σ : Type) :=
  TM2.Cfg (Alphabet tm Γ) (tm.Λ ⊕ L) (tm.σ × σ)

def stackUnion (S : ∀ k, List (tm.Γ k)) (R : ∀ k, List (Γ k)) :
    ∀ k, List (Alphabet tm Γ k)
  | .inl k => S k
  | .inr k => R k

variable {Γ}

def liftStmt (returnTo : L) : tm.Stmt → Stmt tm Γ L σ
  | .push k f s => .push (.inl k) (fun v => f v.1) (liftStmt returnTo s)
  | .peek k f s => .peek (.inl k) (fun v x => (f v.1 x, v.2)) (liftStmt returnTo s)
  | .pop k f s => .pop (.inl k) (fun v x => (f v.1 x, v.2)) (liftStmt returnTo s)
  | .load f s => .load (fun v => (f v.1, v.2)) (liftStmt returnTo s)
  | .branch f s t => .branch (fun v => f v.1) (liftStmt returnTo s) (liftStmt returnTo t)
  | .goto l => .goto (fun v => .inl (l v.1))
  | .halt => .goto (fun _ => .inr returnTo)

def liftCfg (returnTo : L) (callerState : σ) (R : ∀ k, List (Γ k)) (c : tm.Cfg) :
    Cfg tm Γ L σ where
  l := some (c.l.elim (.inr returnTo) Sum.inl)
  var := (c.var, callerState)
  stk := stackUnion tm Γ c.stk R

def program (returnTo : L) (caller : L → Stmt tm Γ L σ) :
    (tm.Λ ⊕ L) → Stmt tm Γ L σ
  | .inl l => liftStmt tm returnTo (tm.m l)
  | .inr l => caller l

variable [DecidableEq K]

private theorem stackUnion_update (S : ∀ k, List (tm.Γ k))
    (R : ∀ k, List (Γ k)) (k : tm.K) (value : List (tm.Γ k)) :
    Function.update (stackUnion tm Γ S R) (.inl k) value =
      stackUnion tm Γ (Function.update S k value) R := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [stackUnion, Function.update]
    · have h' : (Sum.inl j : tm.K ⊕ K) ≠ Sum.inl k := fun he => h (Sum.inl.inj he)
      simp [stackUnion, Function.update, h, h']
  | inr j => simp [stackUnion, Function.update]

private theorem stepAux_lift (returnTo : L) (callerState : σ) (R : ∀ k, List (Γ k))
    (s : tm.Stmt) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    TM2.stepAux (liftStmt tm returnTo s) (v, callerState) (stackUnion tm Γ S R) =
      liftCfg tm returnTo callerState R (TM2.stepAux s v S) := by
  induction s generalizing v S with
  | push k f s ih =>
    simp [liftStmt, TM2.stepAux]
    rw [stackUnion_update]
    exact ih v _
  | peek k f s ih =>
    simp only [liftStmt, TM2.stepAux.eq_2, stackUnion]
    exact ih _ S
  | pop k f s ih =>
    simp [liftStmt, TM2.stepAux, stackUnion]
    rw [stackUnion_update]
    exact ih _ _
  | load f s ih =>
    simp only [liftStmt, TM2.stepAux.eq_4]
    exact ih _ S
  | branch f s t ihs iht =>
    cases h : f v <;> simp [liftStmt, h, ihs, iht]
  | goto l => rfl
  | halt => rfl

private theorem step_lift (returnTo : L) (caller : L → Stmt tm Γ L σ)
    (callerState : σ) (R : ∀ k, List (Γ k)) (c : tm.Cfg) (hc : tm.step c ≠ none) :
    TM2.step (program tm returnTo caller) (liftCfg tm returnTo callerState R c) =
      Option.map (liftCfg tm returnTo callerState R) (tm.step c) := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => exact (hc rfl).elim
  | some l =>
    exact congrArg some (stepAux_lift tm returnTo callerState R (tm.m l) v S)

/-- Run one certified callee from its entry configuration to its return
continuation without consuming any extra TM2 steps or changing caller data. -/
def evalsTo_return (returnTo : L) (caller : L → Stmt tm Γ L σ)
    (callerState : σ) (R : ∀ k, List (Γ k))
    {input : List (tm.Γ tm.k₀)} {output : List (tm.Γ tm.k₁)} {bound : ℕ}
    (run : TM2OutputsInTime tm input (some output) bound) :
    EvalsToInTime (TM2.step (program tm returnTo caller))
      (liftCfg tm returnTo callerState R (initList tm input))
      (some (liftCfg tm returnTo callerState R (haltList tm output))) bound :=
  TM2Comp.evalsToInTime_lift (liftCfg tm returnTo callerState R) run rfl
    (step_lift tm returnTo caller callerState R)

end Turing.BatchSubmissionCall

set_option backward.isDefEq.respectTransparency.types false

namespace HILL.PRG.BatchSubmission

noncomputable section

open Turing StateTransition

def quoteBits (w : Bits) : Bits :=
  w.flatMap (fun b => [true, b])

/-- Every word, including an empty word, pays for one delimiter. -/
def encodeWords (ws : List Bits) : Bits :=
  ws.flatMap (fun w => quoteBits w ++ [false])

/-- A new word-level subroutine compiler; not a finite-alphabet symbol map. -/
def BatchCallsContract : Prop :=
  ∀ (M : Bits → Bits), PolyTimeComputable M →
    ∃ B : Bits → Bits, PolyTimeComputable B ∧
      ∀ (n a : ℕ) (xs : List Bits),
        B (encAdvice n a (encodeWords xs)) =
          encodeWords (xs.map (fun x => M (encAdvice n a x)))

inductive Tape
  | input | header | savedPrefix | reversedWord | accumulator | output
  deriving DecidableEq, Fintype

inductive Label
  | readHeader (second : Bool)
  | scan | copyWord | copyPrefix | restorePrefix | collect
  | clearWord | clearPrefix | reverseOutput
  deriving DecidableEq, Fintype

structure Tapes where
  input : Bits := []
  header : Bits := []
  savedPrefix : Bits := []
  reversedWord : Bits := []
  accumulator : Bits := []
  output : Bits := []

def Tapes.stk (s : Tapes) : Tape → Bits
  | .input => s.input
  | .header => s.header
  | .savedPrefix => s.savedPrefix
  | .reversedWord => s.reversedWord
  | .accumulator => s.accumulator
  | .output => s.output

variable {M : Bits → Bits}
abbrev Witness (M : Bits → Bits) :=
  TM2ComputableInPolyTime (id : Bits → List Bool) (id : Bits → List Bool) M

variable (H : Witness M)

abbrev alphabet : H.tm.K ⊕ Tape → Type := BatchSubmissionCall.Alphabet H.tm (fun _ : Tape => Bool)
abbrev Inst := BatchSubmissionCall.Stmt H.tm (fun _ : Tape => Bool) Label (Option Bool)
abbrev Config := BatchSubmissionCall.Cfg H.tm (fun _ : Tape => Bool) Label (Option Bool)

def jump (l : Label) : Inst H :=
  .load (fun v => (v.1, none)) (.goto (fun _ => .inr l))

def push (k : Tape) (b : Bool) (next : Inst H) : Inst H :=
  .push (.inr k) (fun _ => b) next

def pushInput (b : Bool) (next : Inst H) : Inst H :=
  .push (.inl H.tm.k₀) (fun _ => H.inputAlphabet.symm b) next

def popDecoded (k : H.tm.K ⊕ Tape) (read : alphabet H k → Bool)
    (empty : Inst H) (nonempty : Bool → Inst H) : Inst H :=
  .pop k (fun v x => (v.1, x.map read))
    (.branch (fun v => v.2.isSome)
      (.branch (fun v => v.2.getD false) (nonempty true) (nonempty false))
      empty)

def pop (k : Tape) (empty : Inst H) (nonempty : Bool → Inst H) : Inst H :=
  popDecoded H (.inr k) id empty nonempty

def enter : Inst H :=
  .load (fun _ => (H.tm.initialState, none)) (.goto (fun _ => .inl H.tm.main))

def exit : Inst H :=
  .load (fun _ => (H.tm.initialState, none)) .halt

def caller : Label → Inst H
  | .readHeader second =>
    pop H .input (jump H .clearWord) fun b =>
      push H .header b (jump H (if b then .readHeader second else if second then .scan else .readHeader true))
  | .scan =>
    pop H .input (jump H .clearWord) fun mark =>
      if mark then
        pop H .input (jump H .clearWord)
          (fun b => push H .reversedWord b (jump H .scan))
      else jump H .copyWord
  | .copyWord =>
    pop H .reversedWord (jump H .copyPrefix) fun b =>
      pushInput H b (jump H .copyWord)
  | .copyPrefix =>
    pop H .header (jump H .restorePrefix) fun b =>
      pushInput H b (push H .savedPrefix b (jump H .copyPrefix))
  | .restorePrefix =>
    pop H .savedPrefix (enter H) fun b =>
      push H .header b (jump H .restorePrefix)
  | .collect =>
    popDecoded H (.inl H.tm.k₁) H.outputAlphabet
      (push H .accumulator false (jump H .scan))
      (fun b => push H .accumulator true (push H .accumulator b (jump H .collect)))
  | .clearWord =>
    pop H .reversedWord (jump H .clearPrefix) (fun _ => jump H .clearWord)
  | .clearPrefix =>
    pop H .header (jump H .reverseOutput) (fun _ => jump H .clearPrefix)
  | .reverseOutput =>
    pop H .accumulator (exit H) (fun b => push H .output b (jump H .reverseOutput))

def program : H.tm.Λ ⊕ Label → Inst H := BatchSubmissionCall.program H.tm .collect (caller H)

abbrev step : Config H → Option (Config H) := TM2.step (program H)

def emptyStk : ∀ k : H.tm.K, List (H.tm.Γ k) := fun _ => []

def inputStk (w : Bits) : ∀ k : H.tm.K, List (H.tm.Γ k) :=
  (initList H.tm (w.map H.inputAlphabet.symm)).stk

def outputStk (w : Bits) : ∀ k : H.tm.K, List (H.tm.Γ k) :=
  (haltList H.tm (w.map H.outputAlphabet.symm)).stk

def config (l : Option (H.tm.Λ ⊕ Label)) (s : Tapes)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) : Config H where
  l := l
  var := (H.tm.initialState, none)
  stk := BatchSubmissionCall.stackUnion H.tm (fun _ : Tape => Bool) callee s.stk

abbrev atLabel (l : Label) (s : Tapes) (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    Config H :=
  config H (some (.inr l)) s callee

def machine : FinTM2 := by
  letI := H.tm.kFin
  letI := H.tm.ΛFin
  letI := H.tm.σFin
  exact
    { K := H.tm.K ⊕ Tape
      k₀ := .inr .input
      k₁ := .inr .output
      Γ := alphabet H
      Λ := H.tm.Λ ⊕ Label
      main := .inr (.readHeader false)
      σ := H.tm.σ × Option Bool
      initialState := (H.tm.initialState, none)
      Γk₀Fin := inferInstanceAs (Fintype Bool)
      m := program H }

private def Tapes.set (s : Tapes) (t : Tape) (w : Bits) : Tapes :=
  match t with
  | .input => {s with input := w}
  | .header => {s with header := w}
  | .savedPrefix => {s with savedPrefix := w}
  | .reversedWord => {s with reversedWord := w}
  | .accumulator => {s with accumulator := w}
  | .output => {s with output := w}

private theorem update_right (s : Tapes) (t : Tape) (w : Bits)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    Function.update (BatchSubmissionCall.stackUnion H.tm (fun _ : Tape => Bool) callee s.stk)
      (.inr t) w =
    BatchSubmissionCall.stackUnion H.tm (fun _ : Tape => Bool) callee (s.set t w).stk := by
  funext k
  cases k with
  | inl i => simp [Function.update, BatchSubmissionCall.stackUnion]
  | inr i => cases t <;> cases i <;> simp [Function.update, BatchSubmissionCall.stackUnion, Tapes.set, Tapes.stk]

private theorem update_left (s : Tapes) (t : H.tm.K) (w : List (H.tm.Γ t))
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    Function.update (BatchSubmissionCall.stackUnion H.tm (fun _ : Tape => Bool) callee s.stk)
      (.inl t) w =
    BatchSubmissionCall.stackUnion H.tm (fun _ : Tape => Bool) (Function.update callee t w) s.stk := by
  funext k
  cases k with
  | inl i =>
    by_cases hi : i = t
    · subst i
      simp [Function.update, BatchSubmissionCall.stackUnion]
    · simp [Function.update, BatchSubmissionCall.stackUnion, hi]
  | inr i => simp [Function.update, BatchSubmissionCall.stackUnion]

@[simp] private theorem inputStk_here (w : Bits) :
    inputStk H w H.tm.k₀ = w.map H.inputAlphabet.symm := by simp [inputStk, initList]

@[simp] private theorem outputStk_here (w : Bits) :
    outputStk H w H.tm.k₁ = w.map H.outputAlphabet.symm := by simp [outputStk, haltList]

@[simp] private theorem inputStk_nil :
    inputStk H [] = emptyStk H := by
  funext k
  by_cases hk : k = H.tm.k₀
  · subst k; simp [emptyStk]
  · simp [inputStk, initList, hk, emptyStk]

@[simp] private theorem outputStk_nil :
    outputStk H [] = emptyStk H := by
  funext k
  by_cases hk : k = H.tm.k₁
  · subst k; simp [emptyStk]
  · simp [outputStk, haltList, hk, emptyStk]

private theorem inputStk_push (b : Bool) (w : Bits) :
    Function.update (inputStk H w) H.tm.k₀
      (H.inputAlphabet.symm b :: w.map H.inputAlphabet.symm) = inputStk H (b :: w) := by
  funext k
  by_cases hk : k = H.tm.k₀
  · subst k; simp [Function.update]
  · simp [Function.update, inputStk, initList, hk]

private theorem outputStk_pop (b : Bool) (w : Bits) :
    Function.update (outputStk H (b :: w)) H.tm.k₁
      (w.map H.outputAlphabet.symm) = outputStk H w := by
  funext k
  by_cases hk : k = H.tm.k₁
  · subst k; simp [Function.update]
  · simp [Function.update, outputStk, haltList, hk]

abbrev Run (c d : Config H) (n : ℕ) :=
  EvalsToInTime (step H) c (some d) n

private def one {c d : Config H} (he : step H c = some d) : Run H c d 1 :=
  ⟨⟨1, he⟩, le_rfl⟩

private def seq {c d e : Config H} {m n : ℕ} (h₁ : Run H c d m) (h₂ : Run H d e n) :
    Run H c e (m + n) :=
  ⟨(EvalsToInTime.trans _ _ _ _ _ _ h₁ h₂).toEvalsTo, by
    change h₂.steps + h₁.steps ≤ m + n
    simpa only [Nat.add_comm m n] using Nat.add_le_add h₂.steps_le_m h₁.steps_le_m⟩

private def relax {c d : Config H} {m n : ℕ} (h : Run H c d m) (hn : m ≤ n) :
    Run H c d n := ⟨h.toEvalsTo, h.steps_le_m.trans hn⟩

private theorem prefix_bit_step (second b : Bool) (xs : Bits) (s : Tapes)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    step H (atLabel H (.readHeader second) {s with input := b :: xs} callee) =
      some (atLabel H (if b then .readHeader second else if second then .scan else .readHeader true)
        {s with input := xs, header := b :: s.header} callee) := by
  cases b <;> simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, jump,
    BatchSubmissionCall.stackUnion, Tapes.stk, update_right, Tapes.set]

private theorem scan_bit_step (b : Bool) (xs : Bits) (s : Tapes)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    step H (atLabel H .scan {s with input := true :: b :: xs} callee) =
      some (atLabel H .scan {s with input := xs, reversedWord := b :: s.reversedWord} callee) := by
  cases b <;> simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, jump,
    BatchSubmissionCall.stackUnion, Tapes.stk, update_right, Tapes.set]

private theorem empty_update (t : H.tm.K) :
    Function.update (emptyStk H) t [] = emptyStk H := by
  funext k
  by_cases hk : k = t
  · subst k
    simp [Function.update, emptyStk]
  · simp [Function.update, hk]

private theorem prefix_end_step (second : Bool) (s : Tapes)
    (callee : ∀ k : H.tm.K, List (H.tm.Γ k)) :
    step H (atLabel H (.readHeader second) {s with input := []} callee) =
      some (atLabel H .clearWord {s with input := []} callee) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem scan_end_step (s : Tapes) (rest : Bits)
    (ht : rest = [] ∨ rest = [true]) :
    step H (atLabel H .scan {s with input := rest} (emptyStk H)) =
      some (atLabel H .clearWord {s with input := []} (emptyStk H)) := by
  rcases ht with rfl | rfl <;>
    (simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem scan_delimiter_step (s : Tapes) (xs : Bits) :
    step H (atLabel H .scan {s with input := false :: xs} (emptyStk H)) =
      some (atLabel H .copyWord {s with input := xs} (emptyStk H)) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem copy_word_step (s : Tapes) (b : Bool) (xs w : Bits) :
    step H (atLabel H .copyWord {s with reversedWord := b :: xs} (inputStk H w)) =
      some (atLabel H .copyWord {s with reversedWord := xs} (inputStk H (b :: w))) := by
  cases b <;>
    (simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem copy_word_end_step (s : Tapes) (w : Bits) :
    step H (atLabel H .copyWord {s with reversedWord := []} (inputStk H w)) =
      some (atLabel H .copyPrefix {s with reversedWord := []} (inputStk H w)) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem copy_prefix_step (s : Tapes) (b : Bool) (xs w : Bits) :
    step H (atLabel H .copyPrefix {s with header := b :: xs} (inputStk H w)) =
      some (atLabel H .copyPrefix {s with header := xs, savedPrefix := b :: s.savedPrefix}
        (inputStk H (b :: w))) := by
  cases b <;>
    (simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem copy_prefix_end_step (s : Tapes) (w : Bits) :
    step H (atLabel H .copyPrefix {s with header := []} (inputStk H w)) =
      some (atLabel H .restorePrefix {s with header := []} (inputStk H w)) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem restore_prefix_step (s : Tapes) (b : Bool) (xs w : Bits) :
    step H (atLabel H .restorePrefix {s with savedPrefix := b :: xs} (inputStk H w)) =
      some (atLabel H .restorePrefix {s with savedPrefix := xs, header := b :: s.header} (inputStk H w)) := by
  cases b <;>
    (simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem restore_prefix_end_step (s : Tapes) (w : Bits) :
    step H (atLabel H .restorePrefix {s with savedPrefix := []} (inputStk H w)) =
      some (config H (some (.inl H.tm.main)) {s with savedPrefix := []} (inputStk H w)) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem collect_bit_step (s : Tapes) (b : Bool) (w : Bits) :
    step H (atLabel H .collect s (outputStk H (b :: w))) =
      some (atLabel H .collect {s with accumulator := b :: true :: s.accumulator} (outputStk H w)) := by
  cases b <;>
    (simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem collect_end_step (s : Tapes) :
    step H (atLabel H .collect s (outputStk H [])) =
      some (atLabel H .scan {s with accumulator := false :: s.accumulator} (emptyStk H)) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem clear_word_step (s : Tapes) (b : Bool) (w : Bits) :
    step H (atLabel H .clearWord {s with reversedWord := b :: w} (emptyStk H)) =
      some (atLabel H .clearWord {s with reversedWord := w} (emptyStk H)) := by
  cases b <;>
    (simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem clear_word_end_step (s : Tapes) :
    step H (atLabel H .clearWord {s with reversedWord := []} (emptyStk H)) =
      some (atLabel H .clearPrefix {s with reversedWord := []} (emptyStk H)) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem clear_prefix_step (s : Tapes) (b : Bool) (w : Bits) :
    step H (atLabel H .clearPrefix {s with header := b :: w} (emptyStk H)) =
      some (atLabel H .clearPrefix {s with header := w} (emptyStk H)) := by
  cases b <;>
    (simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem clear_prefix_end_step (s : Tapes) :
    step H (atLabel H .clearPrefix {s with header := []} (emptyStk H)) =
      some (atLabel H .reverseOutput {s with header := []} (emptyStk H)) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private theorem reverse_out_step (s : Tapes) (b : Bool) (w : Bits) :
    step H (atLabel H .reverseOutput {s with accumulator := b :: w} (emptyStk H)) =
      some (atLabel H .reverseOutput {s with accumulator := w, output := b :: s.output}
        (emptyStk H)) := by
  cases b <;>
    (simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
      jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
      inputStk_push, outputStk_pop, emptyStk, empty_update])

private theorem reverse_out_end_step (s : Tapes) :
    step H (atLabel H .reverseOutput {s with accumulator := []} (emptyStk H)) =
      some (config H none {s with accumulator := []} (emptyStk H)) := by
  simp [program, config, BatchSubmissionCall.program, caller, pop, popDecoded, push, pushInput,
    jump, enter, exit, BatchSubmissionCall.stackUnion, Tapes.stk, update_left, update_right, Tapes.set,
    inputStk_push, outputStk_pop, emptyStk, empty_update]

private def copyWordRun (s : Tapes) (word seed : Bits) :
    Run H (atLabel H .copyWord {s with reversedWord := word} (inputStk H seed))
      (atLabel H .copyPrefix {s with reversedWord := []} (inputStk H (word.reverse ++ seed)))
      (word.length + 1) := by
  induction word generalizing seed with
  | nil => exact one H (copy_word_end_step H s seed)
  | cons b rest ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (copy_word_step H s b rest seed)) (ih (b :: seed))

private def copyHeaderRun (s : Tapes) (header saved seed : Bits) :
    Run H (atLabel H .copyPrefix {s with header := header, savedPrefix := saved} (inputStk H seed))
      (atLabel H .restorePrefix {s with header := [], savedPrefix := header.reverse ++ saved}
        (inputStk H (header.reverse ++ seed)))
      (header.length + 1) := by
  induction header generalizing saved seed with
  | nil => exact one H (copy_prefix_end_step H {s with savedPrefix := saved} seed)
  | cons b rest ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (copy_prefix_step H {s with savedPrefix := saved} b rest seed))
        (ih (b :: saved) (b :: seed))

private def restoreHeaderRun (s : Tapes) (saved header seed : Bits) :
    Run H (atLabel H .restorePrefix {s with savedPrefix := saved, header := header} (inputStk H seed))
      (config H (some (.inl H.tm.main)) {s with savedPrefix := [], header := saved.reverse ++ header}
        (inputStk H seed))
      (saved.length + 1) := by
  induction saved generalizing header with
  | nil => exact one H (restore_prefix_end_step H {s with header := header} seed)
  | cons b rest ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (restore_prefix_step H {s with header := header} b rest seed)) (ih (b :: header))

private def callRun (s : Tapes) (seed : Bits) :
    Run H (config H (some (.inl H.tm.main)) s (inputStk H seed))
      (atLabel H .collect s (outputStk H (M seed))) (H.time.eval seed.length) :=
  by
    exact BatchSubmissionCall.evalsTo_return H.tm (Γ := fun _ : Tape => Bool) Label.collect
      (caller H) (none : Option Bool) s.stk (H.outputsFun seed)

private def collectRun (s : Tapes) (w acc : Bits) :
    Run H (atLabel H .collect {s with accumulator := acc} (outputStk H w))
      (atLabel H .scan {s with accumulator := false :: ((quoteBits w).reverse ++ acc)}
        (emptyStk H))
      (w.length + 1) := by
  induction w generalizing acc with
  | nil => exact one H (collect_end_step H {s with accumulator := acc})
  | cons b rest ih =>
    simpa [quoteBits, List.flatMap_cons, List.reverse_append, List.append_assoc,
      Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (collect_bit_step H {s with accumulator := acc} b rest))
        (ih (b :: true :: acc))

private def clearWordRun (s : Tapes) (w : Bits) :
    Run H (atLabel H .clearWord {s with reversedWord := w} (emptyStk H))
      (atLabel H .clearPrefix {s with reversedWord := []} (emptyStk H))
      (w.length + 1) := by
  induction w with
  | nil => exact one H (clear_word_end_step H s)
  | cons b rest ih =>
    simpa [Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (clear_word_step H s b rest)) ih

private def clearHeaderRun (s : Tapes) (w : Bits) :
    Run H (atLabel H .clearPrefix {s with header := w} (emptyStk H))
      (atLabel H .reverseOutput {s with header := []} (emptyStk H))
      (w.length + 1) := by
  induction w with
  | nil => exact one H (clear_prefix_end_step H s)
  | cons b rest ih =>
    simpa [Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (clear_prefix_step H s b rest)) ih

private def reverseOutputRun (s : Tapes) (w out : Bits) :
    Run H (atLabel H .reverseOutput {s with accumulator := w, output := out} (emptyStk H))
      (config H none {s with accumulator := [], output := w.reverse ++ out} (emptyStk H))
      (w.length + 1) := by
  induction w generalizing out with
  | nil => exact one H (reverse_out_end_step H {s with output := out})
  | cons b rest ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm] using
      seq H (one H (reverse_out_step H {s with output := out} b rest))
        (ih (b :: out))

private def scanTapes (input header word acc : Bits) : Tapes where
  input := input
  header := header
  reversedWord := word
  accumulator := acc

private def scanCfg (input header word acc : Bits) : Config H :=
  atLabel H .scan (scanTapes input header word acc) (emptyStk H)

private def finalCfg (out : Bits) : Config H := config H none { output := out } (emptyStk H)

private def cleanup (header word acc : Bits) :
    Run H (atLabel H .clearWord (scanTapes [] header word acc) (emptyStk H))
      (finalCfg H acc.reverse) (word.length + header.length + acc.length + 3) := by
  let a := clearWordRun H (scanTapes [] header [] acc) word
  let b := clearHeaderRun H (scanTapes [] [] [] acc) header
  let c := reverseOutputRun H {} acc []
  simpa [finalCfg, scanTapes, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    seq H (seq H a b) c

private def callChunk (input header word acc : Bits) :
    let seed := header.reverse ++ word.reverse
    let y := M seed
    Run H (atLabel H .copyWord (scanTapes input header word acc) (emptyStk H))
      (scanCfg H input header [] (false :: ((quoteBits y).reverse ++ acc)))
      (word.length + 2 * header.length + H.time.eval seed.length + y.length + 4) := by
  dsimp only
  let a := copyWordRun H (scanTapes input header [] acc) word []
  let b := copyHeaderRun H (scanTapes input [] [] acc) header [] word.reverse
  let c := restoreHeaderRun H (scanTapes input [] [] acc) header.reverse [] (header.reverse ++ word.reverse)
  let d := callRun H (scanTapes input header [] acc) (header.reverse ++ word.reverse)
  let e := collectRun H (scanTapes input header [] []) (M (header.reverse ++ word.reverse)) acc
  have a' : Run H (atLabel H .copyWord (scanTapes input header word acc) (emptyStk H))
      (atLabel H .copyPrefix (scanTapes input header [] acc) (inputStk H word.reverse))
      (word.length + 1) := by
    simpa [scanTapes] using a
  have b' : Run H (atLabel H .copyPrefix (scanTapes input header [] acc) (inputStk H word.reverse))
      (atLabel H .restorePrefix {scanTapes input [] [] acc with savedPrefix := header.reverse}
        (inputStk H (header.reverse ++ word.reverse))) (header.length + 1) := by
    simpa [scanTapes] using b
  have c' : Run H (atLabel H .restorePrefix {scanTapes input [] [] acc with savedPrefix := header.reverse}
        (inputStk H (header.reverse ++ word.reverse)))
      (config H (some (.inl H.tm.main)) (scanTapes input header [] acc)
        (inputStk H (header.reverse ++ word.reverse))) (header.length + 1) := by
    simpa [scanTapes] using c
  have e' : Run H (atLabel H .collect (scanTapes input header [] acc)
        (outputStk H (M (header.reverse ++ word.reverse))))
      (scanCfg H input header [] (false :: ((quoteBits (M (header.reverse ++ word.reverse))).reverse ++ acc)))
      ((M (header.reverse ++ word.reverse)).length + 1) := by
    simpa [scanCfg, scanTapes] using e
  exact relax H (seq H (seq H (seq H (seq H a' b') c') d) e') (by omega)

/-- A truncated final word is ignored. Earlier complete words are still evaluated. -/
def decodeWordsAux : Bits → Bits → List Bits
  | [], _ => []
  | false :: rest, word => word.reverse :: decodeWordsAux rest []
  | [true], _ => []
  | true :: bit :: rest, word => decodeWordsAux rest (bit :: word)

@[simp] private theorem quoteBits_length (w : Bits) : (quoteBits w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b rest ih =>
    simp [quoteBits, Nat.mul_succ, Nat.add_comm]
    omega

private def outputBound (L : ℕ) : ℕ :=
  L + Turing.TM2Comp.maxPushCount₁ H * H.time.eval L

private def scanBudget (L : ℕ) : ℕ := 6 + 2 * L + H.time.eval L + 3 * outputBound H L

private theorem scanBudget_ge (L : ℕ) : 6 ≤ scanBudget H L := by unfold scanBudget; omega

private theorem length_le_outputBound (seed : Bits) {L : ℕ} (h : seed.length ≤ L) :
    (M seed).length ≤ outputBound H L := by
  have hLen : (M seed).length ≤ seed.length + Turing.TM2Comp.maxPushCount₁ H *
      (H.outputsFun seed).toEvalsTo.steps := by
    simpa using Turing.TM2Comp.evalsTo_out_len_le H seed
  exact hLen.trans (Nat.add_le_add h (Nat.mul_le_mul_left _
    ((H.outputsFun seed).steps_le_m.trans (Turing.TM2Comp.Polynomial.eval_mono_nat h))))

set_option maxHeartbeats 1500000 in
private def scanRun (L : ℕ) (input header word acc : Bits)
    (hLen : header.length + word.length + input.length ≤ L) :
    Run H (scanCfg H input header word acc)
      (finalCfg H (acc.reverse ++
        encodeWords ((decodeWordsAux input word).map (fun w => M (header.reverse ++ w)))))
      ((input.length + 1) * scanBudget H L + header.length + word.length + acc.length) := by
  cases hi : input with
  | nil =>
    have hStep := one H (scan_end_step H (scanTapes [] header word acc) [] (Or.inl rfl))
    have tr := seq H hStep (cleanup H header word acc)
    have hCost := scanBudget_ge H L
    have hCost' : 1 + (word.length + header.length + acc.length + 3) ≤
        scanBudget H L + header.length + word.length + acc.length := by omega
    simpa [decodeWordsAux, encodeWords, scanCfg, scanTapes] using relax H tr hCost'
  | cons marker rest =>
    cases hm : marker with
    | false =>
      simp only [hi, hm, List.length_cons] at hLen
      let seed := header.reverse ++ word.reverse
      let y := M seed
      let acc' := false :: ((quoteBits y).reverse ++ acc)
      have hRest : header.length + ([] : Bits).length + rest.length ≤ L := by
        simp only [List.length_nil]
        omega
      have hSeed : seed.length ≤ L := by simp [seed]; omega
      have hTime := Turing.TM2Comp.Polynomial.eval_mono_nat (p := H.time) hSeed
      have hy : y.length ≤ outputBound H L := length_le_outputBound H seed hSeed
      have hHdr : header.length ≤ L := by omega
      have hAcc : acc'.length = acc.length + 2 * y.length + 1 := by
        simp [acc', Nat.add_comm]
      have hReversed : acc'.reverse = acc.reverse ++ quoteBits y ++ [false] := by
        simp [acc', List.reverse_cons, List.reverse_append]
      have hOne : Run H (scanCfg H (false :: rest) header word acc)
          (atLabel H .copyWord (scanTapes rest header word acc) (emptyStk H)) 1 :=
        one H (scan_delimiter_step H (scanTapes rest header word acc) rest)
      let start := seq H hOne (callChunk H rest header word acc)
      let cont := scanRun L rest header [] acc' hRest
      have hCost :
          (1 + (word.length + 2 * header.length + H.time.eval seed.length + y.length + 4)) +
            ((rest.length + 1) * scanBudget H L + header.length + ([] : Bits).length + acc'.length)
          ≤ ((false :: rest).length + 1) * scanBudget H L + header.length + word.length + acc.length := by
        simp only [List.length_cons, List.length_nil, Nat.add_mul, Nat.one_mul, hAcc]
        unfold scanBudget
        omega
      simpa [decodeWordsAux, encodeWords, seed, y, hReversed, List.append_assoc] using
        relax H (seq H start cont) hCost
    | true =>
      cases hr : rest with
      | nil =>
        have hStep := one H (scan_end_step H (scanTapes [] header word acc) [true] (Or.inr rfl))
        have tr := seq H hStep (cleanup H header word acc)
        have hCost := scanBudget_ge H L
        have hCost' : 1 + (word.length + header.length + acc.length + 3) ≤
            2 * scanBudget H L + header.length + word.length + acc.length := by omega
        simpa [decodeWordsAux, encodeWords, scanCfg, scanTapes] using relax H tr hCost'
      | cons b rest =>
        have hRest : header.length + (b :: word).length + rest.length ≤ L := by
          simp only [hi, hm, hr, List.length_cons] at hLen ⊢
          omega
        have hOne : Run H (scanCfg H (true :: b :: rest) header word acc)
            (scanCfg H rest header (b :: word) acc) 1 :=
          one H (scan_bit_step H b rest (scanTapes rest header word acc) (emptyStk H))
        let cont := scanRun L rest header (b :: word) acc hRest
        have hCost := scanBudget_ge H L
        exact relax H (seq H hOne cont) (by
          simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega)
termination_by input.length
decreasing_by all_goals simp_all

/-- Read two unary fields and preserve exactly the consumed prefix. -/
def takeHeader : Bits → Bool → Bits × Option Bits
  | [], _ => ([], none)
  | bit :: rest, second =>
    if !bit && second then ([false], some rest)
    else
      let tail := takeHeader rest (second || !bit)
      (bit :: tail.1, tail.2)

private theorem takeHeader_length (w : Bits) (second : Bool) :
    (takeHeader w second).1.length + ((takeHeader w second).2.map List.length).getD 0 =
      w.length := by
  induction w generalizing second with
  | nil => rfl
  | cons b rest ih =>
    have ht := ih true
    have hf := ih false
    cases second <;> cases b <;> simp [takeHeader] <;> omega

private def headerResult (header : Bits) (rest : Option Bits) : Config H :=
  match rest with
  | none => atLabel H .clearWord (scanTapes [] header [] []) (emptyStk H)
  | some input => scanCfg H input header [] []

private def headerRun (w header : Bits) (second : Bool) :
    Run H (atLabel H (.readHeader second) (scanTapes w header [] []) (emptyStk H))
      (headerResult H ((takeHeader w second).1.reverse ++ header) (takeHeader w second).2)
      (w.length + 1) := by
  induction w generalizing second header with
  | nil => exact one H (prefix_end_step H second (scanTapes [] header [] []) (emptyStk H))
  | cons b rest ih =>
    have stepOne := one H (prefix_bit_step H second b rest (scanTapes rest header [] []) (emptyStk H))
    cases b with
    | true =>
      simpa [takeHeader, scanTapes, List.reverse_cons, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm] using seq H stepOne (ih (true :: header) second)
    | false =>
      cases second with
      | false =>
        simpa [takeHeader, scanTapes, List.reverse_cons, List.append_assoc, Nat.add_comm,
          Nat.add_left_comm] using seq H stepOne (ih (false :: header) true)
      | true =>
        exact relax H stepOne (by simp)

private def batchEval (M : Bits → Bits) (w : Bits) : Bits :=
  let hdr := takeHeader w false
  match hdr.2 with
  | none => []
  | some xs => encodeWords ((decodeWordsAux xs []).map (fun x => M (hdr.1 ++ x)))

private def batchTime : Polynomial ℕ :=
  ((Polynomial.X : Polynomial ℕ) + 1) *
    (Polynomial.C 9 + Polynomial.C 5 * Polynomial.X +
      Polynomial.C (1 + 3 * Turing.TM2Comp.maxPushCount₁ H) * H.time)

private theorem batchTime_eval (L : ℕ) :
    (batchTime H).eval L = (L + 1) * (scanBudget H L + 3) := by
  simp [batchTime, scanBudget, outputBound]
  ring

private def batchRun (w : Bits) :
    Run H (atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H))
      (finalCfg H (batchEval M w)) ((batchTime H).eval w.length) := by
  rw [batchTime_eval]
  have hHead := headerRun H w [] false
  have hSize := takeHeader_length w false
  cases he : takeHeader w false with
  | mk header payload =>
    rw [he] at hHead hSize
    cases payload with
    | none =>
      have hLarge := scanBudget_ge H w.length
      have hStart : Run H (atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H))
          (atLabel H .clearWord (scanTapes [] header.reverse [] []) (emptyStk H)) (w.length + 1) := by
        simpa [headerResult] using hHead
      have hc := cleanup H header.reverse [] []
      have hRun := seq H hStart hc
      have hScale : scanBudget H w.length ≤ (w.length + 1) * scanBudget H w.length :=
        Nat.le_mul_of_pos_left _ (by omega)
      simp only [Option.map_none, Option.getD_none, Nat.add_zero] at hSize
      have hCost : (w.length + 1) + (([] : Bits).length + header.reverse.length +
          ([] : Bits).length + 3) ≤ (w.length + 1) * (scanBudget H w.length + 3) := by
        simp [List.length_reverse, hSize, Nat.mul_add]
        omega
      simpa [batchEval, he] using relax H hRun hCost
    | some input =>
      have hLen : header.reverse.length + ([] : Bits).length + input.length ≤ w.length := by
        simpa using hSize.le
      have hTail := scanRun H w.length input header.reverse [] [] hLen
      have hStart : Run H (atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H))
          (scanCfg H input header.reverse [] []) (w.length + 1) := by
        simpa [headerResult] using hHead
      have hScale : (input.length + 1) * scanBudget H w.length ≤
          (w.length + 1) * scanBudget H w.length :=
        Nat.mul_le_mul_right _ (by simp at hSize; omega)
      have hCost :
          (w.length + 1) +
          ((input.length + 1) * scanBudget H w.length + header.reverse.length +
            ([] : Bits).length + ([] : Bits).length) ≤
          (w.length + 1) * (scanBudget H w.length + 3) := by
        simp only [List.length_reverse, List.length_nil, Nat.add_zero, Nat.mul_add]
        simp at hSize
        omega
      simpa [batchEval, he] using relax H (seq H hStart hTail) hCost

private theorem cfg_eq {a b : Config H} (hl : a.l = b.l) (hv : a.var = b.var)
    (hs : ∀ k, a.stk k = b.stk k) : a = b := by
  have hstk := funext hs
  cases a
  cases b
  cases hl
  cases hv
  cases hstk
  rfl

private theorem initial (w : Bits) :
    initList (machine H) w =
      atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H) := by
  refine cfg_eq H (a := initList (machine H) w)
    (b := atLabel H (.readHeader false) (scanTapes w [] [] []) (emptyStk H)) rfl rfl ?_
  intro k
  cases k with
  | inl k => simp [initList, machine, config, BatchSubmissionCall.stackUnion, emptyStk]
  | inr k => cases k <;> simp [initList, machine, config, BatchSubmissionCall.stackUnion, scanTapes, Tapes.stk]

private theorem terminal (w : Bits) : haltList (machine H) w = finalCfg H w := by
  refine cfg_eq H (a := haltList (machine H) w) (b := finalCfg H w) rfl rfl ?_
  intro k
  cases k with
  | inl k => simp [haltList, machine, finalCfg, config, BatchSubmissionCall.stackUnion, emptyStk]
  | inr k => cases k <;> simp [haltList, machine, finalCfg, config, BatchSubmissionCall.stackUnion, Tapes.stk]

private def certificate : Witness (batchEval M) where
  tm := machine H
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := batchTime H
  outputsFun w := by
    change Run H (initList (machine H) (w.map id))
      (haltList (machine H) ((batchEval M w).map id)) ((batchTime H).eval w.length)
    simpa only [List.map_id, initial, terminal] using batchRun H w

private theorem takeHeader_replicate (n : ℕ) (w : Bits) (second : Bool) :
    takeHeader (List.replicate n true ++ w) second =
      (List.replicate n true ++ (takeHeader w second).1, (takeHeader w second).2) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, takeHeader, ih]

private theorem takeHeader_encAdvice (n a : ℕ) (w : Bits) :
    takeHeader (encAdvice n a w) false = (encAdvice n a [], some w) := by
  simp [encAdvice, enc, takeHeader_replicate, takeHeader]

private theorem decode_quote_append (w acc suffix : Bits) :
    decodeWordsAux (quoteBits w ++ false :: suffix) acc =
      (acc.reverse ++ w) :: decodeWordsAux suffix [] := by
  induction w generalizing acc with
  | nil => simp [quoteBits, decodeWordsAux]
  | cons b rest ih =>
    change decodeWordsAux (quoteBits rest ++ false :: suffix) (b :: acc) = _
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

private theorem decode_encode (words : List Bits) :
    decodeWordsAux (encodeWords words) [] = words := by
  induction words with
  | nil => rfl
  | cons w rest ih =>
    simp only [encodeWords, List.flatMap_cons, List.append_assoc, List.singleton_append]
    rw [decode_quote_append]
    simpa [encodeWords] using ih

/-- Run an arbitrary certified evaluator on each escaped word with the same
security parameter and advice, preserving word boundaries in the output. -/
theorem batchCalls : BatchCallsContract := by
  intro M hM
  obtain ⟨H⟩ := hM
  refine ⟨batchEval M, ⟨certificate H⟩, ?_⟩
  intro n a words
  unfold batchEval
  rw [takeHeader_encAdvice]
  simp only [decode_encode]
  simp [encAdvice, enc, List.append_assoc]

end

end HILL.PRG.BatchSubmission

theorem solution (M : Bits → Bits) (hM : PolyTimeComputable M) :
    let quoteBits := fun (w : Bits) => w.flatMap (fun b => [true, b])
    let encodeWords := fun (ws : List Bits) => ws.flatMap (fun w => quoteBits w ++ [false])
    ∃ B : Bits → Bits, PolyTimeComputable B ∧
      ∀ (n a : ℕ) (xs : List Bits),
        B (encAdvice n a (encodeWords xs)) =
          encodeWords (xs.map (fun x => M (encAdvice n a x))) := by
  exact HILL.PRG.BatchSubmission.batchCalls M hM
