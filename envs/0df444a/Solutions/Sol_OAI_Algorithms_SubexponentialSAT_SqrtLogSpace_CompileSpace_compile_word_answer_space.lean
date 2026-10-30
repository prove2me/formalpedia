-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:46:52.764213+00:00
-- url     : https://prove2.me/submissions/f6082ac7-0324-41b5-95d2-52f079b715e3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-width binary encodings of finite stack alphabets

The primary representation has no appended binary sentinel: the tape alphabet
is `Option Bool`, data bits are wrapped in `some`, and `none` is blank. Thus a
Boolean input stack can use width one and needs no initialization scan.

An explicit binary bottom-marker representation is also provided separately.
No theorem in this file assigns a Turing-machine cost to list operations.
-/

namespace SubexponentialSAT.StackEncoding

universe u

/-- Removing one complete block is the encoding of stack pop, including empty
stacks. No partial-block boundary occurs. -/
theorem drop_width_eq_tail {α : Type u} (c : BlockCode α) (s : List α) :
    (encodeDataStack c s).drop c.width = encodeDataStack c s.tail := by
  cases s with
  | nil => simp
  | cons a s => exact drop_width_cons c a s

end SubexponentialSAT.StackEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
Actual primitive tape programs for encoded stacks. Every instruction below is
one move or one write of `Computation.PrimitiveMachine`; the measured traces
are derived from that transition function.
-/

namespace SubexponentialSAT.StackMachine

open Turing SubexponentialSAT.Computation

theorem execute_append (first second : List Action) (tape : BitTape) :
    execute (first ++ second) tape = execute second (execute first tape) := by
  induction first generalizing tape with
  | nil => rfl
  | cons action rest ih => exact ih (applyAction action tape)

theorem push_bit (bit : Bool) (bits : List Bool) :
    ((dataTape bits).move .left).write (some bit) = dataTape (bit :: bits) := by
  unfold dataTape Tape.mk₁ Tape.mk₂
  rw [Tape.move_left_mk']
  change (Tape.mk' (ListBlank.mk []) ((ListBlank.mk (bits.map some)).cons none)).write
    (some bit) = _
  rw [Tape.write_mk']
  rfl

theorem pop_bit (bit : Bool) (bits : List Bool) :
    ((dataTape (bit :: bits)).write none).move .right = dataTape bits := by
  unfold dataTape Tape.mk₁ Tape.mk₂
  change ((Tape.mk' (ListBlank.mk [])
    ((ListBlank.mk (bits.map some)).cons (some bit))).write none).move .right = _
  rw [Tape.write_mk', Tape.move_right_mk']
  simp only [ListBlank.head_cons, ListBlank.tail_cons]
  have hblank : (ListBlank.mk ([] : List (Option Bool))).cons none = ListBlank.mk [] := by
    have hdefault : (default : Option Bool) = none := rfl
    simpa [hdefault] using
      ListBlank.cons_head_tail (ListBlank.mk ([] : List (Option Bool)))
  rw [hblank]

theorem execute_pushBits (bits tail : List Bool) :
    execute (pushBits bits) (dataTape tail) = dataTape (bits ++ tail) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [pushBits, execute_append, ih, execute_cons, execute_nil, applyAction]
    exact push_bit bit (bits ++ tail)

/-! Reindexing a genuinely finite controller changes no primitive actions. -/

universe u

theorem controlStep_action {Q : Type u} {t : ℕ} (p : Controller Q t)
    (q q' : Q) (action : Action) (tapes : Fin t → BitTape)
    (h : p.transition q (tapes (p.scan q)).head = .inr (q', action)) :
    controlStep p ⟨.inr q, tapes⟩ = some ⟨.inr q',
      Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩ := by
  simp only [controlStep, h]

theorem controlStep_halt {Q : Type u} {t : ℕ} (p : Controller Q t)
    (q : Q) (answer : Bool) (tapes : Fin t → BitTape)
    (h : p.transition q (tapes (p.scan q)).head = .inl answer) :
    controlStep p ⟨.inr q, tapes⟩ = some ⟨.inl answer, tapes⟩ := by
  simp only [controlStep, h]

theorem reindex_step {Q : Type u} {t n : ℕ} (e : Q ≃ Fin n)
    (p : Controller Q t) (c : ControlCfg Q t) :
    (reindex e p).step (reindexCfg e p c) = (controlStep p c).map (reindexCfg e p) := by
  rcases c with ⟨state, tapes⟩
  cases state with
  | inl b => rfl
  | inr q =>
    simp only [PrimitiveMachine.step, reindexCfg, reindex, controlStep,
      Equiv.symm_apply_apply]
    cases h : p.transition q (tapes (p.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨q', action⟩
      cases action <;> rfl

/-! A block reader uses one right move per bit, stores the observed bit in its
finite control, then performs the same number of left moves. -/

/-! Connecting the physical routines to the fixed alphabet encodings. -/

open SubexponentialSAT.StackEncoding

theorem pop_blank : ((dataTape []).write none).move .right = dataTape [] := by
  have hblank : (ListBlank.mk ([] : List (Option Bool))).cons none = ListBlank.mk [] := by
    have hdefault : (default : Option Bool) = none := rfl
    simpa [hdefault] using
      ListBlank.cons_head_tail (ListBlank.mk ([] : List (Option Bool)))
  change (Tape.mk' (ListBlank.mk []) (ListBlank.mk [])).move .right = _
  rw [Tape.move_right_mk']
  change Tape.mk' ((ListBlank.mk []).cons none) (ListBlank.mk []) = _
  rw [hblank]
  rfl

theorem execute_popBits_drop (n : ℕ) (bits : List Bool) :
    execute (popBits n) (dataTape bits) = dataTape (bits.drop n) := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    cases bits with
    | nil =>
      simpa only [popBits, execute_append, execute_cons, execute_nil, applyAction,
        pop_blank, List.drop_nil] using ih []
    | cons bit bits =>
      simpa only [popBits, execute_append, execute_cons, execute_nil, applyAction,
        pop_bit, List.drop_succ_cons] using ih bits

theorem dataTape_input {α : Type u} (e : α ≃ Bool) (input : List Bool) :
    dataTape (encodeDataStack (codeOfBoolEquiv e) (input.map e.symm)) =
      Tape.mk₁ (input.map some) := by
  rw [encodeDataStack_codeOfBoolEquiv]
  simp [dataTape, List.map_map]

/-! Inlining into a larger finite controller. The hypotheses below are
single-instruction transition-table equations, not assumed execution bounds.
They allow the final local control index to denote any caller continuation. -/

end SubexponentialSAT.StackMachine

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackCompiler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
A global finite controller for one-head finite stack programs. A source step
first inspects one finite-alphabet stack top, then changes finite control and
keeps, pops, or pushes that stack. The compiled controller performs only the
primitive bit reads, moves, and writes of StackMachine.controlStep.
-/

namespace SubexponentialSAT.StackCompiler

open Turing SubexponentialSAT.Computation SubexponentialSAT.StackMachine SubexponentialSAT.StackEncoding

theorem mutationActions_correct {α : Type} (code : BlockCode α)
    (op : Mutation α) (stack : List α) :
    execute (mutationActions code op) (dataTape (encodeDataStack code stack)) =
      dataTape (encodeDataStack code (op.apply stack)) := by
  cases op with
  | keep => rfl
  | pop =>
      simpa [mutationActions, Mutation.apply, drop_width_eq_tail] using
        execute_popBits_drop code.width (encodeDataStack code stack)
  | push a =>
      simpa [mutationActions, Mutation.apply, encodeDataStack_cons] using
        execute_pushBits (code.block a) (encodeDataStack code stack)

section FiniteController

variable {Q : Type} [Fintype Q] {t : ℕ} {Γ : Fin t → Type}
  [∀ k, Fintype (Γ k)]
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))

/-- Width-one input coding identifies the simulated input with the physical raw input. -/
theorem compiled_initial (inputAlphabet : Γ p.inputTape ≃ Bool)
    (code_input : codes p.inputTape = codeOfBoolEquiv inputAlphabet)
    (input : List Bool) :
    compiledCfg p codes decode (initialCfg p inputAlphabet input) =
      (compiledMachine p codes decode).init input := by
  have htapes :
      tapeEncoding codes (initialCfg p inputAlphabet input) =
        fun k => if k = p.inputTape then Tape.mk₁ (input.map some) else Tape.mk₁ [] := by
    funext k
    by_cases hk : k = p.inputTape
    · subst k
      simp only [tapeEncoding, initialCfg, Function.update_self, code_input, ↓reduceIte]
      exact dataTape_input inputAlphabet input
    · simp [tapeEncoding, initialCfg, hk, dataTape]
  unfold compiledCfg reindexCfg encodeCfg
  rw [htapes]
  rfl

theorem compiled_terminal (a : StackCfg Q Γ) (answer : Bool)
    (ha : a.state = .inl answer) :
    (compiledCfg p codes decode a).state = .inl answer := by
  unfold compiledCfg reindexCfg encodeCfg
  rw [ha]
  rfl

end FiniteController

end SubexponentialSAT.StackCompiler

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_VisitedTape
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Passive absolute-coordinate instrumentation for the primitive machine.
The interval on every tape includes its initial input cells and every visited
head coordinate. The instrumentation never changes a primitive transition. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation
open scoped BigOperators

theorem headDisplacement_bounds (action : Turing.TM0.Stmt (Option Bool)) :
    -1 ≤ headDisplacement action ∧ headDisplacement action ≤ 1 := by
  cases action with
  | move direction => cases direction <;> decide
  | write symbol =>
      change (-1 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ 1
      decide

theorem locatedStep_position_action {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {q next : Fin machine.stateCount}
    {action : Turing.TM0.Stmt (Option Bool)}
    (hs : locatedStep machine c = some d) (hq : c.config.state = .inr q)
    (ha : machine.transition q (c.config.tapes (machine.scan q)).head = .inr (next, action)) :
    d.position = Function.update c.position (machine.scan q)
      (c.position (machine.scan q) + headDisplacement action) := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  simp [LocatedCfg.monitor, hq, ha]

theorem locatedStep_position_halt {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {q : Fin machine.stateCount} {answer : Bool}
    (hs : locatedStep machine c = some d) (hq : c.config.state = .inr q)
    (ha : machine.transition q (c.config.tapes (machine.scan q)).head = .inl answer) :
    d.position = c.position := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  simp [LocatedCfg.monitor, hq, ha]

theorem locatedStep_position_bounds {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (i : Fin machine.tapeCount) :
    c.position i - 1 ≤ d.position i ∧ d.position i ≤ c.position i + 1 := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases hs : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hs]
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hs, ht]
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hs, ht, Function.update_self]
            have h := headDisplacement_bounds action
            omega
          · simp [LocatedCfg.monitor, hs, ht, Function.update_of_ne hi]

theorem locatedTrace_position_bounds {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) (i : Fin machine.tapeCount) :
    c.position i - (steps : ℤ) ≤ d.position i ∧
      d.position i ≤ c.position i + (steps : ℤ) := by
  induction tr with
  | refl => simp
  | cons hs _ ih =>
      have h := locatedStep_position_bounds hs i
      omega

theorem locatedStep_expands {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (i : Fin machine.tapeCount) :
    d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  cases hstate : c.config.state with
  | inl answer => simp [LocatedCfg.monitor, hstate]
  | inr q =>
      cases htransition : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simp [LocatedCfg.monitor, hstate, htransition]
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hstate, htransition, Function.update_self]
          · simp [LocatedCfg.monitor, hstate, htransition, Function.update_of_ne hi]

theorem locatedStep_envelope {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (hs : locatedStep machine c = some d) (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ i, lower i ≤ d.position i ∧ d.position i ≤ upper i) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  obtain ⟨config, _, rfl⟩ := Option.map_eq_some_iff.mp hs
  intro i
  have hc' := hc i
  have hp' := hp i
  cases hs : c.config.state with
  | inl answer => simpa [LocatedCfg.monitor, hs] using hc'
  | inr q =>
      cases ht : machine.transition q (c.config.tapes (machine.scan q)).head with
      | inl answer => simpa [LocatedCfg.monitor, hs, ht] using hc'
      | inr result =>
          obtain ⟨next, action⟩ := result
          by_cases hi : i = machine.scan q
          · subst i
            simp [LocatedCfg.monitor, hs, ht, Function.update_self] at hp' ⊢
            exact ⟨⟨hc'.1, hp'.1⟩, hc'.2, hp'.2⟩
          · simpa [LocatedCfg.monitor, hs, ht, Function.update_of_ne hi] using hc'

theorem locatedTrace_expands {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (tr : Computation.Trace (locatedStep machine) steps c d)
    (i : Fin machine.tapeCount) :
    d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i := by
  induction tr with
  | refl => exact ⟨le_rfl, le_rfl⟩
  | cons hs _ ih =>
      have h := locatedStep_expands hs i
      exact ⟨ih.1.trans h.1, h.2.trans ih.2⟩

theorem visitedSpace_mono {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    (h : ∀ i, d.lower i ≤ c.lower i ∧ c.upper i ≤ d.upper i) :
    visitedSpace c ≤ visitedSpace d := by
  apply Finset.sum_le_sum
  intro i _
  apply Int.toNat_le_toNat
  have hi := h i
  omega

theorem locatedTrace_visitedSpace_mono {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) :
    visitedSpace c ≤ visitedSpace d :=
  visitedSpace_mono (locatedTrace_expands tr)

theorem trace_suffix {α : Type*} {step : α → Option α}
    {c d intermediate : α} {steps prefixSteps : ℕ}
    (tr : Computation.Trace step steps c d)
    (hp : Computation.Trace step prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) :
    Computation.Trace step (steps - prefixSteps) intermediate d := by
  apply Computation.Trace.of_iterate
  have h := tr.iterate
  conv_lhs at h => rw [← Nat.sub_add_cancel hle]
  rw [Function.iterate_add_apply, hp.iterate] at h
  exact h

theorem locatedTrace_prefix_space {machine : PrimitiveMachine}
    {c d intermediate : LocatedCfg machine} {steps prefixSteps : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d)
    (hp : Computation.Trace (locatedStep machine) prefixSteps c intermediate)
    (hle : prefixSteps ≤ steps) : visitedSpace intermediate ≤ visitedSpace d :=
  locatedTrace_visitedSpace_mono (trace_suffix tr hp hle)

theorem locatedTrace_envelope {machine : PrimitiveMachine} {c d : LocatedCfg machine}
    {steps : ℕ} (tr : Computation.Trace (locatedStep machine) steps c d)
    (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Computation.Trace (locatedStep machine) prefixSteps c intermediate →
      ∀ i, lower i ≤ intermediate.position i ∧ intermediate.position i ≤ upper i) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  induction tr with
  | refl => exact hc
  | @cons steps c next final hs ht ih =>
      apply ih
      · exact locatedStep_envelope hs lower upper hc
          (hp 1 next (by omega) (.cons hs (.refl next)))
      · intro prefixSteps intermediate hle htr
        exact hp (prefixSteps + 1) intermediate (by omega) (.cons hs htr)

theorem locatedTrace_envelope_of_margin {machine : PrimitiveMachine}
    {c d : LocatedCfg machine} {steps budget : ℕ}
    (tr : Computation.Trace (locatedStep machine) steps c d) (ht : steps ≤ budget)
    (lower upper : Fin machine.tapeCount → ℤ)
    (hc : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i)
    (hp : ∀ i, lower i + (budget : ℤ) ≤ c.position i ∧
      c.position i ≤ upper i - (budget : ℤ)) :
    ∀ i, lower i ≤ d.lower i ∧ d.upper i ≤ upper i := by
  apply locatedTrace_envelope tr lower upper hc
  intro prefixSteps intermediate hle htr i
  have hmove := locatedTrace_position_bounds htr i
  have hstart := hp i
  omega

theorem visitedSpace_le_of_envelope {machine : PrimitiveMachine}
    (c : LocatedCfg machine) (lower upper : Fin machine.tapeCount → ℤ)
    (h : ∀ i, lower i ≤ c.lower i ∧ c.upper i ≤ upper i) :
    visitedSpace c ≤ ∑ i, (upper i - lower i + 1).toNat := by
  apply Finset.sum_le_sum
  intro i _
  apply Int.toNat_le_toNat
  have hi := h i
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_GuardedCompiler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A width-one compilation of Boolean programs, with empty pop guarded before
the primitive stack compiler. The output contract reads the entire tape. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.StackCompiler OAI.Algorithms.SubexponentialSAT.StackEncoding OAI.Algorithms.SubexponentialSAT.StackMachine
open scoped BigOperators

theorem guardedPop_apply (bits : List Bool) :
    (guardedPop bits.head?).apply bits = bits.tail := by
  cases bits <;> rfl

theorem transition_empty_ne_pop {r s l : ℕ} (p : BitProgram.Program r s l)
    (q q' : State r l) : transition p q none ≠ .inr (q', .pop) := by
  cases h : p.code q.1 <;> simp [transition, h, guardedPop]

theorem push_actions (bit : Bool) :
    mutationActions boolCode (.push bit) = [.move .left, .write (some bit)] := rfl

theorem pop_actions : mutationActions boolCode .pop = [.write none, .move .right] := rfl

theorem mutation_displacement (displacement : Action → ℤ)
    (left : displacement (.move .left) = -1)
    (right : displacement (.move .right) = 1)
    (write : ∀ bit, displacement (.write bit) = 0)
    (op : Mutation Bool) (bits : List Bool) (safe : op = .pop → bits ≠ []) :
    ((mutationActions boolCode op).map displacement).sum =
      (bits.length : ℤ) - (op.apply bits).length := by
  cases op with
  | keep => simp [mutationActions, Mutation.apply]
  | pop =>
      cases bits with
      | nil => exact False.elim (safe rfl rfl)
      | cons bit bits => simp [pop_actions, Mutation.apply, right, write]
  | push bit => simp [push_actions, Mutation.apply, left, write]

theorem transition_mutation_displacement {r s l : ℕ} (p : BitProgram.Program r s l)
    (q q' : State r l) (op : Mutation Bool) (bits : List Bool)
    (h : transition p q bits.head? = .inr (q', op))
    (displacement : Action → ℤ)
    (left : displacement (.move .left) = -1)
    (right : displacement (.move .right) = 1)
    (write : ∀ bit, displacement (.write bit) = 0) :
    ((mutationActions boolCode op).map displacement).sum =
      (bits.length : ℤ) - (op.apply bits).length := by
  apply mutation_displacement displacement left right write
  intro hop hempty
  subst op
  subst bits
  exact transition_empty_ne_pop p q q' h

theorem stack_step {r s l : ℕ} (p : BitProgram.Program r s l) (c : BitProgram.Cfg r s l) :
    stackStep (stackProgram p) (stackCfg p c) = (BitProgram.step p c).map (stackCfg p) := by
  rcases c with ⟨pc, regs, stk⟩
  cases pc with
  | none => rfl
  | some label =>
      cases h : p.code label <;>
        simp [stackStep, stackProgram, stackCfg, selected, transition, h,
          BitProgram.step, BitProgram.execInstr, Mutation.apply,
          Function.update_eq_self]
      exact congrArg (Function.update stk _) (guardedPop_apply _)

theorem primitive_initial {r s l : ℕ} (p : BitProgram.Program r s l) (input : List Bool) :
    primitiveCfg p (BitProgram.initial p input) = (primitive p).init input := by
  have h : stackCfg p (BitProgram.initial p input) =
      initialCfg (stackProgram p) (Equiv.refl Bool) input := by
    simp [stackCfg, initialCfg, stackProgram,
      Function.update_apply, funext_iff]
  unfold primitiveCfg primitive
  rw [h]
  exact compiled_initial (stackProgram p) (codes s) (decoder s) (Equiv.refl Bool) rfl input

theorem tapeEncoding_bool {r s l : ℕ}
    (a : StackCfg (State r l) (fun _ : Fin s => Bool)) :
    StackCompiler.tapeEncoding (codes s) a = fun i => dataTape (a.stk i) := by
  funext i
  exact congrArg dataTape (encodeDataStack_boolCode (a.stk i))

theorem primitive_tape {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) (i : Fin s) :
    (primitiveCfg p c).tapes i = Turing.Tape.mk₁ ((c.stacks i).map some) := by
  change dataTape (encodeDataStack boolCode (c.stacks i)) = _
  rw [encodeDataStack_boolCode]
  rfl

theorem primitive_halted {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) (h : c.pc = none) :
    (primitiveCfg p c).state = .inl ((c.stacks p.outputStack).head?.getD false) := by
  apply compiled_terminal
  simp [stackCfg, h]

theorem reindex_located_action {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t)
    (c : LocatedCfg (reindex e p)) (q q' : Q) (action : Action)
    (tapes : Fin t → BitTape)
    (hc : c.config = reindexCfg e p ⟨.inr q, tapes⟩)
    (ha : p.transition q (tapes (p.scan q)).head = .inr (q', action)) :
    ∃ d : LocatedCfg (reindex e p),
      locatedStep (reindex e p) c = some d ∧
      d.config = reindexCfg e p
        ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩ ∧
      d.position = Function.update c.position (p.scan q)
        (c.position (p.scan q) + headDisplacement action) := by
  have hs : (reindex e p).step c.config = some (reindexCfg e p
      ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩) := by
    rw [hc, reindex_step, controlStep_action p q q' action tapes ha]
    rfl
  let d := c.monitor (reindexCfg e p
    ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩)
  have hstep : locatedStep (reindex e p) c = some d := by
    rw [locatedStep, hs]
    rfl
  refine ⟨d, hstep, c.monitor_config _, ?_⟩
  have htransition : (reindex e p).transition (e q)
      (c.config.tapes ((reindex e p).scan (e q))).head = .inr (e q', action) := by
    simp only [hc, reindexCfg, reindex, Equiv.symm_apply_apply, ha]
  have hposition := locatedStep_position_action hstep
    (show c.config.state = .inr (e q) by rw [hc]; rfl) htransition
  simpa only [reindex, Equiv.symm_apply_apply] using hposition

theorem reindex_located_halt {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t)
    (c : LocatedCfg (reindex e p)) (q : Q) (answer : Bool)
    (tapes : Fin t → BitTape)
    (hc : c.config = reindexCfg e p ⟨.inr q, tapes⟩)
    (ha : p.transition q (tapes (p.scan q)).head = .inl answer) :
    ∃ d : LocatedCfg (reindex e p),
      locatedStep (reindex e p) c = some d ∧
      d.config = reindexCfg e p ⟨.inl answer, tapes⟩ ∧ d.position = c.position := by
  have hs : (reindex e p).step c.config =
      some (reindexCfg e p ⟨.inl answer, tapes⟩) := by
    rw [hc, reindex_step, controlStep_halt p q answer tapes ha]
    rfl
  let d := c.monitor (reindexCfg e p ⟨.inl answer, tapes⟩)
  have hstep : locatedStep (reindex e p) c = some d := by
    rw [locatedStep, hs]
    rfl
  refine ⟨d, hstep, c.monitor_config _, ?_⟩
  apply locatedStep_position_halt (answer := answer) hstep
    (show c.config.state = .inr (e q) by rw [hc]; rfl)
  simp only [hc, reindexCfg, reindex, Equiv.symm_apply_apply, ha]

theorem reindex_located_fragment {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t) (count : ℕ)
    (state : ℕ → Q) (tapes : ℕ → Fin t → BitTape) (actions : ℕ → Action) (k : Fin t)
    (scan : ∀ i < count, p.scan (state i) = k)
    (next : ∀ i < count,
      p.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)))
    (c : LocatedCfg (reindex e p))
    (hc : c.config = reindexCfg e p ⟨.inr (state 0), tapes 0⟩) :
    ∃ d : LocatedCfg (reindex e p),
      Trace (locatedStep (reindex e p)) count c d ∧
      d.config = reindexCfg e p ⟨.inr (state count), tapes count⟩ ∧
      d.position = Function.update c.position k
        (c.position k + ∑ i ∈ Finset.range count, headDisplacement (actions i)) := by
  have prefixTrace (n : ℕ) (hn : n ≤ count) :
      ∃ d : LocatedCfg (reindex e p),
        Trace (locatedStep (reindex e p)) n c d ∧
        d.config = reindexCfg e p ⟨.inr (state n), tapes n⟩ ∧
        d.position = Function.update c.position k
          (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)) := by
    induction n with
    | zero =>
        refine ⟨c, .refl c, hc, ?_⟩
        simp only [Finset.sum_range_zero, add_zero]
        change (fun i : Fin t => c.position i) =
          Function.update (fun i : Fin t => c.position i) k (c.position k)
        exact (Function.update_eq_self k (fun i : Fin t => c.position i)).symm
    | succ n ih =>
        have hlt : n < count := by omega
        obtain ⟨middle, htrace, hconfig, hposition⟩ := ih (by omega)
        obtain ⟨ha, htapes⟩ := next n hlt
        obtain ⟨d, hstep, hdconfig, hdposition⟩ := reindex_located_action e p middle
          (state n) (state (n + 1)) (actions n) (tapes n) hconfig
          (by simpa only [scan n hlt] using ha)
        refine ⟨d, htrace.trans (.cons hstep (.refl d)), ?_, ?_⟩
        · simpa only [scan n hlt, ← htapes] using hdconfig
        · rw [scan n hlt, hposition] at hdposition
          rw [hdposition]
          change Function.update
              (Function.update (fun i : Fin t => c.position i) k
                (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)))
              k
              (Function.update (fun i : Fin t => c.position i) k
                  (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)) k +
                headDisplacement (actions n)) =
            Function.update (fun i : Fin t => c.position i) k
              (c.position k + ∑ i ∈ Finset.range (n + 1), headDisplacement (actions i))
          funext i
          by_cases hi : i = k
          · subst i
            simp only [Function.update_self, Finset.sum_range_succ]
            rw [add_assoc]
          · simp only [Function.update_of_ne hi]
  exact prefixTrace count le_rfl

theorem mutation_located_trace {r s l : ℕ} (p : BitProgram.Program r s l)
    (k : Fin s) (q : State r l) (op : Mutation Bool)
    (base : Fin s → BitTape) (tape : BitTape)
    (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (actionCfg (stackProgram p) (codes s) k q op base 0 tape)) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) (mutationActions boolCode op).length c d ∧
      d.config = primitiveControlCfg p
        (actionCfg (stackProgram p) (codes s) k q op base
          ⟨(mutationActions boolCode op).length, Nat.lt_succ_self _⟩
          (execute (mutationActions boolCode op) tape)) ∧
      d.position = Function.update c.position k
        (c.position k + ((mutationActions boolCode op).map headDisplacement).sum) := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let state (i : ℕ) : StackCompiler.State (stackProgram p) (codes s) :=
    acting k q op ⟨min i 2, by
      change min i 2 < 3
      omega⟩
  let tapes (i : ℕ) := Function.update base k
    (execute ((mutationActions boolCode op).take i) tape)
  let actions (i : ℕ) := ((mutationActions boolCode op)[i]?).getD (.write none)
  have hscan : ∀ i < (mutationActions boolCode op).length, C.scan (state i) = k := by
    intro i _
    rfl
  have hnext : ∀ i < (mutationActions boolCode op).length,
      C.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)) := by
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi (mutationActions_length boolCode op)
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      cases op <;>
      simp_all [C, state, tapes, actions, controller, acting, codes, boolCode,
        codeOfBoolEquiv, mutationActions, pushBits, popBits, execute, applyAction,
        Function.update_idem]
  obtain ⟨d, htrace, hconfig, hposition⟩ := reindex_located_fragment e C
    (mutationActions boolCode op).length state tapes actions k hscan hnext c
    (by simpa [primitive, primitiveControlCfg, actionCfg, state, tapes, e, C] using hc)
  refine ⟨d, htrace, ?_, ?_⟩
  · cases op <;>
      simpa [primitive, primitiveControlCfg, actionCfg, state, tapes, e, C, codes,
        mutationActions, boolCode, codeOfBoolEquiv, pushBits, popBits] using hconfig
  · cases op <;>
      simpa [primitive, actions, mutationActions, boolCode, codeOfBoolEquiv, pushBits, popBits,
        Finset.sum_range_succ, headDisplacement] using hposition

theorem reader_located_trace {r s l : ℕ} (p : BitProgram.Program r s l)
    (q : State r l) (base : Fin s → BitTape) (tape : BitTape)
    (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (readCfg (stackProgram p) (codes s) q base (0, fun _ => none) tape)) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) 2 c d ∧
      d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => tape.head) tape) ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let k := selected p q
  let state (i : ℕ) : StackCompiler.State (stackProgram p) (codes s) :=
    reading q (⟨min i 2, by change min i 2 < 3; omega⟩,
      if i = 0 then fun _ => none else fun _ => tape.head)
  let tapes (i : ℕ) := Function.update base k (if i = 1 then tape.move .right else tape)
  let actions (i : ℕ) : Action := if i = 0 then .move .right else .move .left
  have hscan : ∀ i < 2, C.scan (state i) = k := by
    intro i _
    rfl
  have hnext : ∀ i < 2,
      C.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)) := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simp [C, state, tapes, actions, k, controller, reading, stackProgram,
        codes, boolCode, codeOfBoolEquiv, applyAction,
        Function.update_idem]
      congr 4
      congr 2
      funext x
      fin_cases x
      change Function.update (fun _ : Fin 1 => none) 0 tape.head 0 = tape.head
      exact Function.update_self 0 tape.head (fun _ : Fin 1 => none)
    · simp [C, state, tapes, actions, k, controller, reading, stackProgram,
        codes, boolCode, codeOfBoolEquiv, applyAction,
        Function.update_idem]
  obtain ⟨d, htrace, hconfig, hposition⟩ := reindex_located_fragment e C
    2 state tapes actions k hscan hnext c
    (by
      change c.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base (0, fun _ => none) tape)
      exact hc)
  refine ⟨d, htrace, ?_, ?_⟩
  · change d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => tape.head) tape)
    exact hconfig
  · rw [hposition]
    have hsum : ∑ i ∈ Finset.range 2, headDisplacement (actions i) = 0 := by
      norm_num [Finset.sum_range_succ, actions, headDisplacement]
    rw [hsum, add_zero]
    change Function.update (fun i : Fin s => c.position i) k (c.position k) =
      (fun i : Fin s => c.position i)
    exact Function.update_eq_self k (fun i : Fin s => c.position i)

theorem read_entry_located {r s l : ℕ} (p : BitProgram.Program r s l)
    (q : State r l) (base : Fin s → BitTape) (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p ⟨.inr (ready q), base⟩) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) 3 c d ∧
      d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => (base (selected p q)).head)
          (base (selected p q))) ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  obtain ⟨middle, hstep, hconfig, hposition⟩ := reindex_located_action e C c
    (ready q) (reading q (0, fun _ => none))
    (.write (base (selected p q)).head) base hc rfl
  have hscan : C.scan (ready q) = selected p q := rfl
  have hmiddle : middle.config = primitiveControlCfg p
      (readCfg (stackProgram p) (codes s) q base (0, fun _ => none)
        (base (selected p q))) := by
    rw [hscan] at hconfig
    simp only [applyAction, Turing.Tape.write_self, Function.update_eq_self] at hconfig
    simpa [primitive, primitiveControlCfg, readCfg, stackProgram, C, e,
      Function.update_eq_self] using hconfig
  obtain ⟨d, htrace, hdconfig, hdposition⟩ := reader_located_trace p q base
    (base (selected p q)) middle hmiddle
  refine ⟨d, .cons hstep htrace, hdconfig, ?_⟩
  rw [hdposition, hposition]
  simp only [headDisplacement, add_zero]
  change Function.update (fun i : Fin s => c.position i) (C.scan (ready q))
      (c.position (C.scan (ready q))) = (fun i : Fin s => c.position i)
  exact Function.update_eq_self (C.scan (ready q)) (fun i : Fin s => c.position i)

theorem decoder_head (s : ℕ) (k : Fin s) (top : Option Bool) :
    decoder s k (registerBits (fun _ : Fin 1 => top)) = top := by
  cases top <;> rfl

theorem dataTape_head (bits : List Bool) : (dataTape bits).head = bits.head? := by
  cases bits <;> rfl

theorem action_return_located {r s l : ℕ} (p : BitProgram.Program r s l)
    (k : Fin s) (q : State r l) (op : Mutation Bool)
    (base : Fin s → BitTape) (tape : BitTape) (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (actionCfg (stackProgram p) (codes s) k q op base
        ⟨(mutationActions boolCode op).length, Nat.lt_succ_self _⟩ tape)) :
    ∃ d : LocatedCfg (primitive p),
      locatedStep (primitive p) c = some d ∧
      d.config = primitiveControlCfg p ⟨.inr (ready q), Function.update base k tape⟩ ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let phase : Fin 3 := ⟨(mutationActions boolCode op).length,
    Nat.lt_succ_of_le (mutationActions_length boolCode op)⟩
  obtain ⟨d, hstep, hconfig, hposition⟩ := reindex_located_action e C c
    (acting k q op phase) (ready q) (.write tape.head) (Function.update base k tape) hc
    (by simp [C, controller, acting, phase, codes])
  refine ⟨d, hstep, ?_, ?_⟩
  · simpa [primitive, primitiveControlCfg, C, e, controller, acting, applyAction,
      Function.update_idem] using hconfig
  · rw [hposition]
    simp only [headDisplacement, add_zero]
    change Function.update (fun i : Fin s => c.position i) (C.scan (acting k q op phase))
        (c.position (C.scan (acting k q op phase))) = (fun i : Fin s => c.position i)
    exact Function.update_eq_self (C.scan (acting k q op phase))
      (fun i : Fin s => c.position i)

theorem stack_located_step {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : StackCfg (State r l) (fun _ : Fin s => Bool)}
    (hs : stackStep (stackProgram p) a = some b)
    {c : LocatedCfg (primitive p)}
    (hc : c.config = compiledCfg (stackProgram p) (codes s) (decoder s) a) :
    ∃ time ≤ 7, ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) time c d ∧
      d.config = compiledCfg (stackProgram p) (codes s) (decoder s) b ∧
      ∀ i : Fin s, d.position i = c.position i + (a.stk i).length - (b.stk i).length := by
  rcases a with ⟨state, S⟩
  cases state with
  | inl answer => simp [stackStep] at hs
  | inr q =>
    let C := controller (stackProgram p) (codes s) (decoder s)
    let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
    let k := selected p q
    let base := fun i => dataTape (S i)
    let readState : StackCompiler.State (stackProgram p) (codes s) :=
      reading q (⟨2, by change 2 < 3; decide⟩, fun _ => (base k).head)
    have hstart : c.config = primitiveControlCfg p ⟨.inr (ready q), base⟩ := by
      simpa only [compiledCfg, encodeCfg, primitiveControlCfg, tapeEncoding_bool,
        Sum.map_inr, base] using hc
    obtain ⟨readEnd, hread, hreadCfg, hreadPos⟩ := read_entry_located p q base c hstart
    have hr : readEnd.config = reindexCfg e C ⟨.inr readState, base⟩ := by
      simpa [primitiveControlCfg, readCfg, readState, stackProgram, k, C, e] using hreadCfg
    cases ht : transition p q (S k).head? with
    | inl answer =>
      dsimp only [k] at ht
      simp only [stackStep, stackProgram, ht, Option.some.injEq] at hs
      subst b
      obtain ⟨d, hlast, hconfig, hposition⟩ := reindex_located_halt e C readEnd
        readState answer base hr (by
          simp [C, controller, readState, reading, codes, boolCode, codeOfBoolEquiv,
            stackProgram, decoder_head, base, dataTape_head, k, ht])
      refine ⟨4, by omega, d, hread.trans (.cons hlast (.refl d)), ?_, ?_⟩
      · simpa only [primitive, compiledCfg, encodeCfg, primitiveControlCfg, tapeEncoding_bool,
          Sum.map_inl, id_eq, base, e, C] using hconfig
      · intro i
        rw [hposition, hreadPos]
        change c.position i = c.position i + (S i).length - (S i).length
        omega
    | inr output =>
      rcases output with ⟨q', op⟩
      dsimp only [k] at ht
      simp only [stackStep, stackProgram, ht, Option.some.injEq] at hs
      subst b
      obtain ⟨actionStart, hdispatch, hdispatchCfg, hdispatchPos⟩ :=
        reindex_located_action e C readEnd readState (acting k q' op 0)
          (.write (base k).head) base hr (by
            simp [C, controller, readState, reading, codes, boolCode, codeOfBoolEquiv,
              stackProgram, decoder_head, base, dataTape_head, k, ht]
            rfl)
      have hactionStart : actionStart.config = primitiveControlCfg p
          (actionCfg (stackProgram p) (codes s) k q' op base 0 (base k)) := by
        simpa [primitiveControlCfg, actionCfg, readState, C, e, controller, reading,
          stackProgram, k, applyAction, Function.update_eq_self] using hdispatchCfg
      have hdispatchPosition : actionStart.position = readEnd.position := by
        rw [hdispatchPos]
        simp only [headDisplacement, add_zero]
        change Function.update (fun i : Fin s => readEnd.position i) (C.scan readState)
            (readEnd.position (C.scan readState)) = (fun i : Fin s => readEnd.position i)
        exact Function.update_eq_self (C.scan readState) (fun i : Fin s => readEnd.position i)
      obtain ⟨actionEnd, haction, hactionCfg, hactionPos⟩ :=
        mutation_located_trace p k q' op base (base k) actionStart hactionStart
      obtain ⟨d, hreturn, hreturnCfg, hreturnPos⟩ := action_return_located p k q' op
        base (execute (mutationActions boolCode op) (base k)) actionEnd hactionCfg
      have htape : execute (mutationActions boolCode op) (base k) =
          dataTape (op.apply (S k)) := by
        simpa only [base, encodeDataStack_boolCode] using mutationActions_correct boolCode op (S k)
      refine ⟨3 + (1 + ((mutationActions boolCode op).length + 1)), ?_, d,
        hread.trans ((Trace.cons hdispatch (Trace.refl actionStart)).trans
          (haction.trans (.cons hreturn (.refl d)))), ?_, ?_⟩
      · have hlength := mutationActions_length boolCode op
        change (mutationActions boolCode op).length ≤ 2 at hlength
        omega
      · rw [htape] at hreturnCfg
        change d.config = primitiveControlCfg p
          ⟨.inr (ready q'), fun i => dataTape (encodeDataStack boolCode
            ((Function.update S k (op.apply (S k))) i))⟩
        simp_rw [encodeDataStack_boolCode]
        have htapes : (fun i => dataTape ((Function.update S k (op.apply (S k))) i)) =
            Function.update base k (dataTape (op.apply (S k))) :=
          Function.comp_update dataTape S k (op.apply (S k))
        rw [htapes]
        exact hreturnCfg
      · intro i
        rw [hreturnPos, hactionPos, hdispatchPosition, hreadPos]
        rw [transition_mutation_displacement p q q' op (S k) ht
          headDisplacement rfl rfl (fun _ => rfl)]
        change Function.update c.position k
          (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) i =
            c.position i + (S i).length - ((Function.update S k (op.apply (S k))) i).length
        by_cases hi : i = k
        · subst i
          change Function.update (fun j : Fin s => c.position j) k
              (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) k =
            c.position k + (S k).length -
              (Function.update S k (op.apply (S k)) k).length
          simp only [Function.update_self]
          omega
        · change Function.update (fun j : Fin s => c.position j) k
              (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) i =
            c.position i + (S i).length -
              (Function.update S k (op.apply (S k)) i).length
          simp only [Function.update_of_ne hi]
          omega

theorem primitive_located_step {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : BitProgram.Cfg r s l} (hs : BitProgram.step p a = some b)
    {c : LocatedCfg (primitive p)} (hc : c.config = primitiveCfg p a) :
    ∃ time ≤ 7, ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) time c d ∧ d.config = primitiveCfg p b ∧
      ∀ i : Fin s, d.position i = c.position i + (a.stacks i).length - (b.stacks i).length := by
  apply stack_located_step p (a := stackCfg p a) (b := stackCfg p b) _ hc
  rw [stack_step, hs]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CompileSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Transfer a genuine bound on every source stack configuration through the
guarded primitive compiler. The bound is independent of the number of source
instructions. Concrete counting programs must prove the source invariant. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace

open GuardedCompiler
open scoped BigOperators

private theorem compile_trace_envelope {r s l : ℕ} (p : BitProgram.Program r s l)
    (anchor : Fin s → ℤ) (bound inputLength : ℕ)
    (hanchor : ∀ i, 0 ≤ anchor i ∧ anchor i ≤ (inputLength : ℤ))
    {a b : BitProgram.Cfg r s l} {sourceSteps : ℕ}
    (tr : BitProgram.Trace p sourceSteps a b) {c : LocatedCfg (primitive p)}
    (hcfg : c.config = primitiveCfg p a)
    (hposition : ∀ i, c.position i = anchor i - ((a.stacks i).length : ℤ))
    (henvelope : ∀ i, -(bound : ℤ) - 7 ≤ c.lower i ∧
      c.upper i ≤ (inputLength : ℤ) + 7)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time c d ∧
      d.config = primitiveCfg p b ∧
      (∀ i, d.position i = anchor i - ((b.stacks i).length : ℤ)) ∧
      ∀ i, -(bound : ℤ) - 7 ≤ d.lower i ∧
        d.upper i ≤ (inputLength : ℤ) + 7 := by
  induction tr generalizing c with
  | refl => exact ⟨0, by omega, c, .refl c, hcfg, hposition, henvelope⟩
  | @cons sourceSteps a next final hs ht ih =>
      obtain ⟨time₁, htime₁, middle, hrun₁, hcfg₁, hshift⟩ :=
        primitive_located_step p hs hcfg
      have hposition₁ : ∀ i,
          middle.position i = anchor i - ((next.stacks i).length : ℤ) := by
        intro i
        rw [hshift i, hposition i]
        omega
      have henvelope₁ : ∀ i, -(bound : ℤ) - 7 ≤ middle.lower i ∧
          middle.upper i ≤ (inputLength : ℤ) + 7 := by
        apply locatedTrace_envelope_of_margin hrun₁ htime₁
          (fun _ => -(bound : ℤ) - 7) (fun _ => (inputLength : ℤ) + 7) henvelope
        intro i
        have hlength := hstacks 0 a (by omega) (.refl a) i
        have ha := hanchor i
        rw [hposition i]
        omega
      have hstacks₁ : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
          BitProgram.Trace p prefixSteps next intermediate →
          ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace
        exact hstacks (prefixSteps + 1) intermediate (by omega) (.cons hs htrace)
      obtain ⟨time₂, htime₂, d, hrun₂, hcfg₂, hposition₂, henvelope₂⟩ :=
        ih hcfg₁ hposition₁ henvelope₁ hstacks₁
      exact ⟨time₁ + time₂, by omega, d, hrun₁.trans hrun₂,
        hcfg₂, hposition₂, henvelope₂⟩

theorem compile_trace_space {r s l : ℕ} (p : BitProgram.Program r s l)
    {input : List Bool} {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config = primitiveCfg p final ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  let anchor : Fin s → ℤ := fun i => if i = p.inputStack then input.length else 0
  have hanchor : ∀ i, 0 ≤ anchor i ∧ anchor i ≤ (input.length : ℤ) := by
    intro i
    dsimp [anchor]
    split_ifs <;> omega
  have hposition : ∀ i : Fin s, (locatedInit (primitive p) input).position i =
      anchor i - (((BitProgram.initial p input).stacks i).length : ℤ) := by
    intro i
    by_cases hi : i = p.inputStack <;> simp [locatedInit, anchor, hi]
  have henvelope : ∀ i, -(bound : ℤ) - 7 ≤ (locatedInit (primitive p) input).lower i ∧
      (locatedInit (primitive p) input).upper i ≤ (input.length : ℤ) + 7 := by
    intro i
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  obtain ⟨time, htime, d, hrun, hcfg, _, hspace⟩ :=
    compile_trace_envelope p anchor bound input.length hanchor tr
      (primitive_initial p input).symm hposition henvelope hstacks
  refine ⟨time, htime, d, hrun, hcfg, ?_⟩
  intro prefixSteps intermediate hle hprefix
  apply (locatedTrace_prefix_space hrun hprefix hle).trans
  apply (visitedSpace_le_of_envelope d _ _ hspace).trans
  have hwidth : ((input.length : ℤ) + 7 - (-(bound : ℤ) - 7) + 1).toNat =
      bound + input.length + 15 := by omega
  simp only [hwidth, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact le_rfl

/-- A full word on an arbitrary fixed tape and a separate Boolean halt are
preserved by the same execution used for both resource bounds. -/
theorem compile_word_answer_space_oai {r s l : ℕ} (p : BitProgram.Program r s l)
    (countStack : Fin s) {input word : List Bool} {answer : Bool}
    {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hword : final.stacks countStack = word)
    (hanswer : final.stacks p.outputStack = [answer])
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config.state = .inl answer ∧
      d.config.tapes countStack = Turing.Tape.mk₁ (word.map some) ∧
      d.config.tapes p.outputStack = Turing.Tape.mk₁ [some answer] ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  obtain ⟨time, htime, d, hrun, hcfg, hspace⟩ := compile_trace_space p tr hstacks
  refine ⟨time, htime, d, hrun, ?_, ?_, ?_, hspace⟩
  · rw [hcfg, primitive_halted p final halted, hanswer]
    rfl
  · rw [hcfg, primitive_tape, hword]
  · rw [hcfg, primitive_tape, hanswer]
    rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace.compile_word_answer_space_oai
