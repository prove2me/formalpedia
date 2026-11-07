-- Prove2me | solution 1 for Monodromy.NativeTuring.macroStep_iota
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:38:47.302329+00:00
-- url     : https://prove2.me/submissions/c87f6e85-ce4c-4f63-9f13-b0b442af5c35

module
public import Definitions.Def_Monodromy_FormalCompilation
public import Theorems.Thm_Monodromy_CounterContinuation_two_returns
public import Theorems.Thm_Monodromy_Counter_Compression_step_firstReturn
public import Theorems.Thm_Monodromy_Counter_TuringCompiler_step_firstReturn
public import Theorems.Thm_Monodromy_CounterContinuation_simulates
public import Theorems.Thm_Monodromy_CounterContinuation_advance_live_phase
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.NativeTuring
open Turing CoupledContinuation
variable (a q : ℕ) [NeZero a] [NeZero q]

noncomputable section

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

theorem haltSignal_prepare (program : Program degree) (left right quotient : ℤ) (index : Fin degree) :
    program.haltSignal (prepare left right ((degree : ℤ) * quotient + index.val)) =
      if program.stop index then 1 else 0 := by
  unfold haltSignal
  rw [controlRoot_prepare]
  have root := congrArg (fun value : Circle => (value : ℂ))
    (Radix.readRoot_digit degree quotient index)
  rw [root]
  exact Choice.dispatch_root
    (fun first second same => Radix.omega_injective degree (Subtype.ext same))
    (fun first second => (Radix.omega_complex_pow degree first).trans
      (Radix.omega_complex_pow degree second).symm)
    (Radix.omega_regular degree) index

end Monodromy.CoupledContinuation.Program

namespace Monodromy.Counter.TuringCompiler

variable (a q : ℕ) [NeZero a] [NeZero q]

omit [NeZero a] [NeZero q] in
theorem dispatch_injective : Function.Injective (dispatch a q) := by
  intro first second same
  exact congrArg Prod.fst ((address a q).injective same)

theorem halt_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    step (program a q machine) (encode a q state) = none ↔ TM0.step machine state = none := by
  simp only [step, encode, program_dispatch, TM0.step]
  cases result : machine state.q state.Tape.head with
  | none => simp
  | some command =>
      rcases command with ⟨target, operation⟩
      cases operation <;> simp [counters]

omit [NeZero q] in
@[simp] theorem encode_boundary (state : TM0.Cfg (Fin a) (Fin q)) :
    Boundary a q (encode a q state).pc := ⟨(state.q, state.Tape.head), rfl⟩

end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}

@[simp] theorem address_dispatch (source : Program 3 m) (row : Fin m) :
    (address source).symm (dispatch source row) = ⟨row, .inl ()⟩ :=
  (address source).symm_apply_apply _

theorem dispatch_injective (source : Program 3 m) : Function.Injective (dispatch source) := by
  intro first second same
  exact congrArg Sigma.fst ((address source).injective same)

@[simp] theorem program_dispatch (source : Program 3 m) (row : Fin m) :
    program source (dispatch source row) =
      match selected : source row with
      | .halt => .halt
      | .inc register next =>
          .dec 1 (mulTarget source row register next selected 0)
            (mulTarget source row register next selected 0)
      | .dec register zero nonzero =>
          .dec 1 (probeTarget source row register zero nonzero selected
            (CounterPrimeProbe.entry (PrimeCode.prime register)))
            (probeTarget source row register zero nonzero selected
              (CounterPrimeProbe.entry (PrimeCode.prime register))) := by
  unfold program
  rw [address_dispatch]
  rfl

private theorem step_none_iff {n k : ℕ} (table : Program n k) (state : Configuration n k) :
    step table state = none ↔ table state.pc = .halt := by
  unfold step
  cases instruction : table state.pc with
  | halt => simp
  | inc => simp
  | dec register zero nonzero => cases value : state.counters register <;> simp [value]

/-- Halting is tested at the encoded dispatch cell, independently of all arithmetic loops. -/
theorem halt_encode (source : Program 3 m) (state : Configuration 3 m) :
    step (program source) (encode source state) = none ↔ step source state = none := by
  rw [step_none_iff, step_none_iff]
  change program source (dispatch source state.pc) = .halt ↔ source state.pc = .halt
  rw [program_dispatch]
  split <;> simp_all

end Monodromy.Counter.Compression

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

variable (a q : ℕ) [NeZero a] [NeZero q]

/-- A halted source configuration halts at its actual native root state. -/
theorem step_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (halted : TM0.step machine state = none) :
    (program a q machine).step (iota a q machine state) = none := by
  have halted3 := (Counter.TuringCompiler.halt_encode a q machine state).mpr halted
  have halted2 := (Counter.Compression.halt_encode (source3 a q machine)
    (Counter.TuringCompiler.encode a q state)).mpr halted3
  have result := StateTransition.fun_respects.mp (CounterContinuation.simulates (source2 a q machine))
    (a₁ := Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q state))
  change Counter.step (source2 a q machine)
    (Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q state)) = none at halted2
  rw [halted2] at result
  exact result

section Marking

variable {m : ℕ} [NeZero m]

@[simp] theorem markedProgram_advance (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (state : Memory) :
    (markedProgram source mark).advance state = (CounterContinuation.compile source).advance state := rfl

theorem markedBoundary_label_iff (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (position : Fin m) (phase : Fin 3) (left right : ℤ) :
    MarkedBoundary source mark (prepare left right (CounterContinuation.label position phase)) ↔
      phase = 0 ∧ mark position = true := by
  have signal := Program.haltSignal_prepare (markedProgram source mark) left right 0
    (finProdFinEquiv (position, phase))
  have stop_at : (markedProgram source mark).stop (finProdFinEquiv (position, phase)) =
      markTable mark (finProdFinEquiv (position, phase)) := rfl
  rw [stop_at] at signal
  have at_label : (markedProgram source mark).haltSignal
      (prepare left right (CounterContinuation.label position phase)) =
      if markTable mark (finProdFinEquiv (position, phase)) then 1 else 0 := by
    simpa only [mul_zero, zero_add, CounterContinuation.label] using signal
  unfold MarkedBoundary
  rw [at_label]
  by_cases phase_zero : phase = 0
  · cases value : mark position <;> simp [markTable, phase_zero, value]
  · simp [markTable, phase_zero]

theorem markedBoundary_encode_iff (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (state : Counter.Configuration 2 m) :
    MarkedBoundary source mark (CounterContinuation.encode state) ↔ mark state.pc = true := by
  unfold CounterContinuation.encode
  rw [markedBoundary_label_iff]
  simp

private theorem advance_of_native_step (source : Counter.Program 2 m) {first last : Memory}
    (transition : (CounterContinuation.compile source).step first = some last) :
    (CounterContinuation.compile source).advance first = last := by
  unfold Program.step at transition
  split at transition
  · contradiction
  · exact Option.some.inj transition

/-- The existing intermediate native phase can never satisfy any phase-zero mark. -/
theorem two_returns_marked (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (first last : Counter.Configuration 2 m) (transition : Counter.step source first = some last) :
    ∃ middle : Memory,
      (CounterContinuation.compile source).step (CounterContinuation.encode first) = some middle ∧
      ¬ MarkedBoundary source mark middle ∧
      (CounterContinuation.compile source).step middle = some (CounterContinuation.encode last) := by
  obtain ⟨middle, initial, final⟩ := CounterContinuation.two_returns source first last transition
  have live : source first.pc ≠ .halt := by
    intro halted
    simp [Counter.step, halted] at transition
  have advance := advance_of_native_step source initial
  refine ⟨middle, initial, ?_, final⟩
  rw [← advance]
  rcases CounterContinuation.advance_live_phase source first live with one | two
  · rw [one, markedBoundary_label_iff]
    simp
  · rw [two, markedBoundary_label_iff]
    simp

/-- Interior actual steps are unchanged when only the root stopping table is replaced. -/
theorem marked_step_of_original (source : Counter.Program 2 m) (mark : Fin m → Bool)
    {first last : Memory} (transition : (CounterContinuation.compile source).step first = some last)
    (interior : ¬ MarkedBoundary source mark first) :
    (markedProgram source mark).step first = some last := by
  change (if (markedProgram source mark).haltSignal first = 1 then none
    else some ((markedProgram source mark).advance first)) = some last
  change (markedProgram source mark).haltSignal first ≠ 1 at interior
  rw [ite_eq_right interior, markedProgram_advance]
  exact congrArg some (advance_of_native_step source transition)

end Marking

variable (a q : ℕ) [NeZero a] [NeZero q]

theorem counterMarked_encode3_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Configuration 3 (Counter.TuringCompiler.size a q)) :
    CounterMarked a q machine (Counter.Compression.encode (source3 a q machine) state).pc ↔
      Counter.TuringCompiler.Boundary a q state.pc := by
  constructor
  · rintro ⟨row, same⟩
    exact ⟨row, Counter.Compression.dispatch_injective (source3 a q machine) same⟩
  · rintro ⟨row, same⟩
    exact ⟨row, congrArg (Counter.Compression.dispatch (source3 a q machine)) same⟩

theorem counterMarked_implies_boundary (machine : TM0.Machine (Fin a) (Fin q))
    {cell : Fin (Counter.Compression.size (source3 a q machine))}
    (marked : CounterMarked a q machine cell) : Counter.Compression.Boundary (source3 a q machine) cell := by
  rcases marked with ⟨row, same⟩
  exact ⟨Counter.TuringCompiler.dispatch a q row, same⟩

theorem boundary_encode2_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))) :
    Boundary a q machine (CounterContinuation.encode state) ↔ CounterMarked a q machine state.pc := by
  change MarkedBoundary (source2 a q machine) (counterMark a q machine)
    (CounterContinuation.encode state) ↔ _
  rw [markedBoundary_encode_iff]
  simp [counterMark]

@[simp] theorem boundary_iota (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) : Boundary a q machine (iota a q machine state) := by
  rw [iota, boundary_encode2_iff, counterMarked_encode3_iff]
  exact Counter.TuringCompiler.encode_boundary a q state

private theorem compression_internal (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))}
    (run : Counter.Compression.InternalReaches (source3 a q machine) first last) :
    CounterInternalReaches a q machine first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      exact previous.tail ⟨edge.1, fun marked => edge.2 (counterMarked_implies_boundary a q machine marked)⟩

private theorem turing_internal_step (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 3 (Counter.TuringCompiler.size a q)}
    (edge : Counter.TuringCompiler.InternalStep a q machine first last) :
    CounterInternalReaches a q machine
      (Counter.Compression.encode (source3 a q machine) first)
      (Counter.Compression.encode (source3 a q machine) last) := by
  obtain ⟨after, initial, rest⟩ := Counter.Compression.step_firstReturn (source3 a q machine) edge.1
  exact Relation.ReflTransGen.head
    ⟨initial, fun marked => edge.2 ((counterMarked_encode3_iff a q machine first).mp marked)⟩
    (compression_internal a q machine rest)

private theorem turing_internal (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 3 (Counter.TuringCompiler.size a q)}
    (run : Counter.TuringCompiler.InternalReaches a q machine first last) :
    CounterInternalReaches a q machine
      (Counter.Compression.encode (source3 a q machine) first)
      (Counter.Compression.encode (source3 a q machine) last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous => exact previous.trans (turing_internal_step a q machine edge)

/-- Nested source compilation has a positive first return to exactly the marked finite PCs. -/
theorem counter_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last) :
    ∃ after,
      Counter.step (source2 a q machine)
        (Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q first)) =
          some after ∧
      CounterInternalReaches a q machine after
        (Counter.Compression.encode (source3 a q machine) (Counter.TuringCompiler.encode a q last)) := by
  obtain ⟨after3, initial3, rest3⟩ := Counter.TuringCompiler.step_firstReturn a q machine transition
  obtain ⟨after2, initial2, rest2⟩ := Counter.Compression.step_firstReturn (source3 a q machine) initial3
  exact ⟨after2, initial2,
    (compression_internal a q machine rest2).trans (turing_internal a q machine rest3)⟩

private theorem native_counter_internal_step (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))}
    (edge : CounterInternalStep a q machine first last) :
    InternalReaches a q machine (CounterContinuation.encode first) (CounterContinuation.encode last) := by
  obtain ⟨middle, initial, middle_unmarked, final⟩ :=
    two_returns_marked (source2 a q machine) (counterMark a q machine) first last edge.1
  have first_unmarked : ¬ Boundary a q machine (CounterContinuation.encode first) := by
    intro marked
    exact edge.2 ((boundary_encode2_iff a q machine first).mp marked)
  exact Relation.ReflTransGen.head ⟨initial, first_unmarked⟩
    (Relation.ReflTransGen.single ⟨final, middle_unmarked⟩)

private theorem native_counter_internal (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Configuration 2 (Counter.Compression.size (source3 a q machine))}
    (run : CounterInternalReaches a q machine first last) :
    InternalReaches a q machine (CounterContinuation.encode first) (CounterContinuation.encode last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous => exact previous.trans (native_counter_internal_step a q machine edge)

/-- Every live TM step is exactly the first return to the analytic native boundary. -/
theorem step_firstReturn (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last) :
    FirstReturn a q machine (iota a q machine first) (iota a q machine last) := by
  obtain ⟨after2, initial2, rest2⟩ := counter_firstReturn a q machine transition
  obtain ⟨middle, initial, middle_unmarked, final⟩ :=
    two_returns_marked (source2 a q machine) (counterMark a q machine) _ _ initial2
  exact ⟨middle, initial, Relation.ReflTransGen.head ⟨final, middle_unmarked⟩
    (native_counter_internal a q machine rest2)⟩

/-- Interior execution is the same actual word-table execution under the boundary stop table. -/
theorem internal_marked_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Memory} (run : InternalReaches a q machine first last) :
    StateTransition.Reaches (boundaryProgram a q machine).step first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      exact previous.tail (marked_step_of_original (source2 a q machine) (counterMark a q machine)
        edge.1 edge.2)

private theorem boundary_stops (machine : TM0.Machine (Fin a) (Fin q))
    {state : Memory} (marked : Boundary a q machine state) :
    (boundaryProgram a q machine).step state = none := by
  change (boundaryProgram a q machine).haltSignal state = 1 at marked
  simp only [Program.step, ite_eq_left marked]

end Monodromy.NativeTuring

/-- The causally executed native first-return macro is the exact total TM step on encoded states. -/
theorem solution (machine : TM0.Machine (Fin a) (Fin q)) (state : TM0.Cfg (Fin a) (Fin q)) :
    macroStep a q machine (iota a q machine state) =
      Part.some ((TM0.step machine state).map (iota a q machine)) := by
  cases transition : TM0.step machine state with
  | none =>
      rw [macroStep, step_halt a q machine state transition]
      rfl
  | some next =>
      obtain ⟨after, initial, interior⟩ := step_firstReturn a q machine transition
      have completed : (boundaryProgram a q machine).eval after = Part.some (iota a q machine next) := by
        apply Part.eq_some_iff.mpr
        exact StateTransition.mem_eval.mpr
          ⟨internal_marked_reaches a q machine interior, boundary_stops a q machine (boundary_iota a q machine next)⟩
      simp only [macroStep, initial, completed, Part.map_some, Option.map_some]
