-- Prove2me | solution 2 for Monodromy.Counter.Reversible.Recording.step_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:04:06.297146+00:00
-- url     : https://prove2.me/submissions/dca93847-36d8-40aa-a47e-a8b1a03ba211

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Counter
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
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
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
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_packing_internal_reaches
public import Theorems.Thm_Monodromy_Counter_Reversible_step_iff

@[expose] public section


-- Inline helper skeleton from Monodromy.Counter.


/-!
# Counter machines and native continuation

The standard finite counter semantics is retained. A three-phase finite
compiler realizes each two-counter step by two actual geometric returns;
the faithful configuration encoding preserves complete partial execution.

Classical finite counter macros and prime coding compile an entire finite
Turing table through three source registers to the same two-counter target.
Every arithmetic loop has a separate finite control region, with marked
source entries and no intermediate return boundary.
-/

@[expose] public section

namespace Monodromy.Counter









variable {n m : ℕ} (program : Program n m) (state : Configuration n m)

theorem step_inc {reg : Fin n} {next : Fin m}
    (instruction : program state.pc = .inc reg next) :
    step program state =
      some ⟨next, Function.update state.counters reg (state.counters reg + 1)⟩ := by
  simp [step, instruction]

theorem step_dec_zero {reg : Fin n} {zero nonzero : Fin m}
    (instruction : program state.pc = .dec reg zero nonzero)
    (value : state.counters reg = 0) :
    step program state = some ⟨zero, state.counters⟩ := by
  simp [step, instruction, value]

theorem step_dec_succ {reg : Fin n} {zero nonzero : Fin m} {value : ℕ}
    (instruction : program state.pc = .dec reg zero nonzero)
    (counter : state.counters reg = value + 1) :
    step program state = some ⟨nonzero, Function.update state.counters reg value⟩ := by
  simp [step, instruction, counter]









variable {k : ℕ}











end Monodromy.Counter

noncomputable section

namespace Monodromy.CounterContinuation

open CoupledContinuation



























variable {m : ℕ} [NeZero m]





end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ} [NeZero m]

















end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation

variable {m : ℕ}



variable [NeZero m]













end Monodromy.CounterContinuation


namespace Monodromy.CounterContinuation

variable {m : ℕ} [NeZero m]



end Monodromy.CounterContinuation

namespace Monodromy.CounterContinuation

open CoupledContinuation









variable {m : ℕ} [NeZero m]







end Monodromy.CounterContinuation

namespace Monodromy.PrimeCode



namespace Basis

variable {n : ℕ} (basis : Basis n)

























end Basis





































end Monodromy.PrimeCode

namespace Monodromy.Counter.RegisterRelocation

variable {n k m : ℕ}





















end Monodromy.Counter.RegisterRelocation

namespace Monodromy.Counter

variable {n m k : ℕ}





end Monodromy.Counter

namespace Monodromy.CounterMultiplication

















































end Monodromy.CounterMultiplication

namespace Monodromy.Counter.DivMod

variable (p : ℕ) [NeZero p]
































































end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]





























































end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]











































































































end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}








































































































end Monodromy.Counter.Compression

namespace Monodromy.Counter.EntryDispatch

variable {a m : ℕ}























end Monodromy.Counter.EntryDispatch

/-!
## Locally reversible counter tables
-/

namespace Monodromy.Counter.Reversible









namespace Action

variable {n : ℕ}



















end Action

variable {n q e : ℕ}

namespace Edge







end Edge

























namespace Action











end Action



































namespace Action



end Action





















end Monodromy.Counter.Reversible

/-!
## Static finite port matchings
-/

namespace Monodromy.ReversiblePorts

variable {q e : ℕ}

























open Counter.Reversible





















end Monodromy.ReversiblePorts

/-!
## Native guarded routing
-/

namespace Monodromy.ReversibleRouting

open CoupledContinuation Counter.Reversible ReversiblePorts

variable {q e : ℕ} [NeZero (q + e)]



variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))





























end Monodromy.ReversibleRouting

/-!
## The fixed reversible native compiler
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation ReversiblePorts

variable {q e : ℕ} [NeZero q]











































































end Monodromy.ReversibleCompilation

/-!
## Complete execution and actual lifted results
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]



















































end Monodromy.ReversibleCompilation

/-!
## Protected source register relocation
-/

namespace Monodromy.Counter.Reversible.RegisterRelocation

variable {n m q e : ℕ}







































end Monodromy.Counter.Reversible.RegisterRelocation

/-!
## Composition by gluing control interfaces
-/

namespace Monodromy.Counter.Reversible.Glue

variable {n q₁ q₂ e₁ e₂ : ℕ}









































/-! Finite traces inside larger control graphs. -/

section FiniteTrace

variable {n m q k e f : ℕ}







end FiniteTrace

end Monodromy.Counter.Reversible.Glue

/-!
## Finite port identification

A partial matching identifies existing output and input positions. Original
edges and actions are retained, including in cyclic networks.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PortNetwork

variable {n q e : ℕ}



variable {original : Table n q e} (wiring : Wiring original)



















































end Monodromy.Counter.Reversible.PortNetwork

end


/-!
## One reversible radix graph: unpacking and packing
-/

namespace Monodromy.Counter.Reversible.Radix

variable (p : ℕ) [NeZero p]




































































































end Monodromy.Counter.Reversible.Radix

/-!
## Read-only remainder observation by identified radix ports
-/

noncomputable section

namespace Monodromy.Counter.Reversible.RadixObservation

variable (p m : ℕ) [NeZero p]



















































































end Monodromy.Counter.Reversible.RadixObservation

end


/-!
## A source specification for reversible transition recording
-/

namespace Monodromy.Counter.Recorded

variable {n m : ℕ}





























end Monodromy.Counter.Recorded


/-!
## Recoverable execution histories

Finite copies of the reversed radix graph record each instruction branch.
The source registers are protected while the history is packed; the workspace
returns to zero at every dispatch. This is an intermediate reversible source
graph, prior to compression into the two native memory coordinates.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.Recording

variable {n m : ℕ}

































































@[simp] theorem copy_ne_mid (row other : Fin m) (position : Fin (Radix.size (base m))) :
    copy row position ≠ mid other := by
  intro same
  have impossible : (Sum.inl (row, position) : Node m) = Sum.inr other :=
    (nodeEquiv m).injective same
  cases impossible














theorem extraOperation_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraOperation program arc = .shift (Fin.castAdd 2 register) 1 := by
  unfold extraOperation
  split <;> simp_all




























@[simp] theorem frame_old (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) :
    frame values history workspace (Fin.castAdd 2 index) = (values index : ℤ) := by
  simp [frame]

@[simp] theorem frame_tail (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin 2) :
    frame values history workspace (historyRegister n index) = ![history, workspace] index := by
  simp [frame, historyRegister]





private theorem tail_ne_old (index : Fin 2) (old : Fin n) :
    historyRegister n index ≠ Fin.castAdd 2 old := by
  intro same
  have values := congrArg Fin.val same
  simp only [historyRegister, Fin.val_natAdd, Fin.val_castAdd] at values
  omega





theorem frame_update (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) (value : ℕ) :
    Function.update (frame values history workspace) (Fin.castAdd 2 index) (value : ℤ) =
      frame (Function.update values index value) history workspace := by
  funext position
  induction position using Fin.addCases with
  | left old =>
      by_cases same : old = index
      · subst old; simp
      · simp [same]
  | right tail =>
      change Function.update (frame values history workspace) (Fin.castAdd 2 index) (value : ℤ)
        (historyRegister n tail) =
          frame (Function.update values index value) history workspace (historyRegister n tail)
      rw [Function.update_of_ne (tail_ne_old tail index)]
      simp only [frame_tail]

theorem shift_frame (values : Fin n → ℕ) (history workspace amount : ℤ) (index : Fin n)
    (value : ℕ) (updated : (values index : ℤ) + amount = value) :
    Action.apply (.shift (Fin.castAdd 2 index) amount) (frame values history workspace) =
      frame (Function.update values index value) history workspace := by
  simpa only [Action.apply, frame_old, updated] using frame_update values history workspace index value

theorem inc_frame (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) :
    Action.apply (.shift (Fin.castAdd 2 index) 1) (frame values history workspace) =
      frame (Function.update values index (values index + 1)) history workspace :=
  shift_frame values history workspace 1 index _ (by simp)

theorem dec_frame (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) (value : ℕ)
    (positive : values index = value + 1) :
    Action.apply (.shift (Fin.castAdd 2 index) (-1)) (frame values history workspace) =
      frame (Function.update values index value) history workspace :=
  shift_frame values history workspace (-1) index _ (by simp [positive])











theorem extraEdge_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraEdge program arc =
      ⟨dispatch arc.val.1, port target (digit arc.val.1 0), .shift (Fin.castAdd 2 register) 1⟩ := by
  unfold extraEdge
  rw [extraOrigin_inc program arc register target instruction,
    extraDestination_inc program arc register target instruction,
    extraOperation_inc program arc register target instruction]
  rfl

theorem extraEdge_dec (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (zero nonzero : Fin m)
    (instruction : program arc.val.1 = .dec register zero nonzero) :
    extraEdge program arc = ![
      ⟨dispatch arc.val.1, port zero (digit arc.val.1 0), .test (Fin.castAdd 2 register) true⟩,
      ⟨dispatch arc.val.1, mid arc.val.1, .test (Fin.castAdd 2 register) false⟩,
      ⟨mid arc.val.1, port nonzero (digit arc.val.1 1), .shift (Fin.castAdd 2 register) (-1)⟩]
      arc.val.2 := by
  unfold extraEdge
  rw [extraOrigin_dec program arc register zero nonzero instruction,
    extraDestination_dec program arc register zero nonzero instruction,
    extraOperation_dec program arc register zero nonzero instruction]
  rcases arc with ⟨⟨row, branch⟩, active⟩
  fin_cases branch <;> rfl


/-! The natural domain is preserved at every intermediate port. -/
















































theorem boundary_encode (state : Counter.Configuration n m) (history : ℕ) :
    Boundary (encode state history) := ⟨state.pc, rfl⟩



theorem not_boundary_mid (row : Fin m) (values : Fin n → ℕ) (history workspace : ℤ) :
    ¬ Boundary (framed (mid row) values history workspace) := by
  rintro ⟨other, same⟩
  exact copy_ne_mid other row (Radix.entry (base m)) same.symm





private theorem extra_step (program : Counter.Program n m) (arc : Extra program)
    (state : State (n + 2) (size m)) (enabled : (extraEdge program arc).enabled state) :
    step (table program) state = some ((extraEdge program arc).execute state) := by
  apply (step_iff _ (deterministic program)).mpr
  refine ⟨arcEquiv program (.inr arc), ?_, ?_⟩
  · simpa only [table_arc, arcEdge] using enabled
  · rw [table_arc]
    rfl

private theorem history_digit (row : Fin m) (branch : Fin 2) (history : ℕ) :
    base m * history + (digit row branch).val =
      Counter.Recorded.push (finProdFinEquiv (row, branch)) history := by
  simp only [base, digit, Counter.Recorded.push, Nat.add_assoc]

private theorem pack_firstReturn (program : Counter.Program n m)
    {initial : State (n + 2) (size m)} {row : Fin m} {symbol : Fin (base m)}
    {values : Fin n → ℕ} {history : ℕ} (marked : Boundary initial)
    (first_step : step (table program) initial =
      some (framed (port row symbol) values history 0)) :
    FirstReturn program initial
      (framed (dispatch row) values (base m * history + symbol.val : ℕ) 0) := by
  exact ⟨marked, ⟨row, rfl⟩, framed (port row symbol) values history 0, first_step,
    packing_internal_reaches program row symbol values history⟩

private theorem inc_firstReturn (program : Counter.Program n m) (before : Counter.Configuration n m)
    (history : ℕ) (register : Fin n) (target : Fin m)
    (instruction : program before.pc = .inc register target) :
    FirstReturn program (encode before history)
      (encode ⟨target, Function.update before.counters register (before.counters register + 1)⟩
        (base m * history + (digit before.pc 0).val)) := by
  let arc : Extra program := ⟨(before.pc, 0), by
    unfold Active
    rw [instruction]⟩
  have fields := extraEdge_inc program arc register target instruction
  have enabled : (extraEdge program arc).enabled (encode before history) := by
    rw [fields]
    exact ⟨rfl, trivial⟩
  have first_step := extra_step program arc (encode before history) enabled
  rw [fields] at first_step
  simp only [Edge.execute, encode, framed, inc_frame] at first_step
  exact pack_firstReturn program (boundary_encode before history) first_step

private theorem zero_firstReturn (program : Counter.Program n m) (before : Counter.Configuration n m)
    (history : ℕ) (register : Fin n) (zero nonzero : Fin m)
    (instruction : program before.pc = .dec register zero nonzero) (empty : before.counters register = 0) :
    FirstReturn program (encode before history)
      (encode ⟨zero, before.counters⟩ (base m * history + (digit before.pc 0).val)) := by
  let arc : Extra program := ⟨(before.pc, 0), by unfold Active; rw [instruction]; trivial⟩
  have fields : extraEdge program arc =
      ⟨dispatch before.pc, port zero (digit before.pc 0), .test (Fin.castAdd 2 register) true⟩ :=
    extraEdge_dec program arc register zero nonzero instruction
  have enabled : (extraEdge program arc).enabled (encode before history) := by
    rw [fields]
    constructor
    · rfl
    · change Action.enabled (.test (Fin.castAdd 2 register) true)
        (frame before.counters history 0)
      simp [Action.enabled, empty]
  have first_step := extra_step program arc (encode before history) enabled
  rw [fields] at first_step
  simp only [Edge.execute, Action.apply, encode, framed] at first_step
  exact pack_firstReturn program (boundary_encode before history) first_step

private theorem positive_firstReturn (program : Counter.Program n m)
    (before : Counter.Configuration n m) (history : ℕ) (register : Fin n) (zero nonzero : Fin m)
    (instruction : program before.pc = .dec register zero nonzero) (value : ℕ)
    (count : before.counters register = value + 1) :
    FirstReturn program (encode before history)
      (encode ⟨nonzero, Function.update before.counters register value⟩
        (base m * history + (digit before.pc 1).val)) := by
  let probe : Extra program := ⟨(before.pc, 1), by unfold Active; rw [instruction]; trivial⟩
  let write : Extra program := ⟨(before.pc, 2), by unfold Active; rw [instruction]; trivial⟩
  have probe_fields : extraEdge program probe =
      ⟨dispatch before.pc, mid before.pc, .test (Fin.castAdd 2 register) false⟩ :=
    extraEdge_dec program probe register zero nonzero instruction
  have write_fields : extraEdge program write =
      ⟨mid before.pc, port nonzero (digit before.pc 1), .shift (Fin.castAdd 2 register) (-1)⟩ :=
    extraEdge_dec program write register zero nonzero instruction
  have probe_enabled : (extraEdge program probe).enabled (encode before history) := by
    rw [probe_fields]
    constructor
    · rfl
    · change Action.enabled (.test (Fin.castAdd 2 register) false)
        (frame before.counters history 0)
      simp [Action.enabled, count]
      omega
  have first_step := extra_step program probe (encode before history) probe_enabled
  rw [probe_fields] at first_step
  simp only [Edge.execute, Action.apply, encode, framed] at first_step
  have write_enabled : (extraEdge program write).enabled
      (framed (mid before.pc) before.counters history 0) := by
    rw [write_fields]
    exact ⟨rfl, trivial⟩
  have second_step := extra_step program write (framed (mid before.pc) before.counters history 0)
    write_enabled
  rw [write_fields] at second_step
  simp only [Edge.execute, framed, dec_frame before.counters history 0 register value count] at second_step
  refine ⟨boundary_encode before history, ⟨nonzero, rfl⟩,
    framed (mid before.pc) before.counters history 0, first_step, ?_⟩
  exact Relation.ReflTransGen.head
    ⟨second_step, not_boundary_mid before.pc before.counters history 0⟩
    (packing_internal_reaches program nonzero (digit before.pc 1)
      (Function.update before.counters register value) history)








































end Monodromy.Counter.Reversible.Recording

end

/-!
## Reversible prime compression

A finite virtual register vector is encoded in prime exponents. All arithmetic
uses the same two-counter radix graph; shared ports select and restore tests.
Exact first returns preserve the entire source configuration. Ordinary traces
are derived from that stronger execution statement.
-/

noncomputable section

namespace Monodromy.Counter.Reversible.PrimeCompression

variable {n q e : ℕ}























































































































































































































































































































































end Monodromy.Counter.Reversible.PrimeCompression

end


/-! Finite source marks on the same native geometric word table. -/

noncomputable section

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]









































end Monodromy.ReversibleCompilation

end

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}
theorem solution (program : Counter.Program n m) {before after : Counter.Configuration n m}
    (transition : Counter.step program before = some after) (history : ℕ) :
    FirstReturn program (encode before history)
      (encode after (Counter.Recorded.push (Counter.Recorded.tag program before) history)) := by
  cases instruction : program before.pc with
  | halt => simp [Counter.step, instruction] at transition
  | inc register target =>
      have result := Option.some.inj ((Counter.step_inc program before instruction).symm.trans transition)
      subst after
      have run := inc_firstReturn program before history register target instruction
      rw [history_digit] at run
      simpa only [Counter.Recorded.tag, Counter.Recorded.branch, instruction] using run
  | dec register zero nonzero =>
      cases count : before.counters register with
      | zero =>
          have result := Option.some.inj
            ((Counter.step_dec_zero program before instruction count).symm.trans transition)
          subst after
          have run := zero_firstReturn program before history register zero nonzero instruction count
          rw [history_digit] at run
          simpa only [Counter.Recorded.tag, Counter.Recorded.branch, instruction, count, ite_true] using run
      | succ value =>
          have result := Option.some.inj
            ((Counter.step_dec_succ program before instruction count).symm.trans transition)
          subst after
          have run := positive_firstReturn program before history register zero nonzero instruction value count
          rw [history_digit] at run
          simpa [Counter.Recorded.tag, Counter.Recorded.branch, instruction, count] using run
