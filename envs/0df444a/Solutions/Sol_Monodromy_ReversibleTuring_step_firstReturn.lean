-- Prove2me | solution 1 for Monodromy.ReversibleTuring.step_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:05:16.510564+00:00
-- url     : https://prove2.me/submissions/041dd6bf-a032-46c0-b21c-6947ea705fc6

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Counter
public import Definitions.Def_Monodromy_FormalCompilation
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
public import Theorems.Thm_Monodromy_Counter_Compression_step_firstReturn
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_counter_internal_reaches
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_step_firstReturn
public import Theorems.Thm_Monodromy_Counter_TuringCompiler_step_firstReturn

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

























































omit [NeZero q] in
@[simp] theorem encode_boundary (state : TM0.Cfg (Fin a) (Fin q)) :
    Boundary a q (encode a q state).pc := ⟨(state.q, state.Tape.head), rfl⟩

















































end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}






















theorem dispatch_injective (source : Program 3 m) : Function.Injective (dispatch source) := by
  intro first second same
  exact congrArg Sigma.fst ((address source).injective same)

















































































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























theorem history_lt (program : Program n m) {first last : State n m}
    (transition : step program first = some last) : first.2 < last.2 := by
  obtain ⟨next, _, result⟩ := Option.map_eq_some_iff.mp transition
  rw [← result]
  change first.2 < push (tag program first.1) first.2
  rw [push, Nat.add_mul, Nat.one_mul]
  omega





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


















































































































































/-! The natural domain is preserved at every intermediate port. -/























































































theorem marked_boundary {mark : Fin m → Bool} {state : State (n + 2) (size m)}
    (marked : Marked mark state) : Boundary state := by
  obtain ⟨row, same, _⟩ := marked
  exact ⟨row, same⟩

theorem marked_encode_iff (mark : Fin m → Bool)
    (state : Counter.Configuration n m) (history : ℕ) :
    Marked mark (encode state history) ↔ mark state.pc = true := by
  constructor
  · rintro ⟨row, same, marked⟩
    have rows := ((copy_eq_iff state.pc row _ _).mp same).1
    exact rows.symm ▸ marked
  · intro marked
    exact ⟨state.pc, rfl, marked⟩







private theorem internal_to_marked (program : Counter.Program n m) (mark : Fin m → Bool)
    {first last : State (n + 2) (size m)} (run : InternalReaches program first last) :
    InternalMarkedReaches program mark first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      exact previous.tail ⟨edge.1, fun marked => edge.2 (marked_boundary marked)⟩





/-- A source first return lifts to the first positive return to the fixed marked ports. -/
theorem marked_firstReturn (program : Counter.Program n m) (mark : Fin m → Bool)
    {first middle last : Counter.Configuration n m}
    (initial : Counter.step program first = some middle)
    (rest : Relation.ReflTransGen (fun current next : Counter.Configuration n m =>
      Counter.step program current = some next ∧ mark current.pc = false) middle last)
    (first_marked : mark first.pc = true) (last_marked : mark last.pc = true) (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      MarkedFirstReturn program mark (encode first history) (encode last finalHistory) := by
  obtain ⟨_, _, next, head, inside⟩ := step_firstReturn program initial history
  obtain ⟨logged, not_smaller, following⟩ := counter_internal_reaches program mark rest
    (Counter.Recorded.push (Counter.Recorded.tag program first) history)
  have growth := Counter.Recorded.history_lt program
    (first := (first, history))
    (last := (middle, Counter.Recorded.push (Counter.Recorded.tag program first) history))
    (by simp only [Counter.Recorded.step, initial, Option.map_some])
  exact ⟨logged, growth.trans_le not_smaller, (marked_encode_iff mark first history).mpr first_marked,
    (marked_encode_iff mark last logged).mpr last_marked, next, head,
    (internal_to_marked program mark inside).trans following⟩





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


-- Inline helper skeleton from Monodromy.FormalCompilation.


/-!
# Finite Turing tables and native continuation

Mathlib's stack evaluator is translated to a Post–Turing table and restricted
to its finite support. The source code fixes the table; its numeric arguments
are supplied through an explicit finite input word.

The native simulation composes the actual finite counter compilers with
fixed geometric Word execution. It preserves full configurations, complete
partial results, halting and divergence. Source steps are causal first returns
marked by finite analytic root observations. Finite executions are realized
by the two matching covering-space lifts.
-/

@[expose] public section

namespace Monodromy.FormalCompilation

open Turing











variable (source : ToPartrec.Code)















































end Monodromy.FormalCompilation

noncomputable section

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

variable (a q : ℕ) [NeZero a] [NeZero q]





































section FiniteTypes

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]















end FiniteTypes

end Monodromy.NativeTuring

namespace Monodromy.NativeTuring

open Turing CoupledContinuation

section Marking

variable {m : ℕ} [NeZero m]



















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
























section FiniteTypes

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]





end FiniteTypes



end Monodromy.NativeTuring

/-!
## Universal simulation with recoverable history

The ordinary two-counter compilation supplies only the source to be made
reversible. A fixed finite recording graph executes it, retaining the complete
configuration and history. Its four source registers are a proof intermediate;
reversibility-preserving compression to two native memory roots is separate.
-/

namespace Monodromy.RecordedTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]









end

end Monodromy.RecordedTuring

namespace Monodromy.ReversibleTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]















private theorem source_marked (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    NativeTuring.counterMark a q machine (RecordedTuring.counterEncode a q machine state).pc = true := by
  unfold RecordedTuring.counterEncode NativeTuring.counterMark
  exact @decide_eq_true _ (by unfold NativeTuring.CounterMarked; infer_instance)
    ((NativeTuring.counterMarked_encode3_iff a q machine
    (Counter.TuringCompiler.encode a q state)).mpr
      (Counter.TuringCompiler.encode_boundary a q state))



































end

end Monodromy.ReversibleTuring

/-!
## Recoverable-history simulation on two counters
-/

noncomputable section

namespace Monodromy.ReversibleTuring.Compression

open Turing Counter.Reversible



variable (a q : ℕ) [NeZero a] [NeZero q]

































































end Monodromy.ReversibleTuring.Compression

end

/-!
## Reversible universality by actual path lifting
-/

noncomputable section

namespace Monodromy.ReversibleNativeTuring

open Turing CoupledContinuation ReversibleTuring

variable (a q : ℕ) [NeZero a] [NeZero q]




































































end Monodromy.ReversibleNativeTuring

end

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.ReversibleTuring
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]
theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      Counter.Reversible.Recording.MarkedFirstReturn (NativeTuring.source2 a q machine)
        (NativeTuring.counterMark a q machine)
        (encode a q machine first history) (encode a q machine last finalHistory) := by
  obtain ⟨middle, initial, rest⟩ := NativeTuring.counter_firstReturn a q machine transition
  have internal : Relation.ReflTransGen
      (fun current next : Counter.Configuration 2 (RecordedTuring.size a q machine) =>
        Counter.step (NativeTuring.source2 a q machine) current = some next ∧
          NativeTuring.counterMark a q machine current.pc = false)
      middle (RecordedTuring.counterEncode a q machine last) := by
    refine Relation.ReflTransGen.mono (r := NativeTuring.CounterInternalStep a q machine)
      (fun current next edge => ?_) _ _ rest
    exact ⟨edge.1, by simpa only
      [NativeTuring.counterMark, decide_eq_false_iff_not] using edge.2⟩
  exact Counter.Reversible.Recording.marked_firstReturn (NativeTuring.source2 a q machine)
    (NativeTuring.counterMark a q machine) initial internal
    (source_marked a q machine first) (source_marked a q machine last) history
