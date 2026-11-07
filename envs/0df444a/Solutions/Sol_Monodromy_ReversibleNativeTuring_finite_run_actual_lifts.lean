-- Prove2me | solution 1 for Monodromy.ReversibleNativeTuring.finite_run_actual_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:08:25.584013+00:00
-- url     : https://prove2.me/submissions/c22f0788-7549-433a-b12a-c667ec731f56

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Continuation
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
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_halt_no_outgoing
public import Theorems.Thm_Monodromy_ReversibleNativeTuring_step_firstReturn
public import Theorems.Thm_Monodromy_StagedProgram_haltSignal_embed

@[expose] public section


-- Inline helper skeleton from Monodromy.Continuation.


@[expose] public section

/-!
# Coupled analytic continuation

Two retained logarithmic memory roots share one upper control root through
`F(w₁,w₂,z) = (exp w₁, exp w₂, exp z / (w₁*w₂))`. The two actual lower
lifts generate the upper input path. The returned root is the actual upper
lift endpoint; integer labels occur only in preparation and proofs.

The matching lower product covering and upper pullback covering are explicit.
Their actual lifts agree with the complete runtime curves. Five fixed loops
provide memory shifts, zero-conditional control writes and a control shift.
Concatenation and reversal follow from lift uniqueness. A finite power-root
observation routes whole base paths by normalized analytic kernels at returns.

Five oriented loops give a finite word language and finite root-controlled
program tables with internal stopping. Effective semantics and machine
simulation are proved in the subsequent research layers.
-/

noncomputable section

namespace Monodromy.CoupledContinuation

open unitInterval












attribute [local fun_prop] analyticAt_fst analyticAt_snd





















































































































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval























end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation









end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation


namespace Monodromy.CoupledPullback
























end Monodromy.CoupledPullback


namespace Monodromy.CoupledPullback











end Monodromy.CoupledPullback

namespace Monodromy.CoupledContinuation



















end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



attribute [local fun_prop] analyticAt_fst analyticAt_snd



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

variable (degree : ℕ) [NeZero degree]



























end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval





























theorem restrictedTrajectory_end (driver : Driver) (state : Memory) :
    restrictedTrajectory driver state 1 = restrictedState (execute driver state) := rfl












/-- The runtime intermediate curve is the unique actual lift for the matching lower cover. -/
theorem intermediateCurve_actual_lift (driver : Driver) (state : Memory) :
    intermediateCurve driver state =
      CoupledPullback.lowerCovering.liftPath driver.restrictedPath
        (CoupledPullback.upperProjection (restrictedState state))
        (driver.restrictedPath.source.trans (restrictedState_over_base state).symm) := by
  apply (CoupledPullback.lowerCovering.eq_liftPath_iff'
    (driver.restrictedPath.source.trans (restrictedState_over_base state).symm)).mpr
  constructor
  · funext t
    exact restricted_lower_projection driver state t
  · have first := restricted_upper_projection driver state 0
    rw [restrictedTrajectory_start] at first
    exact first.symm

/-- The runtime upper trajectory is the unique actual lift for the matching upper cover. -/
theorem restrictedTrajectory_actual_lift (driver : Driver) (state : Memory) :
    restrictedTrajectory driver state =
      CoupledPullback.upperCovering.liftPath (intermediatePath driver state) (restrictedState state)
        (intermediatePath driver state).source := by
  apply (CoupledPullback.upperCovering.eq_liftPath_iff'
    (intermediatePath driver state).source).mpr
  constructor
  · funext t
    exact restricted_upper_projection driver state t
  · exact restrictedTrajectory_start driver state

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval













section FiniteRouting

variable (degree : ℕ) [NeZero degree]



























end FiniteRouting











































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval



































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



namespace Program

variable {degree : ℕ} [NeZero degree]















end Program

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation











end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]



/-- Arbitrary counts describe advance iteration, including counts beyond a stopping return. -/
theorem execute_runDriver (program : Program degree) (count : ℕ) (state : Memory) :
    execute (program.runDriver count state) state = (program.advance)^[count] state := by
  induction count generalizing state with
  | zero => exact execute_idle state
  | succ count induction_hypothesis =>
      rw [runDriver, execute_driver_trans]
      change execute (program.runDriver count (program.advance state)) (program.advance state) = _
      rw [induction_hypothesis, Function.iterate_succ_apply]

theorem advance_of_step (program : Program degree) {first last : Memory}
    (transition : program.step first = some last) : program.advance first = last := by
  unfold step at transition
  split at transition
  · contradiction
  · exact Option.some.inj transition

/-- A finite native step run has the corresponding number of actual advances. -/
theorem reaches_iterate_advance (program : Program degree) {initial final : Memory}
    (run : StateTransition.Reaches program.step initial final) :
    ∃ count, (program.advance)^[count] initial = final := by
  induction run with
  | refl => exact ⟨0, rfl⟩
  | tail _ edge previous =>
      rcases previous with ⟨count, reached⟩
      refine ⟨count + 1, ?_⟩
      rw [Function.iterate_succ_apply', reached]
      exact advance_of_step program edge

/-- Stopping-respecting finite execution is realized by its causally generated base path. -/
theorem runDriver_of_reaches (program : Program degree) {initial final : Memory}
    (run : StateTransition.Reaches program.step initial final) :
    ∃ count, execute (program.runDriver count initial) initial = final := by
  obtain ⟨count, reached⟩ := reaches_iterate_advance program run
  exact ⟨count, (execute_runDriver program count initial).trans reached⟩







end Monodromy.CoupledContinuation.Program

/-!
## Reversible conditional control

A finite permutation of control cells is compiled into signed words of the
existing conditional loop. Its inverse is selected from the returned roots.
-/

namespace Monodromy.ReversibleControl

open CoupledContinuation



























variable {degree : ℕ} [NeZero degree]



























end Monodromy.ReversibleControl

/-! Finite root-controlled memory translations use the same signed native A paths. -/

namespace Monodromy.ReversibleMemory

open CoupledContinuation



























variable {degree : ℕ} [NeZero degree]

















end Monodromy.ReversibleMemory


/-!
## Integer coordinates of actual returned roots

These coordinates state and prove the action of the existing geometric execution.
They do not participate in path generation or add an execution rule.
-/

namespace Monodromy.CoupledContinuation













namespace Program

variable {degree : ℕ} [NeZero degree]

























end Program

end Monodromy.CoupledContinuation


/-!
## Finite cyclic staging in the existing upper branch

The compiler emits only the existing signed geometric words. A finite stage is
packed into the upper branch, and every generated word is executed by the
unchanged native lifting kernel.
-/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast



















variable (count degree : ℕ) [NeZero count] [NeZero degree]

























































end Monodromy.StagedProgram

/-! Static phase-zero stopping for the existing finite-stage compiler. -/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast

variable (count degree : ℕ) [NeZero count] [NeZero degree]































end Monodromy.StagedProgram

/-! First-return predecessor uniqueness for reversible advances. -/

namespace Monodromy.ReversibleReturn

variable {State Source : Type*}









end Monodromy.ReversibleReturn


/-! Marked inverse execution and first-return transport. -/

namespace Monodromy.CoupledContinuation.Program

noncomputable section

variable {degree : ℕ} [NeZero degree]







end

end Monodromy.CoupledContinuation.Program

namespace Monodromy.ReversibleReturn

variable {State : Type*}





end Monodromy.ReversibleReturn

end

end


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













@[simp] theorem program_consume (remainder : Fin p) :
    program p (consume p remainder) = .dec 0 (transfer p remainder) (next p remainder) := by
  simp [program, consume, remainder.isLt]


















































end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]

















@[simp] theorem entry_eq : entry p = divBlock p (Counter.DivMod.consume p 0) := by
  simp [entry, divAddress]











































end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]



















































theorem halt_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    step (program a q machine) (encode a q state) = none ↔ TM0.step machine state = none := by
  simp only [step, encode, program_dispatch, TM0.step]
  cases result : machine state.q state.Tape.head with
  | none => simp
  | some command =>
      rcases command with ⟨target, operation⟩
      cases operation <;> simp [counters]























































end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}
















@[simp] theorem address_dispatch (source : Program 3 m) (row : Fin m) :
    (address source).symm (dispatch source row) = ⟨row, .inl ()⟩ :=
  (address source).symm_apply_apply _





















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



omit [NeZero q] in
@[simp] theorem haltMark_source (table : Table 2 q e) (position : Fin q) :
    haltMark table (Fin.castAdd e position) =
      decide (¬ ∃ edge, (table edge).source = position) := by
  simp [haltMark]









theorem haltSignal_iota (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : State 2 q) :
    (haltingProgram table deterministic compatible).haltSignal (iota (e := e) state) =
      if haltMark table (Fin.castAdd e state.1) then 1 else 0 := by
  have actual := StagedProgram.haltSignal_embed 11 (q + e)
    (stages table deterministic compatible) (haltMark table)
    (state.2 0) (state.2 1) 0 (Fin.castAdd e state.1) 0
  simpa only [haltingProgram, iota, sourcePoint, point, mul_zero, zero_add, ite_true] using actual

theorem haltSignal_iota_iff (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : State 2 q) :
    (haltingProgram table deterministic compatible).haltSignal (iota (e := e) state) = 1 ↔
      ¬ ∃ edge, (table edge).source = state.1 := by
  rw [haltSignal_iota, haltMark_source]
  by_cases outgoing : ∃ edge, (table edge).source = state.1 <;> simp [outgoing]



































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


















































































































































/-! The natural domain is preserved at every intermediate port. -/













































































































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



















































































































































































































/-- A retained source boundary is never removed by the static port matching. -/
theorem boundary_link_none (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (position : Fin q) :
    (wiring basis source deterministic compatible).link (boundary basis source position) = none := by
  change PortNetwork.relationLink (Connection basis source) (boundary basis source position) = none
  exact (PortNetwork.relationLink_none_iff (Connection basis source) _).mpr
    (boundary_unconnected basis source deterministic position)







/-- A source address without outgoing edges is represented by an isolated raw vertex. -/
theorem raw_no_outgoing_halt (basis : PrimeCode.Basis n) (source : Table n q e)
    (position : Fin q) (halted : ¬ HasSource source position) (index : Fin (rawEdges basis source)) :
    (rawTable basis source index).source ≠ boundary basis source position := by
  intro same
  obtain ⟨⟨block, index⟩, rfl⟩ := (rawArcEquiv basis source).surjective index
  simp only [rawTable_arc, rawEdge, Glue.mapEdge, boundary, dite_eq_right halted] at same
  exact haltNode_ne_moduleNode basis source ⟨position, halted⟩ _ _ same.symm

/-- Static halts retain their absence of outgoing edges in the actual compressed table. -/
theorem no_outgoing_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (position : Fin q) (halted : ¬ HasSource source position) :
    ¬ ∃ index, (table basis source deterministic compatible index).source =
      PortNetwork.control (wiring basis source deterministic compatible)
        (boundary basis source position) := by
  rintro ⟨index, same⟩
  have raw_controls := PortNetwork.control_unlinked_injective
    (wiring basis source deterministic compatible)
    ((wiring basis source deterministic compatible).source_free index)
    (boundary_link_none basis source deterministic compatible position) same
  exact raw_no_outgoing_halt basis source position halted index raw_controls

























































































































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







theorem counter_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (halted : TM0.step machine state = none) :
    Counter.step (NativeTuring.source2 a q machine) (counterEncode a q machine state) = none := by
  have first := (Counter.TuringCompiler.halt_encode a q machine state).mpr halted
  exact (Counter.Compression.halt_encode (NativeTuring.source3 a q machine)
    (Counter.TuringCompiler.encode a q state)).mpr first

end

end Monodromy.RecordedTuring

namespace Monodromy.ReversibleTuring

open Turing

noncomputable section

variable (a q : ℕ) [NeZero a] [NeZero q]



















































end

end Monodromy.ReversibleTuring

/-!
## Recoverable-history simulation on two counters
-/

noncomputable section

namespace Monodromy.ReversibleTuring.Compression

open Turing Counter.Reversible



variable (a q : ℕ) [NeZero a] [NeZero q]













































private theorem counter_instruction_halt {n m : ℕ} (program : Counter.Program n m)
    (state : Counter.Configuration n m) (halted : Counter.step program state = none) :
    program state.pc = .halt := by
  cases instruction : program state.pc with
  | halt => rfl
  | inc => simp [Counter.step, instruction] at halted
  | dec register zero nonzero =>
      cases value : state.counters register <;> simp [Counter.step, instruction, value] at halted

/-- A stopped Turing configuration enters a genuinely source-free recording dispatch. -/
theorem source_no_outgoing_of_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    ¬ PrimeCompression.HasSource (ReversibleTuring.table a q machine)
      (PrimeCompression.toNatural (ReversibleTuring.encode a q machine state history)).pc := by
  have instruction := counter_instruction_halt (NativeTuring.source2 a q machine)
    (RecordedTuring.counterEncode a q machine state)
    (RecordedTuring.counter_halt a q machine state halted)
  rintro ⟨index, same⟩
  exact Recording.halt_no_outgoing (NativeTuring.source2 a q machine)
    (RecordedTuring.counterEncode a q machine state).pc instruction index same

/-- Static halting survives compression independently of the encoded memory values. -/
theorem no_outgoing_of_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    ¬ ∃ index, (table a q machine index).source = (encode a q machine state history).1 :=
  PrimeCompression.no_outgoing_boundary basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (PrimeCompression.toNatural (ReversibleTuring.encode a q machine state history)).pc
    (source_no_outgoing_of_halt a q machine state history halted)















end Monodromy.ReversibleTuring.Compression

end

/-!
## Reversible universality by actual path lifting
-/

noncomputable section

namespace Monodromy.ReversibleNativeTuring

open Turing CoupledContinuation ReversibleTuring

variable (a q : ℕ) [NeZero a] [NeZero q]



















/-- Every source step is a positive run of actual native returns with its larger history. -/
theorem step_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      StateTransition.Reaches₁ (program a q machine).step
        (iota a q machine first history) (iota a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, _, _, next, initial, rest⟩ :=
    step_firstReturn a q machine transition history
  exact ⟨finalHistory, grew, Relation.TransGen.head' initial
    (Relation.ReflTransGen.mono (fun _ _ edge => edge.1) _ _ rest)⟩

/-- Stopping is detected from the actual static halt address, without a global completeness premise. -/
theorem step_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    (program a q machine).step (iota a q machine state history) = none := by
  have signal := (ReversibleCompilation.haltSignal_iota_iff (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.encode a q machine state history)).mpr
      (Compression.no_outgoing_of_halt a q machine state history halted)
  change (if (program a q machine).haltSignal (iota a q machine state history) = 1 then none
    else some ((program a q machine).advance (iota a q machine state history))) = none
  exact ite_eq_left signal



theorem respects (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (program a q machine).step (Related a q machine) := by
  intro original native related
  obtain ⟨history, rfl⟩ := related
  cases transition : TM0.step machine original with
  | none => exact step_halt a q machine original history transition
  | some next =>
      obtain ⟨finalHistory, _, run⟩ := step_reaches a q machine transition history
      exact ⟨iota a q machine next finalHistory, ⟨finalHistory, rfl⟩, run⟩










































end Monodromy.ReversibleNativeTuring

end

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.ReversibleNativeTuring
open Turing CoupledContinuation ReversibleTuring
variable (a q : ℕ) [NeZero a] [NeZero q]
theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (history : ℕ)
    (run : StateTransition.Reaches (TM0.step machine) first last) :
    ∃ finalHistory, ∃ count : ℕ,
      let initial := iota a q machine first history
      let driver := (program a q machine).runDriver count initial
      intermediateCurve driver initial =
        CoupledPullback.lowerCovering.liftPath driver.restrictedPath
          (CoupledPullback.upperProjection (restrictedState initial))
          (driver.restrictedPath.source.trans (restrictedState_over_base initial).symm) ∧
      restrictedTrajectory driver initial =
        CoupledPullback.upperCovering.liftPath (intermediatePath driver initial) (restrictedState initial)
          (intermediatePath driver initial).source ∧
      restrictedTrajectory driver initial 1 = restrictedState (iota a q machine last finalHistory) := by
  obtain ⟨native, ⟨finalHistory, rfl⟩, actual⟩ :=
    StateTransition.tr_reaches (respects a q machine) ⟨history, rfl⟩ run
  obtain ⟨count, endpoint⟩ := (program a q machine).runDriver_of_reaches actual
  refine ⟨finalHistory, count, ?_⟩
  dsimp only
  refine ⟨intermediateCurve_actual_lift _ _, restrictedTrajectory_actual_lift _ _, ?_⟩
  rw [restrictedTrajectory_end, endpoint]
