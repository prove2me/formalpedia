-- Prove2me | solution 1 for Monodromy.ReversibleTuring.Compression.result_iff
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:07:29.484416+00:00
-- url     : https://prove2.me/submissions/dd78a8cc-be0d-480a-b5f2-b850a6505d63

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
public import Theorems.Thm_Monodromy_Counter_Reversible_PrimeCompression_encode_injective
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_embed_injective
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_halt_no_outgoing
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_valid_nonnegative
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_valid_step
public import Theorems.Thm_Monodromy_Counter_TuringCompiler_encode_injective
public import Theorems.Thm_Monodromy_ReversibleTuring_Compression_step_firstReturn

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







/-- Prime valuations recover every register, uniformly in the finite dimension. -/
theorem factorization_encode (registers : Fin n → ℕ) (index : Fin n) :
    (basis.encode registers).factorization (basis.prime index) = registers index := by
  unfold encode
  rw [Nat.factorization_prod_apply (fun other _ => pow_ne_zero _ (basis.isPrime other).ne_zero)]
  rw [Finset.sum_eq_single index]
  · exact Nat.factorization_pow_self (basis.isPrime index)
  · intro other _ different
    rw [(basis.isPrime other).factorization_pow]
    exact Finsupp.single_eq_of_ne' (basis.distinct.ne different)
  · simp

theorem decode_encode : Function.LeftInverse basis.decode basis.encode := by
  intro registers
  funext index
  exact basis.factorization_encode registers index















end Basis













@[simp] theorem three_decode (code : ℕ) : three.decode code = decode code := rfl

theorem three_encode (registers : Fin 3 → ℕ) : three.encode registers = encode registers := by
  change (∏ index : Fin 3, prime index ^ registers index) =
    2 ^ registers 0 * 3 ^ registers 1 * 5 ^ registers 2
  simp [Fin.prod_univ_succ, prime, mul_assoc]





theorem decode_encode : Function.LeftInverse decode encode := by
  intro registers
  simpa only [three_encode, three_decode] using three.decode_encode registers

theorem encode_injective : Function.Injective encode := decode_encode.injective













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







theorem encode_injective (source : Program 3 m) : Function.Injective (encode source) := by
  intro first second same
  have positions := dispatch_injective source (congrArg Configuration.pc same)
  have values : PrimeCode.encode first.counters = PrimeCode.encode second.counters :=
    congrFun (congrArg Configuration.counters same) 0
  have registers := PrimeCode.encode_injective values
  cases first
  cases second
  simp_all































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





















theorem step_none_iff (table : Table n q e) (state : State n q) :
    step table state = none ↔ ¬ ∃ index, (table index).enabled state := by
  unfold step
  split_ifs <;> simp_all



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













































































































@[simp] theorem frame_old (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) :
    frame values history workspace (Fin.castAdd 2 index) = (values index : ℤ) := by
  simp [frame]

@[simp] theorem frame_tail (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin 2) :
    frame values history workspace (historyRegister n index) = ![history, workspace] index := by
  simp [frame, historyRegister]

@[simp] theorem frame_history (values : Fin n → ℕ) (history workspace : ℤ) :
    frame values history workspace (historyRegister n 0) = history := by simp

@[simp] theorem frame_workspace (values : Fin n → ℕ) (history workspace : ℤ) :
    frame values history workspace (historyRegister n 1) = workspace := by simp






























/-! The natural domain is preserved at every intermediate port. -/







@[simp] theorem valid_copy_iff (program : Counter.Program n m) (row : Fin m)
    (position : Fin (Radix.size (base m))) (values : Fin (n + 2) → ℤ) :
    Valid program (copy row position, values) ↔
      OldNonnegative values ∧ Radix.Valid (base m) (position, values ∘ historyRegister n) := by
  simp only [Valid, copy, Equiv.symm_apply_apply, admissible]



@[simp] theorem valid_dispatch_iff (program : Counter.Program n m) (row : Fin m)
    (values : Fin (n + 2) → ℤ) :
    Valid program (dispatch row, values) ↔
      OldNonnegative values ∧ 0 ≤ values (historyRegister n 0) ∧
        values (historyRegister n 1) = 0 := by
  change Valid program (copy row (Radix.entry (base m)), values) ↔ _
  rw [valid_copy_iff]
  simp only [Radix.Valid, Radix.entry, Radix.global, Equiv.symm_apply_apply,
    Radix.admissible, Function.comp_apply, Matrix.cons_val_zero]
  constructor
  · rintro ⟨old, history, _, empty⟩
    exact ⟨old, history, empty⟩
  · rintro ⟨old, history, empty⟩
    exact ⟨old, history, by omega, empty⟩



theorem valid_encode (program : Counter.Program n m) (state : Counter.Configuration n m)
    (history : ℕ) : Valid program (encode state history) := by
  change Valid program (dispatch state.pc, frame state.counters history 0)
  rw [valid_dispatch_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro index
    simpa only [frame_old] using Int.natCast_nonneg (state.counters index)
  · simpa only [frame_history] using Int.natCast_nonneg history
  · exact frame_workspace _ _ _




















theorem valid_reaches (program : Counter.Program n m) {first last : State (n + 2) (size m)}
    (valid : Valid program first) (run : StateTransition.Reaches (step (table program)) first last) :
    Valid program last := by
  induction run with
  | refl => exact valid
  | tail _ transition previous => exact valid_step program previous transition

/-- Every intermediate state of every encoded recording run has only nonnegative counters. -/
theorem encode_reaches_nonnegative (program : Counter.Program n m)
    (initial : Counter.Configuration n m) (history : ℕ) {state : State (n + 2) (size m)}
    (run : StateTransition.Reaches (step (table program)) (encode initial history) state)
    (index : Fin (n + 2)) : 0 ≤ state.2 index :=
  valid_nonnegative program state (valid_reaches program (valid_encode program initial history) run) index






































































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





























































































theorem naturalState_toNatural (state : State n q) (nonnegative : ∀ index, 0 ≤ state.2 index) :
    naturalState (toNatural state) = state := by
  apply Prod.ext
  · rfl
  · funext index
    exact Int.toNat_of_nonneg (nonnegative index)



























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





theorem counterEncode_injective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (counterEncode a q machine) :=
  (Counter.Compression.encode_injective (NativeTuring.source3 a q machine)).comp
    (Counter.TuringCompiler.encode_injective a q)

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







theorem encode_injective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (fun pair : TM0.Cfg (Fin a) (Fin q) × ℕ =>
      encode a q machine pair.1 pair.2) := by
  intro first second same
  have logged : (RecordedTuring.counterEncode a q machine first.1, first.2) =
      (RecordedTuring.counterEncode a q machine second.1, second.2) := by
    apply Counter.Reversible.Recording.embed_injective
    exact same
  exact Prod.ext
    (RecordedTuring.counterEncode_injective a q machine (congrArg Prod.fst logged))
    (congrArg (fun state : Counter.Recorded.State 2 (RecordedTuring.size a q machine) => state.2) logged)











































end

end Monodromy.ReversibleTuring

/-!
## Recoverable-history simulation on two counters
-/

noncomputable section

namespace Monodromy.ReversibleTuring.Compression

open Turing Counter.Reversible



variable (a q : ℕ) [NeZero a] [NeZero q]

















private theorem source_nonnegative (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ∀ index, 0 ≤ (ReversibleTuring.encode a q machine state history).2 index := by
  intro index
  exact Recording.encode_reaches_nonnegative (NativeTuring.source2 a q machine)
    (RecordedTuring.counterEncode a q machine state) history Relation.ReflTransGen.refl index

theorem encode_injective (machine : TM0.Machine (Fin a) (Fin q)) :
    Function.Injective (fun pair : TM0.Cfg (Fin a) (Fin q) × ℕ =>
      encode a q machine pair.1 pair.2) := by
  intro first second same
  have natural := PrimeCompression.encode_injective basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine) same
  have original := congrArg PrimeCompression.naturalState natural
  rw [PrimeCompression.naturalState_toNatural _ (source_nonnegative a q machine first.1 first.2),
    PrimeCompression.naturalState_toNatural _ (source_nonnegative a q machine second.1 second.2)] at original
  exact ReversibleTuring.encode_injective a q machine original























/-- Every Turing step runs the two-counter table with the same strictly growing history. -/
theorem step_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      StateTransition.Reaches₁ (step (table a q machine))
        (encode a q machine first history) (encode a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, _, _, next, initial, rest⟩ :=
    step_firstReturn a q machine transition history
  exact ⟨finalHistory, grew, Relation.TransGen.head' initial
    (Relation.ReflTransGen.mono (fun _ _ edge => edge.1) _ _ rest)⟩

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

theorem step_halt (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) (halted : TM0.step machine state = none) :
    step (table a q machine) (encode a q machine state history) = none := by
  rw [step_none_iff]
  rintro ⟨index, enabled⟩
  exact no_outgoing_of_halt a q machine state history halted ⟨index, enabled.1⟩



theorem respects (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (step (table a q machine)) (Related a q machine) := by
  intro original compiled related
  obtain ⟨history, rfl⟩ := related
  cases transition : TM0.step machine original with
  | none => exact step_halt a q machine original history transition
  | some next =>
      obtain ⟨finalHistory, _, run⟩ := step_reaches a q machine transition history
      exact ⟨encode a q machine next finalHistory, ⟨finalHistory, rfl⟩, run⟩









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
open Monodromy.ReversibleTuring.Compression
open Turing Counter.Reversible
variable (a q : ℕ) [NeZero a] [NeZero q]
theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    (first last : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (∃ finalHistory, Monodromy.ReversibleTuring.Compression.encode a q machine last finalHistory ∈
      Monodromy.Counter.Reversible.eval (Monodromy.ReversibleTuring.Compression.table a q machine) (Monodromy.ReversibleTuring.Compression.encode a q machine first history)) ↔
      last ∈ StateTransition.eval (TM0.step machine) first := by
  constructor
  · rintro ⟨finalHistory, finished⟩
    obtain ⟨original, ⟨originalHistory, related⟩, source_finished⟩ :=
      StateTransition.tr_eval_rev (Monodromy.ReversibleTuring.Compression.respects a q machine) ⟨history, rfl⟩ finished
    have same : (original, originalHistory) = (last, finalHistory) :=
      @Monodromy.ReversibleTuring.Compression.encode_injective a q _ _ machine (original, originalHistory) (last, finalHistory) related
    have configurations : original = last := congrArg Prod.fst same
    simpa only [configurations] using source_finished
  · intro source_finished
    obtain ⟨final, ⟨finalHistory, rfl⟩, finished⟩ :=
      StateTransition.tr_eval (Monodromy.ReversibleTuring.Compression.respects a q machine) ⟨history, rfl⟩ source_finished
    exact ⟨finalHistory, finished⟩
