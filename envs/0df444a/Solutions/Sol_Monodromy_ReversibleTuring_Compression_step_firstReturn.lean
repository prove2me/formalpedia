-- Prove2me | solution 1 for Monodromy.ReversibleTuring.Compression.step_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:06:31.972317+00:00
-- url     : https://prove2.me/submissions/33a79504-211c-494b-9a53-37b720500cc5

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
public import Theorems.Thm_Monodromy_Counter_Reversible_PrimeCompression_integer_internal_reaches
public import Theorems.Thm_Monodromy_Counter_Reversible_PrimeCompression_step_firstReturn
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_valid_nonnegative
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_valid_step
public import Theorems.Thm_Monodromy_ReversibleTuring_step_firstReturn

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

@[simp] theorem unitShift_reverse (action : Action n) :
    UnitShift (reverseAction action) ↔ UnitShift action := by
  cases action with
  | test => rfl
  | shift register amount =>
      change (-amount = 1 ∨ -amount = -1) ↔ amount = 1 ∨ amount = -1
      omega

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



@[simp] theorem unitShift_mapAction (register : Fin n → Fin m) (action : Action n) :
    Action.UnitShift (mapAction register action) ↔ Action.UnitShift action := by
  cases action <;> rfl



































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





































theorem unitShift (index : Fin (edges p)) : Action.UnitShift (table p index).action := by
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  rw [table_arc]
  change Action.UnitShift (operation p arc)
  rcases arc with position | ⟨remainder, phase⟩
  · fin_cases position <;> simp [operation, Action.UnitShift]
  · fin_cases phase <;> simp [operation, Action.UnitShift]






























































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


















theorem stable (program : Counter.Program n m) : Stable (table program) (Valid program) :=
  fun {_ _} valid transition => valid_step program valid transition






































































private theorem extra_unitShift (program : Counter.Program n m) (arc : Extra program) :
    Action.UnitShift (extraOperation program arc) := by
  cases instruction : program arc.val.1 with
  | inc register target =>
      rw [extraOperation_inc program arc register target instruction]
      exact Or.inl rfl
  | dec register zero nonzero =>
      rw [extraOperation_dec program arc register zero nonzero instruction]
      rcases arc with ⟨⟨row, branch⟩, active⟩
      fin_cases branch <;> simp [Action.UnitShift]
  | halt =>
      have active := arc.property
      unfold Active at active
      rw [instruction] at active
      exact active.elim

/-- Every shift of the statically compiled recording graph is exactly one unit. -/
theorem unitShift (program : Counter.Program n m) (index : Fin (edges program)) :
    Action.UnitShift (table program index).action := by
  obtain ⟨arc, rfl⟩ := (arcEquiv program).surjective index
  rw [table_arc]
  rcases arc with ⟨row, edge⟩ | arc
  · change Action.UnitShift
      (RegisterRelocation.mapAction (historyRegister n)
        (reverseAction (Radix.table (base m) edge).action))
    rw [RegisterRelocation.unitShift_mapAction, Action.unitShift_reverse]
    exact Radix.unitShift (base m) edge
  · exact extra_unitShift program arc

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







































































































theorem naturalState_toNatural (state : State n q) (nonnegative : ∀ index, 0 ≤ state.2 index) :
    naturalState (toNatural state) = state := by
  apply Prod.ext
  · rfl
  · funext index
    exact Int.toNat_of_nonneg (nonnegative index)





/-- Integer source endpoints on the natural lattice retain the exact compiled first return. -/
theorem integer_step_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action)
    {first last : State n q} (transition : step source first = some last)
    (first_natural : ∀ index, 0 ≤ first.2 index) (last_natural : ∀ index, 0 ≤ last.2 index) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  apply step_firstReturn basis source deterministic compatible unit
  rw [naturalState_toNatural first first_natural, naturalState_toNatural last last_natural]
  exact transition



theorem marked_boundary (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    {mark : Fin q → Bool} {state : State 2 (size basis source deterministic compatible)}
    (marked : Marked basis source deterministic compatible mark state) :
    Boundary basis source deterministic compatible state := by
  obtain ⟨position, equal, _⟩ := marked
  exact ⟨position, equal⟩

theorem marked_encode_iff (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (mark : Fin q → Bool) (state : Counter.Configuration n q) :
    Marked basis source deterministic compatible mark
      (encode basis source deterministic compatible state) ↔ mark state.pc = true := by
  constructor
  · rintro ⟨position, equal, marked⟩
    have addresses := boundary_injective basis source
      (PortNetwork.control_unlinked_injective (wiring basis source deterministic compatible)
        (boundary_link_none basis source deterministic compatible state.pc)
        (boundary_link_none basis source deterministic compatible position) equal)
    rw [addresses]
    exact marked
  · exact fun marked => ⟨state.pc, rfl, marked⟩







private theorem internal_to_marked (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source) (mark : Fin q → Bool)
    {first last : State 2 (size basis source deterministic compatible)}
    (run : InternalReaches basis source deterministic compatible first last) :
    InternalMarkedReaches basis source deterministic compatible mark first last := by
  exact Relation.ReflTransGen.mono
    (fun _ _ edge => ⟨edge.1, fun marked => edge.2 (marked_boundary basis source deterministic compatible marked)⟩)
    _ _ run





/-- A marked source first return has exactly the same complete compressed endpoints. -/
theorem marked_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action) (mark : Fin q → Bool)
    (valid : State n q → Prop) (stable : Stable source valid)
    (nonnegative : ∀ state, valid state → ∀ index, 0 ≤ state.2 index)
    {first middle last : State n q} (initial : step source first = some middle)
    (rest : Relation.ReflTransGen (fun current next : State n q =>
      step source current = some next ∧ mark current.1 = false) middle last)
    (first_marked : mark first.1 = true) (last_marked : mark last.1 = true) (first_valid : valid first) :
    MarkedFirstReturn basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  have middle_valid := stable first_valid initial
  obtain ⟨_, _, next, head, inside⟩ := integer_step_firstReturn basis source deterministic compatible unit
    initial (nonnegative _ first_valid) (nonnegative _ middle_valid)
  refine ⟨(marked_encode_iff basis source deterministic compatible mark _).mpr first_marked,
    (marked_encode_iff basis source deterministic compatible mark _).mpr last_marked,
    next, head, ?_⟩
  exact (internal_to_marked basis source deterministic compatible mark inside).trans
    (integer_internal_reaches basis source deterministic compatible unit mark valid stable nonnegative rest middle_valid)

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

























theorem sourceMark_true_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 4 (Recording.size (RecordedTuring.size a q machine))) :
    sourceMark a q machine state.1 = true ↔ ReversibleTuring.Boundary a q machine state := by
  change decide (Recording.Marked (n := 2) (NativeTuring.counterMark a q machine)
    (state.1, fun _ => 0)) = true ↔
      Recording.Marked (n := 2) (NativeTuring.counterMark a q machine) (state.1, fun _ => 0)
  exact ⟨of_decide_eq_true, decide_eq_true⟩

theorem sourceMark_false_iff (machine : TM0.Machine (Fin a) (Fin q))
    (state : State 4 (Recording.size (RecordedTuring.size a q machine))) :
    sourceMark a q machine state.1 = false ↔ ¬ ReversibleTuring.Boundary a q machine state := by
  rw [← sourceMark_true_iff a q machine state]
  cases sourceMark a q machine state.1 <;> decide





































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
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      PrimeCompression.MarkedFirstReturn basis (ReversibleTuring.table a q machine)
        (source_deterministic a q machine) (source_targetCompatible a q machine)
        (sourceMark a q machine)
        (Monodromy.ReversibleTuring.Compression.encode a q machine first history) (Monodromy.ReversibleTuring.Compression.encode a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, first_marked, last_marked, middle, initial, rest⟩ :=
    ReversibleTuring.step_firstReturn a q machine transition history
  have source_rest : Relation.ReflTransGen
      (fun current next : State 4 (Recording.size (RecordedTuring.size a q machine)) =>
        step (ReversibleTuring.table a q machine) current = some next ∧
          sourceMark a q machine current.1 = false)
      middle (ReversibleTuring.encode a q machine last finalHistory) := by
    exact Relation.ReflTransGen.mono
      (fun current _ edge => ⟨edge.1, (sourceMark_false_iff a q machine current).mpr edge.2⟩)
      _ _ rest
  have first_valid : Recording.Valid (NativeTuring.source2 a q machine)
      (ReversibleTuring.encode a q machine first history) :=
    Recording.valid_encode (NativeTuring.source2 a q machine)
      (RecordedTuring.counterEncode a q machine first) history
  have actual := PrimeCompression.marked_firstReturn basis (ReversibleTuring.table a q machine)
    (source_deterministic a q machine) (source_targetCompatible a q machine)
    (Recording.unitShift (NativeTuring.source2 a q machine)) (sourceMark a q machine)
    (Recording.Valid (NativeTuring.source2 a q machine))
    (Recording.stable (NativeTuring.source2 a q machine))
    (Recording.valid_nonnegative (NativeTuring.source2 a q machine)) initial source_rest
    ((sourceMark_true_iff a q machine (ReversibleTuring.encode a q machine first history)).mpr first_marked)
    ((sourceMark_true_iff a q machine (ReversibleTuring.encode a q machine last finalHistory)).mpr last_marked)
    first_valid
  exact ⟨finalHistory, grew, actual⟩
