-- Prove2me | solution 1 for Monodromy.Counter.Reversible.PrimeCompression.integer_internal_reaches
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:05:32.940092+00:00
-- url     : https://prove2.me/submissions/1624c839-a11b-4ccb-b80d-958a04634279

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
public import Theorems.Thm_Monodromy_Counter_Reversible_PrimeCompression_step_firstReturn

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

/-- An unmarked source step remains unmarked throughout its entire compiled execution. -/
theorem integer_unmarked_step (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action) (mark : Fin q → Bool)
    {first last : State n q} (transition : step source first = some last)
    (unmarked : mark first.1 = false)
    (first_natural : ∀ index, 0 ≤ first.2 index) (last_natural : ∀ index, 0 ≤ last.2 index) :
    InternalMarkedReaches basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  obtain ⟨_, _, next, initial, inside⟩ :=
    integer_step_firstReturn basis source deterministic compatible unit transition first_natural last_natural
  apply Relation.ReflTransGen.head (b := next) ?_
    (internal_to_marked basis source deterministic compatible mark inside)
  refine ⟨initial, ?_⟩
  rw [marked_encode_iff]
  change ¬ mark first.1 = true
  rw [unmarked]
  decide





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
open Monodromy.Counter.Reversible.PrimeCompression
variable {n q e : ℕ}
theorem solution (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action) (mark : Fin q → Bool)
    (valid : State n q → Prop) (stable : Stable source valid)
    (nonnegative : ∀ state, valid state → ∀ index, 0 ≤ state.2 index)
    {first last : State n q}
    (run : Relation.ReflTransGen (fun current next : State n q =>
      step source current = some next ∧ mark current.1 = false) first last)
    (first_valid : valid first) :
    InternalMarkedReaches basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
  have lifted : valid last ∧ InternalMarkedReaches basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by
    induction run with
    | refl => exact ⟨first_valid, Relation.ReflTransGen.refl⟩
    | tail _ edge previous =>
        have last_valid := stable previous.1 edge.1
        exact ⟨last_valid, previous.2.trans
          (integer_unmarked_step basis source deterministic compatible unit mark edge.1 edge.2
            (nonnegative _ previous.1) (nonnegative _ last_valid))⟩
  exact lifted.2
