-- Prove2me | solution 2 for Monodromy.Counter.Reversible.RadixObservation.reaches_result
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:03:19.76984+00:00
-- url     : https://prove2.me/submissions/dc242baa-b6d2-4a66-8113-c1a4a195ccee

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
public import Theorems.Thm_Monodromy_Counter_Reversible_Radix_reaches_result
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

























@[simp] theorem reverseAction_involutive (action : Action n) :
    reverseAction (reverseAction action) = action := by
  cases action <;> simp [reverseAction]



@[simp] theorem reverseAction_apply (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).apply (action.apply values) = values := by
  cases action with
  | test => rfl
  | shift register amount =>
      funext index
      by_cases selected : index = register
      · subst index
        simp [reverseAction, Action.apply]
      · simp [reverseAction, Action.apply, Function.update_of_ne selected]

@[simp] theorem reverseAction_enabled_apply (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).enabled (action.apply values) ↔ action.enabled values := by
  cases action <;> rfl



namespace Action



end Action



@[simp] theorem reverseEdge_involutive (edge : Edge n q) :
    reverseEdge (reverseEdge edge) = edge := by
  cases edge
  simp [reverseEdge]



@[simp] theorem reverseTable_involutive (table : Table n q e) :
    reverseTable (reverseTable table) = table := by
  funext index
  exact reverseEdge_involutive _





/-- Reversing an enabled edge retraces precisely the same values and control addresses. -/
theorem StepRel.reverse {table : Table n q e} {first last : State n q}
    (transition : StepRel table first last) : StepRel (reverseTable table) last first := by
  obtain ⟨index, enabled, rfl⟩ := transition
  refine ⟨index, ⟨rfl, ?_⟩, ?_⟩
  · exact (reverseAction_enabled_apply _ _).mpr enabled.2
  · apply Prod.ext
    · exact enabled.1
    · exact reverseAction_apply _ _

theorem StepRel_reverse_iff (table : Table n q e) (first last : State n q) :
    StepRel table first last ↔ StepRel (reverseTable table) last first := by
  constructor
  · exact StepRel.reverse
  · intro transition
    simpa only [reverseTable_involutive] using transition.reverse

/-- The bounded finite edge search realizes graph reversal exactly. -/
theorem step_reverse_iff (table : Table n q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (first last : State n q) :
    step table first = some last ↔ step (reverseTable table) last = some first := by
  rw [step_iff table deterministic,
    step_iff (reverseTable table) (reverseTable_deterministic table compatible), StepRel_reverse_iff]

/-- Every actual finite execution is traversable in reverse by the reversed static table. -/
theorem reaches_reverse (table : Table n q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State n q}
    (run : StateTransition.Reaches (step table) first last) :
    StateTransition.Reaches (step (reverseTable table)) last first := by
  apply Relation.ReflTransGen.mono (fun before after transition =>
    (step_reverse_iff table deterministic compatible after before).mp transition)
  exact Relation.ReflTransGen.swap last first run

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

/-- Inclusion of the chosen edges preserves live steps; exit edges may be added. -/
theorem step_map_live (source : Table n q e) (target : Table n k f)
    (control : Fin q → Fin k) (edge : Fin e → Fin f)
    (agrees : ∀ index, target (edge index) = mapEdge control (source index))
    (source_valid : Deterministic source) (target_valid : Deterministic target)
    {first last : State n q} (transition : step source first = some last) :
    step target (mapState control first) = some (mapState control last) := by
  obtain ⟨index, enabled, result⟩ := (step_iff source source_valid).mp transition
  apply (step_iff target target_valid).mpr
  refine ⟨edge index, ?_, ?_⟩
  · rw [agrees]
    exact ⟨congrArg control enabled.1, enabled.2⟩
  · rw [agrees]
    exact congrArg (mapState control) result

/-- Every finite source trace runs inside the target with its full register vector. -/
theorem reaches_map_live (source : Table n q e) (target : Table n k f)
    (control : Fin q → Fin k) (edge : Fin e → Fin f)
    (agrees : ∀ index, target (edge index) = mapEdge control (source index))
    (source_valid : Deterministic source) (target_valid : Deterministic target)
    {first last : State n q} (run : StateTransition.Reaches (step source) first last) :
    StateTransition.Reaches (step target) (mapState control first) (mapState control last) := by
  exact Relation.ReflTransGen.lift (mapState control)
    (fun _ _ transition => step_map_live source target control edge agrees
      source_valid target_valid transition) _ _ run



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

























/-- A wire is a literal equality of control positions, not a new transition. -/
theorem interface {exit entry : Fin q} (linked : wiring.link exit = some entry) :
    control wiring exit = control wiring entry := by
  apply congrArg (nodeEquiv wiring)
  apply Subtype.ext
  rw [representative_linked wiring exit entry linked,
    representative_unlinked wiring entry (wiring.terminal linked)]

























end Monodromy.Counter.Reversible.PortNetwork

end


/-!
## One reversible radix graph: unpacking and packing
-/

namespace Monodromy.Counter.Reversible.Radix

variable (p : ℕ) [NeZero p]
































































































/-- Reversing the same radix graph packs a quotient and its finite remainder. -/
theorem reverse_pack (quotient : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (step (reverseTable (table p)))
      (point p (finish p remainder) quotient 0)
      (point p (entry p) (p * quotient + remainder.val : ℕ) 0) := by
  have run := reaches_reverse (table p) (deterministic p) (targetCompatible p)
    (reaches_result p (p * quotient + remainder.val))
  have digit : Counter.DivMod.residue p (p * quotient + remainder.val) = remainder := by
    apply Fin.ext
    exact (Nat.mul_add_mod_self_left p quotient remainder.val).trans (Nat.mod_eq_of_lt remainder.isLt)
  have divide : (p * quotient + remainder.val) / p = quotient := by
    rw [Nat.add_comm, Nat.add_mul_div_left remainder.val quotient (Nat.pos_of_ne_zero (NeZero.ne p)),
      Nat.div_eq_of_lt remainder.isLt, Nat.zero_add]
  simpa only [digit, divide] using run



end Monodromy.Counter.Reversible.Radix

/-!
## Read-only remainder observation by identified radix ports
-/

noncomputable section

namespace Monodromy.Counter.Reversible.RadixObservation

variable (p m : ℕ) [NeZero p]































omit [NeZero p] in
@[simp] theorem finishQuery_finish (remainder : Fin p) :
    finishQuery p (Radix.finish p remainder) = some remainder := by
  simp [finishQuery, Radix.finish, Radix.block]









omit [NeZero p] in
@[simp] theorem link_finish (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (remainder : Fin p) :
    link p m permutation (rawControl p m 0 row (Radix.finish p remainder)) =
      some (rawControl p m 1 (permutation remainder row) (Radix.finish p remainder)) := by
  simp [link, rawControl]

















theorem front_finish (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) (remainder : Fin p) :
    front p m permutation row (Radix.finish p remainder) =
      back p m permutation (permutation remainder row) (Radix.finish p remainder) :=
  PortNetwork.interface _ (link_finish p m permutation row remainder)

@[simp] theorem table_front (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (index : Fin (Radix.edges p)) :
    table p m permutation (arcEquiv p m ((0, row), index)) =
      Glue.mapEdge (front p m permutation row) (Radix.table p index) := by
  change Glue.mapEdge (PortNetwork.control (wiring p m permutation))
    (rawTable p m (arcEquiv p m ((0, row), index))) = _
  rw [rawTable_arc]
  simp only [component, ite_true]
  rfl

@[simp] theorem table_back (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (index : Fin (Radix.edges p)) :
    table p m permutation (arcEquiv p m ((1, row), index)) =
      Glue.mapEdge (back p m permutation row) (reverseTable (Radix.table p) index) := by
  change Glue.mapEdge (PortNetwork.control (wiring p m permutation))
    (rawTable p m (arcEquiv p m ((1, row), index))) = _
  rw [rawTable_arc]
  simp only [component, Fin.isValue, Fin.reduceEq, ite_false]
  rfl



















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
open Monodromy.Counter.Reversible.RadixObservation
variable (p m : ℕ) [NeZero p]
theorem solution (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) (value : ℕ) :
    StateTransition.Reaches (step (table p m permutation))
      (point p m permutation (inputPort p m permutation row) value 0)
      (point p m permutation (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row)) value 0) := by
  have forward := Glue.reaches_map_live (Radix.table p) (table p m permutation)
    (front p m permutation row) (fun index => arcEquiv p m ((0, row), index))
    (fun index => table_front p m permutation row index)
    (Radix.deterministic p) (deterministic p m permutation) (Radix.reaches_result p value)
  have backward := Glue.reaches_map_live (reverseTable (Radix.table p)) (table p m permutation)
    (back p m permutation (permutation (Counter.DivMod.residue p value) row))
    (fun index => arcEquiv p m ((1, permutation (Counter.DivMod.residue p value) row), index))
    (fun index => table_back p m permutation _ index)
    (reverseTable_deterministic _ (Radix.targetCompatible p)) (deterministic p m permutation)
    (Radix.reverse_pack p (value / p) (Counter.DivMod.residue p value))
  change StateTransition.Reaches (step (table p m permutation))
    (point p m permutation (inputPort p m permutation row) value 0)
    (point p m permutation (front p m permutation row (Radix.finish p (Counter.DivMod.residue p value)))
      (value / p : ℕ) 0) at forward
  rw [front_finish] at forward
  change StateTransition.Reaches (step (table p m permutation))
    (point p m permutation (back p m permutation (permutation (Counter.DivMod.residue p value) row)
      (Radix.finish p (Counter.DivMod.residue p value))) (value / p : ℕ) 0)
    (point p m permutation (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row))
      (p * (value / p) + (Counter.DivMod.residue p value).val : ℕ) 0) at backward
  have restore : p * (value / p) + (Counter.DivMod.residue p value).val = value := by
    simpa only [Counter.DivMod.residue, Nat.add_comm] using Nat.mod_add_div value p
  rw [restore] at backward
  exact forward.trans backward
