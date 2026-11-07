-- Prove2me | solution 2 for Monodromy.Counter.Reversible.Recording.valid_step
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:02:09.002313+00:00
-- url     : https://prove2.me/submissions/de62fa88-48be-4a8f-a7b4-a3f4977c813a

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
public import Theorems.Thm_Monodromy_Counter_Reversible_Radix_valid_reverse_step
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













theorem enabled_project (register : Fin n → Fin m) (action : Action n) (values : Fin m → ℤ) :
    (mapAction register action).enabled values ↔ action.enabled (values ∘ register) := by
  cases action <;> rfl

theorem apply_project (register : Fin n → Fin m) (faithful : Function.Injective register)
    (action : Action n) (values : Fin m → ℤ) :
    (mapAction register action).apply values ∘ register = action.apply (values ∘ register) := by
  cases action with
  | test => rfl
  | shift index amount =>
      funext selected
      by_cases same : selected = index
      · subst selected
        simp [mapAction, Action.apply]
      · have distinct : register selected ≠ register index := fun equal => same (faithful equal)
        simp [mapAction, Action.apply, Function.update_of_ne, same, distinct]

/-- Protected registers retain their arbitrary prior values. -/
theorem apply_outside (register : Fin n → Fin m) (action : Action n) (values : Fin m → ℤ)
    (index : Fin m) (outside : ∀ selected, register selected ≠ index) :
    (mapAction register action).apply values index = values index := by
  cases action with
  | test => rfl
  | shift selected amount =>
      exact Function.update_of_ne (outside selected).symm _ _





















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
















































































theorem extraOperation_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraOperation program arc = .shift (Fin.castAdd 2 register) 1 := by
  unfold extraOperation
  split <;> simp_all




































private theorem tail_ne_old (index : Fin 2) (old : Fin n) :
    historyRegister n index ≠ Fin.castAdd 2 old := by
  intro same
  have values := congrArg Fin.val same
  simp only [historyRegister, Fin.val_natAdd, Fin.val_castAdd] at values
  omega























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

@[simp] theorem valid_port_iff (program : Counter.Program n m) (row : Fin m)
    (symbol : Fin (base m)) (values : Fin (n + 2) → ℤ) :
    Valid program (port row symbol, values) ↔
      OldNonnegative values ∧ 0 ≤ values (historyRegister n 0) ∧
        0 ≤ values (historyRegister n 1) := by
  change Valid program (copy row (Radix.finish (base m) symbol), values) ↔ _
  rw [valid_copy_iff]
  simp [Radix.Valid, Radix.finish, Radix.block, Radix.admissible]






private theorem old_nonnegative_mapped (action : Action 2) (values : Fin (n + 2) → ℤ)
    (old : OldNonnegative values) :
    OldNonnegative ((RegisterRelocation.mapAction (historyRegister n) action).apply values) := by
  intro index
  rw [RegisterRelocation.apply_outside (historyRegister n) action values (Fin.castAdd 2 index)
    (fun tail => tail_ne_old tail index)]
  exact old index

private theorem old_nonnegative_shift (register : Fin n) (amount : ℤ)
    (values : Fin (n + 2) → ℤ) (old : OldNonnegative values)
    (safe : 0 ≤ values (Fin.castAdd 2 register) + amount) :
    OldNonnegative (Action.apply (.shift (Fin.castAdd 2 register) amount) values) := by
  intro index
  by_cases selected : index = register
  · subst index
    simpa only [Action.apply, Function.update_self] using safe
  · simpa [Action.apply, selected] using old index

private theorem shift_old_tail (register : Fin n) (amount : ℤ)
    (values : Fin (n + 2) → ℤ) (tail : Fin 2) :
    Action.apply (.shift (Fin.castAdd 2 register) amount) values (historyRegister n tail) =
      values (historyRegister n tail) :=
  Function.update_of_ne (tail_ne_old tail register) _ _

private theorem valid_port_shift (program : Counter.Program n m) (row : Fin m)
    (symbol : Fin (base m)) (values : Fin (n + 2) → ℤ) (register : Fin n) (amount : ℤ)
    (old : OldNonnegative values) (safe : 0 ≤ values (Fin.castAdd 2 register) + amount)
    (history : 0 ≤ values (historyRegister n 0)) (workspace : 0 ≤ values (historyRegister n 1)) :
    Valid program (port row symbol, Action.apply (.shift (Fin.castAdd 2 register) amount) values) := by
  rw [valid_port_iff]
  exact ⟨old_nonnegative_shift register amount values old safe,
    by rw [shift_old_tail]; exact history,
    by rw [shift_old_tail]; exact workspace⟩

private theorem packing_valid_edge (program : Counter.Program n m) (row : Fin m)
    (index : Fin (Radix.edges (base m))) (values : Fin (n + 2) → ℤ)
    (valid : Valid program (copy row (packing n m index).source, values))
    (enabled : (packing n m index).action.enabled values) :
    Valid program (copy row (packing n m index).target, (packing n m index).action.apply values) := by
  rcases (valid_copy_iff program row _ values).mp valid with ⟨old, radix_valid⟩
  let original := reverseTable (Radix.table (base m)) index
  have guard : original.action.enabled (values ∘ historyRegister n) :=
    (RegisterRelocation.enabled_project (historyRegister n) original.action values).mp enabled
  have transition : step (reverseTable (Radix.table (base m)))
      (original.source, values ∘ historyRegister n) =
      some (original.target, original.action.apply (values ∘ historyRegister n)) := by
    apply (step_iff _ (reverseTable_deterministic _ (Radix.targetCompatible (base m)))).mpr
    exact ⟨index, ⟨rfl, guard⟩, rfl⟩
  have result := Radix.valid_reverse_step (base m) radix_valid transition
  rw [valid_copy_iff]
  refine ⟨old_nonnegative_mapped original.action values old, ?_⟩
  change Radix.Valid (base m)
    (original.target, (RegisterRelocation.mapAction (historyRegister n) original.action).apply values ∘
      historyRegister n)
  rw [RegisterRelocation.apply_project (historyRegister n) (historyRegister_injective n)]
  exact result

private theorem extra_valid_edge (program : Counter.Program n m) (arc : Extra program)
    (values : Fin (n + 2) → ℤ) (valid : Valid program ((extraEdge program arc).source, values))
    (enabled : (extraEdge program arc).action.enabled values) :
    Valid program ((extraEdge program arc).target, (extraEdge program arc).action.apply values) := by
  cases instruction : program arc.val.1 with
  | inc register target =>
      rw [extraEdge_inc program arc register target instruction] at valid enabled ⊢
      rcases (valid_dispatch_iff program arc.val.1 values).mp valid with ⟨old, history, empty⟩
      apply valid_port_shift program target (digit arc.val.1 0) values register 1 old
      · have nonnegative := old register
        omega
      · exact history
      · omega
  | dec register zero nonzero =>
      rw [extraEdge_dec program arc register zero nonzero instruction] at valid enabled ⊢
      rcases arc with ⟨⟨row, branch⟩, active⟩
      fin_cases branch
      · rcases (valid_dispatch_iff program row values).mp valid with ⟨old, history, empty⟩
        change Valid program (port zero (digit row 0), values)
        rw [valid_port_iff]
        exact ⟨old, history, by omega⟩
      · rcases (valid_dispatch_iff program row values).mp valid with ⟨old, history, empty⟩
        change Valid program (mid row, values)
        rw [valid_mid_iff, instruction]
        refine ⟨old, history, empty, ?_⟩
        change Action.enabled (.test (Fin.castAdd 2 register) false) values at enabled
        have not_zero : values (Fin.castAdd 2 register) ≠ 0 := by
          simpa only [Action.enabled, Bool.false_eq_true, iff_false] using enabled
        have nonnegative := old register
        omega
      · rcases (valid_mid_iff program row values).mp valid with ⟨old, history, empty, selected⟩
        have positive : 0 < values (Fin.castAdd 2 register) := by
          simpa only [instruction] using selected
        apply valid_port_shift program nonzero (digit row 1) values register (-1) old
        · omega
        · exact history
        · omega
  | halt =>
      have active := arc.property
      unfold Active at active
      rw [instruction] at active
      exact active.elim














































































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
theorem solution (program : Counter.Program n m) {first last : State (n + 2) (size m)}
    (valid : Valid program first) (transition : step (table program) first = some last) :
    Valid program last := by
  obtain ⟨index, enabled, rfl⟩ := (step_iff _ (deterministic program)).mp transition
  obtain ⟨arc, rfl⟩ := (arcEquiv program).surjective index
  rcases first with ⟨position, values⟩
  have position_eq : (arcEdge program arc).source = position := by
    simpa only [table_arc] using enabled.1
  subst position
  have action_enabled : (arcEdge program arc).action.enabled values := by
    simpa only [table_arc] using enabled.2
  clear enabled
  simp only [table_arc, Edge.execute]
  rcases arc with ⟨row, index⟩ | arc
  · exact packing_valid_edge program row index values valid action_enabled
  · exact extra_valid_edge program arc values valid action_enabled
