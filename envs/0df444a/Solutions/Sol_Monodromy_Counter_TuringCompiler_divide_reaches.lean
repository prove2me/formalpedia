-- Prove2me | solution 1 for Monodromy.Counter.TuringCompiler.divide_reaches
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:00:00.181104+00:00
-- url     : https://prove2.me/submissions/acb9e061-2eb8-4e82-9a66-2314be4eb050

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
public import Theorems.Thm_Monodromy_Counter_DivMod_consume_reaches
public import Theorems.Thm_Monodromy_Counter_step_map_live

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











/-- A register injection preserves each complete step, including the zero and halt cases. -/
theorem step_embed (register : Fin n → Fin k) (faithful : Function.Injective register)
    (background : Fin k → ℕ) (source : Program n m) (state : Configuration n m) :
    step (program register source) (embed register background state) =
      (step source state).map (embed register background) := by
  cases operation : source state.pc with
  | inc index target =>
      simp [step, program, instruction, embed, operation, faithful.extend_apply, faithful.extend_update]
  | dec index zero nonzero =>
      cases value : state.counters index <;>
        simp [step, program, instruction, embed, operation, value,
          faithful.extend_apply, faithful.extend_update]
  | halt => simp [step, program, instruction, embed, operation]

/-- The same relocation transports any finite arithmetic macro run. -/
theorem reaches_embed (register : Fin n → Fin k) (faithful : Function.Injective register)
    (background : Fin k → ℕ) (source : Program n m) {first last : Configuration n m}
    (run : StateTransition.Reaches (step source) first last) :
    StateTransition.Reaches (step (program register source))
      (embed register background first) (embed register background last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous =>
      apply previous.tail
      have actual : step source _ = some _ := edge
      rw [step_embed register faithful background source, actual]
      rfl





theorem pairIntoThree_injective (active : Fin 2) : Function.Injective (pairIntoThree active) := by
  intro first second same
  fin_cases active <;> fin_cases first <;> fin_cases second <;>
    first | rfl | norm_num [pairIntoThree, Fin.ext_iff] at same

end Monodromy.Counter.RegisterRelocation

namespace Monodromy.Counter

variable {n m k : ℕ}





end Monodromy.Counter

namespace Monodromy.CounterMultiplication

















































end Monodromy.CounterMultiplication

namespace Monodromy.Counter.DivMod

variable (p : ℕ) [NeZero p]















@[simp] theorem program_transfer (remainder : Fin p) :
    program p (transfer p remainder) = .dec 1 (finish p remainder) (restore p remainder) := by
  have first : ¬ p + remainder.val < p := by omega
  have second : p + remainder.val < 2 * p := by omega
  simp [program, transfer, first, second]

@[simp] theorem program_restore (remainder : Fin p) :
    program p (restore p remainder) = .inc 0 (transfer p remainder) := by
  have first : ¬ 2 * p + remainder.val < p := by omega
  have second : ¬ 2 * p + remainder.val < 2 * p := by omega
  have third : 2 * p + remainder.val < 3 * p := by omega
  simp [program, restore, first, second, third]

@[simp] theorem program_finish (remainder : Fin p) : program p (finish p remainder) = .halt := by
  have first : ¬ 3 * p + remainder.val < p := by omega
  have second : ¬ 3 * p + remainder.val < 2 * p := by omega
  have third : ¬ 3 * p + remainder.val < 3 * p := by omega
  have fourth : 3 * p + remainder.val < 4 * p := by omega
  simp [program, finish, first, second, third, fourth]





private theorem update_first (first second value : ℕ) :
    Function.update ![first, second] 0 value = ![value, second] := by
  funext index
  fin_cases index <;> simp

private theorem update_second (first second value : ℕ) :
    Function.update ![first, second] 1 value = ![first, value] := by
  funext index
  fin_cases index <;> simp







@[simp] theorem step_transfer_zero (remainder : Fin p) (first : ℕ) :
    Counter.step (program p) (configuration p (transfer p remainder) first 0) =
      some (configuration p (finish p remainder) first 0) := by
  simp [Counter.step, configuration]

@[simp] theorem step_transfer_succ (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (transfer p remainder) first (second + 1)) =
      some (configuration p (restore p remainder) first second) := by
  simp [Counter.step, configuration, update_second]

@[simp] theorem step_restore (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (restore p remainder) first second) =
      some (configuration p (transfer p remainder) (first + 1) second) := by
  simp [Counter.step, configuration, update_first]








private theorem reaches_step {first second : Counter.Configuration 2 (size p)}
    (edge : Counter.step (program p) first = some second) :
    StateTransition.Reaches (Counter.step (program p)) first second := by
  apply Relation.ReflTransGen.single
  exact edge

private theorem prepend {first middle last : Counter.Configuration 2 (size p)}
    (edge : Counter.step (program p) first = some middle)
    (rest : StateTransition.Reaches (Counter.step (program p)) middle last) :
    StateTransition.Reaches (Counter.step (program p)) first last := by
  change Relation.ReflTransGen (fun a b => b ∈ Counter.step (program p) a) _ _
  exact Relation.ReflTransGen.head edge rest



/-- Moving the workspace back preserves its finite remainder address. -/
theorem transfer_reaches (remainder : Fin p) (first second : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (transfer p remainder) first second)
      (configuration p (finish p remainder) (first + second) 0) := by
  induction second generalizing first with
  | zero =>
      simpa only [Nat.add_zero] using
        (reaches_step p (step_transfer_zero p remainder first))
  | succ second recursive =>
      have run := prepend p (step_transfer_succ p remainder first second)
        (prepend p (step_restore p remainder first second) (recursive (first + 1)))
      simpa only [Nat.add_assoc, Nat.add_comm 1 second] using run

/-- The division macro uses no unbounded storage besides its two input counters. -/
theorem reaches_divmod (input : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (consume p 0) input 0)
      (configuration p (finish p (residue p input)) (input / p) 0) := by
  have consumed := consume_reaches p input 0 0
  simp only [Fin.val_zero, Nat.add_zero, Nat.zero_add] at consumed
  have restored := transfer_reaches p (residue p input) 0 (input / p)
  simp only [Nat.zero_add] at restored
  exact consumed.trans restored



omit [NeZero p] in
/-- Distinct bounded remainders remain distinct final program addresses. -/
theorem finish_injective : Function.Injective (finish p) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  dsimp [finish] at values
  omega



end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]





























































end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]




















omit [NeZero a] [NeZero q] in
@[simp] theorem address_divide (row : Row a q) (cell : Fin (DivMod.size (base a))) :
    (address a q).symm (divide a q row cell) =
      (row, Sum.inr (Sum.inr (Sum.inr cell))) :=
  (address a q).symm_apply_apply _




















omit [NeZero q] in
@[simp] theorem divTarget_finish (row : Row a q) (target : Fin q)
    (remainder : Fin (base a)) :
    divTarget a q row target (DivMod.finish (base a) remainder) =
      dispatch a q (target, symbol a remainder) := by
  have terminal : ∃ r, DivMod.finish (base a) remainder = DivMod.finish (base a) r :=
    ⟨remainder, rfl⟩
  have chosen : terminal.choose = remainder :=
    (DivMod.finish_injective (base a) terminal.choose_spec).symm
  simp only [divTarget, dite_eq_left terminal, chosen]





















omit [NeZero a] [NeZero q] in
theorem divide_not_boundary (row : Row a q) (cell : Fin (DivMod.size (base a))) :
    ¬ Boundary a q (divide a q row cell) := by
  rintro ⟨other, same⟩
  have incompatible := congrArg Prod.snd ((address a q).injective same)
  cases incompatible





private theorem map_internal {m : ℕ}
    (machine : TM0.Machine (Fin a) (Fin q)) (oldProgram : Program 3 m)
    (rename : Fin m → Fin (size a q))
    (agrees : ∀ cell, oldProgram cell ≠ .halt →
      program a q machine (rename cell) = mapInstruction rename (oldProgram cell))
    (internal : ∀ cell, oldProgram cell ≠ .halt → ¬ Boundary a q (rename cell))
    {first last : Configuration 3 m}
    (run : StateTransition.Reaches (step oldProgram) first last) :
    InternalReaches a q machine (mapConfiguration rename first) (mapConfiguration rename last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | @tail middle last _ edge previous =>
      apply previous.tail
      constructor
      · exact step_map_live rename oldProgram (program a q machine) agrees edge
      · apply internal
        intro halted
        simp [step, halted] at edge



private theorem div_live (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (cell : Fin (DivMod.size (base a)))
    (live : RegisterRelocation.program
      (RegisterRelocation.pairIntoThree (popRegister direction))
      (DivMod.program (base a)) cell ≠ .halt) :
    program a q machine (divTarget a q row target cell) =
      mapInstruction (divTarget a q row target)
        (RegisterRelocation.program
          (RegisterRelocation.pairIntoThree (popRegister direction))
          (DivMod.program (base a)) cell) ∧
    ¬ Boundary a q (divTarget a q row target cell) := by
  have not_finish : ¬ ∃ remainder, cell = DivMod.finish (base a) remainder := by
    rintro ⟨remainder, rfl⟩
    simp [RegisterRelocation.program, RegisterRelocation.instruction] at live
  constructor
  · simp [divTarget, not_finish, program, body, selected, RegisterRelocation.program]
  · simpa only [divTarget, dite_eq_right not_finish] using divide_not_boundary a q row cell



private theorem extend_frame (active : Fin 2) (old value spectator : ℕ) :
    Function.extend (RegisterRelocation.pairIntoThree active) ![value, 0]
      (frame active old spectator) = frame active value spectator := by
  have first := (RegisterRelocation.pairIntoThree_injective active).extend_apply
    ![value, 0] (frame active old spectator) (0 : Fin 2)
  have scratch := (RegisterRelocation.pairIntoThree_injective active).extend_apply
    ![value, 0] (frame active old spectator) (1 : Fin 2)
  fin_cases active <;> funext index <;> fin_cases index
  all_goals first
    | exact first
    | exact scratch
    | apply Function.extend_apply'
      rintro ⟨source, same⟩
      fin_cases source <;> norm_num [RegisterRelocation.pairIntoThree, Fin.ext_iff] at same





























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
open Monodromy.Counter.TuringCompiler
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]
theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (value spectator : ℕ) :
    InternalReaches a q machine
      ⟨divTarget a q row target (DivMod.consume (base a) 0),
        frame (popRegister direction) value spectator⟩
      ⟨dispatch a q (target, symbol a (DivMod.residue (base a) value)),
        frame (popRegister direction) (value / base a) spectator⟩ := by
  have relocated := RegisterRelocation.reaches_embed
    (RegisterRelocation.pairIntoThree (popRegister direction))
    (RegisterRelocation.pairIntoThree_injective (popRegister direction))
    (frame (popRegister direction) value spectator)
    (DivMod.program (base a)) (DivMod.reaches_divmod (base a) value)
  have embedded := map_internal a q machine _ (divTarget a q row target)
    (fun cell live => (div_live a q machine row target direction selected cell live).1)
    (fun cell live => (div_live a q machine row target direction selected cell live).2)
    relocated
  simpa only [mapConfiguration, RegisterRelocation.embed, DivMod.configuration,
    extend_frame, divTarget_finish] using embedded
