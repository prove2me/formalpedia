-- Prove2me | solution 1 for Monodromy.Counter.TuringCompiler.multiply_reaches
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:00:02.332245+00:00
-- url     : https://prove2.me/submissions/fbac510c-5279-47da-b7a3-5001b999dbc2

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
public import Theorems.Thm_Monodromy_CounterMultiplication_consume_reach
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















theorem program_zero (factor : ℕ) :
    program factor 0 = .dec 0 (transfer factor) (phase factor factor) := by
  simp [program]



theorem program_transfer (factor : ℕ) :
    program factor (transfer factor) = .dec 1 (finish factor) (restore factor) := by
  simp [program, transfer]

theorem program_restore (factor : ℕ) :
    program factor (restore factor) = .inc 0 (transfer factor) := by
  have outside : ¬ factor + 2 ≤ factor := by omega
  simp [program, restore, outside]

theorem program_finish (factor : ℕ) : program factor (finish factor) = .halt := by
  have outside : ¬ factor + 3 ≤ factor := by omega
  simp [program, finish, outside]





theorem step_begin_transfer (factor second : ℕ) :
    Counter.step (program factor) (configuration factor 0 0 second) =
      some (configuration factor (transfer factor) 0 second) :=
  Counter.step_dec_zero (program factor) _ (program_zero factor) rfl

theorem step_transfer (factor first second : ℕ) :
    Counter.step (program factor) (configuration factor (transfer factor) first (second + 1)) =
      some (configuration factor (restore factor) first second) := by
  rw [Counter.step_dec_succ (program factor) _ (program_transfer factor) rfl]
  apply congrArg some
  congr 1
  funext register
  fin_cases register <;> simp [configuration, Function.update]

theorem step_restore (factor first second : ℕ) :
    Counter.step (program factor) (configuration factor (restore factor) first second) =
      some (configuration factor (transfer factor) (first + 1) second) := by
  rw [Counter.step_inc (program factor) _ (program_restore factor)]
  apply congrArg some
  congr 1
  funext register
  fin_cases register <;> simp [configuration, Function.update]

theorem step_finish (factor first : ℕ) :
    Counter.step (program factor) (configuration factor (transfer factor) first 0) =
      some (configuration factor (finish factor) first 0) :=
  Counter.step_dec_zero (program factor) _ (program_transfer factor) rfl







/-- The final loop transfers the second register into the first, leaving zero behind. -/
theorem transfer_reach (factor first second : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor (transfer factor) first second)
      (configuration factor (transfer factor) (first + second) 0) := by
  induction second generalizing first with
  | zero =>
      simp only [Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | succ second induction_hypothesis =>
      have rest := induction_hypothesis (first := first + 1)
      have arithmetic : first + 1 + second = first + (second + 1) := by omega
      rw [arithmetic] at rest
      exact Relation.ReflTransGen.head (step_transfer factor first second)
        (Relation.ReflTransGen.head (step_restore factor first second) rest)

/-- Entry and exit are explicit cells of the same finite two-counter table. -/
theorem reaches_result (factor input : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor 0 input 0)
      (configuration factor (finish factor) (factor * input) 0) := by
  have consumed := consume_reach factor input 0
  simp only [Nat.zero_add] at consumed
  have moved := transfer_reach factor 0 (factor * input)
  simp only [Nat.zero_add] at moved
  exact consumed.trans (Relation.ReflTransGen.head (step_begin_transfer factor (factor * input))
    (moved.tail (step_finish factor (factor * input))))



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


















omit [NeZero a] [NeZero q] in
@[simp] theorem address_multiply (row : Row a q) (cell : Fin (base a + 4)) :
    (address a q).symm (multiply a q row cell) = (row, Sum.inr (Sum.inl cell)) :=
  (address a q).symm_apply_apply _




















omit [NeZero a] [NeZero q] in
@[simp] theorem mulTarget_finish (row : Row a q) :
    mulTarget a q row (CounterMultiplication.finish (base a)) = add a q row row.2 := by
  simp [mulTarget]



















omit [NeZero a] [NeZero q] in
theorem multiply_not_boundary (row : Row a q) (cell : Fin (base a + 4)) :
    ¬ Boundary a q (multiply a q row cell) := by
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

private theorem mul_live (machine : TM0.Machine (Fin a) (Fin q))
    (row : Row a q) (target : Fin q) (direction : Dir)
    (selected : machine row.1 row.2 = some (target, .move direction))
    (cell : Fin (base a + 4))
    (live : RegisterRelocation.program
      (RegisterRelocation.pairIntoThree (pushRegister direction))
      (CounterMultiplication.program (base a)) cell ≠ .halt) :
    program a q machine (mulTarget a q row cell) =
      mapInstruction (mulTarget a q row)
        (RegisterRelocation.program
          (RegisterRelocation.pairIntoThree (pushRegister direction))
          (CounterMultiplication.program (base a)) cell) ∧
    ¬ Boundary a q (mulTarget a q row cell) := by
  have not_finish : cell ≠ CounterMultiplication.finish (base a) := by
    intro same
    subst cell
    simp [RegisterRelocation.program, RegisterRelocation.instruction,
      CounterMultiplication.program_finish] at live
  constructor
  · simp [mulTarget, not_finish, program, body, selected, RegisterRelocation.program]
  · simpa only [mulTarget, ite_eq_right not_finish] using multiply_not_boundary a q row cell





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
      ⟨mulTarget a q row 0, frame (pushRegister direction) value spectator⟩
      ⟨add a q row row.2, frame (pushRegister direction) (base a * value) spectator⟩ := by
  have relocated := RegisterRelocation.reaches_embed
    (RegisterRelocation.pairIntoThree (pushRegister direction))
    (RegisterRelocation.pairIntoThree_injective (pushRegister direction))
    (frame (pushRegister direction) value spectator)
    (CounterMultiplication.program (base a))
    (CounterMultiplication.reaches_result (base a) value)
  have embedded := map_internal a q machine _ (mulTarget a q row)
    (fun cell live => (mul_live a q machine row target direction selected cell live).1)
    (fun cell live => (mul_live a q machine row target direction selected cell live).2)
    relocated
  simpa only [mapConfiguration, RegisterRelocation.embed, CounterMultiplication.configuration,
    extend_frame, mulTarget_finish] using embedded
