-- Prove2me | solution 2 for Monodromy.CounterPrimeProbe.restore_reaches
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:00:51.12274+00:00
-- url     : https://prove2.me/submissions/9b5ba1e7-27c8-4cfa-8d6f-17029e134d48

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





















end Monodromy.Counter.RegisterRelocation

namespace Monodromy.Counter

variable {n m k : ℕ}



/-- Running-row agreement preserves every finite path while leaving exits free for continuation. -/
theorem reaches_map_live (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, oldProgram label ≠ .halt →
      newProgram (address label) = mapInstruction address (oldProgram label))
    {first last : Configuration n m} (execution : StateTransition.Reaches (step oldProgram) first last) :
    StateTransition.Reaches (step newProgram)
      (mapConfiguration address first) (mapConfiguration address last) := by
  induction execution with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ running reached =>
      exact reached.tail (step_map_live address oldProgram newProgram agrees running)

end Monodromy.Counter

namespace Monodromy.CounterMultiplication











@[simp] theorem phase_zero (factor : ℕ) : phase factor 0 = 0 := by
  apply Fin.ext
  simp [phase]

theorem phase_val (factor remaining : ℕ) (bound : remaining ≤ factor) :
    (phase factor remaining).val = remaining :=
  Nat.mod_eq_of_lt (by omega)

theorem program_zero (factor : ℕ) :
    program factor 0 = .dec 0 (transfer factor) (phase factor factor) := by
  simp [program]

theorem program_phase (factor remaining : ℕ) (bound : remaining < factor) :
    program factor (phase factor (remaining + 1)) = .inc 1 (phase factor remaining) := by
  have current := phase_val factor (remaining + 1) (by omega)
  have inside : remaining + 1 ≤ factor := by omega
  simp [program, current, inside]

theorem program_transfer (factor : ℕ) :
    program factor (transfer factor) = .dec 1 (finish factor) (restore factor) := by
  simp [program, transfer]

theorem program_restore (factor : ℕ) :
    program factor (restore factor) = .inc 0 (transfer factor) := by
  have outside : ¬ factor + 2 ≤ factor := by omega
  simp [program, restore, outside]



theorem step_phase (factor remaining first second : ℕ) (bound : remaining < factor) :
    Counter.step (program factor) (configuration factor (phase factor (remaining + 1)) first second) =
      some (configuration factor (phase factor remaining) first (second + 1)) := by
  rw [Counter.step_inc (program factor) _ (program_phase factor remaining bound)]
  apply congrArg some
  congr 1
  funext register
  fin_cases register <;> simp [configuration, Function.update]



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



/-- Every countdown pass has a fixed finite length and retains the first register. -/
theorem increments_reach (factor remaining first second : ℕ) (bound : remaining ≤ factor) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor (phase factor remaining) first second)
      (configuration factor 0 first (second + remaining)) := by
  induction remaining generalizing second with
  | zero =>
      simp only [phase_zero, Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | succ remaining induction_hypothesis =>
      have first_step := step_phase factor remaining first second (by omega)
      have rest := induction_hypothesis (second := second + 1) (by omega)
      have arithmetic : second + 1 + remaining = second + (remaining + 1) := by omega
      rw [arithmetic] at rest
      exact Relation.ReflTransGen.head first_step rest



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





end Monodromy.CounterMultiplication

namespace Monodromy.Counter.DivMod

variable (p : ℕ) [NeZero p]
































































end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]





















@[simp] theorem program_mulAddress (address : Fin (p + 4)) :
    program p (mulAddress p address) =
      Counter.mapInstruction (mulAddress p) (CounterMultiplication.program p address) := by
  simp [program, mulAddress]















omit [NeZero p] in
private theorem mul_configuration (address : Fin (p + 4)) (first second : ℕ) :
    Counter.mapConfiguration (mulAddress p) (CounterMultiplication.configuration p address first second) =
      configuration p (mulAddress p address) first second := rfl























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
open Monodromy.CounterPrimeProbe
variable (p : ℕ) [NeZero p]
theorem solution (remainder : Fin p) (quotient : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (mulAddress p (CounterMultiplication.phase p remainder.val)) quotient 0)
      (configuration p (Monodromy.CounterPrimeProbe.failure p) (remainder.val + p * quotient) 0) := by
  have seeded := CounterMultiplication.increments_reach p remainder.val quotient 0
    (Nat.le_of_lt remainder.isLt)
  simp only [Nat.zero_add] at seeded
  have consumed := CounterMultiplication.consume_reach p quotient remainder.val
  have transferred := CounterMultiplication.transfer_reach p 0 (remainder.val + p * quotient)
  simp only [Nat.zero_add] at transferred
  have run : StateTransition.Reaches (Counter.step (CounterMultiplication.program p))
      (CounterMultiplication.configuration p (CounterMultiplication.phase p remainder.val) quotient 0)
      (CounterMultiplication.configuration p (CounterMultiplication.finish p) (remainder.val + p * quotient) 0) :=
    seeded.trans (consumed.trans
      (Relation.ReflTransGen.head
        (CounterMultiplication.step_begin_transfer p (remainder.val + p * quotient))
        (transferred.tail (CounterMultiplication.step_finish p (remainder.val + p * quotient)))))
  have mapped := Counter.reaches_map_live (mulAddress p) (CounterMultiplication.program p) (program p)
    (fun address _ => program_mulAddress p address) run
  simpa only [mul_configuration, Monodromy.CounterPrimeProbe.failure] using mapped
