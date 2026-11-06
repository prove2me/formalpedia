-- Prove2me | solution 1 for Monodromy.CounterPrimeProbe.restore_reaches
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:12:47.748911+00:00
-- url     : https://prove2.me/submissions/2b8fe0d0-ea82-45d6-b3d9-708979571104

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

@[expose] public section

open Monodromy
open Monodromy.CounterPrimeProbe
variable (p : ℕ) [NeZero p]

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

/-- Finite prefixes may be linked into a new program by replacing only their halt exits. -/
theorem step_map_live (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, oldProgram label ≠ .halt →
      newProgram (address label) = mapInstruction address (oldProgram label))
    {state result : Configuration n m} (running : step oldProgram state = some result) :
    step newProgram (mapConfiguration address state) = some (mapConfiguration address result) := by
  have live : oldProgram state.pc ≠ .halt := by
    intro stopped
    simp [step, stopped] at running
  have same : step newProgram (mapConfiguration address state) =
      (step oldProgram state).map (mapConfiguration address) := by
    unfold step
    simp only [mapConfiguration, agrees state.pc live]
    cases instruction : oldProgram state.pc with
    | inc => rfl
    | dec register =>
        cases value : state.counters register <;> simp [mapInstruction, mapConfiguration, value]
    | halt => rfl
  rw [running] at same
  exact same

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

theorem step_consume (factor first second : ℕ) :
    Counter.step (program factor) (configuration factor 0 (first + 1) second) =
      some (configuration factor (phase factor factor) first second) := by
  rw [Counter.step_dec_succ (program factor) _ (program_zero factor) rfl]
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

/-- Consuming the first register adds exactly factor times its original value to the second. -/
theorem consume_reach (factor first second : ℕ) :
    StateTransition.Reaches (Counter.step (program factor))
      (configuration factor 0 first second)
      (configuration factor 0 0 (second + factor * first)) := by
  induction first generalizing second with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      exact Relation.ReflTransGen.refl
  | succ first induction_hypothesis =>
      have pass : StateTransition.Reaches (Counter.step (program factor))
          (configuration factor 0 (first + 1) second)
          (configuration factor 0 first (second + factor)) :=
        Relation.ReflTransGen.head (step_consume factor first second)
          (increments_reach factor factor first second (by omega))
      have rest := induction_hypothesis (second := second + factor)
      have arithmetic : second + factor + factor * first = second + factor * (first + 1) := by ring
      rw [arithmetic] at rest
      exact pass.trans rest

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

namespace Monodromy.CounterPrimeProbe

@[simp] theorem program_mulAddress (address : Fin (p + 4)) :
    program p (mulAddress p address) =
      Counter.mapInstruction (mulAddress p) (CounterMultiplication.program p address) := by
  simp [program, mulAddress]

omit [NeZero p] in
private theorem mul_configuration (address : Fin (p + 4)) (first second : ℕ) :
    Counter.mapConfiguration (mulAddress p) (CounterMultiplication.configuration p address first second) =
      configuration p (mulAddress p address) first second := rfl

end Monodromy.CounterPrimeProbe

/-- The multiplier countdown first writes the bounded remainder, then restores the original number. -/
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
