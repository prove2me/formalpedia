-- Prove2me | solution 1 for Monodromy.Counter.Compression.step_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:37:26.458609+00:00
-- url     : https://prove2.me/submissions/a5b6b269-25c2-413d-ae58-ab10171291ec

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
open Monodromy.Counter
open Monodromy.Counter.Compression
variable {m : ℕ}

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
theorem step_halt (instruction : program state.pc = .halt) :
    step program state = none := by
  simp [step, instruction]
variable {k : ℕ}
theorem mapConfiguration_injective (address : Fin m → Fin k)
    (faithful : Function.Injective address) :
    Function.Injective (mapConfiguration (n := n) address) := by
  intro first second same
  cases first
  cases second
  congr 1
  · exact faithful (congrArg Configuration.pc same)
  · exact congrArg Configuration.counters same
theorem step_map (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, newProgram (address label) = mapInstruction address (oldProgram label))
    (state : Configuration n m) :
    step newProgram (mapConfiguration address state) =
      (step oldProgram state).map (mapConfiguration address) := by
  unfold step
  simp only [mapConfiguration, agrees]
  cases instruction : oldProgram state.pc with
  | inc => rfl
  | dec register =>
      cases value : state.counters register <;> simp [mapInstruction, mapConfiguration, value]
  | halt => rfl
end Monodromy.Counter
namespace Monodromy.PrimeCode
namespace Basis
variable {n : ℕ} (basis : Basis n)
theorem encode_positive (registers : Fin n → ℕ) : 0 < basis.encode registers := by
  apply Finset.prod_pos
  intro index _
  exact pow_pos (basis.isPrime index).pos _
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
theorem encode_injective : Function.Injective basis.encode := basis.decode_encode.injective
@[simp] theorem encode_zero : basis.encode (fun _ => 0) = 1 := by simp [encode]
theorem encode_increment (registers : Fin n → ℕ) (index : Fin n) :
    basis.encode (Function.update registers index (registers index + 1)) =
      basis.prime index * basis.encode registers := by
  unfold encode
  rw [Fintype.prod_eq_mul_prod_compl index, Fintype.prod_eq_mul_prod_compl index]
  rw [Function.update_self, pow_succ]
  have unchanged :
      (∏ other ∈ ({index}ᶜ : Finset (Fin n)), basis.prime other ^
        Function.update registers index (registers index + 1) other) =
      ∏ other ∈ ({index}ᶜ : Finset (Fin n)), basis.prime other ^ registers other := by
    apply Finset.prod_congr rfl
    intro other present
    have different : other ≠ index := by simpa using present
    rw [Function.update_of_ne different]
  rw [unchanged]
  ac_rfl
theorem prime_dvd_encode_iff (registers : Fin n → ℕ) (index : Fin n) :
    basis.prime index ∣ basis.encode registers ↔ registers index ≠ 0 := by
  rw [(basis.isPrime index).dvd_iff_one_le_factorization (basis.encode_positive registers).ne',
    basis.factorization_encode]
  omega
theorem register_zero_iff (registers : Fin n → ℕ) (index : Fin n) :
    registers index = 0 ↔ ¬ basis.prime index ∣ basis.encode registers := by
  rw [basis.prime_dvd_encode_iff]
  omega
theorem remainder_zero_iff (registers : Fin n → ℕ) (index : Fin n) :
    basis.encode registers % basis.prime index = 0 ↔ registers index ≠ 0 := by
  rw [← Nat.dvd_iff_mod_eq_zero, basis.prime_dvd_encode_iff]
theorem encode_decrement (registers : Fin n → ℕ) (index : Fin n)
    (nonzero : registers index ≠ 0) :
    basis.encode (Function.update registers index (registers index - 1)) =
      basis.encode registers / basis.prime index := by
  let previous := Function.update registers index (registers index - 1)
  have restores : Function.update previous index (previous index + 1) = registers := by
    funext other
    by_cases same : other = index
    · subst other
      simp only [previous, Function.update_self]
      omega
    · simp [previous, same]
  have restores_code := basis.encode_increment previous index
  rw [restores] at restores_code
  change basis.encode previous = basis.encode registers / basis.prime index
  rw [restores_code, Nat.mul_div_cancel_left _ (basis.isPrime index).pos]
end Basis
@[simp] theorem three_prime (index : Fin 3) : three.prime index = prime index := rfl
@[simp] theorem three_decode (code : ℕ) : three.decode code = decode code := rfl
theorem three_encode (registers : Fin 3 → ℕ) : three.encode registers = encode registers := by
  change (∏ index : Fin 3, prime index ^ registers index) =
    2 ^ registers 0 * 3 ^ registers 1 * 5 ^ registers 2
  simp [Fin.prod_univ_succ, prime, mul_assoc]
theorem encode_positive (registers : Fin 3 → ℕ) : 0 < encode registers := by
  simpa only [three_encode] using three.encode_positive registers
theorem factorization_encode (registers : Fin 3 → ℕ) (index : Fin 3) :
    (encode registers).factorization (prime index) = registers index := by
  simpa only [three_encode, three_prime] using three.factorization_encode registers index
theorem decode_encode : Function.LeftInverse decode encode := by
  intro registers
  simpa only [three_encode, three_decode] using three.decode_encode registers
theorem encode_injective : Function.Injective encode := decode_encode.injective
@[simp] theorem encode_zero : encode (fun _ => 0) = 1 := by
  simpa only [three_encode] using three.encode_zero
theorem encode_increment (registers : Fin 3 → ℕ) (index : Fin 3) :
    encode (Function.update registers index (registers index + 1)) = prime index * encode registers := by
  simpa only [three_encode, three_prime] using three.encode_increment registers index
theorem prime_dvd_encode_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    prime index ∣ encode registers ↔ registers index ≠ 0 := by
  simpa only [three_encode, three_prime] using three.prime_dvd_encode_iff registers index
theorem register_zero_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    registers index = 0 ↔ ¬ prime index ∣ encode registers := by
  simpa only [three_encode, three_prime] using three.register_zero_iff registers index
theorem remainder_zero_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    encode registers % prime index = 0 ↔ registers index ≠ 0 := by
  simpa only [three_encode, three_prime] using three.remainder_zero_iff registers index
theorem encode_decrement (registers : Fin 3 → ℕ) (index : Fin 3)
    (nonzero : registers index ≠ 0) :
    encode (Function.update registers index (registers index - 1)) = encode registers / prime index := by
  simpa only [three_encode, three_prime] using three.encode_decrement registers index nonzero
end Monodromy.PrimeCode
namespace Monodromy.Counter
variable {n m k : ℕ}
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
theorem program_finish (factor : ℕ) : program factor (finish factor) = .halt := by
  have outside : ¬ factor + 3 ≤ factor := by omega
  simp [program, finish, outside]
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
theorem halted (factor first second : ℕ) :
    Counter.step (program factor) (configuration factor (finish factor) first second) = none :=
  Counter.step_halt (program factor) _ (program_finish factor)
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
theorem eval_result (factor input : ℕ) :
    Counter.eval (program factor) (configuration factor 0 input 0) =
      Part.some (configuration factor (finish factor) (factor * input) 0) := by
  apply Part.eq_some_iff.mpr
  exact StateTransition.mem_eval.mpr ⟨reaches_result factor input, halted factor (factor * input) 0⟩
end Monodromy.CounterMultiplication
namespace Monodromy.Counter.DivMod
variable (p : ℕ) [NeZero p]
@[simp] theorem program_consume (remainder : Fin p) :
    program p (consume p remainder) = .dec 0 (transfer p remainder) (next p remainder) := by
  simp [program, consume, remainder.isLt]
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
@[simp] theorem program_bump : program p (bump p) = .inc 1 (consume p 0) := by
  have first : ¬ 4 * p < p := by omega
  have second : ¬ 4 * p < 2 * p := by omega
  have third : ¬ 4 * p < 3 * p := by omega
  simp [program, bump, first, second, third]
private theorem update_first (first second value : ℕ) :
    Function.update ![first, second] 0 value = ![value, second] := by
  funext index
  fin_cases index <;> simp
private theorem update_second (first second value : ℕ) :
    Function.update ![first, second] 1 value = ![first, value] := by
  funext index
  fin_cases index <;> simp
@[simp] theorem step_consume_zero (remainder : Fin p) (second : ℕ) :
    Counter.step (program p) (configuration p (consume p remainder) 0 second) =
      some (configuration p (transfer p remainder) 0 second) := by
  simp [Counter.step, configuration]
@[simp] theorem step_consume_succ (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (consume p remainder) (first + 1) second) =
      some (configuration p (next p remainder) first second) := by
  simp [Counter.step, configuration, update_first]
@[simp] theorem step_bump (first second : ℕ) :
    Counter.step (program p) (configuration p (bump p) first second) =
      some (configuration p (consume p 0) first (second + 1)) := by
  simp [Counter.step, configuration, update_second]
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
@[simp] theorem step_finish (remainder : Fin p) (first second : ℕ) :
    Counter.step (program p) (configuration p (finish p remainder) first second) = none := by
  simp [Counter.step, configuration]
theorem residue_small (remainder : Fin p) : residue p remainder.val = remainder := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt remainder.isLt
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
theorem consume_reaches (first second : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (consume p remainder) first second)
      (configuration p (transfer p (residue p (first + remainder.val))) 0
        (second + (first + remainder.val) / p)) := by
  induction first generalizing second remainder with
  | zero =>
      simpa only [Nat.zero_add, residue_small, Nat.div_eq_of_lt remainder.isLt, Nat.add_zero] using
        (reaches_step p (step_consume_zero p remainder second))
  | succ first recursive =>
      by_cases bound : remainder.val + 1 < p
      · let next_remainder : Fin p := ⟨remainder.val + 1, bound⟩
        have next_step : Counter.step (program p)
            (configuration p (consume p remainder) (first + 1) second) =
            some (configuration p (consume p next_remainder) first second) := by
          simpa only [next, dif_pos bound] using step_consume_succ p remainder first second
        have run := prepend p next_step (recursive second next_remainder)
        have same_sum : first + next_remainder.val = first + 1 + remainder.val := by
          dsimp [next_remainder]
          omega
        simpa only [same_sum] using run
      · have last : remainder.val + 1 = p := by omega
        have next_step : Counter.step (program p)
            (configuration p (consume p remainder) (first + 1) second) =
            some (configuration p (bump p) first second) := by
          simpa only [next, dif_neg bound] using step_consume_succ p remainder first second
        have run := prepend p next_step
          (prepend p (step_bump p first second) (recursive (second + 1) 0))
        have same_sum : first + 1 + remainder.val = first + p := by omega
        have residue_eq : residue p (first + p) = residue p first := by
          apply Fin.ext
          exact Nat.add_mod_right first p
        simpa only [Fin.val_zero, Nat.add_zero, same_sum, residue_eq,
          Nat.add_div_right first (Nat.pos_of_ne_zero (NeZero.ne p)),
          Nat.add_assoc, Nat.add_comm 1 (first / p)] using run
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
theorem reaches_divmod (input : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (consume p 0) input 0)
      (configuration p (finish p (residue p input)) (input / p) 0) := by
  have consumed := consume_reaches p input 0 0
  simp only [Fin.val_zero, Nat.add_zero, Nat.zero_add] at consumed
  have restored := transfer_reaches p (residue p input) 0 (input / p)
  simp only [Nat.zero_add] at restored
  exact consumed.trans restored
theorem eval_divmod (input : ℕ) :
    Counter.eval (program p) (configuration p (consume p 0) input 0) =
      Part.some (configuration p (finish p (residue p input)) (input / p) 0) := by
  apply Part.eq_some_iff.mpr
  exact StateTransition.mem_eval.mpr ⟨reaches_divmod p input, step_finish p _ _ _⟩
omit [NeZero p] in
theorem finish_injective : Function.Injective (finish p) := by
  intro first second same
  apply Fin.ext
  have values := congrArg Fin.val same
  dsimp [finish] at values
  omega
@[simp] theorem finish_residue_val (input : ℕ) :
    (finish p (residue p input)).val = 3 * p + input % p := rfl
end Monodromy.Counter.DivMod
namespace Monodromy.CounterPrimeProbe
variable (p : ℕ) [NeZero p]
@[simp] theorem entry_eq : entry p = divBlock p (Counter.DivMod.consume p 0) := by
  simp [entry, divAddress]
@[simp] theorem program_divBlock (address : Fin (Counter.DivMod.size p)) :
    program p (divBlock p address) =
      Counter.mapInstruction (divAddress p) (Counter.DivMod.program p address) := by
  simp [program, divBlock]
@[simp] theorem program_mulAddress (address : Fin (p + 4)) :
    program p (mulAddress p address) =
      Counter.mapInstruction (mulAddress p) (CounterMultiplication.program p address) := by
  simp [program, mulAddress]
theorem div_agrees (address : Fin (Counter.DivMod.size p))
    (live : Counter.DivMod.program p address ≠ .halt) :
    program p (divAddress p address) =
      Counter.mapInstruction (divAddress p) (Counter.DivMod.program p address) := by
  have actual : divAddress p address = divBlock p address := by
    unfold divAddress
    cases operation : Counter.DivMod.program p address <;> simp_all
  rw [actual, program_divBlock]
@[simp] theorem div_finish_zero :
    divAddress p (Counter.DivMod.finish p 0) = success p := by
  unfold divAddress
  rw [Counter.DivMod.program_finish]
  simp [success, Counter.DivMod.finish]
theorem div_finish_nonzero (remainder : Fin p) (nonzero : remainder.val ≠ 0) :
    divAddress p (Counter.DivMod.finish p remainder) =
      mulAddress p (CounterMultiplication.phase p remainder.val) := by
  have different : 3 * p + remainder.val ≠ 3 * p := by omega
  unfold divAddress
  rw [Counter.DivMod.program_finish]
  change (if 3 * p + remainder.val = 3 * p then divBlock p (Counter.DivMod.finish p remainder)
    else mulAddress p (CounterMultiplication.phase p ((3 * p + remainder.val) - 3 * p))) = _
  rw [if_neg different]
  simp only [Nat.add_sub_cancel_left]
@[simp] theorem program_success : program p (success p) = .halt := by
  simp [success, Counter.mapInstruction]
@[simp] theorem program_failure : program p (failure p) = .halt := by
  simp [failure, Counter.mapInstruction, CounterMultiplication.program_finish]
theorem exits_distinct : success p ≠ failure p := by
  intro same
  have values := congrArg Fin.val same
  dsimp [success, failure, divBlock, mulAddress, Counter.DivMod.finish,
    Counter.DivMod.size, CounterMultiplication.finish] at values
  omega
private theorem div_configuration (address : Fin (Counter.DivMod.size p)) (first second : ℕ) :
    Counter.mapConfiguration (divAddress p) (Counter.DivMod.configuration p address first second) =
      configuration p (divAddress p address) first second := rfl
omit [NeZero p] in
private theorem mul_configuration (address : Fin (p + 4)) (first second : ℕ) :
    Counter.mapConfiguration (mulAddress p) (CounterMultiplication.configuration p address first second) =
      configuration p (mulAddress p address) first second := rfl
theorem divide_reaches (input : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (divAddress p (Counter.DivMod.finish p (Counter.DivMod.residue p input)))
        (input / p) 0) := by
  have run := Counter.reaches_map_live (divAddress p) (Counter.DivMod.program p) (program p)
    (div_agrees p) (Counter.DivMod.reaches_divmod p input)
  simpa only [div_configuration, entry] using run
theorem restore_reaches (remainder : Fin p) (quotient : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (mulAddress p (CounterMultiplication.phase p remainder.val)) quotient 0)
      (configuration p (failure p) (remainder.val + p * quotient) 0) := by
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
  simpa only [mul_configuration, failure] using mapped
theorem reaches_success (input : ℕ) (divides : p ∣ input) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (success p) (input / p) 0) := by
  have remainder_zero : Counter.DivMod.residue p input = 0 := by
    apply Fin.ext
    exact Nat.dvd_iff_mod_eq_zero.mp divides
  simpa only [remainder_zero, div_finish_zero] using divide_reaches p input
theorem reaches_failure (input : ℕ) (nondivides : ¬ p ∣ input) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (failure p) input 0) := by
  have remainder_nonzero : (Counter.DivMod.residue p input).val ≠ 0 := by
    intro zero
    exact nondivides (Nat.dvd_iff_mod_eq_zero.mpr zero)
  have divided := divide_reaches p input
  rw [div_finish_nonzero p _ remainder_nonzero] at divided
  have restored := restore_reaches p (Counter.DivMod.residue p input) (input / p)
  have reconstruct : (Counter.DivMod.residue p input).val + p * (input / p) = input :=
    Nat.mod_add_div input p
  rw [reconstruct] at restored
  exact divided.trans restored
theorem eval_result (input : ℕ) :
    Counter.eval (program p) (configuration p (entry p) input 0) =
      Part.some (if p ∣ input then configuration p (success p) (input / p) 0
        else configuration p (failure p) input 0) := by
  apply Part.eq_some_iff.mpr
  apply StateTransition.mem_eval.mpr
  by_cases divides : p ∣ input
  · simp only [if_pos divides]
    exact ⟨reaches_success p input divides,
      Counter.step_halt _ _ (program_success p)⟩
  · simp only [if_neg divides]
    exact ⟨reaches_failure p input divides,
      Counter.step_halt _ _ (program_failure p)⟩
theorem entry_live : program p (entry p) ≠ .halt := by
  rw [entry_eq, program_divBlock, Counter.DivMod.program_consume]
  simp [Counter.mapInstruction]
theorem entry_ne_success : entry p ≠ success p := by
  rw [entry_eq]
  intro same
  have values := congrArg Fin.val same
  have positive : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  dsimp [success, divBlock, Counter.DivMod.consume, Counter.DivMod.finish] at values
  omega
theorem entry_ne_failure : entry p ≠ failure p := by
  rw [entry_eq]
  intro same
  have values := congrArg Fin.val same
  dsimp [failure, divBlock, mulAddress, Counter.DivMod.consume,
    Counter.DivMod.size, CounterMultiplication.finish] at values
  omega
private theorem positive_run {first last : Counter.Configuration 2 (size p)}
    (run : StateTransition.Reaches (Counter.step (program p)) first last)
    (different : first ≠ last) :
    StateTransition.Reaches₁ (Counter.step (program p)) first last := by
  unfold StateTransition.Reaches at run
  unfold StateTransition.Reaches₁
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp run with same | moves
  · exact False.elim (different same.symm)
  · exact moves
theorem reaches_success₁ (input : ℕ) (divides : p ∣ input) :
    StateTransition.Reaches₁ (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (success p) (input / p) 0) := by
  apply positive_run p (reaches_success p input divides)
  intro same
  exact entry_ne_success p (congrArg Counter.Configuration.pc same)
theorem reaches_failure₁ (input : ℕ) (nondivides : ¬ p ∣ input) :
    StateTransition.Reaches₁ (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (failure p) input 0) := by
  apply positive_run p (reaches_failure p input nondivides)
  intro same
  exact entry_ne_failure p (congrArg Counter.Configuration.pc same)
end Monodromy.CounterPrimeProbe
namespace Monodromy.Counter.Compression
variable {m : ℕ}
@[simp] theorem address_dispatch (source : Program 3 m) (row : Fin m) :
    (address source).symm (dispatch source row) = ⟨row, .inl ()⟩ :=
  (address source).symm_apply_apply _
@[simp] theorem address_multiply (source : Program 3 m) (row : Fin m)
    (register : Fin 3) (next : Fin m) (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) :
    (address source).symm (multiply source row register next selected cell) =
      ⟨row, .inr (cell.cast (by simp [blockSize, selected]))⟩ :=
  (address source).symm_apply_apply _
@[simp] theorem address_probe (source : Program 3 m) (row : Fin m)
    (register : Fin 3) (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) :
    (address source).symm (probe source row register zero nonzero selected cell) =
      ⟨row, .inr (cell.cast (by simp [blockSize, selected]))⟩ :=
  (address source).symm_apply_apply _
theorem dispatch_injective (source : Program 3 m) : Function.Injective (dispatch source) := by
  intro first second same
  exact congrArg Sigma.fst ((address source).injective same)
@[simp] theorem mulTarget_finish (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next) :
    mulTarget source row register next selected (CounterMultiplication.finish (PrimeCode.prime register)) =
      dispatch source next := by simp [mulTarget]
@[simp] theorem probeTarget_success (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero) :
    probeTarget source row register zero nonzero selected
      (CounterPrimeProbe.success (PrimeCode.prime register)) = dispatch source nonzero := by
  simp [probeTarget]
@[simp] theorem probeTarget_failure (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero) :
    probeTarget source row register zero nonzero selected
      (CounterPrimeProbe.failure (PrimeCode.prime register)) = dispatch source zero := by
  have distinct := (CounterPrimeProbe.exits_distinct (PrimeCode.prime register)).symm
  simp [probeTarget, distinct]
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
@[simp] theorem program_multiply (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) :
    program source (multiply source row register next selected cell) =
      mapInstruction (mulTarget source row register next selected)
        (CounterMultiplication.program (PrimeCode.prime register) cell) := by
  unfold program
  rw [address_multiply]
  simp only [body]
  split
  next chosen => cases selected.symm.trans chosen
  next other target chosen =>
    rcases Instruction.inc.inj (selected.symm.trans chosen) with ⟨rfl, rfl⟩
    rfl
  next other zero nonzero chosen => cases selected.symm.trans chosen
@[simp] theorem program_probe (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) :
    program source (probe source row register zero nonzero selected cell) =
      mapInstruction (probeTarget source row register zero nonzero selected)
        (CounterPrimeProbe.program (PrimeCode.prime register) cell) := by
  unfold program
  rw [address_probe]
  simp only [body]
  split
  next chosen => cases selected.symm.trans chosen
  next other target chosen => cases selected.symm.trans chosen
  next other z nz chosen =>
    rcases Instruction.dec.inj (selected.symm.trans chosen) with ⟨rfl, rfl, rfl⟩
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
@[simp] theorem encode_boundary (source : Program 3 m) (state : Configuration 3 m) :
    Boundary source (encode source state).pc := ⟨state.pc, rfl⟩
theorem multiply_not_boundary (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4)) :
    ¬ Boundary source (multiply source row register next selected cell) := by
  rintro ⟨other, same⟩
  have incompatible := (address source).injective same
  cases incompatible
theorem probe_not_boundary (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register))) :
    ¬ Boundary source (probe source row register zero nonzero selected cell) := by
  rintro ⟨other, same⟩
  have incompatible := (address source).injective same
  cases incompatible
private theorem map_internal {k : ℕ} (source : Program 3 m) (oldProgram : Program 2 k)
    (rename : Fin k → Fin (size source))
    (agrees : ∀ cell, oldProgram cell ≠ .halt →
      program source (rename cell) = mapInstruction rename (oldProgram cell))
    (internal : ∀ cell, oldProgram cell ≠ .halt → ¬ Boundary source (rename cell))
    {first last : Configuration 2 k}
    (run : StateTransition.Reaches (step oldProgram) first last) :
    InternalReaches source (mapConfiguration rename first) (mapConfiguration rename last) := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | @tail middle last _ edge previous =>
      apply previous.tail
      constructor
      · exact step_map_live rename oldProgram (program source) agrees edge
      · apply internal
        intro halted
        simp [step, halted] at edge
private theorem mul_live (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next)
    (cell : Fin (PrimeCode.prime register + 4))
    (live : CounterMultiplication.program (PrimeCode.prime register) cell ≠ .halt) :
    program source (mulTarget source row register next selected cell) =
      mapInstruction (mulTarget source row register next selected)
        (CounterMultiplication.program (PrimeCode.prime register) cell) ∧
    ¬ Boundary source (mulTarget source row register next selected cell) := by
  have not_finish : cell ≠ CounterMultiplication.finish (PrimeCode.prime register) := by
    intro same
    subst cell
    exact live (CounterMultiplication.program_finish _)
  constructor
  · simp only [mulTarget, if_neg not_finish, program_multiply]
  · simpa only [mulTarget, if_neg not_finish] using
      multiply_not_boundary source row register next selected cell
private theorem probe_live (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (cell : Fin (CounterPrimeProbe.size (PrimeCode.prime register)))
    (live : CounterPrimeProbe.program (PrimeCode.prime register) cell ≠ .halt) :
    program source (probeTarget source row register zero nonzero selected cell) =
      mapInstruction (probeTarget source row register zero nonzero selected)
        (CounterPrimeProbe.program (PrimeCode.prime register) cell) ∧
    ¬ Boundary source (probeTarget source row register zero nonzero selected cell) := by
  have not_success : cell ≠ CounterPrimeProbe.success (PrimeCode.prime register) := by
    intro same
    subst cell
    exact live (CounterPrimeProbe.program_success _)
  have not_failure : cell ≠ CounterPrimeProbe.failure (PrimeCode.prime register) := by
    intro same
    subst cell
    exact live (CounterPrimeProbe.program_failure _)
  constructor
  · simp only [probeTarget, if_neg not_success, if_neg not_failure, program_probe]
  · simpa only [probeTarget, if_neg not_success, if_neg not_failure] using
      probe_not_boundary source row register zero nonzero selected cell
theorem multiply_reaches (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next) (value : ℕ) :
    InternalReaches source
      ⟨mulTarget source row register next selected 0, ![value, 0]⟩
      ⟨dispatch source next, ![PrimeCode.prime register * value, 0]⟩ := by
  have run := map_internal source (CounterMultiplication.program (PrimeCode.prime register))
    (mulTarget source row register next selected)
    (fun cell live => (mul_live source row register next selected cell live).1)
    (fun cell live => (mul_live source row register next selected cell live).2)
    (CounterMultiplication.reaches_result (PrimeCode.prime register) value)
  simpa only [mapConfiguration, CounterMultiplication.configuration, mulTarget_finish] using run
theorem probe_success_reaches (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (value : ℕ) (divides : PrimeCode.prime register ∣ value) :
    InternalReaches source
      ⟨probeTarget source row register zero nonzero selected
        (CounterPrimeProbe.entry (PrimeCode.prime register)), ![value, 0]⟩
      ⟨dispatch source nonzero, ![value / PrimeCode.prime register, 0]⟩ := by
  have run := map_internal source (CounterPrimeProbe.program (PrimeCode.prime register))
    (probeTarget source row register zero nonzero selected)
    (fun cell live => (probe_live source row register zero nonzero selected cell live).1)
    (fun cell live => (probe_live source row register zero nonzero selected cell live).2)
    (CounterPrimeProbe.reaches_success (PrimeCode.prime register) value divides)
  simpa only [mapConfiguration, CounterPrimeProbe.configuration, probeTarget_success] using run
theorem probe_failure_reaches (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero)
    (value : ℕ) (nondivides : ¬ PrimeCode.prime register ∣ value) :
    InternalReaches source
      ⟨probeTarget source row register zero nonzero selected
        (CounterPrimeProbe.entry (PrimeCode.prime register)), ![value, 0]⟩
      ⟨dispatch source zero, ![value, 0]⟩ := by
  have run := map_internal source (CounterPrimeProbe.program (PrimeCode.prime register))
    (probeTarget source row register zero nonzero selected)
    (fun cell live => (probe_live source row register zero nonzero selected cell live).1)
    (fun cell live => (probe_live source row register zero nonzero selected cell live).2)
    (CounterPrimeProbe.reaches_failure (PrimeCode.prime register) value nondivides)
  simpa only [mapConfiguration, CounterPrimeProbe.configuration, probeTarget_failure] using run
private theorem dispatch_inc (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (next : Fin m) (selected : source row = .inc register next) :
    program source (dispatch source row) =
      .dec 1 (mulTarget source row register next selected 0)
        (mulTarget source row register next selected 0) := by
  rw [program_dispatch]
  split
  next chosen => cases selected.symm.trans chosen
  next other target chosen =>
    rcases Instruction.inc.inj (selected.symm.trans chosen) with ⟨rfl, rfl⟩
    rfl
  next other zero nonzero chosen => cases selected.symm.trans chosen
private theorem dispatch_dec (source : Program 3 m) (row : Fin m) (register : Fin 3)
    (zero nonzero : Fin m) (selected : source row = .dec register zero nonzero) :
    program source (dispatch source row) =
      .dec 1 (probeTarget source row register zero nonzero selected
        (CounterPrimeProbe.entry (PrimeCode.prime register)))
        (probeTarget source row register zero nonzero selected
          (CounterPrimeProbe.entry (PrimeCode.prime register))) := by
  rw [program_dispatch]
  split
  next chosen => cases selected.symm.trans chosen
  next other target chosen => cases selected.symm.trans chosen
  next other z nz chosen =>
    rcases Instruction.dec.inj (selected.symm.trans chosen) with ⟨rfl, rfl, rfl⟩
    rfl
private theorem step_none_iff {n k : ℕ} (table : Program n k) (state : Configuration n k) :
    step table state = none ↔ table state.pc = .halt := by
  unfold step
  cases instruction : table state.pc with
  | halt => simp
  | inc => simp
  | dec register zero nonzero => cases value : state.counters register <;> simp [value]
theorem halt_encode (source : Program 3 m) (state : Configuration 3 m) :
    step (program source) (encode source state) = none ↔ step source state = none := by
  rw [step_none_iff, step_none_iff]
  change program source (dispatch source state.pc) = .halt ↔ source state.pc = .halt
  rw [program_dispatch]
  split <;> simp_all
theorem internal_from_boundary (source : Program 3 m)
    {first last : Configuration 2 (size source)}
    (run : InternalReaches source first last) (boundary : Boundary source first.pc) :
    first = last := by
  rcases Relation.ReflTransGen.cases_head run with same | ⟨next, edge, _⟩
  · exact same
  · exact False.elim (edge.2 boundary)
theorem inc_firstReturn (source : Program 3 m) (state : Configuration 3 m)
    (register : Fin 3) (next : Fin m) (selected : source state.pc = .inc register next) :
    FirstReturn source (encode source state)
      (encode source ⟨next, Function.update state.counters register (state.counters register + 1)⟩) := by
  refine ⟨⟨mulTarget source state.pc register next selected 0,
    ![PrimeCode.encode state.counters, 0]⟩, ?_, ?_⟩
  · exact step_dec_zero (program source) (encode source state)
      (dispatch_inc source state.pc register next selected) rfl
  · simpa only [encode, PrimeCode.encode_increment] using
      multiply_reaches source state.pc register next selected (PrimeCode.encode state.counters)
theorem dec_zero_firstReturn (source : Program 3 m) (state : Configuration 3 m)
    (register : Fin 3) (zero nonzero : Fin m)
    (selected : source state.pc = .dec register zero nonzero) (value : state.counters register = 0) :
    FirstReturn source (encode source state) (encode source ⟨zero, state.counters⟩) := by
  refine ⟨⟨probeTarget source state.pc register zero nonzero selected
    (CounterPrimeProbe.entry (PrimeCode.prime register)),
    ![PrimeCode.encode state.counters, 0]⟩, ?_, ?_⟩
  · exact step_dec_zero (program source) (encode source state)
      (dispatch_dec source state.pc register zero nonzero selected) rfl
  · simpa only [encode] using probe_failure_reaches source state.pc register zero nonzero selected
      (PrimeCode.encode state.counters) ((PrimeCode.register_zero_iff state.counters register).mp value)
theorem dec_succ_firstReturn (source : Program 3 m) (state : Configuration 3 m)
    (register : Fin 3) (zero nonzero : Fin m)
    (selected : source state.pc = .dec register zero nonzero)
    (value : ℕ) (counter : state.counters register = value + 1) :
    FirstReturn source (encode source state)
      (encode source ⟨nonzero, Function.update state.counters register value⟩) := by
  have positive : state.counters register ≠ 0 := by omega
  have code := PrimeCode.encode_decrement state.counters register positive
  have previous : state.counters register - 1 = value := by omega
  rw [previous] at code
  refine ⟨⟨probeTarget source state.pc register zero nonzero selected
    (CounterPrimeProbe.entry (PrimeCode.prime register)),
    ![PrimeCode.encode state.counters, 0]⟩, ?_, ?_⟩
  · exact step_dec_zero (program source) (encode source state)
      (dispatch_dec source state.pc register zero nonzero selected) rfl
  · simpa only [encode, code] using probe_success_reaches source state.pc register zero nonzero selected
      (PrimeCode.encode state.counters) ((PrimeCode.prime_dvd_encode_iff state.counters register).mpr positive)
end Monodromy.Counter.Compression
open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Compression
variable {m : ℕ}

theorem solution (source : Program 3 m) {first last : Configuration 3 m}
    (transition : step source first = some last) :
    FirstReturn source (encode source first) (encode source last) := by
  cases instruction : source first.pc with
  | halt => simp [step, instruction] at transition
  | inc register next =>
      have destination : (⟨next, Function.update first.counters register (first.counters register + 1)⟩ :
          Configuration 3 m) = last := by
        simpa only [step_inc source first instruction, Option.some.injEq] using transition
      subst last
      exact inc_firstReturn source first register next instruction
  | dec register zero nonzero =>
      cases counter : first.counters register with
      | zero =>
          have destination : (⟨zero, first.counters⟩ : Configuration 3 m) = last := by
            simpa only [step_dec_zero source first instruction counter, Option.some.injEq] using transition
          subst last
          exact dec_zero_firstReturn source first register zero nonzero instruction counter
      | succ value =>
          have destination : (⟨nonzero, Function.update first.counters register value⟩ :
              Configuration 3 m) = last := by
            simpa only [step_dec_succ source first instruction counter, Option.some.injEq] using transition
          subst last
          exact dec_succ_firstReturn source first register zero nonzero instruction value counter
