-- Prove2me | solution 2 for Monodromy.Counter.Compression.step_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:01:44.902738+00:00
-- url     : https://prove2.me/submissions/354a369f-ceec-4414-b63e-0a3c956875b6

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
public import Theorems.Thm_Monodromy_CounterPrimeProbe_restore_reaches
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





theorem encode_positive (registers : Fin n → ℕ) : 0 < basis.encode registers := by
  apply Finset.prod_pos
  intro index _
  exact pow_pos (basis.isPrime index).pos _

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



theorem three_encode (registers : Fin 3 → ℕ) : three.encode registers = encode registers := by
  change (∏ index : Fin 3, prime index ^ registers index) =
    2 ^ registers 0 * 3 ^ registers 1 * 5 ^ registers 2
  simp [Fin.prod_univ_succ, prime, mul_assoc]











/-- Incrementing a source register multiplies the single code by its fixed prime. -/
theorem encode_increment (registers : Fin 3 → ℕ) (index : Fin 3) :
    encode (Function.update registers index (registers index + 1)) = prime index * encode registers := by
  simpa only [three_encode, three_prime] using three.encode_increment registers index

/-- Divisibility is precisely the nonzero test for the corresponding source register. -/
theorem prime_dvd_encode_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    prime index ∣ encode registers ↔ registers index ≠ 0 := by
  simpa only [three_encode, three_prime] using three.prime_dvd_encode_iff registers index

theorem register_zero_iff (registers : Fin 3 → ℕ) (index : Fin 3) :
    registers index = 0 ↔ ¬ prime index ∣ encode registers := by
  simpa only [three_encode, three_prime] using three.register_zero_iff registers index



/-- A nonzero source decrement is exact division of the positive code. -/
theorem encode_decrement (registers : Fin 3 → ℕ) (index : Fin 3)
    (nonzero : registers index ≠ 0) :
    encode (Function.update registers index (registers index - 1)) = encode registers / prime index := by
  simpa only [three_encode, three_prime] using three.encode_decrement registers index nonzero

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







end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]



















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
  rw [ite_eq_right different]
  simp only [Nat.add_sub_cancel_left]

@[simp] theorem program_success : program p (success p) = .halt := by
  simp [success, Counter.mapInstruction]

@[simp] theorem program_failure : program p (failure p) = .halt := by
  simp [failure, Counter.mapInstruction, CounterMultiplication.program_finish]

/-- The two final addresses are distinct finite-control outcomes. -/
theorem exits_distinct : success p ≠ failure p := by
  intro same
  have values := congrArg Fin.val same
  dsimp [success, failure, divBlock, mulAddress, Counter.DivMod.finish,
    Counter.DivMod.size, CounterMultiplication.finish] at values
  omega

private theorem div_configuration (address : Fin (Counter.DivMod.size p)) (first second : ℕ) :
    Counter.mapConfiguration (divAddress p) (Counter.DivMod.configuration p address first second) =
      configuration p (divAddress p address) first second := rfl



/-- Division reaches a success address or an actual multiplier countdown entry. -/
theorem divide_reaches (input : ℕ) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (divAddress p (Counter.DivMod.finish p (Counter.DivMod.residue p input)))
        (input / p) 0) := by
  have run := Counter.reaches_map_live (divAddress p) (Counter.DivMod.program p) (program p)
    (div_agrees p) (Counter.DivMod.reaches_divmod p input)
  simpa only [div_configuration, entry] using run



/-- Divisible inputs are divided; the workspace returns to zero. -/
theorem reaches_success (input : ℕ) (divides : p ∣ input) :
    StateTransition.Reaches (Counter.step (program p))
      (configuration p (entry p) input 0)
      (configuration p (success p) (input / p) 0) := by
  have remainder_zero : Counter.DivMod.residue p input = 0 := by
    apply Fin.ext
    exact Nat.dvd_iff_mod_eq_zero.mp divides
  simpa only [remainder_zero, div_finish_zero] using divide_reaches p input

/-- Every other input is restored exactly, with a distinct final control outcome. -/
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















end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]











































































































end Monodromy.Counter.TuringCompiler

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
  · simp only [mulTarget, ite_eq_right not_finish, program_multiply]
  · simpa only [mulTarget, ite_eq_right not_finish] using
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
  · simp only [probeTarget, ite_eq_right not_success, ite_eq_right not_failure, program_probe]
  · simpa only [probeTarget, ite_eq_right not_success, ite_eq_right not_failure] using
      probe_not_boundary source row register zero nonzero selected cell

/-- Multiplication runs only through its allocated internal addresses, then returns to dispatch. -/
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

/-- A divisible code loses exactly one prime factor; all intermediate sources are internal. -/
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

/-- A failed divisibility test restores the entire code before taking its zero branch. -/
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
