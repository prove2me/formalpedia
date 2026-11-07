-- Prove2me | solution 2 for Monodromy.Structure.conditional_gates_strictly_extend
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:03:40.547831+00:00
-- url     : https://prove2.me/submissions/189073e3-1648-47da-a4a4-7e4a68c325ec

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_CanonicalIO
public import Definitions.Def_Monodromy_Counter
public import Definitions.Def_Monodromy_Effectiveness
public import Definitions.Def_Monodromy_FiniteSupport
public import Definitions.Def_Monodromy_FormalCompilation
public import Definitions.Def_Monodromy_ForwardBoundary
public import Definitions.Def_Monodromy_IntegerPrimrec
public import Definitions.Def_Monodromy_NativeIO
public import Definitions.Def_Monodromy_Observation
public import Definitions.Def_Monodromy_Structure
public import Definitions.Def_Monodromy_Tape
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
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.Basic
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Finite.Basic
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
public import Theorems.Thm_Monodromy_CounterContinuation_simulates
public import Theorems.Thm_Monodromy_Counter_Compression_step_firstReturn
public import Theorems.Thm_Monodromy_Counter_TuringCompiler_step_firstReturn
public import Theorems.Thm_Monodromy_CoupledContinuation_Program_eval_prepareInt
public import Theorems.Thm_Monodromy_CoupledContinuation_Word_evalInt_translation
public import Theorems.Thm_Monodromy_FormalCompilation_eval1
public import Theorems.Thm_Monodromy_IntegerPrimrec_add
public import Theorems.Thm_Monodromy_IntegerPrimrec_remainder
public import Theorems.Thm_Monodromy_Observation_exists_bounded_visit
public import Theorems.Thm_Monodromy_Observation_stopped_dom_iff

@[expose] public section


-- Inline helper skeleton from Monodromy.FiniteSupport.


/-!
# Finite support and pointed renaming

A finite support includes the initial label and every reachable transition
target. Restricting to that pointed finite carrier preserves the entire
configuration and execution. Pointed finite enumeration then preserves both
the blank symbol and the distinguished initial control label.
-/

@[expose] public section

namespace Monodromy.FiniteSupport

open Turing

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]



namespace Support

variable {source : TM0.Machine Γ Q} (support : Support source)













omit [Inhabited Γ] in
/-- Forgetting the target certificate recovers the original fixed table entry. -/
theorem restrict_value (label : support.Control) (symbol : Γ) :
    (support.restrict label symbol).map (fun entry => (entry.1.val, entry.2)) = source label.val symbol := by
  unfold restrict
  split <;> simp_all

/-- Restriction preserves one complete transition, including halt. -/
theorem step_embed (configuration : TM0.Cfg Γ support.Control) :
    (TM0.step support.restrict configuration).map support.embed =
      TM0.step source (support.embed configuration) := by
  rcases configuration with ⟨label, tape⟩
  change ((support.restrict label tape.head).map _).map support.embed =
    (source label.val tape.head).map _
  rw [← support.restrict_value label tape.head, Option.map_map, Option.map_map]
  rfl

/-- Embedding is a refinement on all finite-control configurations. -/
theorem respects : StateTransition.Respects (TM0.step support.restrict) (TM0.step source)
    (fun first second => support.embed first = second) := by
  apply StateTransition.fun_respects.mpr
  intro configuration
  cases result : TM0.step support.restrict configuration with
  | none =>
      change TM0.step source (support.embed configuration) = none
      simp [← support.step_embed, result]
  | some successor =>
      apply Relation.TransGen.single
      simp [← support.step_embed, result]

/-- Restriction preserves the entire partial execution and final configuration. -/
theorem eval_embed (configuration : TM0.Cfg Γ support.Control) :
    StateTransition.eval (TM0.step source) (support.embed configuration) =
      support.embed <$> StateTransition.eval (TM0.step support.restrict) configuration :=
  StateTransition.tr_eval' (TM0.step support.restrict) (TM0.step source) support.embed
    support.respects configuration





/-- Input initialization uses the same blank, label, and full tape. -/
theorem embed_init (input : List Γ) :
    support.embed (TM0.init input) = TM0.init input := rfl



end Support

end Monodromy.FiniteSupport


/-! Pointed finite enumeration preserves the blank symbol, initial label, and complete execution. -/

namespace Monodromy.FiniteRenaming

open Turing

section Enumeration

variable (α : Type*) [Fintype α] [Inhabited α]









@[simp] theorem from_toFin (value : α) : fromFin α (toFin α value) = value :=
  (enumeration α).symm_apply_apply value



end Enumeration

section Machine

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]







theorem configuration_init (input : List Γ) :
    configuration (TM0.init input : TM0.Cfg Γ Q) = TM0.init (input.map (toFin Γ)) :=
  TM0.map_init (toFin Γ) (toFin Q) input

theorem respects (source : TM0.Machine Γ Q) :
    StateTransition.Respects (TM0.step source) (TM0.step (machine source))
      (fun first second => configuration first = second) := by
  simpa only [machine, configuration, Set.mem_univ, true_and] using
    source.map_respects (toFin Γ) (fromFin Γ) (toFin Q) (fromFin Q)
      (S := Set.univ) (TM0.univ_supports source) (from_toFin Γ)
      (fun state _ => from_toFin Q state)

theorem eval_configuration (source : TM0.Machine Γ Q) (state : TM0.Cfg Γ Q) :
    StateTransition.eval (TM0.step (machine source)) (configuration state) =
      (configuration (Γ := Γ) (Q := Q)) <$> StateTransition.eval (TM0.step source) state :=
  StateTransition.tr_eval' (TM0.step source) (TM0.step (machine source)) (configuration (Γ := Γ) (Q := Q))
    (respects source) state

end Machine

open Turing

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Fintype Q] [Inhabited Q]



end Monodromy.FiniteRenaming

end


-- Inline helper skeleton from Monodromy.Tape.


/-!
# Canonical half-tape codes

Positional encoding descends to blank-padded tapes and preserves every cell.
-/

@[expose] public section

namespace Monodromy.TapeCode

open Turing

variable {a : ℕ} [NeZero a]



@[simp] theorem encode_mk (word : List (Fin a)) :
    encode (ListBlank.mk word) = Nat.ofDigits (a + 1) (word.map Fin.val) := rfl

@[simp] theorem encode_empty : encode (∅ : ListBlank (Fin a)) = 0 := rfl

/-- Push, pop and head observation are arithmetic identities on the blank quotient itself. -/
theorem encode_cons (symbol : Fin a) (tape : ListBlank (Fin a)) :
    encode (tape.cons symbol) = symbol.val + (a + 1) * encode tape := by
  refine ListBlank.induction_on tape (fun word => ?_)
  simp only [ListBlank.cons_mk, encode_mk, List.map_cons, Nat.ofDigits_cons]

theorem decomposition (tape : ListBlank (Fin a)) :
    encode tape = tape.head.val + (a + 1) * encode tape.tail := by
  simpa only [ListBlank.cons_head_tail] using encode_cons tape.head tape.tail

theorem head_code (tape : ListBlank (Fin a)) :
    encode tape % (a + 1) = tape.head.val := by
  rw [decomposition, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (Nat.lt_succ_of_lt tape.head.isLt)]

theorem tail_code (tape : ListBlank (Fin a)) :
    encode tape / (a + 1) = encode tape.tail := by
  rw [decomposition, Nat.add_mul_div_left _ _ (Nat.succ_pos a),
    Nat.div_eq_of_lt (Nat.lt_succ_of_lt tape.head.isLt), zero_add]

/-- Every tape cell is determined by the same fixed code, through repeated quotienting. -/
theorem nth_eq_of_code_eq (index : ℕ) (first second : ListBlank (Fin a))
    (same : encode first = encode second) : first.nth index = second.nth index := by
  induction index generalizing first second with
  | zero =>
      simp only [ListBlank.nth_zero]
      apply Fin.ext
      rw [← head_code first, ← head_code second, same]
  | succ index recursive =>
      rw [ListBlank.nth_succ, ListBlank.nth_succ]
      apply recursive
      rw [← tail_code first, ← tail_code second, same]

/-- The whole infinite blank-padded half-tape has a canonical, injective natural code. -/
theorem encode_injective : Function.Injective (@encode a _) := by
  intro first second same
  apply ListBlank.ext
  intro index
  exact nth_eq_of_code_eq index first second same

theorem encode_eq_zero_iff (tape : ListBlank (Fin a)) : encode tape = 0 ↔ tape = ∅ := by
  constructor
  · intro zero
    apply encode_injective
    exact zero.trans encode_empty.symm
  · rintro rfl
    exact encode_empty

end Monodromy.TapeCode

end


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

/-- Relocation preserves the full partial result, including divergence. -/
theorem eval_map (address : Fin m → Fin k)
    (oldProgram : Program n m) (newProgram : Program n k)
    (agrees : ∀ label, newProgram (address label) = mapInstruction address (oldProgram label))
    (state : Configuration n m) :
    eval newProgram (mapConfiguration address state) =
      mapConfiguration address <$> eval oldProgram state := by
  apply StateTransition.tr_eval' (step oldProgram) (step newProgram) (mapConfiguration address)
  intro first second same
  subst second
  cases source : step oldProgram first with
  | none => simpa [source] using step_map address oldProgram newProgram agrees first
  | some successor =>
      refine ⟨mapConfiguration address successor, rfl, Relation.TransGen.single ?_⟩
      simp [step_map address oldProgram newProgram agrees first, source]

end Monodromy.Counter

noncomputable section

namespace Monodromy.CounterContinuation

open CoupledContinuation



theorem label_eq {m : ℕ} (position : Fin m) (phase : Fin 3) :
    label position phase = (phase.val : ℤ) + 3 * (position.val : ℤ) := by
  simp [label, finProdFinEquiv]























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







/-- Complete results, halting, and divergence agree through the faithful native encoding. -/
theorem eval_encode (program : Counter.Program 2 m) (state : Counter.Configuration 2 m) :
    (compile program).eval (encode state) = encode <$> Counter.eval program state :=
  StateTransition.tr_eval' (Counter.step program) (compile program).step encode (simulates program) state





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

















end Basis











@[simp] theorem three_prime (index : Fin 3) : three.prime index = prime index := rfl



theorem three_encode (registers : Fin 3 → ℕ) : three.encode registers = encode registers := by
  change (∏ index : Fin 3, prime index ^ registers index) =
    2 ^ registers 0 * 3 ^ registers 1 * 5 ^ registers 2
  simp [Fin.prod_univ_succ, prime, mul_assoc]



/-- Prime valuations recover each source register exactly. -/
theorem factorization_encode (registers : Fin 3 → ℕ) (index : Fin 3) :
    (encode registers).factorization (prime index) = registers index := by
  simpa only [three_encode, three_prime] using three.factorization_encode registers index

















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













@[simp] theorem program_consume (remainder : Fin p) :
    program p (consume p remainder) = .dec 0 (transfer p remainder) (next p remainder) := by
  simp [program, consume, remainder.isLt]


















































end Monodromy.Counter.DivMod

namespace Monodromy.CounterPrimeProbe

variable (p : ℕ) [NeZero p]

















@[simp] theorem entry_eq : entry p = divBlock p (Counter.DivMod.consume p 0) := by
  simp [entry, divAddress]











































end Monodromy.CounterPrimeProbe

namespace Monodromy.Counter.TuringCompiler

open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]



















































theorem halt_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    step (program a q machine) (encode a q state) = none ↔ TM0.step machine state = none := by
  simp only [step, encode, program_dispatch, TM0.step]
  cases result : machine state.q state.Tape.head with
  | none => simp
  | some command =>
      rcases command with ⟨target, operation⟩
      cases operation <;> simp [counters]















































theorem firstReturn_positive (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Configuration 3 (size a q)} (run : FirstReturn a q machine first last) :
    StateTransition.Reaches₁ (step (program a q machine)) first last := by
  rcases run with ⟨after, initial, rest⟩
  apply Relation.TransGen.head'
    (r := fun current next => next ∈ step (program a q machine) current) initial
  induction rest with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous => exact previous.tail edge.1

/-- The statically compiled table refines the entire TM transition system. -/
theorem respects (machine : TM0.Machine (Fin a) (Fin q)) :
    StateTransition.Respects (TM0.step machine) (step (program a q machine))
      (fun source target => encode a q source = target) := by
  apply StateTransition.fun_respects.mpr
  intro state
  cases transition : TM0.step machine state with
  | none =>
      change step (program a q machine) (encode a q state) = none
      exact (halt_encode a q machine state).mpr transition
  | some next =>
      exact firstReturn_positive a q machine (step_firstReturn a q machine transition)

/-- Complete configurations, termination, and divergence are preserved together. -/
theorem eval_encode (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) :
    eval (program a q machine) (encode a q state) =
      encode a q <$> StateTransition.eval (TM0.step machine) state :=
  StateTransition.tr_eval' (TM0.step machine) (step (program a q machine))
    (encode a q) (respects a q machine) state



end Monodromy.Counter.TuringCompiler

namespace Monodromy.Counter.Compression

variable {m : ℕ}
















@[simp] theorem address_dispatch (source : Program 3 m) (row : Fin m) :
    (address source).symm (dispatch source row) = ⟨row, .inl ()⟩ :=
  (address source).symm_apply_apply _





















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







































private theorem step_none_iff {n k : ℕ} (table : Program n k) (state : Configuration n k) :
    step table state = none ↔ table state.pc = .halt := by
  unfold step
  cases instruction : table state.pc with
  | halt => simp
  | inc => simp
  | dec register zero nonzero => cases value : state.counters register <;> simp [value]

/-- Halting is tested at the encoded dispatch cell, independently of all arithmetic loops. -/
theorem halt_encode (source : Program 3 m) (state : Configuration 3 m) :
    step (program source) (encode source state) = none ↔ step source state = none := by
  rw [step_none_iff, step_none_iff]
  change program source (dispatch source state.pc) = .halt ↔ source state.pc = .halt
  rw [program_dispatch]
  split <;> simp_all













theorem firstReturn_positive (source : Program 3 m)
    {first last : Configuration 2 (size source)} (run : FirstReturn source first last) :
    StateTransition.Reaches₁ (step (program source)) first last := by
  rcases run with ⟨after, initial, rest⟩
  apply Relation.TransGen.head'
    (r := fun current next => next ∈ step (program source) current) initial
  induction rest with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ edge previous => exact previous.tail edge.1

/-- The finite compiler preserves source execution and halting from every encoded configuration. -/
theorem respects (source : Program 3 m) :
    StateTransition.Respects (step source) (step (program source))
      (fun original compiled => encode source original = compiled) := by
  apply StateTransition.fun_respects.mpr
  intro state
  cases transition : step source state with
  | none =>
      change step (program source) (encode source state) = none
      exact (halt_encode source state).mpr transition
  | some next => exact firstReturn_positive source (step_firstReturn source transition)

/-- Complete configurations, termination, and divergence are preserved by prime compression. -/
theorem eval_encode (source : Program 3 m) (state : Configuration 3 m) :
    eval (program source) (encode source state) = encode source <$> eval source state :=
  StateTransition.tr_eval' (step source) (step (program source))
    (encode source) (respects source) state





end Monodromy.Counter.Compression

namespace Monodromy.Counter.EntryDispatch

variable {a m : ℕ}





@[simp] theorem program_prefix (source : Program 2 m) (entries : Fin a → Fin m)
    (symbol : Fin a) :
    program source entries (Fin.castAdd m symbol) =
      .dec 1 (Fin.natAdd a (entries symbol)) (Fin.natAdd a (entries symbol)) := by
  simp [program]

@[simp] theorem program_body (source : Program 2 m) (entries : Fin a → Fin m) (cell : Fin m) :
    program source entries (Fin.natAdd a cell) = mapInstruction (Fin.natAdd a) (source cell) := by
  simp [program]







/-- One actual source instruction enters the selected body address without changing storage. -/
theorem prefix_step (source : Program 2 m) (entries : Fin a → Fin m)
    (symbol : Fin a) (registers : Fin 2 → ℕ) (workspace : registers 1 = 0) :
    step (program source entries) (entryState symbol registers) =
      some (mapConfiguration (Fin.natAdd a) ⟨entries symbol, registers⟩) := by
  simp [step, entryState, workspace, mapConfiguration]

/-- Every relocated body preserves its complete partial execution. -/
theorem eval_body (source : Program 2 m) (entries : Fin a → Fin m)
    (state : Configuration 2 m) :
    eval (program source entries) (mapConfiguration (Fin.natAdd a) state) =
      mapConfiguration (Fin.natAdd a) <$> eval source state :=
  eval_map (Fin.natAdd a) source (program source entries)
    (fun cell => program_body source entries cell) state

/-- Static entry dispatch preserves complete results, termination, and divergence. -/
theorem eval_prefix (source : Program 2 m) (entries : Fin a → Fin m)
    (symbol : Fin a) (registers : Fin 2 → ℕ) (workspace : registers 1 = 0) :
    eval (program source entries) (entryState symbol registers) =
      mapConfiguration (Fin.natAdd a) <$> eval source ⟨entries symbol, registers⟩ := by
  have run : StateTransition.Reaches (step (program source entries)) (entryState symbol registers)
      (mapConfiguration (Fin.natAdd a) ⟨entries symbol, registers⟩) :=
    Relation.ReflTransGen.single (prefix_step source entries symbol registers workspace)
  exact (StateTransition.reaches_eval run).trans (eval_body source entries _)



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





































theorem initial0 (values : List ℕ) :
    TM1to0.trCfg (machine1 source) (TM1.init (tapeData values)) =
      (TM0.init (tapeData values) : TM0.Cfg Alphabet (Control0 source)) := rfl

/-- Compilation preserves the complete partial function on every numeric argument list. -/
theorem eval0 (values : List ℕ) :
    StateTransition.eval (TM0.step (machine0 source))
      (TM0.init (tapeData values) : TM0.Cfg Alphabet (Control0 source)) =
      halt0 source <$> source.eval values := by
  have translated := StateTransition.tr_eval' (TM1.step (machine1 source)) (TM0.step (machine0 source))
    (TM1to0.trCfg (machine1 source)) (TM1to0.tr_respects (machine1 source))
    (TM1.init (tapeData values))
  rw [initial0, eval1] at translated
  exact translated.trans (by rfl)

/-- The actual control carrier is finite; embedding preserves the entire final configuration. -/
theorem eval_finite (values : List ℕ) :
    (finiteSupport source).embed <$>
      StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData values)) =
      halt0 source <$> source.eval values := by
  rw [← (finiteSupport source).eval_embed, (finiteSupport source).embed_init]
  exact eval0 source values



omit source in
/-- Every partial recursive unary numeric function has a finite table with exact encoded output. -/
theorem every_partrec {f : ℕ → Part ℕ} (partial_recursive : Partrec f) :
    ∃ source : ToPartrec.Code, ∀ input : ℕ,
      (finiteSupport source).embed <$>
        StateTransition.eval (TM0.step (finiteSupport source).restrict) (TM0.init (tapeData [input])) =
        (fun result => halt0 source [result]) <$> f input := by
  obtain ⟨source, correct⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr partial_recursive)
  refine ⟨source, fun input => ?_⟩
  rw [eval_finite, correct ⟨[input], rfl⟩]
  rfl

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


-- Inline helper skeleton from Monodromy.CanonicalIO.


/-!
# A fixed numeric tape interface

Binary symbols carry the number; delimiters, blank columns and the stack
bottom marker leave the accumulator unchanged. The decoder is independent
of the source program and its control labels.
-/

@[expose] public section

namespace Monodromy.CanonicalIO

open Turing PartrecToTM2











theorem decode_posNum (value : PosNum) : decodeBits (trPosNum value) = (value : ℕ) := by
  induction value with
  | one => rfl
  | bit0 value previous =>
      change decodeBits (trPosNum value) + decodeBits (trPosNum value) = (value : ℕ) + value
      rw [previous]
  | bit1 value previous =>
      change decodeBits (trPosNum value) + decodeBits (trPosNum value) + 1 = (value : ℕ) + value + 1
      rw [previous]

theorem decode_num (value : Num) : decodeBits (trNum value) = (value : ℕ) := by
  cases value with
  | zero => rfl
  | pos value => exact decode_posNum value

theorem decode_nat (value : ℕ) : decodeBits (trNat value) = value := by
  change decodeBits (trNum (value : Num)) = value
  rw [decode_num, Num.to_of_nat]

set_option backward.isDefEq.respectTransparency false in
/-- Packing the main stack changes its orientation but preserves every numeric bit. -/
theorem decode_packed (word : List Γ') :
    decodeWord (TM2to1.trInit K'.main word) = decodeBits word := by
  rw [decodeBits, ← List.foldl_reverse]
  cases reversed : word.reverse with
  | nil =>
      simp only [decodeWord, TM2to1.trInit, reversed]
      rfl
  | cons bit tail =>
      simp only [decodeWord, TM2to1.trInit, reversed, List.map_cons, List.headI_cons,
        List.tail_cons, List.foldl_cons, List.foldl_map, readSymbol, Function.update_self]

/-- The output protocol is a single numeric item, with a fixed decoder. -/
theorem decode_output (value : ℕ) :
    decodeWord (TM2to1.trInit K'.main (trList [value])) = value := by
  rw [decode_packed]
  simp only [trList]
  change (trNat value ++ [Γ'.cons]).foldr (fun bit result => readBit result bit) 0 = value
  rw [List.foldr_append]
  exact decode_nat value









@[simp] theorem decodeTape_mk (word : List Alphabet) : decodeTape (ListBlank.mk word) = decodeWord word := rfl



















theorem increment_posNum (value : PosNum) : increment (trPosNum value) = trPosNum value.succ := by
  induction value with
  | one => rfl
  | bit0 => rfl
  | bit1 value previous => exact congrArg (List.cons Γ'.bit0) previous

theorem increment_nat (value : ℕ) : increment (trNat value) = trNat (value + 1) := by
  simp only [trNat, Nat.cast_succ, Num.add_one]
  cases (value : Num) with
  | zero => rfl
  | pos positive => exact increment_posNum positive



theorem primrec_incrementStep : Primrec incrementStep :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const Γ'.bit0))
    (Primrec.list_cons.comp (Primrec.const Γ'.bit1) (Primrec.fst.comp Primrec.snd))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const Γ'.bit1))
      (Primrec.list_cons.comp (Primrec.const Γ'.bit0) (Primrec.snd.comp Primrec.snd))
      (Primrec.const [Γ'.bit1]))

theorem primrec_increment : Primrec increment := by
  apply (Primrec.list_rec Primrec.id (Primrec.const [Γ'.bit1])
    (primrec_incrementStep.comp Primrec.snd).to₂).of_eq
  intro word
  induction word with
  | nil => rfl
  | cons bit tail previous =>
      cases bit with
      | consₗ => rfl
      | cons => rfl
      | bit0 => rfl
      | bit1 => exact congrArg (List.cons Γ'.bit0) previous

theorem primrec_trNat : Primrec trNat := by
  apply (Primrec.nat_rec₁ [] (primrec_increment.comp Primrec.snd).to₂).of_eq
  intro value
  induction value with
  | zero => rfl
  | succ value previous =>
      change increment (Nat.rec [] (fun _ bits => increment bits) value) = trNat (value + 1)
      rw [previous, increment_nat]







theorem primrec_markBottom : Primrec markBottom :=
  Primrec.list_cons.comp
    ((Primrec.dom_finite bottomMarker).comp Primrec.list_headI)
    Primrec.list_tail

/-- Canonical numeric input is a primitive recursive representation, independent of the program. -/
theorem primrec_tapeData : Primrec (fun value => FormalCompilation.tapeData [value]) := by
  have symbols : Primrec (fun value => trNat value ++ [Γ'.cons]) :=
    Primrec.list_append.comp primrec_trNat (Primrec.const [Γ'.cons])
  have reversed : Primrec (fun value => (trNat value ++ [Γ'.cons]).reverse) :=
    Primrec.list_reverse.comp symbols
  exact primrec_markBottom.comp (Primrec.list_map reversed
    ((Primrec.dom_finite pack).comp Primrec.snd).to₂)





set_option backward.isDefEq.respectTransparency false in
/-- The first packed output symbol is a delimiter and contributes no numeric bit. -/
theorem output_head_neutral (value : ℕ) :
    readSymbol 0 (FormalCompilation.tapeData [value]).headI = 0 := by
  change readSymbol 0 (TM2to1.trInit K'.main (trNat value ++ [Γ'.cons])).headI = 0
  simp [TM2to1.trInit, readSymbol, readBit]

theorem decode_output_tail (value : ℕ) :
    decodeWord (FormalCompilation.tapeData [value]).tail = value := by
  have neutral := output_head_neutral value
  have whole := decode_output value
  change decodeWord (FormalCompilation.tapeData [value]) = value at whole
  cases word : FormalCompilation.tapeData [value] with
  | nil => simpa only [word, List.tail_nil] using whole
  | cons head tail =>
      rw [word] at neutral whole
      change readSymbol 0 head = 0 at neutral
      simpa only [decodeWord, List.foldl_cons, neutral, List.tail_cons] using whole

/-- The right stack alone supplies the numeric answer; control and current head are unused. -/
theorem decode_halt_right (source : ToPartrec.Code) (value : ℕ) :
    decodeTape (FormalCompilation.halt0 source [value]).Tape.right = value := by
  change decodeTape (ListBlank.mk (FormalCompilation.tapeData [value])).tail = value
  rw [ListBlank.tail_mk, decodeTape_mk]
  exact decode_output_tail value

end Monodromy.CanonicalIO

end


-- Inline helper skeleton from Monodromy.IntegerPrimrec.


/-!
# Effective integer primitives

The canonical signed encoding reduces integer arithmetic and positive-base
Euclidean division to primitive recursive operations on natural numbers.
-/

@[expose] public section

namespace Monodromy.IntegerPrimrec





theorem split_primrec : Primrec split :=
  Primrec.encode_iff.mp ((Primrec.encode : Primrec (Encodable.encode : ℤ → ℕ)).of_eq
    (fun value => by cases value <;> rfl))

theorem join_primrec : Primrec join :=
  Primrec.encode_iff.mp ((Primrec.encode : Primrec (Encodable.encode : ℕ ⊕ ℕ → ℕ)).of_eq
    (fun value => by cases value <;> rfl))

theorem ofNat : Primrec Int.ofNat := join_primrec.comp Primrec.sumInl

theorem negSucc : Primrec Int.negSucc := join_primrec.comp Primrec.sumInr

theorem cases {α β : Type*} [Primcodable α] [Primcodable β] {key : α → ℤ}
    {positive negative : α → ℕ → β} (key_primrec : Primrec key)
    (positive_primrec : Primrec₂ positive) (negative_primrec : Primrec₂ negative) :
    Primrec (fun input : α => Sum.elim (positive input) (negative input) (split (key input))) :=
  Primrec.sumCasesOn (split_primrec.comp key_primrec) positive_primrec negative_primrec









theorem negate : Primrec (fun value : ℤ => -value) := by
  have positive : Primrec (fun value : ℕ => -(value : ℤ)) :=
    (Primrec.nat_casesOn₁ (0 : ℤ) negSucc).of_eq (by intro value; cases value <;> rfl)
  exact (cases Primrec.id (positive.comp Primrec.snd).to₂ (ofNat.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq
    (by intro value; cases value <;> rfl)

theorem scale_nat (coefficient : ℕ) : Primrec (fun value : ℤ => (coefficient : ℤ) * value) := by
  induction coefficient with
  | zero => simpa using (Primrec.const (0 : ℤ))
  | succ coefficient previous =>
      exact (add.comp previous Primrec.id).of_eq (by intro value; change (coefficient : ℤ) * value + value = _; push_cast; ring)

theorem scale (coefficient : ℤ) : Primrec (fun value : ℤ => coefficient * value) := by
  cases coefficient with
  | ofNat value => exact scale_nat value
  | negSucc value =>
      exact (negate.comp (scale_nat (value + 1))).of_eq (by intro input; simp [Int.negSucc_eq]; ring)





end Monodromy.IntegerPrimrec

end


-- Inline helper skeleton from Monodromy.Effectiveness.


/-!
# The effective content of cover execution

Fixed words of the five native loops have primitive recursive integer
interpretations. Complete native word execution
agrees with this proof interpretation, including results and divergence.
The trajectory-generating core uses the actual covering lifts throughout.
-/

@[expose] public section

namespace Monodromy.Effectiveness



end Monodromy.Effectiveness

noncomputable section

namespace Monodromy.CoupledContinuation





namespace Program

variable {degree : ℕ} [NeZero degree]

theorem primrec_indexInt : Primrec (indexInt degree) := by
  apply Primrec.fin_val_iff.mp
  have degree_eq : degree - 1 + 1 = degree := by
    have positive := Nat.pos_of_ne_zero (NeZero.ne degree)
    omega
  exact ((IntegerPrimrec.remainder (degree - 1)).comp
    (Primrec.snd : Primrec (Prod.snd : Labels → ℤ))).of_eq
      (by intro labels; simp [degree_eq, indexInt])











end Program

end Monodromy.CoupledContinuation

namespace Monodromy.PrimeReadout



theorem primrec_power (base : ℕ) : Primrec (fun power : ℕ => base ^ power) :=
  (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const base) Primrec.id



/-- For a prime, the bounded readout agrees with the exact factorization exponent. -/
theorem exponent_eq_factorization {prime : ℕ} (is_prime : prime.Prime) (input : ℕ) :
    exponent prime input = input.factorization prime := by
  by_cases zero : input = 0
  · subst input
    simp [exponent]
  · apply Nat.findGreatest_eq_iff.mpr
    refine ⟨(Nat.factorization_lt prime zero).le, ?_, ?_⟩
    · intro _
      exact (is_prime.pow_dvd_iff_le_factorization zero).mpr le_rfl
    · intro power larger _ divides
      exact (not_lt_of_ge ((is_prime.pow_dvd_iff_le_factorization zero).mp divides)) larger

end Monodromy.PrimeReadout

namespace Monodromy.TapeCode.Readout



theorem wordCode_foldr (a : ℕ) (word : List (Fin a)) :
    wordCode a word = word.foldr (fun letter total => letter.val + (a + 1) * total) 0 := by
  induction word with
  | nil => rfl
  | cons letter rest recursive => simpa [wordCode, Nat.ofDigits_cons] using congrArg (fun total => letter.val + (a + 1) * total) recursive

theorem primrec_wordCode (a : ℕ) : Primrec (wordCode a) := by
  have folded : Primrec (fun word : List (Fin a) =>
      word.foldr (fun letter total => letter.val + (a + 1) * total) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp
        (Primrec.fin_val.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.nat_mul.comp (Primrec.const (a + 1)) (Primrec.snd.comp Primrec.snd))).to₂
  exact folded.of_eq (fun word => (wordCode_foldr a word).symm)

section Decoder

variable {a : ℕ} [NeZero a]





















variable (read : Fin a → ℕ → ℕ) (neutral : ∀ initial, read 0 initial = initial)





@[simp] theorem tapeFold_mk (word : List (Fin a)) (initial : ℕ) :
    tapeFold read neutral (Turing.ListBlank.mk word) initial =
      word.foldl (fun total letter => read letter total) initial := rfl

@[simp] theorem tapeFold_empty (initial : ℕ) :
    tapeFold read neutral (∅ : Turing.ListBlank (Fin a)) initial = initial := rfl

theorem tapeFold_cons (letter : Fin a) (tape : Turing.ListBlank (Fin a)) (initial : ℕ) :
    tapeFold read neutral (tape.cons letter) initial =
      tapeFold read neutral tape (read letter initial) := by
  refine Turing.ListBlank.induction_on tape (fun word => ?_)
  rw [Turing.ListBlank.cons_mk]
  rfl

theorem tapeFold_head_tail (tape : Turing.ListBlank (Fin a)) (initial : ℕ) :
    tapeFold read neutral tape initial = tapeFold read neutral tape.tail (read tape.head initial) := by
  simpa only [Turing.ListBlank.cons_head_tail] using tapeFold_cons read neutral tape.head tape.tail initial

theorem digit_encode (tape : Turing.ListBlank (Fin a)) :
    digit a (TapeCode.encode tape) = tape.head.castSucc := by
  apply Fin.ext
  exact TapeCode.head_code tape

theorem step_encode (tape : Turing.ListBlank (Fin a)) (initial : ℕ) :
    step read (TapeCode.encode tape, initial) = (TapeCode.encode tape.tail, read tape.head initial) := by
  simp [step, TapeCode.tail_code, digit_encode, extend]

theorem step_zero (neutral : ∀ initial, read 0 initial = initial) (initial : ℕ) : step read (0, initial) = (0, initial) := by
  have blank_digit : digit a 0 = (0 : Fin a).castSucc := by apply Fin.ext; rfl
  change (0 / (a + 1), extend read (digit a 0) initial) = (0, initial)
  rw [blank_digit]
  simp only [extend, Fin.lastCases_castSucc, neutral, Nat.zero_div]

theorem run_zero (neutral : ∀ initial, read 0 initial = initial) (fuel initial : ℕ) : run read fuel (0, initial) = (0, initial) :=
  Function.iterate_fixed (step_zero read neutral initial) fuel

theorem run_succ (fuel : ℕ) (state : ℕ × ℕ) :
    run read (fuel + 1) state = run read fuel (step read state) :=
  Function.iterate_succ_apply _ _ _

/-- The numeric code itself is a sufficient uniform bound on the number of useful reads. -/
private theorem run_code (neutral : ∀ initial, read 0 initial = initial) (code : ℕ) :
    ∀ tape : Turing.ListBlank (Fin a), TapeCode.encode tape = code →
      ∀ fuel : ℕ, code ≤ fuel → ∀ initial : ℕ,
        run read fuel (code, initial) = (0, tapeFold read neutral tape initial) := by
  induction code using Nat.strong_induction_on with
  | h code recursive =>
      intro tape encoding fuel enough initial
      by_cases zero : code = 0
      · have blank : tape = ∅ := (TapeCode.encode_eq_zero_iff tape).mp (encoding.trans zero)
        rw [zero, blank, tapeFold_empty]
        exact run_zero read neutral fuel initial
      · have positive : 0 < code := Nat.pos_of_ne_zero zero
        have base_large : 1 < a + 1 := by
          have nonempty := Nat.pos_of_ne_zero (NeZero.ne a)
          omega
        have smaller : TapeCode.encode tape.tail < code := by
          rw [← TapeCode.tail_code tape, encoding]
          exact Nat.div_lt_self positive base_large
        cases fuel with
        | zero => omega
        | succ fuel =>
            have actual_step : step read (code, initial) =
                (TapeCode.encode tape.tail, read tape.head initial) := by
              rw [← encoding]
              exact step_encode read tape initial
            rw [run_succ, actual_step]
            have rest := recursive (TapeCode.encode tape.tail) smaller tape.tail rfl fuel
              (by omega) (read tape.head initial)
            exact rest.trans (congrArg (fun value => (0, value))
              (tapeFold_head_tail read neutral tape initial).symm)

/-- The code is fully consumed and its fold is exact after any sufficient bounded iteration. -/
theorem run_tape_state (tape : Turing.ListBlank (Fin a)) (fuel : ℕ)
    (enough : TapeCode.encode tape ≤ fuel) (initial : ℕ) :
    run read fuel (TapeCode.encode tape, initial) = (0, tapeFold read neutral tape initial) :=
  run_code read neutral (TapeCode.encode tape) tape rfl fuel enough initial

/-- Every representative, including arbitrary blank padding, has the same bounded numeric readout. -/
theorem run_tape (tape : Turing.ListBlank (Fin a)) (fuel : ℕ)
    (enough : TapeCode.encode tape ≤ fuel) (initial : ℕ) :
    (run read fuel (TapeCode.encode tape, initial)).2 = tapeFold read neutral tape initial :=
  congrArg Prod.snd (run_tape_state read neutral tape fuel enough initial)

/-- The fixed total primitive-recursive decoder agrees with the blank-invariant tape fold. -/
theorem decode_tape (tape : Turing.ListBlank (Fin a)) :
    decode read (TapeCode.encode tape) = tapeFold read neutral tape 0 :=
  run_tape read neutral tape (TapeCode.encode tape) le_rfl 0



end Decoder

end Monodromy.TapeCode.Readout

/-!
## Direct analytic comparison

The same finite word table has a globally real analytic successor on three
real coordinates. Its complete execution on the exact integer lattice agrees
with native transport. The comparison evaluates formulas directly and carries
no assertion about off-lattice conjugacy, physical robustness, or equal cost.
-/



namespace Monodromy.AnalyticComparison

















end Monodromy.AnalyticComparison

namespace Monodromy.AnalyticComparison

open CoupledContinuation

























variable {degree : ℕ} [NeZero degree]





























end Monodromy.AnalyticComparison

end

end


-- Inline helper skeleton from Monodromy.Observation.


/-!
# Closed observations

An observation that evolves on its own carries the complete stopping semantics.
A finite such quotient bounds the information available to internal control.
-/

@[expose] public section

namespace Monodromy.Observation

universe u



/-- An observation closed under evolution preserves the entire partial execution. -/
theorem observed_eval {S F : Type u} (observe : S → F) (next : S → S)
    (advance : F → F) (halt : F → Bool)
    (closed : ∀ state, observe (next state) = advance (observe state)) (state : S) :
    StateTransition.eval (stopped advance halt) (observe state) =
      observe <$> StateTransition.eval (stopped next (fun s => halt (observe s))) state := by
  apply StateTransition.tr_eval' _ _ observe
  apply StateTransition.fun_respects.mpr
  intro source
  by_cases done : halt (observe source) = true
  · simp [stopped, done, StateTransition.FRespects]
  · simp only [stopped, done, StateTransition.FRespects]
    apply Relation.TransGen.single
    simp [stopped, done, closed source]

theorem observed_dom {S F : Type u} (observe : S → F) (next : S → S)
    (advance : F → F) (halt : F → Bool)
    (closed : ∀ state, observe (next state) = advance (observe state)) (state : S) :
    (StateTransition.eval (stopped next (fun s => halt (observe s))) state).Dom ↔
      (StateTransition.eval (stopped advance halt) (observe state)).Dom := by
  rw [observed_eval observe next advance halt closed state]
  rfl



end Monodromy.Observation

namespace Monodromy.Observation

variable {S : Type*}





/-- Finite autonomous stopping has a complete cardinality-bounded search. -/
theorem finite_stopped_dom_iff [Fintype S] (next : S → S) (halt : S → Bool) (state : S) :
    (StateTransition.eval (stopped next halt) state).Dom ↔
      ∃ rounds < Fintype.card S, halt ((next^[rounds]) state) = true := by
  rw [stopped_dom_iff]
  exact ⟨exists_bounded_visit next halt state, fun ⟨rounds, _, stops⟩ => ⟨rounds, stops⟩⟩



theorem finiteHalts_eq_true [Fintype S] (next : S → S) (halt : S → Bool) (state : S) :
    finiteHalts next halt state = true ↔
      (StateTransition.eval (stopped next halt) state).Dom := by
  rw [finite_stopped_dom_iff]
  simp [finiteHalts]

end Monodromy.Observation

end


-- Inline helper skeleton from Monodromy.ForwardBoundary.


/-!
# The computational boundary of fixed observations

Removing the two zero-conditional loops leaves
a finite control quotient with a bounded primitive-recursive halting test.
One actual conditional loop yields a strictly different halting domain under
the same fixed input representation.
-/

@[expose] public section

namespace Monodromy.ForwardBoundary

/-- Decidable predicates stay decidable under computable changes of input representation. -/
theorem computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β]
    {predicate : β → Prop} {initial : α → β} (decision : ComputablePred predicate)
    (effective : Computable initial) : ComputablePred (fun input => predicate (initial input)) := by
  obtain ⟨decider, computes⟩ := decision
  exact ⟨fun input => decider (initial input), computes.comp effective⟩



theorem hardFunction_partrec : Partrec hardFunction :=
  Nat.Partrec.Code.eval_part.comp (Computable.ofNat Nat.Partrec.Code) (Computable.const 0)

theorem hardFunction_undecidable : ¬ ComputablePred (fun input => (hardFunction input).Dom) := by
  intro decision
  have codes := computablePred_comp decision
    (Computable.encode : Computable (Encodable.encode : Nat.Partrec.Code → ℕ))
  exact ComputablePred.halting_problem 0
    (codes.of_eq (fun code => by simp [hardFunction]))

end Monodromy.ForwardBoundary

namespace Monodromy.CoupledContinuation











end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]



/-- Equality of control residues is exactly the finite observation needed below. -/
theorem indexInt_eq_of_mod_eq {first second : Labels}
    (same : first.2 % (degree : ℤ) = second.2 % (degree : ℤ)) :
    indexInt degree first = indexInt degree second := by
  apply Fin.ext
  have values := (indexInt_cast (degree := degree) first).trans
    (same.trans (indexInt_cast (degree := degree) second).symm)
  exact_mod_cast values



theorem quotient_closed (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    indexInt degree (program.nextInt labels) = program.quotientNext (indexInt degree labels) := by
  unfold nextInt quotientNext
  rw [Word.evalInt_translation _ (free _) labels]
  apply indexInt_eq_of_mod_eq
  change (labels.2 + (Word.evalInt (program.table (indexInt degree labels)) 0).2) % (degree : ℤ) =
    (((indexInt degree labels).val : ℤ) +
      (Word.evalInt (program.table (indexInt degree labels)) 0).2) % (degree : ℤ)
  simp only [Int.add_emod, indexInt_cast, Int.emod_emod]

/-- Complete stopping semantics descend to the closed finite observation. -/
theorem probeFree_evalInt_dom (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    (program.evalInt labels).Dom ↔
      (StateTransition.eval (Observation.stopped program.quotientNext program.stop)
        (indexInt degree labels)).Dom := by
  change (StateTransition.eval
    (Observation.stopped program.nextInt (fun state => program.stop (indexInt degree state))) labels).Dom ↔ _
  exact Observation.observed_dom (indexInt degree) program.nextInt program.quotientNext program.stop
    (quotient_closed program free) labels





theorem probeFreeHalts_eq_true (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    program.probeFreeHalts labels = true ↔ (program.evalInt labels).Dom := by
  rw [probeFree_evalInt_dom program free labels]
  exact Observation.finiteHalts_eq_true program.quotientNext program.stop (indexInt degree labels)



theorem probeFreeHalts_native (program : Program degree) (free : program.ProbeFree) (labels : Labels) :
    program.probeFreeHalts labels = true ↔ (program.eval (Labels.prepare labels)).Dom := by
  rw [eval_prepareInt]
  change program.probeFreeHalts labels = true ↔ (program.evalInt labels).Dom
  exact probeFreeHalts_eq_true program free labels

end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

/-- The bounded decision procedure is primitive recursive in the complete initial labels. -/
theorem primrec_probeFreeHalts (program : Program degree) : Primrec program.probeFreeHalts :=
  (Primrec.dom_finite (Observation.finiteHalts program.quotientNext program.stop)).comp
    (primrec_indexInt (degree := degree))

/-- Decidability holds for actual native execution under the fixed branch presentation. -/
theorem probeFree_native_halting_primrec (program : Program degree) (free : program.ProbeFree) :
    PrimrecPred (fun labels : Labels => (program.eval (Labels.prepare labels)).Dom) := by
  have decision : PrimrecPred (fun labels : Labels => program.probeFreeHalts labels = true) :=
    Primrec.eq.comp (primrec_probeFreeHalts program) (Primrec.const true)
  exact decision.of_eq (probeFreeHalts_native program free)

end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]



end Monodromy.CoupledContinuation.Program

namespace Monodromy.CoupledContinuation







end Monodromy.CoupledContinuation

end


-- Inline helper skeleton from Monodromy.NativeIO.


/-!
# A fixed numeric interface

One primitive-recursive preparation and readout serve every finite native
program. A static prefix supplies the initial head symbol to the compiled
Turing table. Complete results are obtained by actual covering-space lifts;
the numeric readout recovers the right tape from its prime-three exponent.
-/

@[expose] public section

noncomputable section

namespace Monodromy.NativeInterface

open Turing CoupledContinuation












theorem read_neutral (value : ℕ) : read 0 value = value := by
  have blank : FiniteRenaming.fromFin Alphabet (0 : Fin letters) = default := by
    simpa only [Fin.default_eq_zero] using (FiniteRenaming.fromFin Alphabet).map_pt
  change CanonicalIO.readSymbol value (FiniteRenaming.fromFin Alphabet 0) = value
  rw [blank]
  exact CanonicalIO.read_blank value





theorem primrec_word : Primrec word :=
  Primrec.list_map CanonicalIO.primrec_tapeData
    ((Primrec.dom_finite (fun letter : Alphabet => FiniteRenaming.toFin Alphabet letter)).comp Primrec.snd).to₂

theorem primrec_rightCode : Primrec rightCode :=
  (TapeCode.Readout.primrec_wordCode letters).comp (Primrec.list_tail.comp primrec_word)

theorem primrec_inputLabels : Primrec inputLabels := by
  have memory : Primrec (fun input : ℕ => Int.ofNat (3 ^ rightCode input)) :=
    IntegerPrimrec.ofNat.comp ((PrimeReadout.primrec_power 3).comp primrec_rightCode)
  have control : Primrec (fun input : ℕ => 3 * ((word input).headI.val : ℤ)) :=
    (IntegerPrimrec.scale 3).comp
      (IntegerPrimrec.ofNat.comp (Primrec.fin_val.comp (Primrec.list_headI.comp primrec_word)))
  exact (memory.pair (Primrec.const 0)).pair control





variable (source : ToPartrec.Code)




















/-- The fixed integer preparation is precisely the native encoding of the finite entry prefix. -/
theorem initial_encode (input : ℕ) :
    CounterContinuation.encode (initial source input) = Labels.prepare (inputLabels input) := by
  simp [initial, Counter.EntryDispatch.entryState, CounterContinuation.encode,
    CounterContinuation.label_eq, Labels.prepare, inputLabels]

/-- Static input-head dispatch supplies the complete, correctly encoded initial tape configuration. -/
theorem initial_body (input : ℕ) :
    (⟨entries source (word input).headI, ![3 ^ rightCode input, 0]⟩ :
      Counter.Configuration 2 (bodySize source)) =
      Counter.Compression.encode
        (NativeTuring.source3 letters (controls source) (table source))
        (Counter.TuringCompiler.encode letters (controls source)
          (TM0.init (word input) : TM0.Cfg (Fin letters) (Fin (controls source)))) := by
  simp [Counter.Compression.encode, Counter.TuringCompiler.encode,
    Counter.TuringCompiler.counters, PrimeCode.encode, TM0.init,
    Tape.mk₁, Tape.mk₂, Tape.mk', ListBlank.tail_mk, entries, rightCode,
    TapeCode.Readout.wordCode, Fin.default_eq_zero]

/-- Entry dispatch preserves complete source results before the existing native compilation. -/
theorem prefix_eval (input : ℕ) :
    Counter.eval (counterProgram source) (initial source input) =
      Counter.mapConfiguration (Fin.natAdd letters) <$>
        Counter.eval (body source)
          (Counter.Compression.encode
            (NativeTuring.source3 letters (controls source) (table source))
            (Counter.TuringCompiler.encode letters (controls source)
              (TM0.init (word input) : TM0.Cfg (Fin letters) (Fin (controls source))))) := by
  have entered := Counter.EntryDispatch.eval_prefix (body source) (entries source)
    (word input).headI ![3 ^ rightCode input, 0] rfl
  rw [initial_body] at entered
  exact entered








/-- Complete native results agree with the finite Turing table after the static entry prefix. -/
theorem native_eval (input : ℕ) :
    (program source).eval (Labels.prepare (inputLabels input)) =
      Labels.prepare <$> (resultLabels source <$>
        StateTransition.eval (TM0.step (table source))
          (TM0.init (word input))) := by
  unfold program
  rw [← initial_encode source input, CounterContinuation.eval_encode, prefix_eval]
  simp only [body, NativeTuring.source2]
  rw [Counter.Compression.eval_encode]
  simp only [NativeTuring.source3]
  rw [Counter.TuringCompiler.eval_encode]
  rfl

private theorem part_map_injective {A B : Type*} (prepare : A → B)
    (faithful : Function.Injective prepare) : Function.Injective (Part.map prepare) := by
  intro first second same
  apply Part.ext
  intro value
  have member (part : Part A) : prepare value ∈ Part.map prepare part ↔ value ∈ part := by
    rw [Part.mem_map_iff]
    constructor
    · rintro ⟨found, belongs, encoded⟩
      have recovered : found = value := faithful encoded
      simpa only [recovered] using belongs
    · intro belongs
      exact ⟨value, belongs, rfl⟩
  have observed : prepare value ∈ Part.map prepare first ↔ prepare value ∈ Part.map prepare second := by
    rw [same]
  exact (member first).symm.trans (observed.trans (member second))

/-- The arithmetic interpretation is derived from actual native execution. -/
theorem evalInt_input (input : ℕ) :
    (program source).evalInt (inputLabels input) =
      resultLabels source <$> StateTransition.eval (TM0.step (table source))
        (TM0.init (word input)) := by
  apply part_map_injective Labels.prepare CoupledContinuation.prepare_injective
  have same := native_eval source input
  rw [CoupledContinuation.Program.eval_prepareInt] at same
  simpa only [Part.map_eq_map] using same

private theorem exponent_code (registers : Fin 3 → ℕ) :
    PrimeReadout.exponent 3 (PrimeCode.encode registers) = registers 1 := by
  rw [PrimeReadout.exponent_eq_factorization (by decide : Nat.Prime 3)]
  simpa [PrimeCode.prime] using PrimeCode.factorization_encode registers (1 : Fin 3)

/-- The right tape is read from the prime-three exponent; its head and control are unnecessary. -/
theorem output_result (state : TM0.Cfg (Fin letters) (Fin (controls source))) :
    outputLabels (resultLabels source state) =
      TapeCode.Readout.decode read (TapeCode.encode state.Tape.right) := by
  change TapeCode.Readout.decode read
    (PrimeReadout.exponent 3
      (PrimeCode.encode (Counter.TuringCompiler.counters
        (TapeCode.encode state.Tape.left) (TapeCode.encode state.Tape.right)))) = _
  rw [exponent_code]
  rfl

/-- Pointed alphabet renaming preserves the complete blank-invariant numeric fold. -/
theorem decode_renamed_tape (tape : ListBlank Alphabet) :
    TapeCode.Readout.decode read (TapeCode.encode (tape.map (FiniteRenaming.toFin Alphabet))) =
      CanonicalIO.decodeTape tape := by
  rw [TapeCode.Readout.decode_tape read read_neutral]
  refine ListBlank.induction_on tape (fun word => ?_)
  simp [ListBlank.map_mk, TapeCode.Readout.tapeFold_mk, CanonicalIO.decodeTape_mk,
    CanonicalIO.decodeWord, List.foldl_map, read]



theorem output_renamed (state : TM0.Cfg Alphabet (FiniteControl source)) :
    outputLabels (resultLabels source (FiniteRenaming.configuration state)) =
      rawOutput source ((FormalCompilation.finiteSupport source).embed state) := by
  rw [output_result]
  exact decode_renamed_tape state.Tape.right

theorem renamed_initial (input : ℕ) :
    FiniteRenaming.configuration
      (TM0.init (FormalCompilation.tapeData [input]) :
        TM0.Cfg Alphabet (FiniteControl source)) =
      (TM0.init (word input) : TM0.Cfg (Fin letters) (Fin (controls source))) := by
  simpa only [word] using
    (FiniteRenaming.configuration_init (Q := FiniteControl source)
      (FormalCompilation.tapeData [input]))

/-- Numeric output is the fixed right-tape readout of the complete finite-support execution. -/
theorem numeric_eval (input : ℕ) :
    outputLabels <$> (program source).evalInt (inputLabels input) =
      rawOutput source <$> ((FormalCompilation.finiteSupport source).embed <$>
        StateTransition.eval (TM0.step (FormalCompilation.finiteSupport source).restrict)
          (TM0.init (FormalCompilation.tapeData [input]))) := by
  rw [evalInt_input, ← renamed_initial source input]
  simp only [table]
  rw [FiniteRenaming.eval_configuration]
  simp only [Part.map_eq_map, Part.map_map]
  apply congrArg (fun reader => Part.map reader
    (StateTransition.eval (TM0.step (FormalCompilation.finiteSupport source).restrict)
      (TM0.init (FormalCompilation.tapeData [input]))))
  funext state
  exact output_renamed source state

omit source in
/-- Every partial recursive function has an actual native realization with the same numeric interface. -/
theorem every_partrec {function : ℕ → Part ℕ} (effective : Partrec function) :
    ∃ source : ToPartrec.Code, ∀ input : ℕ,
      outputLabels <$> (program source).evalInt (inputLabels input) = function input := by
  obtain ⟨source, correct⟩ := FormalCompilation.every_partrec effective
  refine ⟨source, fun input => ?_⟩
  rw [numeric_eval, correct input]
  change Part.map (rawOutput source)
    (Part.map (fun result => FormalCompilation.halt0 source [result]) (function input)) = function input
  rw [Part.map_map]
  apply Part.map_id'
  intro result
  exact CanonicalIO.decode_halt_right source result

omit source in
/-- Prepared lattice membership is exactly the graph of the actual native partial execution. -/
theorem prepared_result_iff {degree : ℕ} [NeZero degree]
    (native : CoupledContinuation.Program degree) (initial result : Labels) :
    Labels.prepare result ∈ native.eval (Labels.prepare initial) ↔ result ∈ native.evalInt initial := by
  rw [CoupledContinuation.Program.eval_prepareInt, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨found, completed, same⟩
    have recovered : found = result := CoupledContinuation.prepare_injective same
    simpa only [recovered] using completed
  · intro completed
    exact ⟨result, completed, rfl⟩

omit source in
/-- The lower-bound graph is stated directly in terms of actual geometric program results. -/
theorem every_partrec_graph {function : ℕ → Part ℕ} (effective : Partrec function) :
    ∃ source : ToPartrec.Code, ∀ input value : ℕ,
      value ∈ function input ↔ ∃ labels : Labels,
        Labels.prepare labels ∈ (program source).eval (Labels.prepare (inputLabels input)) ∧
          outputLabels labels = value := by
  obtain ⟨source, correct⟩ := every_partrec effective
  refine ⟨source, fun input value => ?_⟩
  rw [← correct input, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · rintro ⟨labels, completed, output⟩
    exact ⟨labels, (prepared_result_iff _ _ _).mpr completed, output⟩
  · rintro ⟨labels, completed, output⟩
    exact ⟨labels, (prepared_result_iff _ _ _).mp completed, output⟩



end Monodromy.NativeInterface

end

end


-- Inline helper skeleton from Monodromy.Structure.


/-!
# The computational class of native continuation

Finite words of the five geometric loops, with internal finite-root routing,
realize exactly the partial recursive functions under one fixed numeric
interface. Removing the two zero-conditional loops leaves a finite stopping
quotient and strictly reduces this class.
-/

@[expose] public section

namespace Monodromy.Structure

open CoupledContinuation NativeInterface







theorem computes_iff {degree : ℕ} [NeZero degree]
    (native : Program degree) (function : ℕ → Part ℕ) :
    Computes native function ↔
      ∀ input, outputLabels <$> native.evalInt (inputLabels input) = function input := by
  constructor
  · intro correct input
    apply Part.ext
    intro value
    rw [Part.map_eq_map, Part.mem_map_iff]
    have meaning := correct input value
    simp_rw [NativeInterface.prepared_result_iff] at meaning
    exact meaning.symm
  · intro correct input value
    rw [← correct input, Part.map_eq_map, Part.mem_map_iff]
    simp_rw [NativeInterface.prepared_result_iff]

theorem computes_dom {degree : ℕ} [NeZero degree] {native : Program degree}
    {function : ℕ → Part ℕ} (correct : Computes native function) (input : ℕ) :
    (native.eval (Labels.prepare (inputLabels input))).Dom ↔ (function input).Dom := by
  rw [Program.eval_prepareInt, ← (computes_iff native function).mp correct input]
  rfl



theorem realizable_of_computes {degree : ℕ} [NeZero degree]
    {function : ℕ → Part ℕ} (native : Program degree) (correct : Computes native function) :
    Realizable function := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne degree)
  exact ⟨predecessor, native, correct⟩



/-- The actual Turing-to-counter-to-continuation compiler gives the matching lower bound. -/
theorem realizable_of_partrec {function : ℕ → Part ℕ}
    (effective : Partrec function) : Realizable function := by
  obtain ⟨source, correct⟩ := NativeInterface.every_partrec_graph effective
  exact realizable_of_computes (NativeInterface.program source) correct





/-- Finite stopping observations remain decidable after the same fixed input preparation. -/
theorem no_probeFree_hardFunction {degree : ℕ} [NeZero degree]
    (native : Program degree) (free : native.ProbeFree) :
    ¬ Computes native ForwardBoundary.hardFunction := by
  intro correct
  have decision : ComputablePred (fun input : ℕ =>
      (native.eval (Labels.prepare (inputLabels input))).Dom) :=
    ForwardBoundary.computablePred_comp
      (initial := inputLabels)
      (predicate := fun labels : Labels => (native.eval (Labels.prepare labels)).Dom)
      (Program.probeFree_native_halting_primrec native free).computablePred
      NativeInterface.primrec_inputLabels.to_comp
  exact ForwardBoundary.hardFunction_undecidable
    (decision.of_eq (fun input => computes_dom correct input))



end Monodromy.Structure

namespace Monodromy.Structure

open CoupledContinuation NativeInterface





end Monodromy.Structure

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Structure
open CoupledContinuation NativeInterface
theorem solution :
    ∃ function : ℕ → Part ℕ, Realizable function ∧ ¬ ProbeFreeRealizable function := by
  refine ⟨ForwardBoundary.hardFunction,
    realizable_of_partrec ForwardBoundary.hardFunction_partrec, ?_⟩
  rintro ⟨degree, native, free, correct⟩
  exact no_probeFree_hardFunction native free correct
