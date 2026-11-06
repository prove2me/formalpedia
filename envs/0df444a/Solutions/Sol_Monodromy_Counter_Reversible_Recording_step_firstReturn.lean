-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Recording.step_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:15:40.480523+00:00
-- url     : https://prove2.me/submissions/a689456d-12e8-4ec4-9496-2688893ed5c9

module
public import Theorems.Thm_Monodromy_Counter_Reversible_step_iff
public import Theorems.Thm_Monodromy_Counter_Reversible_Radix_reaches_result
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
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}


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

end Monodromy.Counter

namespace Monodromy.Counter.Reversible
variable {n q e : ℕ}

theorem step_none_iff (table : Table n q e) (state : State n q) :
    step table state = none ↔ ¬ ∃ index, (table index).enabled state := by
  unfold step
  split_ifs <;> simp_all

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

@[simp] theorem reverseEdge_involutive (edge : Edge n q) :
    reverseEdge (reverseEdge edge) = edge := by
  cases edge
  simp [reverseEdge]

@[simp] theorem reverseTable_involutive (table : Table n q e) :
    reverseTable (reverseTable table) = table := by
  funext index
  exact reverseEdge_involutive _

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

namespace Monodromy.Counter.Reversible.RegisterRelocation
variable {n m q e : ℕ}

theorem enabled_project (register : Fin n → Fin m) (action : Action n) (values : Fin m → ℤ) :
    (mapAction register action).enabled values ↔ action.enabled (values ∘ register) := by
  cases action <;> rfl

theorem action_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (action : Action n) (values : Fin n → ℤ) :
    (mapAction register action).apply (Function.extend register values background) =
      Function.extend register (action.apply values) background := by
  cases action with
  | test => rfl
  | shift index amount =>
      simp only [mapAction, Action.apply, faithful.extend_apply, faithful.extend_update]

theorem edge_enabled_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (edge : Fin e) (state : State n q) :
    (mapTable register source edge).enabled (embed register background state) ↔
      (source edge).enabled state := by
  simp only [Edge.enabled, mapTable, embed, enabled_project, Function.extend_comp faithful]

theorem edge_execute_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (edge : Fin e) (state : State n q) :
    (mapTable register source edge).execute (embed register background state) =
      embed register background ((source edge).execute state) := by
  simp only [Edge.execute, mapTable, embed, action_embed register faithful]

/-- Relocation preserves the complete step, including its stopping decision. -/
theorem step_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (valid : Deterministic source)
    (state : State n q) :
    step (mapTable register source) (embed register background state) =
      (step source state).map (embed register background) := by
  cases result : step source state with
  | none =>
      rw [Option.map_none, step_none_iff]
      have absent := (step_none_iff source state).mp result
      rintro ⟨edge, enabled⟩
      exact absent ⟨edge, (edge_enabled_embed register faithful background source edge state).mp enabled⟩
  | some next =>
      rw [Option.map_some]
      apply (step_iff _ (deterministic register faithful source valid)).mpr
      obtain ⟨edge, enabled, result⟩ := (step_iff source valid).mp result
      refine ⟨edge, (edge_enabled_embed register faithful background source edge state).mpr enabled, ?_⟩
      rw [edge_execute_embed register faithful background source edge state, result]

end Monodromy.Counter.Reversible.RegisterRelocation

namespace Monodromy.Counter.Reversible.Glue
variable {n m q k e f : ℕ}

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

end Monodromy.Counter.Reversible.Glue

namespace Monodromy.Counter.Reversible.Radix
variable (p : ℕ) [NeZero p]

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

namespace Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}

@[simp] theorem copy_ne_mid (row other : Fin m) (position : Fin (Radix.size (base m))) :
    copy row position ≠ mid other := by
  intro same
  have impossible : (Sum.inl (row, position) : Node m) = Sum.inr other :=
    (nodeEquiv m).injective same
  cases impossible

theorem extraOperation_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraOperation program arc = .shift (Fin.castAdd 2 register) 1 := by
  unfold extraOperation
  split <;> simp_all

@[simp] theorem frame_old (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) :
    frame values history workspace (Fin.castAdd 2 index) = (values index : ℤ) := by
  simp [frame]

@[simp] theorem frame_tail (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin 2) :
    frame values history workspace (historyRegister n index) = ![history, workspace] index := by
  simp [frame, historyRegister]

@[simp] theorem frame_history (values : Fin n → ℕ) (history workspace : ℤ) :
    frame values history workspace (historyRegister n 0) = history := by simp

@[simp] theorem frame_workspace (values : Fin n → ℕ) (history workspace : ℤ) :
    frame values history workspace (historyRegister n 1) = workspace := by simp

private theorem tail_ne_old (index : Fin 2) (old : Fin n) :
    historyRegister n index ≠ Fin.castAdd 2 old := by
  intro same
  have values := congrArg Fin.val same
  simp only [historyRegister, Fin.val_natAdd, Fin.val_castAdd] at values
  omega

theorem frame_extend (values : Fin n → ℕ) (history workspace : ℤ) :
    Function.extend (historyRegister n) ![history, workspace] (frame values 0 0) =
      frame values history workspace := by
  funext index
  induction index using Fin.addCases with
  | left old =>
      rw [Function.extend_apply' _ _ _ (by rintro ⟨tail, same⟩; exact tail_ne_old tail old same)]
      simp
  | right tail =>
      change Function.extend (historyRegister n) ![history, workspace] (frame values 0 0)
        (historyRegister n tail) = frame values history workspace (historyRegister n tail)
      rw [(historyRegister_injective n).extend_apply]
      exact (frame_tail values history workspace tail).symm

theorem framed_embed (control : Fin (size m)) (values : Fin n → ℕ) (history workspace : ℤ) :
    RegisterRelocation.embed (historyRegister n) (frame values 0 0)
      (control, ![history, workspace]) = framed control values history workspace := by
  simp only [RegisterRelocation.embed, framed, frame_extend]

theorem frame_update (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) (value : ℕ) :
    Function.update (frame values history workspace) (Fin.castAdd 2 index) (value : ℤ) =
      frame (Function.update values index value) history workspace := by
  funext position
  induction position using Fin.addCases with
  | left old =>
      by_cases same : old = index
      · subst old; simp
      · simp [same]
  | right tail =>
      change Function.update (frame values history workspace) (Fin.castAdd 2 index) (value : ℤ)
        (historyRegister n tail) =
          frame (Function.update values index value) history workspace (historyRegister n tail)
      rw [Function.update_of_ne (tail_ne_old tail index)]
      simp only [frame_tail]

theorem shift_frame (values : Fin n → ℕ) (history workspace amount : ℤ) (index : Fin n)
    (value : ℕ) (updated : (values index : ℤ) + amount = value) :
    Action.apply (.shift (Fin.castAdd 2 index) amount) (frame values history workspace) =
      frame (Function.update values index value) history workspace := by
  simpa only [Action.apply, frame_old, updated] using frame_update values history workspace index value

theorem inc_frame (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) :
    Action.apply (.shift (Fin.castAdd 2 index) 1) (frame values history workspace) =
      frame (Function.update values index (values index + 1)) history workspace :=
  shift_frame values history workspace 1 index _ (by simp)

theorem dec_frame (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) (value : ℕ)
    (positive : values index = value + 1) :
    Action.apply (.shift (Fin.castAdd 2 index) (-1)) (frame values history workspace) =
      frame (Function.update values index value) history workspace :=
  shift_frame values history workspace (-1) index _ (by simp [positive])

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

theorem boundary_encode (state : Counter.Configuration n m) (history : ℕ) :
    Boundary (encode state history) := ⟨state.pc, rfl⟩

theorem not_boundary_copy (row : Fin m) (position : Fin (Radix.size (base m)))
    (interior : position ≠ Radix.entry (base m)) (values : Fin (n + 2) → ℤ) :
    ¬ Boundary (copy row position, values) := by
  rintro ⟨other, same⟩
  exact interior ((copy_eq_iff row other _ _).mp same).2

theorem not_boundary_mid (row : Fin m) (values : Fin n → ℕ) (history workspace : ℤ) :
    ¬ Boundary (framed (mid row) values history workspace) := by
  rintro ⟨other, same⟩
  exact copy_ne_mid other row (Radix.entry (base m)) same.symm

private theorem local_step_not_entry {first last : State 2 (Radix.size (base m))}
    (transition : step (reverseTable (Radix.table (base m))) first = some last) :
    first.1 ≠ Radix.entry (base m) := by
  intro at_entry
  obtain ⟨index, enabled, _⟩ := (step_iff _
    (reverseTable_deterministic _ (Radix.targetCompatible (base m)))).mp transition
  exact Radix.no_incoming_entry (base m) index (enabled.1.trans at_entry)

/-- The copied packer cannot visit a dispatch before its terminal return. -/
theorem packing_internal_reaches (program : Counter.Program n m)
    (row : Fin m) (symbol : Fin (base m)) (values : Fin n → ℕ) (history : ℕ) :
    InternalReaches program
      (framed (port row symbol) values history 0)
      (framed (dispatch row) values (base m * history + symbol.val : ℕ) 0) := by
  let source := reverseTable (Radix.table (base m))
  let route : State 2 (Radix.size (base m)) → State (n + 2) (size m) :=
    fun state => Glue.mapState (copy row)
      (RegisterRelocation.embed (historyRegister n) (frame values 0 0) state)
  have mapped : Relation.ReflTransGen (InternalStep program)
      (route (Radix.point (base m) (Radix.finish (base m) symbol) history 0))
      (route (Radix.point (base m) (Radix.entry (base m))
        (base m * history + symbol.val : ℕ) 0)) := by
    apply Relation.ReflTransGen.lift route
      (fun first last transition => ?_) _ _ (Radix.reverse_pack (base m) history symbol)
    have relocated : step (packing n m)
        (RegisterRelocation.embed (historyRegister n) (frame values 0 0) first) =
        some (RegisterRelocation.embed (historyRegister n) (frame values 0 0) last) := by
      change step (RegisterRelocation.mapTable (historyRegister n) source)
        (RegisterRelocation.embed (historyRegister n) (frame values 0 0) first) = _
      rw [RegisterRelocation.step_embed (historyRegister n) (historyRegister_injective n)
        (frame values 0 0) source
        (reverseTable_deterministic _ (Radix.targetCompatible (base m))), transition, Option.map_some]
    constructor
    · exact Glue.step_map_live (packing n m) (table program) (copy row)
        (fun index => arcEquiv program (.inl (row, index)))
        (fun index => by simp only [table_arc, arcEdge])
        (packing_deterministic n m) (deterministic program) relocated
    · exact not_boundary_copy row first.1 (local_step_not_entry transition)
        (RegisterRelocation.embed (historyRegister n) (frame values 0 0) first).2
  simpa only [route, Radix.point, RegisterRelocation.embed, Glue.mapState, framed,
    frame_extend, port, dispatch] using mapped

private theorem extra_step (program : Counter.Program n m) (arc : Extra program)
    (state : State (n + 2) (size m)) (enabled : (extraEdge program arc).enabled state) :
    step (table program) state = some ((extraEdge program arc).execute state) := by
  apply (step_iff _ (deterministic program)).mpr
  refine ⟨arcEquiv program (.inr arc), ?_, ?_⟩
  · simpa only [table_arc, arcEdge] using enabled
  · rw [table_arc]
    rfl

private theorem history_digit (row : Fin m) (branch : Fin 2) (history : ℕ) :
    base m * history + (digit row branch).val =
      Counter.Recorded.push (finProdFinEquiv (row, branch)) history := by
  simp only [base, digit, Counter.Recorded.push, Nat.add_assoc]

private theorem pack_firstReturn (program : Counter.Program n m)
    {initial : State (n + 2) (size m)} {row : Fin m} {symbol : Fin (base m)}
    {values : Fin n → ℕ} {history : ℕ} (marked : Boundary initial)
    (first_step : step (table program) initial =
      some (framed (port row symbol) values history 0)) :
    FirstReturn program initial
      (framed (dispatch row) values (base m * history + symbol.val : ℕ) 0) := by
  exact ⟨marked, ⟨row, rfl⟩, framed (port row symbol) values history 0, first_step,
    packing_internal_reaches program row symbol values history⟩

private theorem inc_firstReturn (program : Counter.Program n m) (before : Counter.Configuration n m)
    (history : ℕ) (register : Fin n) (target : Fin m)
    (instruction : program before.pc = .inc register target) :
    FirstReturn program (encode before history)
      (encode ⟨target, Function.update before.counters register (before.counters register + 1)⟩
        (base m * history + (digit before.pc 0).val)) := by
  let arc : Extra program := ⟨(before.pc, 0), by
    unfold Active
    rw [instruction]⟩
  have fields := extraEdge_inc program arc register target instruction
  have enabled : (extraEdge program arc).enabled (encode before history) := by
    rw [fields]
    exact ⟨rfl, trivial⟩
  have first_step := extra_step program arc (encode before history) enabled
  rw [fields] at first_step
  simp only [Edge.execute, encode, framed, inc_frame] at first_step
  exact pack_firstReturn program (boundary_encode before history) first_step

private theorem zero_firstReturn (program : Counter.Program n m) (before : Counter.Configuration n m)
    (history : ℕ) (register : Fin n) (zero nonzero : Fin m)
    (instruction : program before.pc = .dec register zero nonzero) (empty : before.counters register = 0) :
    FirstReturn program (encode before history)
      (encode ⟨zero, before.counters⟩ (base m * history + (digit before.pc 0).val)) := by
  let arc : Extra program := ⟨(before.pc, 0), by unfold Active; rw [instruction]; trivial⟩
  have fields : extraEdge program arc =
      ⟨dispatch before.pc, port zero (digit before.pc 0), .test (Fin.castAdd 2 register) true⟩ :=
    extraEdge_dec program arc register zero nonzero instruction
  have enabled : (extraEdge program arc).enabled (encode before history) := by
    rw [fields]
    constructor
    · rfl
    · change Action.enabled (.test (Fin.castAdd 2 register) true)
        (frame before.counters history 0)
      simp [Action.enabled, empty]
  have first_step := extra_step program arc (encode before history) enabled
  rw [fields] at first_step
  simp only [Edge.execute, Action.apply, encode, framed] at first_step
  exact pack_firstReturn program (boundary_encode before history) first_step

private theorem positive_firstReturn (program : Counter.Program n m)
    (before : Counter.Configuration n m) (history : ℕ) (register : Fin n) (zero nonzero : Fin m)
    (instruction : program before.pc = .dec register zero nonzero) (value : ℕ)
    (count : before.counters register = value + 1) :
    FirstReturn program (encode before history)
      (encode ⟨nonzero, Function.update before.counters register value⟩
        (base m * history + (digit before.pc 1).val)) := by
  let probe : Extra program := ⟨(before.pc, 1), by unfold Active; rw [instruction]; trivial⟩
  let write : Extra program := ⟨(before.pc, 2), by unfold Active; rw [instruction]; trivial⟩
  have probe_fields : extraEdge program probe =
      ⟨dispatch before.pc, mid before.pc, .test (Fin.castAdd 2 register) false⟩ :=
    extraEdge_dec program probe register zero nonzero instruction
  have write_fields : extraEdge program write =
      ⟨mid before.pc, port nonzero (digit before.pc 1), .shift (Fin.castAdd 2 register) (-1)⟩ :=
    extraEdge_dec program write register zero nonzero instruction
  have probe_enabled : (extraEdge program probe).enabled (encode before history) := by
    rw [probe_fields]
    constructor
    · rfl
    · change Action.enabled (.test (Fin.castAdd 2 register) false)
        (frame before.counters history 0)
      simp [Action.enabled, count]
      omega
  have first_step := extra_step program probe (encode before history) probe_enabled
  rw [probe_fields] at first_step
  simp only [Edge.execute, Action.apply, encode, framed] at first_step
  have write_enabled : (extraEdge program write).enabled
      (framed (mid before.pc) before.counters history 0) := by
    rw [write_fields]
    exact ⟨rfl, trivial⟩
  have second_step := extra_step program write (framed (mid before.pc) before.counters history 0)
    write_enabled
  rw [write_fields] at second_step
  simp only [Edge.execute, framed, dec_frame before.counters history 0 register value count] at second_step
  refine ⟨boundary_encode before history, ⟨nonzero, rfl⟩,
    framed (mid before.pc) before.counters history 0, first_step, ?_⟩
  exact Relation.ReflTransGen.head
    ⟨second_step, not_boundary_mid before.pc before.counters history 0⟩
    (packing_internal_reaches program nonzero (digit before.pc 1)
      (Function.update before.counters register value) history)

end Monodromy.Counter.Reversible.Recording

theorem solution (program : Counter.Program n m) {before after : Counter.Configuration n m}
    (transition : Counter.step program before = some after) (history : ℕ) :
    FirstReturn program (encode before history)
      (encode after (Counter.Recorded.push (Counter.Recorded.tag program before) history)) := by

  cases instruction : program before.pc with
  | halt => simp [Counter.step, instruction] at transition
  | inc register target =>
      have result := Option.some.inj ((Counter.step_inc program before instruction).symm.trans transition)
      subst after
      have run := inc_firstReturn program before history register target instruction
      rw [history_digit] at run
      simpa only [Counter.Recorded.tag, Counter.Recorded.branch, instruction] using run
  | dec register zero nonzero =>
      cases count : before.counters register with
      | zero =>
          have result := Option.some.inj
            ((Counter.step_dec_zero program before instruction count).symm.trans transition)
          subst after
          have run := zero_firstReturn program before history register zero nonzero instruction count
          rw [history_digit] at run
          simpa only [Counter.Recorded.tag, Counter.Recorded.branch, instruction, count, ite_true] using run
      | succ value =>
          have result := Option.some.inj
            ((Counter.step_dec_succ program before instruction count).symm.trans transition)
          subst after
          have run := positive_firstReturn program before history register zero nonzero instruction value count
          rw [history_digit] at run
          simpa [Counter.Recorded.tag, Counter.Recorded.branch, instruction, count] using run
