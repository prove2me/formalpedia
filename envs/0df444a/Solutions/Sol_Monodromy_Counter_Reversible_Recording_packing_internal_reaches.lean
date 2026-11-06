-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Recording.packing_internal_reaches
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:13:21.205707+00:00
-- url     : https://prove2.me/submissions/3e108a61-84ca-4c38-ae90-466c49e579c4

import Definitions.Def_Monodromy_Counter
import Theorems.Thm_Monodromy_Counter_Reversible_Radix_reaches_result

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording

variable {n m : ℕ}

namespace Monodromy.Counter.Reversible

variable {n q e : ℕ}

private theorem Action.Compatible.not_both {first second : Action n} (compatible : Compatible first second)
    (values : Fin n → ℤ) : ¬ (enabled first values ∧ enabled second values) := by
  cases first <;> cases second <;> simp only [Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  rename_i firstZero secondZero
  cases firstZero <;> cases secondZero <;> simp_all [enabled]

private theorem enabled_index_unique (table : Table n q e) (deterministic : Deterministic table)
    {first second : Fin e} {state : State n q}
    (first_enabled : (table first).enabled state) (second_enabled : (table second).enabled state) :
    first = second := by
  by_contra different
  have compatible := deterministic first second different (first_enabled.1.trans second_enabled.1.symm)
  exact (compatible.not_both state.2) ⟨first_enabled.2, second_enabled.2⟩

private theorem StepRel.deterministic (table : Table n q e) (deterministic : Deterministic table)
    {initial first second : State n q} (left : StepRel table initial first)
    (right : StepRel table initial second) : first = second := by
  obtain ⟨left_index, left_enabled, rfl⟩ := left
  obtain ⟨right_index, right_enabled, rfl⟩ := right
  rw [enabled_index_unique table deterministic left_enabled right_enabled]

private theorem step_iff (table : Table n q e) (deterministic : Deterministic table)
    {first last : State n q} : step table first = some last ↔ StepRel table first last := by
  unfold step
  split_ifs with available
  · constructor
    · intro result
      exact ⟨_, Fin.find_spec available, Option.some.inj result⟩
    · intro result
      exact congrArg some (StepRel.deterministic table deterministic
        ⟨_, Fin.find_spec available, rfl⟩ result)
  · simp only [false_iff]
    rintro ⟨index, enabled, _⟩
    exact available ⟨index, enabled⟩

private theorem step_none_iff (table : Table n q e) (state : State n q) :
    step table state = none ↔ ¬ ∃ index, (table index).enabled state := by
  unfold step
  split_ifs <;> simp_all

private theorem reverseAction_involutive (action : Action n) :
    reverseAction (reverseAction action) = action := by
  cases action <;> simp [reverseAction]

@[simp] private theorem reverseAction_apply (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).apply (action.apply values) = values := by
  cases action with
  | test => rfl
  | shift register amount =>
      funext index
      by_cases selected : index = register
      · subst index
        simp [reverseAction, Action.apply]
      · simp [reverseAction, Action.apply, Function.update_of_ne selected]

@[simp] private theorem reverseAction_enabled_apply (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).enabled (action.apply values) ↔ action.enabled values := by
  cases action <;> rfl

@[simp] private theorem reverseEdge_involutive (edge : Edge n q) :
    reverseEdge (reverseEdge edge) = edge := by
  cases edge
  simp [reverseEdge, reverseAction_involutive]

@[simp] private theorem reverseTable_involutive (table : Table n q e) :
    reverseTable (reverseTable table) = table := by
  funext index
  exact reverseEdge_involutive _

private theorem StepRel.reverse {table : Table n q e} {first last : State n q}
    (transition : StepRel table first last) : StepRel (reverseTable table) last first := by
  obtain ⟨index, enabled, rfl⟩ := transition
  refine ⟨index, ⟨rfl, ?_⟩, ?_⟩
  · exact (reverseAction_enabled_apply _ _).mpr enabled.2
  · apply Prod.ext
    · exact enabled.1
    · exact reverseAction_apply _ _

private theorem StepRel_reverse_iff (table : Table n q e) (first last : State n q) :
    StepRel table first last ↔ StepRel (reverseTable table) last first := by
  constructor
  · exact StepRel.reverse
  · intro transition
    simpa only [reverseTable_involutive] using transition.reverse

private theorem step_reverse_iff (table : Table n q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (first last : State n q) :
    step table first = some last ↔ step (reverseTable table) last = some first := by
  rw [step_iff table deterministic,
    step_iff (reverseTable table) (reverseTable_deterministic table compatible), StepRel_reverse_iff]

private theorem reaches_reverse (table : Table n q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State n q}
    (run : StateTransition.Reaches (step table) first last) :
    StateTransition.Reaches (step (reverseTable table)) last first := by
  apply Relation.ReflTransGen.mono (fun before after transition =>
    (step_reverse_iff table deterministic compatible after before).mp transition)
  exact Relation.ReflTransGen.swap last first run

end Monodromy.Counter.Reversible

namespace Monodromy.Counter.Reversible.RegisterRelocation

variable {n m q e : ℕ}

private theorem enabled_project (register : Fin n → Fin m) (action : Action n) (values : Fin m → ℤ) :
    (mapAction register action).enabled values ↔ action.enabled (values ∘ register) := by
  cases action <;> rfl

private theorem action_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (action : Action n) (values : Fin n → ℤ) :
    (mapAction register action).apply (Function.extend register values background) =
      Function.extend register (action.apply values) background := by
  cases action with
  | test => rfl
  | shift index amount =>
      simp only [mapAction, Action.apply, faithful.extend_apply, faithful.extend_update]

private theorem edge_enabled_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (edge : Fin e) (state : State n q) :
    (mapTable register source edge).enabled (embed register background state) ↔
      (source edge).enabled state := by
  simp only [Edge.enabled, mapTable, embed, enabled_project, Function.extend_comp faithful]

private theorem edge_execute_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
    (background : Fin m → ℤ) (source : Table n q e) (edge : Fin e) (state : State n q) :
    (mapTable register source edge).execute (embed register background state) =
      embed register background ((source edge).execute state) := by
  simp only [Edge.execute, mapTable, embed, action_embed register faithful]

private theorem step_embed (register : Fin n → Fin m) (faithful : Function.Injective register)
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

variable {n q k e f : ℕ}

private theorem step_map_live (source : Table n q e) (target : Table n k f)
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

private theorem reverse_pack (p : ℕ) [NeZero p] (quotient : ℕ) (remainder : Fin p) :
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

private theorem not_boundary_copy (row : Fin m) (position : Fin (Radix.size (base m)))
    (interior : position ≠ Radix.entry (base m)) (values : Fin (n + 2) → ℤ) :
    ¬ Boundary (copy row position, values) := by
  rintro ⟨other, same⟩
  exact interior ((copy_eq_iff row other _ _).mp same).2

private theorem local_step_not_entry {first last : State 2 (Radix.size (base m))}
    (transition : step (reverseTable (Radix.table (base m))) first = some last) :
    first.1 ≠ Radix.entry (base m) := by
  intro at_entry
  obtain ⟨index, enabled, _⟩ := (step_iff _
    (reverseTable_deterministic _ (Radix.targetCompatible (base m)))).mp transition
  exact Radix.no_incoming_entry (base m) index (enabled.1.trans at_entry)

private theorem tail_ne_old (index : Fin 2) (old : Fin n) :
    historyRegister n index ≠ Fin.castAdd 2 old := by
  intro same
  have values := congrArg Fin.val same
  simp only [historyRegister, Fin.val_natAdd, Fin.val_castAdd] at values
  omega

@[simp] private theorem frame_tail (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin 2) :
    frame values history workspace (historyRegister n index) = ![history, workspace] index := by
  simp [frame, historyRegister]

private theorem frame_extend (values : Fin n → ℕ) (history workspace : ℤ) :
    Function.extend (historyRegister n) ![history, workspace] (frame values 0 0) =
      frame values history workspace := by
  funext index
  induction index using Fin.addCases with
  | left old =>
      rw [Function.extend_apply' _ _ _ (by rintro ⟨tail, same⟩; exact tail_ne_old tail old same)]
      simp [frame]
  | right tail =>
      change Function.extend (historyRegister n) ![history, workspace] (frame values 0 0)
        (historyRegister n tail) = frame values history workspace (historyRegister n tail)
      rw [(historyRegister_injective n).extend_apply]
      exact (frame_tail values history workspace tail).symm

end Monodromy.Counter.Reversible.Recording

theorem solution (program : Counter.Program n m)
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
  simpa only [route, Radix.point, Reversible.RegisterRelocation.embed, Glue.mapState, framed,
    frame_extend, port, dispatch] using mapped
