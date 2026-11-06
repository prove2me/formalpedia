-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Recording.valid_step
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:37:18.716196+00:00
-- url     : https://prove2.me/submissions/2a9410ca-78ac-4519-8d4a-7673da228a30

module
public import Definitions.Def_Monodromy_Counter
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}

namespace Monodromy.Counter.Reversible

variable {n q e : ℕ}

namespace Action

private theorem Compatible.not_both {first second : Action n} (compatible : Compatible first second)
    (values : Fin n → ℤ) : ¬ (enabled first values ∧ enabled second values) := by
  cases first <;> cases second <;> simp only [Compatible] at compatible
  rcases compatible with ⟨rfl, different⟩
  rename_i firstZero secondZero
  cases firstZero <;> cases secondZero <;> simp_all [enabled]

end Action

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

namespace RegisterRelocation

variable {n m q e : ℕ}

private theorem enabled_project (register : Fin n → Fin m) (action : Action n) (values : Fin m → ℤ) :
    (mapAction register action).enabled values ↔ action.enabled (values ∘ register) := by
  cases action <;> rfl

private theorem apply_project (register : Fin n → Fin m) (faithful : Function.Injective register)
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

private theorem apply_outside (register : Fin n → Fin m) (action : Action n) (values : Fin m → ℤ)
    (index : Fin m) (outside : ∀ selected, register selected ≠ index) :
    (mapAction register action).apply values index = values index := by
  cases action with
  | test => rfl
  | shift selected amount =>
      exact Function.update_of_ne (outside selected).symm _ _

end RegisterRelocation

namespace Radix

variable (p : ℕ) [NeZero p]

private theorem valid_reverse_step {first last : State 2 (size p)}
    (valid : Valid p first) (transition : step (reverseTable (table p)) first = some last) :
    Valid p last := by
  obtain ⟨index, enabled, rfl⟩ :=
    (step_iff _ (reverseTable_deterministic _ (targetCompatible p))).mp transition
  obtain ⟨arc, rfl⟩ := (arcEquiv p).surjective index
  rcases first with ⟨position, values⟩
  have position_eq : nodeEquiv p (destination p arc) = position := by
    simpa only [reverseTable, reverseEdge, table_arc, Edge.enabled] using enabled.1
  subst position
  have action_enabled : (reverseAction (operation p arc)).enabled values := by
    simpa only [reverseTable, reverseEdge, table_arc] using enabled.2
  clear enabled
  rcases arc with index | ⟨remainder, index⟩ <;> fin_cases index <;>
    simp_all [Valid, admissible, reverseTable, reverseEdge, table_arc, Edge.execute,
      reverseAction, Action.apply, Action.enabled, origin, destination, operation]
  all_goals try omega

end Radix

noncomputable section

namespace Recording

variable {n m : ℕ}

private theorem extraOperation_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraOperation program arc = .shift (Fin.castAdd 2 register) 1 := by
  unfold extraOperation
  split <;> simp_all

private theorem extraEdge_inc (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraEdge program arc =
      ⟨dispatch arc.val.1, port target (digit arc.val.1 0), .shift (Fin.castAdd 2 register) 1⟩ := by
  unfold extraEdge
  rw [extraOrigin_inc program arc register target instruction,
    extraDestination_inc program arc register target instruction,
    extraOperation_inc program arc register target instruction]
  rfl

private theorem extraEdge_dec (program : Counter.Program n m) (arc : Extra program)
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

private theorem valid_copy_iff (program : Counter.Program n m) (row : Fin m)
    (position : Fin (Radix.size (base m))) (values : Fin (n + 2) → ℤ) :
    Valid program (copy row position, values) ↔
      OldNonnegative values ∧ Radix.Valid (base m) (position, values ∘ historyRegister n) := by
  simp only [Valid, copy, Equiv.symm_apply_apply, admissible]

private theorem valid_dispatch_iff (program : Counter.Program n m) (row : Fin m)
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

private theorem valid_port_iff (program : Counter.Program n m) (row : Fin m)
    (symbol : Fin (base m)) (values : Fin (n + 2) → ℤ) :
    Valid program (port row symbol, values) ↔
      OldNonnegative values ∧ 0 ≤ values (historyRegister n 0) ∧
        0 ≤ values (historyRegister n 1) := by
  change Valid program (copy row (Radix.finish (base m) symbol), values) ↔ _
  rw [valid_copy_iff]
  simp [Radix.Valid, Radix.finish, Radix.block, Radix.admissible]

private theorem tail_ne_old (index : Fin 2) (old : Fin n) :
    historyRegister n index ≠ Fin.castAdd 2 old := by
  intro same
  have values := congrArg Fin.val same
  simp only [historyRegister, Fin.val_natAdd, Fin.val_castAdd] at values
  omega

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

end Recording

end
end Monodromy.Counter.Reversible

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
