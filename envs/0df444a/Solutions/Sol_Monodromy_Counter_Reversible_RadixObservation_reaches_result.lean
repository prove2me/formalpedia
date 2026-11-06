-- Prove2me | solution 1 for Monodromy.Counter.Reversible.RadixObservation.reaches_result
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:17:00.382061+00:00
-- url     : https://prove2.me/submissions/4e5c7c93-05e7-48f7-9710-a7429bc25a66

module
public import Definitions.Def_Monodromy_Counter
public import Theorems.Thm_Monodromy_Counter_Reversible_Radix_reaches_result
public import Theorems.Thm_Monodromy_Counter_Reversible_step_iff

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.RadixObservation
variable (p m : ℕ) [NeZero p]

namespace RadixObservationProof

@[simp] theorem reverseAction_involutive {n : ℕ} (action : Action n) :
    reverseAction (reverseAction action) = action := by
  cases action <;> simp [reverseAction]

@[simp] theorem reverseAction_apply {n : ℕ} (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).apply (action.apply values) = values := by
  cases action with
  | test => rfl
  | shift register amount =>
      funext index
      by_cases selected : index = register
      · subst index
        simp [reverseAction, Action.apply]
      · simp [reverseAction, Action.apply, Function.update_of_ne selected]

@[simp] theorem reverseAction_enabled_apply {n : ℕ} (action : Action n) (values : Fin n → ℤ) :
    (reverseAction action).enabled (action.apply values) ↔ action.enabled values := by
  cases action <;> rfl

@[simp] theorem reverseEdge_involutive {n q : ℕ} (edge : Edge n q) :
    reverseEdge (reverseEdge edge) = edge := by
  cases edge
  simp [reverseEdge]

@[simp] theorem reverseTable_involutive {n q e : ℕ} (table : Table n q e) :
    reverseTable (reverseTable table) = table := by
  funext index
  exact reverseEdge_involutive _

/-- Reversing an enabled edge retraces precisely the same values and control addresses. -/
theorem stepRel_reverse {n q e : ℕ} {table : Table n q e} {first last : State n q}
    (transition : StepRel table first last) : StepRel (reverseTable table) last first := by
  obtain ⟨index, enabled, rfl⟩ := transition
  refine ⟨index, ⟨rfl, ?_⟩, ?_⟩
  · exact (reverseAction_enabled_apply _ _).mpr enabled.2
  · apply Prod.ext
    · exact enabled.1
    · exact reverseAction_apply _ _

theorem stepRel_reverse_iff {n q e : ℕ} (table : Table n q e) (first last : State n q) :
    StepRel table first last ↔ StepRel (reverseTable table) last first := by
  constructor
  · exact stepRel_reverse
  · intro transition
    simpa only [reverseTable_involutive] using stepRel_reverse transition

/-- The bounded finite edge search realizes graph reversal exactly. -/
theorem step_reverse_iff {n q e : ℕ} (table : Table n q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (first last : State n q) :
    step table first = some last ↔ step (reverseTable table) last = some first := by
  rw [step_iff table deterministic,
    step_iff (reverseTable table) (reverseTable_deterministic table compatible), stepRel_reverse_iff]

/-- Every actual finite execution is traversable in reverse by the reversed static table. -/
theorem reaches_reverse {n q e : ℕ} (table : Table n q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State n q}
    (run : StateTransition.Reaches (step table) first last) :
    StateTransition.Reaches (step (reverseTable table)) last first := by
  apply Relation.ReflTransGen.mono (fun before after transition =>
    (step_reverse_iff table deterministic compatible after before).mp transition)
  exact Relation.ReflTransGen.swap last first run

/-- Reversing the radix graph packs a quotient and its finite remainder. -/
theorem radix_reverse_pack (p : ℕ) [NeZero p] (quotient : ℕ) (remainder : Fin p) :
    StateTransition.Reaches (step (reverseTable (Radix.table p)))
      (Radix.point p (Radix.finish p remainder) quotient 0)
      (Radix.point p (Radix.entry p) (p * quotient + remainder.val : ℕ) 0) := by
  have run := reaches_reverse (Radix.table p) (Radix.deterministic p) (Radix.targetCompatible p)
    (Radix.reaches_result p (p * quotient + remainder.val))
  have digit : Counter.DivMod.residue p (p * quotient + remainder.val) = remainder := by
    apply Fin.ext
    exact (Nat.mul_add_mod_self_left p quotient remainder.val).trans (Nat.mod_eq_of_lt remainder.isLt)
  have divide : (p * quotient + remainder.val) / p = quotient := by
    rw [Nat.add_comm, Nat.add_mul_div_left remainder.val quotient (Nat.pos_of_ne_zero (NeZero.ne p)),
      Nat.div_eq_of_lt remainder.isLt, Nat.zero_add]
  simpa only [digit, divide] using run

/-- Inclusion of the chosen edges preserves live steps; exit edges may be added. -/
theorem glue_step_map_live {n q k e f : ℕ} (source : Table n q e) (target : Table n k f)
    (control : Fin q → Fin k) (edge : Fin e → Fin f)
    (agrees : ∀ index, target (edge index) = Glue.mapEdge control (source index))
    (source_valid : Deterministic source) (target_valid : Deterministic target)
    {first last : State n q} (transition : step source first = some last) :
    step target (Glue.mapState control first) = some (Glue.mapState control last) := by
  obtain ⟨index, enabled, result⟩ := (step_iff source source_valid).mp transition
  apply (step_iff target target_valid).mpr
  refine ⟨edge index, ?_, ?_⟩
  · rw [agrees]
    exact ⟨congrArg control enabled.1, enabled.2⟩
  · rw [agrees]
    exact congrArg (Glue.mapState control) result

/-- Every finite source trace runs inside the target with its full register vector. -/
theorem glue_reaches_map_live {n q k e f : ℕ} (source : Table n q e) (target : Table n k f)
    (control : Fin q → Fin k) (edge : Fin e → Fin f)
    (agrees : ∀ index, target (edge index) = Glue.mapEdge control (source index))
    (source_valid : Deterministic source) (target_valid : Deterministic target)
    {first last : State n q} (run : StateTransition.Reaches (step source) first last) :
    StateTransition.Reaches (step target) (Glue.mapState control first) (Glue.mapState control last) := by
  exact Relation.ReflTransGen.lift (Glue.mapState control)
    (fun _ _ transition => glue_step_map_live source target control edge agrees
      source_valid target_valid transition) _ _ run

/-- A wire is a literal equality of control positions, not a new transition. -/
theorem port_interface {n q e : ℕ} {original : Table n q e}
    (wiring : PortNetwork.Wiring original) {exit entry : Fin q}
    (linked : wiring.link exit = some entry) :
    PortNetwork.control wiring exit = PortNetwork.control wiring entry := by
  apply congrArg (PortNetwork.nodeEquiv wiring)
  apply Subtype.ext
  rw [PortNetwork.representative_linked wiring exit entry linked,
    PortNetwork.representative_unlinked wiring entry (wiring.terminal linked)]

@[simp] theorem finishQuery_finish (p : ℕ) (remainder : Fin p) :
    finishQuery p (Radix.finish p remainder) = some remainder := by
  simp [finishQuery, Radix.finish, Radix.block]

@[simp] theorem link_finish (p m : ℕ) [NeZero p] (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (remainder : Fin p) :
    link p m permutation (rawControl p m 0 row (Radix.finish p remainder)) =
      some (rawControl p m 1 (permutation remainder row) (Radix.finish p remainder)) := by
  simp [link, rawControl]

theorem front_finish (p m : ℕ) [NeZero p] (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (remainder : Fin p) :
    front p m permutation row (Radix.finish p remainder) =
      back p m permutation (permutation remainder row) (Radix.finish p remainder) :=
  port_interface (wiring p m permutation) (link_finish p m permutation row remainder)

@[simp] theorem table_front (p m : ℕ) [NeZero p] (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (index : Fin (Radix.edges p)) :
    table p m permutation (arcEquiv p m ((0, row), index)) =
      Glue.mapEdge (front p m permutation row) (Radix.table p index) := by
  change Glue.mapEdge (PortNetwork.control (wiring p m permutation))
    (rawTable p m (arcEquiv p m ((0, row), index))) = _
  rw [rawTable_arc]
  simp only [component, ite_true]
  rfl

@[simp] theorem table_back (p m : ℕ) [NeZero p] (permutation : Fin p → Equiv.Perm (Fin m))
    (row : Fin m) (index : Fin (Radix.edges p)) :
    table p m permutation (arcEquiv p m ((1, row), index)) =
      Glue.mapEdge (back p m permutation row) (reverseTable (Radix.table p) index) := by
  change Glue.mapEdge (PortNetwork.control (wiring p m permutation))
    (rawTable p m (arcEquiv p m ((1, row), index))) = _
  rw [rawTable_arc]
  simp only [component, Fin.isValue, Fin.reduceEq, ite_false]
  rfl

end RadixObservationProof

/-- The actual remainder port selects a reversed copy, which restores both counter values. -/
theorem solution (permutation : Fin p → Equiv.Perm (Fin m)) (row : Fin m) (value : ℕ) :
    StateTransition.Reaches (step (table p m permutation))
      (point p m permutation (inputPort p m permutation row) value 0)
      (point p m permutation (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row)) value 0) := by
  have forward := RadixObservationProof.glue_reaches_map_live (Radix.table p) (table p m permutation)
    (front p m permutation row) (fun index => arcEquiv p m ((0, row), index))
    (fun index => RadixObservationProof.table_front p m permutation row index)
    (Radix.deterministic p) (deterministic p m permutation) (Radix.reaches_result p value)
  have backward := RadixObservationProof.glue_reaches_map_live (reverseTable (Radix.table p))
    (table p m permutation)
    (back p m permutation (permutation (Counter.DivMod.residue p value) row))
    (fun index => arcEquiv p m ((1, permutation (Counter.DivMod.residue p value) row), index))
    (fun index => RadixObservationProof.table_back p m permutation _ index)
    (reverseTable_deterministic _ (Radix.targetCompatible p)) (deterministic p m permutation)
    (RadixObservationProof.radix_reverse_pack p (value / p) (Counter.DivMod.residue p value))
  change StateTransition.Reaches (step (table p m permutation))
    (point p m permutation (inputPort p m permutation row) value 0)
    (point p m permutation (front p m permutation row (Radix.finish p (Counter.DivMod.residue p value)))
      (value / p : ℕ) 0) at forward
  rw [RadixObservationProof.front_finish] at forward
  change StateTransition.Reaches (step (table p m permutation))
    (point p m permutation (back p m permutation (permutation (Counter.DivMod.residue p value) row)
      (Radix.finish p (Counter.DivMod.residue p value))) (value / p : ℕ) 0)
    (point p m permutation (outputPort p m permutation (permutation (Counter.DivMod.residue p value) row))
      (p * (value / p) + (Counter.DivMod.residue p value).val : ℕ) 0) at backward
  have restore : p * (value / p) + (Counter.DivMod.residue p value).val = value := by
    simpa only [Counter.DivMod.residue, Nat.add_comm] using Nat.mod_add_div value p
  rw [restore] at backward
  exact forward.trans backward
