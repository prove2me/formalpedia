-- Prove2me | solution 1 for Monodromy.ReversibleCompilation.counter_departure
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T15:04:01.20572+00:00
-- url     : https://prove2.me/submissions/5b659e9c-79ce-4dc0-9438-07b3eb84c069

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Continuation
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
public import Theorems.Thm_Monodromy_Counter_Reversible_step_iff
public import Theorems.Thm_Monodromy_ReversibleCompilation_step_reaches
public import Theorems.Thm_Monodromy_ReversibleRouting_run_pair
public import Theorems.Thm_Monodromy_StagedProgram_cycle_ofFn
public import Theorems.Thm_Monodromy_StagedProgram_haltSignal_embed

@[expose] public section


-- Inline helper skeleton from Monodromy.Continuation.


@[expose] public section

/-!
# Coupled analytic continuation

Two retained logarithmic memory roots share one upper control root through
`F(w₁,w₂,z) = (exp w₁, exp w₂, exp z / (w₁*w₂))`. The two actual lower
lifts generate the upper input path. The returned root is the actual upper
lift endpoint; integer labels occur only in preparation and proofs.

The matching lower product covering and upper pullback covering are explicit.
Their actual lifts agree with the complete runtime curves. Five fixed loops
provide memory shifts, zero-conditional control writes and a control shift.
Concatenation and reversal follow from lift uniqueness. A finite power-root
observation routes whole base paths by normalized analytic kernels at returns.

Five oriented loops give a finite word language and finite root-controlled
program tables with internal stopping. Effective semantics and machine
simulation are proved in the subsequent research layers.
-/

noncomputable section

namespace Monodromy.CoupledContinuation

open unitInterval












attribute [local fun_prop] analyticAt_fst analyticAt_snd





















































































































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval























end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation









end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation


namespace Monodromy.CoupledPullback
























end Monodromy.CoupledPullback


namespace Monodromy.CoupledPullback











end Monodromy.CoupledPullback

namespace Monodromy.CoupledContinuation



















end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



attribute [local fun_prop] analyticAt_fst analyticAt_snd



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval

variable (degree : ℕ) [NeZero degree]



























end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval














































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval













section FiniteRouting

variable (degree : ℕ) [NeZero degree]



























end FiniteRouting











































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation

open unitInterval



































end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



namespace Program

variable {degree : ℕ} [NeZero degree]















end Program

end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation











end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation





end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation



end Monodromy.CoupledContinuation

namespace Monodromy.CoupledContinuation.Program

variable {degree : ℕ} [NeZero degree]

















end Monodromy.CoupledContinuation.Program

/-!
## Reversible conditional control

A finite permutation of control cells is compiled into signed words of the
existing conditional loop. Its inverse is selected from the returned roots.
-/

namespace Monodromy.ReversibleControl

open CoupledContinuation



























variable {degree : ℕ} [NeZero degree]



























end Monodromy.ReversibleControl

/-! Finite root-controlled memory translations use the same signed native A paths. -/

namespace Monodromy.ReversibleMemory

open CoupledContinuation



























variable {degree : ℕ} [NeZero degree]







theorem advance_prepare (moves : Fin degree → ℤ × ℤ) (left right quotient : ℤ) (index : Fin degree) :
    (program moves).advance (prepare left right ((degree : ℤ) * quotient + index.val)) =
      prepare (left + (moves index).1) (right + (moves index).2)
        ((degree : ℤ) * quotient + index.val) := by
  rw [Program.advance_prepare]
  exact execute_memoryWord (moves index) left right _









end Monodromy.ReversibleMemory


/-!
## Integer coordinates of actual returned roots

These coordinates state and prove the action of the existing geometric execution.
They do not participate in path generation or add an execution rule.
-/

namespace Monodromy.CoupledContinuation













namespace Program

variable {degree : ℕ} [NeZero degree]

























end Program

end Monodromy.CoupledContinuation


/-!
## Finite cyclic staging in the existing upper branch

The compiler emits only the existing signed geometric words. A finite stage is
packed into the upper branch, and every generated word is executed by the
unchanged native lifting kernel.
-/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast



















variable (count degree : ℕ) [NeZero count] [NeZero degree]




























/-- A complete cycle is the ordinary composition of the supplied stage advances. -/
theorem iterate_embed (stages : Fin count → Program degree) (steps : ℕ)
    (phase : Fin count) (state : Memory) :
    ((compile count degree stages).advance)^[steps] (embed count phase state) =
      embed count ((finRotate count)^[steps] phase)
        ((List.range steps).foldl
          (fun point position => (stages ((finRotate count)^[position] phase)).advance point) state) := by
  induction steps with
  | zero => rfl
  | succ steps recursive =>
      rw [Function.iterate_succ_apply', recursive, advance_embed]
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Function.iterate_succ_apply']

theorem rotate_iterate (steps : ℕ) (phase : Fin count) :
    (finRotate count)^[steps] phase = phase + (steps : Fin count) := by
  induction steps with
  | zero => simp
  | succ steps recursive =>
      rw [Function.iterate_succ_apply', recursive, finRotate_apply]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]


























end Monodromy.StagedProgram

/-! Static phase-zero stopping for the existing finite-stage compiler. -/

namespace Monodromy.StagedProgram

open CoupledContinuation
open Fin.NatCast

variable (count degree : ℕ) [NeZero count] [NeZero degree]



@[simp] theorem markedCompile_advance (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    : (markedCompile count degree stages mark).advance =
      (compile count degree stages).advance := rfl





theorem halt_embed_iff (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (left right quotient : ℤ) (index : Fin degree) (phase : Fin count) :
    (markedCompile count degree stages mark).haltSignal
      (embed count phase (prepare left right ((degree : ℤ) * quotient + index.val))) = 1 ↔
      phase = 0 ∧ mark index = true := by
  rw [haltSignal_embed]
  by_cases zero : phase = 0
  · cases mark index <;> simp [zero]
  · simp [zero]

theorem step_embed (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (left right quotient : ℤ) (index : Fin degree) (phase : Fin count) :
    (markedCompile count degree stages mark).step
      (embed count phase (prepare left right ((degree : ℤ) * quotient + index.val))) =
      if phase = 0 ∧ mark index = true then none else
        some (embed count (finRotate count phase)
          ((stages phase).advance (prepare left right ((degree : ℤ) * quotient + index.val)))) := by
  simp only [Program.step, halt_embed_iff, markedCompile_advance, advance_embed]

/-- Nonzero packed phases always execute their actual next stage. -/
theorem interior_step (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (phase : Fin count) (nonzero : phase ≠ 0) (state : Memory) :
    (markedCompile count degree stages mark).step (embed count phase state) =
      some (embed count (finRotate count phase) ((stages phase).advance state)) := by
  obtain ⟨labels, rfl⟩ := labelsEquiv.surjective state
  change (markedCompile count degree stages mark).step (embed count phase (Labels.prepare labels)) =
    some (embed count (finRotate count phase) ((stages phase).advance (Labels.prepare labels)))
  have actual := step_embed count degree stages mark labels.1.1 labels.1.2
    (labels.2 / (degree : ℤ)) (Program.indexInt degree labels) phase
  rw [Program.control_decomposition] at actual
  simpa only [nonzero, false_and, ite_false, Labels.prepare] using actual

/-- The existing finite root observation reads the packed clock phase. -/
theorem phaseRoot_embed (phase : Fin count) (state : Memory) :
    controlRoot count (embed count phase state) = (Radix.omega count phase : ℂ) := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  rw [show embed count phase (prepare left right control) =
      prepare left right ((count : ℤ) * control + phase.val) from
    embed_prepare count phase (((left, right), control) : Labels), controlRoot_prepare]
  exact congrArg (fun root : Circle => (root : ℂ)) (Radix.readRoot_digit count control phase)



theorem phaseBoundary_embed_iff (phase : Fin count) (state : Memory) :
    PhaseBoundary count (embed count phase state) ↔ phase = 0 := by
  have root_zero : (Radix.omega count (0 : Fin count) : ℂ) = 1 := by simp [Radix.omega]
  unfold PhaseBoundary
  rw [phaseRoot_embed]
  constructor
  · intro same
    apply Radix.omega_injective count
    exact Subtype.ext (same.trans root_zero.symm)
  · rintro rfl
    exact root_zero

/-- Before a complete clock cycle, its phase cannot revisit zero. -/
theorem rotated_zero_ne_zero (steps : ℕ) (positive : 0 < steps) (before : steps < count) :
    ((finRotate count)^[steps] (0 : Fin count)) ≠ 0 := by
  rw [rotate_iterate, zero_add]
  intro same
  have values := congrArg Fin.val same
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt before, Fin.val_zero] at values
  omega

/-- Arbitrary stage effects cannot create an early phase-zero return. -/
theorem cycle_interior (stages : Fin count → Program degree) (mark : Fin degree → Bool)
    (state : Memory) (steps : ℕ) (positive : 0 < steps) (before : steps < count) :
    ¬ PhaseBoundary count (((markedCompile count degree stages mark).advance)^[steps]
      (embed count 0 state)) := by
  simp only [markedCompile_advance]
  rw [iterate_embed, phaseBoundary_embed_iff]
  exact rotated_zero_ne_zero count steps positive before







end Monodromy.StagedProgram

/-! First-return predecessor uniqueness for reversible advances. -/

namespace Monodromy.ReversibleReturn

variable {State Source : Type*}









end Monodromy.ReversibleReturn


/-! Marked inverse execution and first-return transport. -/

namespace Monodromy.CoupledContinuation.Program

noncomputable section

variable {degree : ℕ} [NeZero degree]







end

end Monodromy.CoupledContinuation.Program

namespace Monodromy.ReversibleReturn

variable {State : Type*}





end Monodromy.ReversibleReturn

end

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





end Monodromy.Counter

namespace Monodromy.CounterMultiplication

















































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

















theorem guards_distinct : guards.Nodup := by decide

theorem guards_exhaustive (guard : ReversibleControl.Guard) : guard ∈ guards := by
  cases guard with
  | none => simp [guards]
  | some entry =>
      rcases entry with ⟨register, atZero⟩
      fin_cases register <;> cases atZero <;> simp [guards]

end Monodromy.ReversiblePorts

/-!
## Native guarded routing
-/

namespace Monodromy.ReversibleRouting

open CoupledContinuation Counter.Reversible ReversiblePorts

variable {q e : ℕ} [NeZero (q + e)]



variable (table : Table 2 q e) (owner : Fin e → Fin q)
  (matching : ∀ guard, Matching owner (selected table guard))

























/-- All five stages send an enabled source or target owner to its exact edge port. -/
theorem run_owner (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values) :
    run table owner matching guards (point values (Fin.castAdd e (owner edge))) =
      point values (Fin.natAdd q edge) := by
  have result := (run_pair table owner matching compatible values edge enabled guards guards_distinct).1
  simpa only [ite_eq_left (guards_exhaustive _)] using result

/-- Reverse stage order returns the edge port to its owner with both memories unchanged. -/
theorem run_port (compatible : CompatibleOwner table owner) (values : Fin 2 → ℤ)
    (edge : Fin e) (enabled : (table edge).action.enabled values) :
    run table owner matching guards.reverse (point values (Fin.natAdd q edge)) =
      point values (Fin.castAdd e (owner edge)) := by
  have result := (run_pair table owner matching compatible values edge enabled guards.reverse
    (List.nodup_reverse.mpr guards_distinct)).2
  simpa only [List.mem_reverse, ite_eq_left (guards_exhaustive _)] using result

end Monodromy.ReversibleRouting

/-!
## The fixed reversible native compiler
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation ReversiblePorts

variable {q e : ℕ} [NeZero q]





theorem apply_coordinates (action : Action 2) (values : Fin 2 → ℤ) :
    ((action.apply values) 0, (action.apply values) 1) =
      (values 0 + (displacement action).1, values 1 + (displacement action).2) := by
  cases action with
  | test => simp [Action.apply, displacement]
  | shift register amount => fin_cases register <;> simp [Action.apply, displacement]

theorem enabled_after_apply (action : Action 2) (values : Fin 2 → ℤ)
    (enabled : action.enabled values) : action.enabled (action.apply values) := by
  cases action <;> exact enabled













theorem update_port (table : Table 2 q e) (edge : Fin e) (values : Fin 2 → ℤ) :
    (update table).advance (portPoint (q := q) edge values) =
      portPoint (q := q) edge ((table edge).action.apply values) := by
  have actual := ReversibleMemory.advance_prepare (moves table) (values 0) (values 1) 0
    (Fin.natAdd q edge)
  simp only [mul_zero, zero_add] at actual
  have coordinates := apply_coordinates (table edge).action values
  have left : ((table edge).action.apply values) 0 =
      values 0 + (displacement (table edge).action).1 := congrArg Prod.fst coordinates
  have right : ((table edge).action.apply values) 1 =
      values 1 + (displacement (table edge).action).2 := congrArg Prod.snd coordinates
  simpa only [update, portPoint, point, moves, finSumFinEquiv_symm_apply_natAdd,
    left, right] using actual











theorem sourceLayers_edge (table : Table 2 q e) (deterministic : Deterministic table)
    (edge : Fin e) (values : Fin 2 → ℤ) (enabled : (table edge).action.enabled values) :
    (sourceLayers table deterministic).foldl (fun state program => program.advance state)
      (sourcePoint (e := e) ((table edge).source, values)) = portPoint (q := q) edge values := by
  simpa only [sourceLayers, List.foldl_map, sourcePoint, point, portPoint,
    ReversibleRouting.run, ReversibleRouting.point] using
    ReversibleRouting.run_owner table (fun edge => (table edge).source)
      (sourceMatching table deterministic) deterministic values edge enabled

theorem targetLayers_edge (table : Table 2 q e) (compatible : TargetCompatible table)
    (edge : Fin e) (values : Fin 2 → ℤ) (enabled : (table edge).action.enabled values) :
    (targetLayers table compatible).foldl (fun state program => program.advance state)
      (portPoint (q := q) edge values) = sourcePoint (e := e) ((table edge).target, values) := by
  simpa only [targetLayers, List.foldl_map, sourcePoint, point, portPoint,
    ReversibleRouting.run, ReversibleRouting.point] using
    ReversibleRouting.run_port table (fun edge => (table edge).target)
      (targetMatching table compatible) compatible values edge enabled

/-- The actual native layers execute an enabled source edge, without calling its successor. -/
theorem layers_edge (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (edge : Fin e) (values : Fin 2 → ℤ)
    (enabled : (table edge).action.enabled values) :
    (layers table deterministic compatible).foldl (fun state program => program.advance state)
      (sourcePoint (e := e) ((table edge).source, values)) =
      sourcePoint (e := e) ((table edge).target, (table edge).action.apply values) := by
  rw [layers, List.foldl_append, sourceLayers_edge table deterministic edge values enabled,
    List.foldl_cons, update_port, targetLayers_edge table compatible edge _
      (enabled_after_apply (table edge).action values enabled)]



omit [NeZero q] in
theorem ofFn_stages (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) :
    List.ofFn (stages table deterministic compatible) = layers table deterministic compatible := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, layers_length]
  · intro index _ _
    rw [List.getElem_ofFn]
    rfl







/-- One source edge is eleven consecutive returns of one fixed native word table. -/
theorem cycle_edge (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (edge : Fin e) (values : Fin 2 → ℤ)
    (enabled : (table edge).action.enabled values) :
    ((program table deterministic compatible).advance)^[11]
      (iota (e := e) ((table edge).source, values)) =
      iota (e := e) ((table edge).target, (table edge).action.apply values) := by
  change ((StagedProgram.compile 11 (q + e) (stages table deterministic compatible)).advance)^[11]
    (StagedProgram.embed 11 0 (sourcePoint (e := e) ((table edge).source, values))) = _
  rw [StagedProgram.cycle_ofFn, ofFn_stages, layers_edge table deterministic compatible edge values enabled]
  rfl

theorem cycle_step (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (transition : step table first = some last) :
    ((program table deterministic compatible).advance)^[11] (iota (e := e) first) =
      iota (e := e) last := by
  obtain ⟨edge, enabled, rfl⟩ := (step_iff table deterministic).mp transition
  rcases first with ⟨position, values⟩
  obtain ⟨rfl, action_enabled⟩ := enabled
  exact cycle_edge table deterministic compatible edge values action_enabled























end Monodromy.ReversibleCompilation

/-!
## Complete execution and actual lifted results
-/

namespace Monodromy.ReversibleCompilation

open Counter.Reversible CoupledContinuation

variable {q e : ℕ} [NeZero q]



omit [NeZero q] in
@[simp] theorem haltMark_source (table : Table 2 q e) (position : Fin q) :
    haltMark table (Fin.castAdd e position) =
      decide (¬ ∃ edge, (table edge).source = position) := by
  simp [haltMark]





@[simp] theorem haltingProgram_advance (table : Table 2 q e)
    (deterministic : Deterministic table) (compatible : TargetCompatible table) :
    (haltingProgram table deterministic compatible).advance = (program table deterministic compatible).advance := rfl



theorem haltSignal_iota (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : State 2 q) :
    (haltingProgram table deterministic compatible).haltSignal (iota (e := e) state) =
      if haltMark table (Fin.castAdd e state.1) then 1 else 0 := by
  have actual := StagedProgram.haltSignal_embed 11 (q + e)
    (stages table deterministic compatible) (haltMark table)
    (state.2 0) (state.2 1) 0 (Fin.castAdd e state.1) 0
  simpa only [haltingProgram, iota, sourcePoint, point, mul_zero, zero_add, ite_true] using actual

theorem haltSignal_iota_iff (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (state : State 2 q) :
    (haltingProgram table deterministic compatible).haltSignal (iota (e := e) state) = 1 ↔
      ¬ ∃ edge, (table edge).source = state.1 := by
  rw [haltSignal_iota, haltMark_source]
  by_cases outgoing : ∃ edge, (table edge).source = state.1 <;> simp [outgoing]































/-- Eleven actual native returns form the first positive phase-zero return. -/
theorem step_firstReturn (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) :
    ((haltingProgram table deterministic compatible).advance)^[11] (iota (e := e) first) =
        iota (e := e) last ∧
      StagedProgram.PhaseBoundary 11 (iota (e := e) first) ∧
      StagedProgram.PhaseBoundary 11 (iota (e := e) last) ∧
      (∀ round : ℕ, 0 < round → round < 11 →
        ¬ StagedProgram.PhaseBoundary 11
          (((haltingProgram table deterministic compatible).advance)^[round] (iota (e := e) first))) ∧
      StateTransition.Reaches₁ (haltingProgram table deterministic compatible).step
        (iota (e := e) first) (iota (e := e) last) := by
  refine ⟨?_, ?_, ?_, ?_, step_reaches table deterministic compatible transition⟩
  · rw [haltingProgram_advance]
    exact cycle_step table deterministic compatible transition
  · exact (StagedProgram.phaseBoundary_embed_iff 11 0 (sourcePoint (e := e) first)).mpr rfl
  · exact (StagedProgram.phaseBoundary_embed_iff 11 0 (sourcePoint (e := e) last)).mpr rfl
  · intro round positive before
    exact StagedProgram.cycle_interior 11 (q + e) (stages table deterministic compatible)
      (haltMark table) (sourcePoint (e := e) first) round positive before



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













private theorem stopped_phase (stages : Fin 11 → Program (q + e)) (bits : Fin (q + e) → Bool)
    (state : Memory) (stopped : (StagedProgram.markedCompile 11 (q + e) stages bits).haltSignal state = 1) :
    StagedProgram.PhaseBoundary 11 state := by
  obtain ⟨⟨base, phase⟩, rfl⟩ := (StagedProgram.packedEquiv 11).surjective state
  apply (StagedProgram.phaseBoundary_embed_iff 11 phase base).mpr
  by_contra nonzero
  have inactive : (StagedProgram.markedCompile 11 (q + e) stages bits).step
      (StagedProgram.embed 11 phase base) = none := by
    exact ite_eq_left stopped
  have active := StagedProgram.interior_step 11 (q + e) stages bits phase nonzero base
  rw [inactive] at active
  cases active

theorem markedBoundary_phase (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {state : Memory}
    (marked : MarkedBoundary table deterministic compatible mark state) :
    StagedProgram.PhaseBoundary 11 state :=
  stopped_phase (stages table deterministic compatible) (markSource mark) state marked

























end Monodromy.ReversibleCompilation

end

end

end


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.ReversibleCompilation
open Counter.Reversible CoupledContinuation
variable {q e : ℕ} [NeZero q]
theorem solution (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) :
    ∃ next, (haltingProgram table deterministic compatible).step (iota (e := e) first) = some next ∧
      NativeInternalReaches table deterministic compatible mark next (iota (e := e) last) := by
  let P := haltingProgram table deterministic compatible
  let initial := iota (e := e) first
  obtain ⟨cycle, _, _, interior, _⟩ := step_firstReturn table deterministic compatible transition
  obtain ⟨edge, enabled, _⟩ := (Counter.Reversible.step_iff table deterministic).mp transition
  have initial_active : P.haltSignal initial ≠ 1 := by
    intro stopped
    exact ((haltSignal_iota_iff table deterministic compatible first).mp stopped) ⟨edge, enabled.1⟩
  have active (round : ℕ) (before : round < 11) :
      P.step (P.advance^[round] initial) = some (P.advance^[round + 1] initial) := by
    rw [Function.iterate_succ_apply']
    apply ite_eq_right
    by_cases zero : round = 0
    · subst round
      exact initial_active
    · intro stopped
      exact interior round (by omega) before
        (stopped_phase (stages table deterministic compatible) (haltMark table)
          (P.advance^[round] initial) stopped)
  have unmarked (round : ℕ) (positive : 0 < round) (before : round < 11) :
      ¬ MarkedBoundary table deterministic compatible mark (P.advance^[round] initial) := by
    intro marked
    exact interior round positive before (markedBoundary_phase table deterministic compatible mark marked)
  have middle (round : ℕ) (bound : round ≤ 10) :
      NativeInternalReaches table deterministic compatible mark (P.advance initial)
        (P.advance^[round + 1] initial) := by
    induction round with
    | zero => exact Relation.ReflTransGen.refl
    | succ round previous =>
        exact (previous (by omega)).tail ⟨active (round + 1) (by omega),
          unmarked (round + 1) (by omega) (by omega)⟩
  refine ⟨P.advance initial, ?_, ?_⟩
  · simpa only [Nat.zero_add, Function.iterate_zero_apply, Function.iterate_one] using active 0 (by decide)
  · have inside := middle 10 (by decide)
    rw [cycle] at inside
    exact inside
