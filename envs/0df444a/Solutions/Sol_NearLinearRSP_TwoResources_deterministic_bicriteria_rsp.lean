-- Prove2me | solution 1 for NearLinearRSP.TwoResources.deterministic_bicriteria_rsp
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-15T18:37:45.541378+00:00
-- url     : https://prove2.me/submissions/7ab93ea0-6137-4128-a5ca-8e80a3a43631

import Theorems.Thm_NearLinearRSP_TwoResources_Implementation_initialization_and_expectation_correct

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

universe u_1

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem ramStep_of_halted :
  ∀ (p : Program) (input : RAMInput) (S : RAMState)
    (h : S.halted = true),
  ramStep p input S = S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.1.1.1

theorem execute_add :
  ∀ (p : Program) (input : RAMInput) (a b : ℕ) (S : RAMState),
  execute p input (a + b) S = execute p input b (execute p input a S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.1.1.2.1

theorem execute_of_halted :
  ∀ (p : Program) (input : RAMInput) (k : ℕ) (S : RAMState)
    (h : S.halted = true),
  execute p input k S = S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.1.1.2.2

theorem Execution.steps_pos :
  ∀ {p : Program} {input : RAMInput}
    {initial final : RAMState} {k : ℕ} (h : Execution p input initial final k)
    (hi : initial.halted = false),
  0 < k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.1.2.1

theorem Execution.steps_unique :
  ∀ {p : Program} {input : RAMInput}
    {initial final₁ final₂ : RAMState} {k₁ k₂ : ℕ}
    (h₁ : Execution p input initial final₁ k₁)
    (h₂ : Execution p input initial final₂ k₂),
  k₁ = k₂ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.1.2.2.1

theorem Execution.deterministic :
  ∀ {p : Program} {input : RAMInput}
    {initial final₁ final₂ : RAMState} {k₁ k₂ : ℕ}
    (h₁ : Execution p input initial final₁ k₁)
    (h₂ : Execution p input initial final₂ k₂),
  k₁ = k₂ ∧ final₁ = final₂ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.1.2.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
namespace Mission

theorem countdown_prefix :
  ∀ (input : RAMInput),
  execute countdownProgram input 10 initialState =
      countdownLoopState (512 / (input.reals 0 / 4) ^ 2) 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.2.1.1

theorem countdown_iteration :
  ∀ (input : RAMInput) (x : ℝ) (k : ℕ)
    (hk : (k : ℝ) < x),
  execute countdownProgram input 4 (countdownLoopState x k) =
      countdownLoopState x (k + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.2.1.2.1

theorem countdown_iterations :
  ∀ (input : RAMInput) (x : ℝ) (k : ℕ)
    (hk : k ≤ Nat.ceil x),
  execute countdownProgram input (4 * k) (countdownLoopState x 0) =
      countdownLoopState x k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.2.1.2.2

theorem countdown_exit :
  ∀ (input : RAMInput) (x : ℝ),
  execute countdownProgram input 4 (countdownLoopState x (Nat.ceil x)) =
      countdownFinalState x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.2.2.1.1

theorem countdown_evaluation :
  ∀ (input : RAMInput),
  execute countdownProgram input
      (14 + 4 * Nat.ceil (512 / (input.reals 0 / 4) ^ 2)) initialState =
      countdownFinalState (512 / (input.reals 0 / 4) ^ 2) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.2.2.1.2

theorem execution_of_bounded_halt :
  ∀ (p : Program) (input : RAMInput)
    (initial : RAMState) (n : ℕ)
    (hh : (execute p input n initial).halted = true),
  ∃ steps ≤ n, Execution p input initial (execute p input n initial) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.2.2.2.1

theorem countdownProgram_correct :
  ∀ (I : Instance) (ε : ℝ),
  ∃ (steps : ℕ) (out : RAMState),
      Execution countdownProgram (encodeInput I ε) initialState out steps ∧
      steps ≤ 14 + 4 * outerQ ε ∧ out.nm 0 = outerQ ε :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.1.2.2.2.2

theorem countdownProgram_cost :
  ∀ (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1),
  ∃ (steps : ℕ) (out : RAMState),
      Execution countdownProgram (encodeInput I ε) initialState out steps ∧
      (steps : ℝ) ≤ 32786 / ε ^ 2 ∧ out.nm 0 = outerQ ε :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.1.1.1

end Mission
end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Structured

theorem initialStore_at :
  initialStore.at 0 = initialState :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.1.1.2.1

theorem queryStore_at :
  ∀ (snapshot : RAMState) (target : ℕ),
  (queryStore snapshot target).at 0 = queryStart snapshot target :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.1.1.2.2

theorem Cmd.compile_length :
  ∀ (c : Cmd) (base : ℕ),
  (c.compile base).length = c.size :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.1.2.1

theorem run_countdown_loop :
  ∀ (input : RAMInput) (g : Guard) (body : Cmd)
    (state : ℕ → Store) (bodyCost : ℕ → ℕ)
    (hexit : g.eval (state 0) = false)
    (hguard : ∀ k, g.eval (state (k + 1)) = true)
    (hbody : ∀ k, Run input body (state (k + 1)) (state k) (bodyCost (k + 1)))
    (k : ℕ),
  Run input (.loop g body) (state k) (state 0) (loopCost bodyCost k) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.1.2.2.1

theorem loopCost_le :
  ∀ (bodyCost : ℕ → ℕ) (bound k : ℕ)
    (h : ∀ j, 1 ≤ j → j ≤ k → bodyCost j ≤ bound),
  loopCost bodyCost k ≤ (bound + 2) * k + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.1.2.2.2

theorem CodeAt.left :
  ∀ {p a b : Program} {base : ℕ} (h : CodeAt p base (a ++ b)),
  CodeAt p base a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.2.1.1

theorem CodeAt.right :
  ∀ {p a b : Program} {base : ℕ} (h : CodeAt p base (a ++ b)),
  CodeAt p (base + a.length) b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.2.1.2.1

theorem CodeAt.head :
  ∀ {p : Program} {base : ℕ} {i : RAMInstr} {code : Program}
    (h : CodeAt p base (i :: code)),
  p[base]?.getD .halt = i :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.2.1.2.2

theorem codeAt_prefix :
  ∀ (pre code post : Program),
  CodeAt (pre ++ code ++ post) pre.length code :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.2.2.1.1

theorem atom_step :
  ∀ (a : Atom) (input : RAMInput) (s : Store) (pc : ℕ) (p : Program)
    (h : p[pc]?.getD .halt = a.val),
  ramStep p input (s.at pc) = (a.eval input s).at (pc + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.2.2.1.2

theorem guard_step :
  ∀ (g : Guard) (input : RAMInput) (s : Store)
    (pc yes no : ℕ) (p : Program) (h : p[pc]?.getD .halt = g.instr yes no),
  ramStep p input (s.at pc) = s.at (if g.eval s then yes else no) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.2.2.2.1

theorem jump_step :
  ∀ (input : RAMInput) (s : Store) (pc target : ℕ) (p : Program)
    (h : p[pc]?.getD .halt = .jump target),
  ramStep p input (s.at pc) = s.at target :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.1.2.2.2.2.2

theorem compile_correct :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (hrun : Run input c s t n),
  ∀ (p : Program) (base : ℕ), CodeAt p base (c.compile base) →
      execute p input n (s.at base) = t.at (base + c.size) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.1.1.1

theorem compiled_execution :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n),
  ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input (s.at 0) out steps ∧ steps ≤ n + 1 ∧
      Store.ofRAM out = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.1.1.2.1

theorem compiled_preprocessing :
  ∀ {input : RAMInput} {c : Cmd} {t : Store} {n : ℕ}
    (h : Run input c initialStore t n),
  ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input initialState out steps ∧ steps ≤ n + 1 ∧
      Store.ofRAM out = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.1.1.2.2

theorem compiled_query :
  ∀ {input : RAMInput} {c : Cmd} {t : Store} {n : ℕ}
    (snapshot : RAMState) (target : ℕ)
    (h : Run input c (queryStore snapshot target) t n),
  ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input (queryStart snapshot target) out steps ∧
      steps ≤ n + 1 ∧ Store.ofRAM out = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.1.2.1

end Structured
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem standalone_RSP_FirstMin__fold_choice_le_seed :
  ∀ {α : Type} (f : α → ℝ) (xs : List α) (x : α),
  f (xs.foldl (fun a b => if f b < f a then b else a) x) ≤ f x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.1.2.2.1

theorem standalone_RSP_FirstMin__fold_choice_le_member :
  ∀ {α : Type} (f : α → ℝ) (xs : List α)
    (x y : α) (hy : y ∈ xs),
  f (xs.foldl (fun a b => if f b < f a then b else a) x) ≤ f y :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.1.2.2.2

theorem firstMin_le_of_mem :
  ∀ {α : Type} (f : α → ℝ) (xs : List α)
    (fallback y : α) (hy : y ∈ xs),
  f (firstMin f xs fallback) ≤ f y :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.1.1

theorem standalone_RSP_FirstMin__fold_choice_pred :
  ∀ {α : Type} (f : α → ℝ) (xs : List α)
    (P : α → Prop) (x : α) (hx : P x) (hall : ∀ y ∈ xs, P y),
  P (xs.foldl (fun a b => if f b < f a then b else a) x) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.1.2.1

theorem firstMin_mem :
  ∀ {α : Type} (f : α → ℝ) (xs : List α) (fallback : α)
    (h : xs ≠ []),
  firstMin f xs fallback ∈ xs :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.1.2.2

theorem dp_faithfulness_saturated :
  ∀ (A : InnerInput) (T : Table) (u v i j : ℕ)
    (h : tickLimit A ≤ i ∨ tickLimit A ≤ j),
  dpValue A T v i j = edgeExpectation A T u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue

@[simp] theorem choose_none_left :
  ∀ {α : Type} (key : α → ℝ) (x : Option α),
  choose key none x = x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.2.1.2

@[simp] theorem choose_none_right :
  ∀ {α : Type} (key : α → ℝ) (x : Option α),
  choose key x none = x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.2.2.1

theorem choose_assoc :
  ∀ {α : Type} (key : α → ℝ) (a b c : Option α),
  choose key (choose key a b) c = choose key a (choose key b c) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.2.2.2

theorem fold_choose :
  ∀ {α : Type} (key : α → ℝ) (xs : List α) (a : Option α),
  xs.foldl (fun a b => choose key a (some b)) a = choose key a (winner key xs) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.1.1.1

theorem winner_append :
  ∀ {α : Type} (key : α → ℝ) (xs ys : List α),
  winner key (xs ++ ys) = choose key (winner key xs) (winner key ys) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.1.1.2.1

@[simp] theorem winner_nil :
  ∀ {α : Type} (key : α → ℝ),
  winner key [] = none :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.1.1.2.2

@[simp] theorem winner_singleton :
  ∀ {α : Type} (key : α → ℝ) (x : α),
  winner key [x] = some x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.1.2.1

theorem fold_some :
  ∀ {α : Type} (key : α → ℝ) (xs : List α) (x : α),
  xs.foldl (fun a b => choose key a (some b)) (some x) =
      some (xs.foldl (fun a b => if key b < key a then b else a) x) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.1.2.2.1

theorem winner_eq_firstMin :
  ∀ {α : Type} (key : α → ℝ) (xs : List α)
    (fallback : α) (hne : xs ≠ []),
  winner key xs = some (firstMin key xs fallback) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.1.2.2.2

theorem Tree.champion_eq_winner :
  ∀ {α : Type} (key : α → ℝ) {h : ℕ} (t : Tree α h),
  t.champion key = winner key t.leaves :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.2.1.1

theorem Tree.champion_eq_firstMin :
  ∀ {α : Type} (key : α → ℝ) {h : ℕ}
    (t : Tree α h) (fallback : α) (hne : t.leaves ≠ []),
  t.champion key = some (firstMin key t.leaves fallback) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.2.1.2.1

theorem Path.index_lt :
  ∀ {h : ℕ} (p : Path h),
  p.index < 2 ^ h :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.2.1.2.2

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

@[ext] theorem store_ext :
  ∀ (s t : Store)
    (hnr : ∀ a, s.nr a = t.nr a) (hrr : ∀ a, s.rr a = t.rr a)
    (hnm : ∀ a, s.nm a = t.nm a) (hrm : ∀ a, s.rm a = t.rm a),
  s = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.2.2.1.1

theorem run_atoms :
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (atoms as) s (evalAtoms input as s) as.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.2.2.1.2

theorem merge_decode :
  ∀ (a b : Record),
  (merge a b).decode = choose Record.key a.decode b.decode :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.2.2.2.1

theorem loadChildren_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input loadChildren s = loaded s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.2.2.2.2.2

theorem storeLeft_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input storeLeft s = writeRecord s (s.nr 7) ⟨s.nr 8, s.rr 0⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.1.1.1

theorem storeRight_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input storeRight s = writeRecord s (s.nr 7) ⟨s.nr 9, s.rr 1⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.1.1.2.1

theorem selectChild_run :
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 3 = 0),
  ∃ k ≤ 6, Run input selectChild s
      (writeRecord s (s.nr 7) (merge ⟨s.nr 8, s.rr 0⟩ ⟨s.nr 9, s.rr 1⟩)) k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.1.1.2.2

theorem refreshNode_run :
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 3 = 0),
  ∃ k ≤ 15, Run input refreshNode s (refreshed s) k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.1.2.1

theorem refreshed_record :
  ∀ (s : Store),
  readRecord (refreshed s) (s.nr 1 + s.nr 0) =
      merge (readRecord s (s.nr 1 + (s.nr 0 + s.nr 0)))
        (readRecord s (s.nr 1 + (s.nr 0 + s.nr 0 + s.nr 4))) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.1.2.2.1

theorem refreshed_other :
  ∀ (s : Store) (a : ℕ) (ha : a ≠ s.nr 1 + s.nr 0),
  (refreshed s).nm a = s.nm a ∧ (refreshed s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.1.2.2.2

theorem refreshed_header :
  ∀ (s : Store) (a : ℕ) (ha : a < 5),
  (refreshed s).nr a = s.nr a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.2.1.1

theorem parentHop_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input parentHop s = advanced s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.2.1.2.1

theorem repairBody_run :
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 3 = 0),
  ∃ k ≤ 17, Run input repairBody s (repairStep s) k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.2.1.2.2

@[simp] theorem hops_zero :
  hops 0 = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.2.2.1.1

theorem hops_pos :
  ∀ (n : ℕ) (hn : 0 < n),
  hops n = hops (n / 2) + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.2.2.1.2

theorem hops_le_of_lt_pow :
  ∀ (n h : ℕ) (hn : n < 2 ^ h),
  hops n ≤ h :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.2.2.2.1

theorem hops_le_clog :
  ∀ (n capacity : ℕ) (hn : n < capacity),
  hops n ≤ Nat.clog 2 capacity :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.1.2.2.2.2

theorem repairStep_header :
  ∀ (s : Store) (a : ℕ) (ha : 0 < a) (ha' : a < 5),
  (repairStep s).nr a = s.nr a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.1.1.1

theorem repairStep_parent :
  ∀ (capacity : ℕ) (s : Store) (h : ParentLayout capacity s),
  (repairStep s).nr 0 = s.nr 0 / 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.1.1.2.1

theorem repairStep_layout :
  ∀ (capacity : ℕ) (s : Store) (h : ParentLayout capacity s),
  ParentLayout capacity (repairStep s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.1.1.2.2

theorem repairAncestors_run :
  ∀ (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s),
  ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * hops (s.nr 0) + 1 ∧ out.nr 0 = 0 ∧ ParentLayout capacity out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.1.2.1

theorem repairAncestors_logarithmic :
  ∀ (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s),
  ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * Nat.clog 2 capacity + 1 ∧ out.nr 0 = 0 ∧ ParentLayout capacity out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.1.2.2.1

@[simp] theorem ancestors_zero :
  ancestors 0 = [] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.1.2.2.2

theorem ancestors_pos :
  ∀ (n : ℕ) (hn : 0 < n),
  ancestors n = n :: ancestors (n / 2) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.2.1.1

theorem le_of_mem_ancestors :
  ∀ (n v : ℕ) (hv : v ∈ ancestors n),
  v ≤ n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.2.1.2.1

theorem repairStep_record_other :
  ∀ (s : Store) (v : ℕ) (hv : v ≠ s.nr 0),
  readRecord (repairStep s) (s.nr 1 + v) = readRecord s (s.nr 1 + v) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.2.1.2.2

theorem repairStep_ready :
  ∀ (capacity : ℕ) (truth : ℕ → Record) (s : Store)
    (h : ParentLayout capacity s) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hinternal : s.nr 0 + s.nr 0 + 1 < capacity)
    (hc : Coherent capacity truth) (hr : Ready capacity truth s),
  Ready capacity truth (repairStep s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.2.2.1.1

theorem repairAncestors_correct :
  ∀ (input : RAMInput) (capacity : ℕ)
    (truth : ℕ → Record) (s : Store) (h : ParentLayout capacity s)
    (hone : s.nr 4 = 1) (hinternal : s.nr 0 + s.nr 0 + 1 < capacity)
    (hc : Coherent capacity truth) (hr : Ready capacity truth s),
  ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * hops (s.nr 0) + 1 ∧ out.nr 0 = 0 ∧
      (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout capacity out ∧
      ∀ v < capacity, readRecord out (s.nr 1 + v) = truth v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.2.2.1.2

theorem writeLeaf_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input writeLeaf s = leafWritten s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.2.2.2.1

theorem leafWritten_header :
  ∀ (s : Store) (a : ℕ) (ha : a ≠ 7),
  (leafWritten s).nr a = s.nr a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.1.2.2.2.2.2

theorem updateStart_header :
  ∀ (s : Store) (a : ℕ) (ha : 0 < a) (ha' : a < 5),
  (updateStart s).nr a = s.nr a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.1.1.1

theorem leafWritten_other :
  ∀ (s : Store) (a : ℕ) (ha : a ≠ s.nr 1 + s.nr 0),
  (leafWritten s).nm a = s.nm a ∧ (leafWritten s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.1.1.2.1

theorem updateStart_parent :
  ∀ (capacity : ℕ) (s : Store) (h : ParentLayout capacity s),
  (updateStart s).nr 0 = s.nr 0 / 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.1.1.2.2

theorem updateStart_layout :
  ∀ (capacity : ℕ) (s : Store) (h : ParentLayout capacity s),
  ParentLayout capacity (updateStart s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.1.2.1

theorem updateStart_ready :
  ∀ (capacity : ℕ) (truth : ℕ → Record) (s : Store)
    (h : ParentLayout capacity s) (hpositive : 0 < s.nr 0)
    (hr : Ready capacity truth s) (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 2⟩),
  Ready capacity truth (updateStart s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.1.2.2.1

theorem updateLeaf_correct :
  ∀ (input : RAMInput) (leaves : ℕ)
    (truth : ℕ → Record) (s : Store) (h : ParentLayout (2 * leaves) s)
    (hone : s.nr 4 = 1) (hpositive : 0 < s.nr 0)
    (hc : Coherent (2 * leaves) truth) (hr : Ready (2 * leaves) truth s)
    (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 2⟩),
  ∃ out k, Run input updateLeaf s out k ∧
      k ≤ 19 * Nat.clog 2 (2 * leaves) + 6 ∧ out.nr 0 = 0 ∧
      (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout (2 * leaves) out ∧
      ∀ v < 2 * leaves, readRecord out (s.nr 1 + v) = truth v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.1.2.2.2

theorem run_final_unique :
  ∀ {input : RAMInput} {c : Cmd} {s t u : Store} {n m : ℕ}
    (h : Run input c s t n) (h' : Run input c s u m),
  t = u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.2.1.1

theorem WinnerFrame.refl :
  ∀ (W capacity : ℕ) (s : Store),
  WinnerFrame W capacity s s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.2.1.2.1

theorem WinnerFrame.trans :
  ∀ (W capacity : ℕ) (s u t : Store)
    (h : WinnerFrame W capacity s u) (h' : WinnerFrame W capacity u t),
  WinnerFrame W capacity s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.2.1.2.2

theorem repairStep_frame :
  ∀ (capacity : ℕ) (s : Store) (hn : s.nr 0 < capacity),
  WinnerFrame (s.nr 1) capacity s (repairStep s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.2.2.1.1

theorem repairAncestors_run_frame :
  ∀ (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s),
  ∃ out k, Run input repairAncestors s out k ∧ WinnerFrame (s.nr 1) capacity s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.2.2.1.2

theorem repairAncestors_frame :
  ∀ (input : RAMInput) (capacity : ℕ) (s out : Store) (k : ℕ)
    (h : ParentLayout capacity s) (hrun : Run input repairAncestors s out k),
  WinnerFrame (s.nr 1) capacity s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.2.2.2.1

theorem updateStart_frame :
  ∀ (capacity : ℕ) (s : Store) (hn : s.nr 0 < capacity),
  WinnerFrame (s.nr 1) capacity s (updateStart s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.2.2.2.2

theorem updateLeaf_frame :
  ∀ (input : RAMInput) (capacity : ℕ) (s out : Store) (k : ℕ)
    (h : ParentLayout capacity s) (hrun : Run input updateLeaf s out k),
  WinnerFrame (s.nr 1) capacity s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.1.1

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

theorem run_atoms :
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (Cmd.atoms as) s (evalAtoms input as s) as.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.1.2.1

@[simp] theorem Cmd.atoms_size :
  ∀ (as : List Atom),
  (Cmd.atoms as).size = as.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.1.2.2

@[ext] theorem Store.ext :
  ∀ {s t : Store} (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm),
  s = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.2.1.1

theorem run_atoms_append :
  ∀ (input : RAMInput) (as bs : List Atom) (s : Store),
  evalAtoms input (as ++ bs) s = evalAtoms input bs (evalAtoms input as s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.2.1.2

theorem run_bounded_loop :
  ∀ (input : RAMInput) (g : Guard) (body : Cmd)
    (limit bound : ℕ) (P : ℕ → Store → Prop)
    (hguard : ∀ k s, k ≤ limit → P k s → g.eval s = decide (k < limit))
    (hstep : ∀ k s, k < limit → P k s →
      ∃ t n, Run input body s t n ∧ P (k + 1) t ∧ n ≤ bound)
    (k : ℕ) (s : Store) (hk : k ≤ limit) (hs : P k s),
  ∃ t n, Run input (.loop g body) s t n ∧ P limit t ∧
      n ≤ (bound + 2) * (limit - k) + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.2.2.1

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem treeLeafAtoms_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeLeafAtoms s = treeLeafPrepared s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.2.2.2

theorem treeLeafPrepare_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ steps ≤ 13, Run input treeLeafPrepare s (treeLeafReady s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.2.1.1

theorem treeLeafReady_values :
  ∀ (s : Store) (hz : s.nr 3 = 0) (hone : s.nr 4 = 1),
  (treeLeafReady s).nr 0 = s.nr 170 + s.nr 172 ∧
    (treeLeafReady s).nr 10 = s.nr 172 + 1 ∧
    (treeLeafReady s).nr 175 = s.nm (s.nr 171 + s.nr 172) ∧
    (treeLeafReady s).nm (targetAddress (s.nm (s.nr 171 + s.nr 172)) + s.nr 173) = 0 ∧
    (treeLeafReady s).rr 2 =
      (if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.2.1.2.1

theorem treeLeafReady_queue_header :
  ∀ (s : Store) (r : ℕ) (hr : 0 < r) (hr' : r < 5),
  (treeLeafReady s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.2.1.2.2

theorem treeInitializeLeaf_run :
  ∀ (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeLeafReady s))
    (hone : s.nr 4 = 1) (hpositive : 0 < s.nr 170 + s.nr 172)
    (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeLeafReady s))
    (hnew : truth (s.nr 170 + s.nr 172) =
      ⟨s.nr 172 + 1, if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170⟩),
  ∃ out steps, Run input treeInitializeLeaf s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 19 ∧
      Queue.ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.2.2.1.1

theorem treeSeedBody_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ steps ≤ 16, Run input treeSeedBody s (treeSeedStep input s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.2.2.1.2

theorem treeSeedStep_counter :
  ∀ (input : RAMInput) (s : Store),
  (treeSeedStep input s).nr 172 = s.nr 172 + s.nr 4 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.2.2.2.1

theorem treeSeedStep_fixed :
  ∀ (input : RAMInput) (s : Store),
  (treeSeedStep input s).nr 4 = s.nr 4 ∧
    (treeSeedStep input s).nr 12 = s.nr 12 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.2.2.2.2

theorem treeSeedStep_memory :
  ∀ (input : RAMInput) (s : Store),
  (treeSeedStep input s).nm =
      Function.update s.nm (targetAddress (s.nm (s.nr 171 + s.nr 172)) + s.nr 173) (s.nr 3) ∧
    (treeSeedStep input s).rm = Function.update s.rm (s.nr 13 + s.nr 172)
      (if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.1.1.1

theorem treeSeedLoop_run :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (hone : s.nr 4 = 1) (hend : s.nr 172 + remaining = s.nr 12),
  ∃ steps ≤ 18 * remaining + 1,
      Run input (.loop (.nat .lt 172 12) treeSeedBody) s
        (treeSeedSteps input remaining s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.1.1.2.1

theorem treeSeed_run :
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 4 = 1),
  ∃ steps ≤ 18 * s.nr 12 + 2,
      Run input treeSeed s (treeSeedSteps input (s.nr 12) (treeSeedStart s)) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.1.1.2.2

theorem treeSeedStep_nr_fixed :
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∈ [3,4,12,13,123,171,173]),
  (treeSeedStep input s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.1.2.1

theorem treeSeedStep_top_fixed :
  ∀ (input : RAMInput) (s : Store),
  (treeSeedStep input s).rr 170 = s.rr 170 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.1.2.2.1

theorem TreeSeedInv.step :
  ∀ {xs : List ℕ} {A R source off k : ℕ} {top : ℝ} {s : Store}
    (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (hk : k < xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  TreeSeedInv xs A R source off top (k + 1) (treeSeedStep input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.1.2.2.2

theorem TreeSeedInv.steps :
  ∀ {xs : List ℕ} {A R source off k : ℕ} {top : ℝ} {s : Store}
    (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (remaining : ℕ) (hend : k + remaining = xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  TreeSeedInv xs A R source off top xs.length (treeSeedSteps input remaining s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.1.1

theorem treeSeed_correct :
  ∀ (input : RAMInput) (xs : List ℕ) (A R source off : ℕ) (top : ℝ)
    (s : Store) (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A)
    (hR : s.nr 13 = R) (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  ∃ out steps, Run input treeSeed s out steps ∧ steps ≤ 18 * xs.length + 2 ∧
      TreeSeedInv xs A R source off top xs.length out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.1.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

theorem Atom.nat_frame :
  ∀ (a : Atom) (input : RAMInput) (s : Store) (r : ℕ)
    (h : r ∉ a.natWrites),
  (a.eval input s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.1.2.2

theorem Atom.real_frame :
  ∀ (a : Atom) (input : RAMInput) (s : Store) (r : ℕ)
    (h : r ∉ a.realWrites),
  (a.eval input s).rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.2.1.1

theorem Atom.natMemory_frame :
  ∀ (a : Atom) (input : RAMInput) (s : Store)
    (h : a.writesNatMemory = false),
  (a.eval input s).nm = s.nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.2.1.2

theorem Atom.realMemory_frame :
  ∀ (a : Atom) (input : RAMInput) (s : Store)
    (h : a.writesRealMemory = false),
  (a.eval input s).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.2.2.1

theorem Run.nat_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.natWrites),
  t.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.2.2.2

theorem Run.real_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.realWrites),
  t.rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.1

theorem Run.natMemory_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesNatMemory = false),
  t.nm = s.nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.2.1

theorem Run.realMemory_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesRealMemory = false),
  t.rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.2.2

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem TreeSeedInv.step_memory_frame :
  ∀ {xs : List ℕ} {A R source off k : ℕ} {top : ℝ}
    {s : Store} (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (hk : k < xs.length) (a : ℕ)
    (hn : ∀ v ∈ xs, a ≠ targetAddress v + off)
    (hr : a < R ∨ R + xs.length ≤ a),
  (treeSeedStep input s).nm a = s.nm a ∧ (treeSeedStep input s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.2.1

theorem TreeSeedInv.steps_memory_frame :
  ∀ {xs : List ℕ} {A R source off k : ℕ} {top : ℝ}
    {s : Store} (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (remaining : ℕ) (hend : k + remaining = xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A) (a : ℕ)
    (hn : ∀ v ∈ xs, a ≠ targetAddress v + off)
    (hr : a < R ∨ R + xs.length ≤ a),
  (treeSeedSteps input remaining s).nm a = s.nm a ∧
      (treeSeedSteps input remaining s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.2.2.1

theorem treeSeed_register_frame :
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input treeSeed s out steps)
    (hr : r ∉ ({0,10,172,174,175,176,177,178} : Finset ℕ)),
  out.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.2.2.2

theorem treeSeed_real_register_frame :
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input treeSeed s out steps) (hr : r ≠ 2),
  out.rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.2.1.1

theorem treeSeedStart_inv :
  ∀ (xs : List ℕ) (A R source off : ℕ) (top : ℝ) (s : Store)
    (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A) (hR : s.nr 13 = R)
    (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v),
  TreeSeedInv xs A R source off top 0 (treeSeedStart s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.2.1.2.1

theorem treeSeed_framed :
  ∀ (input : RAMInput) (xs : List ℕ) (A R source off : ℕ) (top : ℝ)
    (s : Store) (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A)
    (hR : s.nr 13 = R) (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  ∃ out steps, Run input treeSeed s out steps ∧ steps ≤ 18 * xs.length + 2 ∧
      TreeSeedInv xs A R source off top xs.length out ∧
      (∀ a, (∀ v ∈ xs, a ≠ targetAddress v + off) →
        (a < R ∨ R + xs.length ≤ a) → out.nm a = s.nm a ∧ out.rm a = s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.2.1.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

theorem heapTruth_internal :
  ∀ (B : ℕ) (leaf : ℕ → Record) (v : ℕ)
    (hv : 0 < v) (hB : v < B),
  heapTruth B leaf v = merge (heapTruth B leaf (v + v)) (heapTruth B leaf (v + v + 1)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.2.2.1.1

theorem heapTruth_leaf :
  ∀ (B : ℕ) (leaf : ℕ → Record) (v : ℕ)
    (hv : B ≤ v),
  heapTruth B leaf v = leaf v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.2.2.1.2

theorem heapTruth_coherent :
  ∀ (B : ℕ) (leaf : ℕ → Record),
  Coherent (2 * B) (heapTruth B leaf) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.2.2.2.1

@[simp] theorem merge_self :
  ∀ (r : Record),
  merge r r = r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.2.2.2.2

theorem heapTruth_const :
  ∀ (B : ℕ) (r : Record) (v : ℕ),
  heapTruth B (fun _ => r) v = r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.1.1.1

theorem mem_ancestors_self :
  ∀ (n : ℕ) (hn : 0 < n),
  n ∈ ancestors n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.1.1.2.1

theorem parent_mem_ancestors :
  ∀ (n v : ℕ) (hv : v ∈ ancestors n) (hp : 0 < v / 2),
  v / 2 ∈ ancestors n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.1.1.2.2

theorem child_not_mem_ancestors :
  ∀ (k v : ℕ) (hv : 0 < v) (hk : v ∉ ancestors k),
  v + v ∉ ancestors k ∧ v + v + 1 ∉ ancestors k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.1.2.1

theorem heapTruth_frame :
  ∀ (B : ℕ) (leaf leaf' : ℕ → Record) (k : ℕ)
    (hk : 0 < k) (hchange : ∀ v, v ≠ k → leaf' v = leaf v),
  ∀ v, v ∉ ancestors k → heapTruth B leaf' v = heapTruth B leaf v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.1.2.2.1

theorem leafRecords_add :
  ∀ (leaf : ℕ → Record) (start a b : ℕ),
  leafRecords leaf start (a+b) =
      leafRecords leaf start a ++ leafRecords leaf (start+a) b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.1.2.2.2

theorem heapTruth_decode_subtree :
  ∀ (B : ℕ) (leaf : ℕ → Record) (h v : ℕ)
    (hv : 0 < v) (hlo : B ≤ v * 2^h) (hhi : (v+1)*2^h ≤ 2*B),
  (heapTruth B leaf v).decode =
      winner Record.key (leafRecords leaf (v * 2^h) (2^h)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.1.1

theorem heapTruth_root :
  ∀ (h : ℕ) (leaf : ℕ → Record),
  (heapTruth (2^h) leaf 1).decode = winner Record.key (leafRecords leaf (2^h) (2^h)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.1.2.1

theorem choose_map :
  ∀ {α β : Type} (key : β → ℝ) (f : α → β) (a b : Option α),
  choose key (a.map f) (b.map f) = (choose (key ∘ f) a b).map f :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.1.2.2

theorem winner_map :
  ∀ {α β : Type} (key : β → ℝ) (f : α → β) (xs : List α),
  winner key (xs.map f) = (winner (key ∘ f) xs).map f :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.2.1.1

theorem heapTruth_firstMin :
  ∀ (h : ℕ) (leaf : ℕ → Record) (xs : List ℕ)
    (encode : ℕ → Record) (hslots : leafRecords leaf (2^h) (2^h) = xs.map encode)
    (fallback : ℕ) (hne : xs ≠ []),
  (heapTruth (2^h) leaf 1).decode =
      some (encode (firstMin (fun v => (encode v).key) xs fallback)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.2.1.2

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory
namespace RSP.Tails

theorem mass_nonneg :
  ∀ (r : ℝ≥0) (n : ℕ),
  0 ≤ mass r n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.2.2.1

theorem mass_succ_mul :
  ∀ (r : ℝ≥0) (n : ℕ),
  mass r (n + 1) * (n + 1 : ℝ) = (r : ℝ) * mass r n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.2.2.2

theorem mass_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (mass r) 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.1.1

theorem poisson_pgf_hasSum :
  ∀ (r : ℝ≥0) (z : ℝ),
  HasSum (fun n : ℕ => mass r n * z ^ n) (Real.exp ((r : ℝ) * (z - 1))) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.1.2.1

theorem poisson_pgf :
  ∀ (r : ℝ≥0) (z : ℝ),
  (∫ n : ℕ, z ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (z - 1)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.1.2.2

theorem firstMoment_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * (n : ℝ)) (r : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.2.1

theorem factorialMoment_two_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * ((n : ℝ) * ((n : ℝ) - 1))) ((r : ℝ) ^ 2) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.2.2.1

theorem secondMoment_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * (n : ℝ) ^ 2) ((r : ℝ) ^ 2 + (r : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.2.2.2

theorem poisson_integrable_sq :
  ∀ (r : ℝ≥0),
  Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.2.1.1

theorem poisson_memLp_two :
  ∀ (r : ℝ≥0),
  MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.2.1.2.1

theorem poisson_mean :
  ∀ (r : ℝ≥0),
  (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = (r : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.2.1.2.2

theorem poisson_secondMoment :
  ∀ (r : ℝ≥0),
  (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + (r : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.2.2.1.1

theorem poisson_variance :
  ∀ (r : ℝ≥0),
  variance (fun n : ℕ => (n : ℝ)) (poissonMeasure r) = (r : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.2.2.1.2

theorem poisson_upper_tail :
  ∀ (r : ℝ≥0) (a : ℝ) (ha : (r : ℝ) < a),
  poissonMeasure r {n : ℕ | a ≤ (n : ℝ)} ≤
      ENNReal.ofReal ((r : ℝ) / (a - (r : ℝ)) ^ 2) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.2.2.2.1

theorem poisson_lower_tail :
  ∀ (r : ℝ≥0) (a : ℝ) (ha : a < (r : ℝ)),
  poissonMeasure r {n : ℕ | (n : ℝ) ≤ a} ≤
      ENNReal.ofReal ((r : ℝ) / ((r : ℝ) - a) ^ 2) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.2.2.2.2

theorem completeness_ratio :
  ∀ (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε),
  (q / (1 + ε / 2)) / (q - q / (1 + ε / 2)) ^ 2 =
      (4 + 2 * ε) / (q * ε ^ 2) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.1.1.1

theorem soundness_ratio :
  ∀ (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε),
  (q * (1 + ε) / (1 + ε / 2)) /
        (q * (1 + ε) / (1 + ε / 2) - q) ^ 2 =
      (4 + 6 * ε + 2 * ε ^ 2) / (q * ε ^ 2) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.1.1.2.1

theorem completeness_ratio_le :
  ∀ (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2),
  (q / (1 + ε / 2)) / (q - q / (1 + ε / 2)) ^ 2 ≤
      1 / (8 * (k : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.1.1.2.2

theorem soundness_ratio_le :
  ∀ (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2),
  (q * (1 + ε) / (1 + ε / 2)) /
        (q * (1 + ε) / (1 + ε / 2) - q) ^ 2 ≤
      1 / (8 * (k : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.1.2.1

theorem poisson_completeness_tail :
  ∀ (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2) (hr : (r : ℝ) = q / (1 + ε / 2)),
  (poissonMeasure r).real {n : ℕ | q ≤ (n : ℝ)} ≤ 1 / (8 * (k : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.1.2.2.1

theorem poisson_completeness_tail_of_le :
  ∀ (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2) (hr : (r : ℝ) ≤ q / (1 + ε / 2)),
  (poissonMeasure r).real {n : ℕ | q ≤ (n : ℝ)} ≤ 1 / (8 * (k : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.1.2.2.2

theorem poisson_soundness_tail :
  ∀ (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (hr : (r : ℝ) = q * (1 + ε) / (1 + ε / 2)),
  (poissonMeasure r).real {n : ℕ | (n : ℝ) < q} ≤ 1 / (8 * (k : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.2.1.1

theorem resource_union_bound :
  ∀ {Ω : Type u_1} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (events : Fin k → Set Ω)
    (h : ∀ i, μ.real (events i) ≤ 1 / (8 * (k : ℝ))),
  μ.real (⋃ i, events i) ≤ 1 / 8 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).1.1.2.2.1.1.2.1.2.1

theorem poisson_completeness_union :
  ∀ {Ω : Type u_1} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : ℝ≥0) (hr : (r : ℝ) = q / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure r) μ),
  μ.real (⋃ i, {ω | q ≤ (X i ω : ℝ)}) ≤ 1 / 8 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).1.1.2.2.1.1.2.1.2.2

theorem poisson_completeness_union_of_le :
  ∀ {Ω : Type u_1} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : Fin k → ℝ≥0) (hr : ∀ i, (r i : ℝ) ≤ q / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) μ),
  μ.real (⋃ i, {ω | q ≤ (X i ω : ℝ)}) ≤ 1 / 8 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).1.1.2.2.1.1.2.2.1.1

theorem countdown_pos :
  ∀ (k : ℕ) (ε : ℝ) (hk : 0 < k) (hε : 0 < ε),
  0 < countdown k ε :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.2.2.1.2

theorem countdown_sufficient :
  ∀ (k : ℕ) (ε : ℝ) (hε : 0 < ε),
  128 * (k : ℝ) ≤ (countdown k ε : ℝ) * ε ^ 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.2.2.2.1

theorem poisson_soundness_union :
  ∀ {Ω : Type u_1} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : ℝ≥0) (hr : (r : ℝ) = q * (1 + ε) / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure r) μ),
  μ.real (⋃ i, {ω | (X i ω : ℝ) < q}) ≤ 1 / 8 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).1.1.2.2.1.1.2.2.2.2

end RSP.Tails
end

set_option autoImplicit false
section
set_option autoImplicit false
open NearLinearRSP.TwoResources
namespace RSP.PoissonBridge

theorem lengthRate_nonneg :
  ∀ (A : InnerInput),
  0 ≤ lengthRate A :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.1.1

theorem costRate_nonneg :
  ∀ (A : InnerInput),
  0 ≤ costRate A :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.1.2.1

theorem poissonCountMass_nonneg :
  ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℕ),
  0 ≤ ActuarialValuation.poissonCountMass r n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.1.2.2

theorem poissonCountMass_hasSum :
  ∀ (r : ℝ) (hr : 0 ≤ r),
  HasSum (ActuarialValuation.poissonCountMass r) 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.2.1

theorem poissonCountMass_sum_le_one :
  ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℕ),
  (∑ a ∈ Finset.range n, ActuarialValuation.poissonCountMass r a) ≤ 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.2.2.1

theorem edgeMass_nonneg :
  ∀ (A : InnerInput) (u v a b : ℕ),
  0 ≤ edgeMass A u v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.2.2.2

theorem edgeMass_rectangle_eq :
  ∀ (A : InnerInput) (u v na nb : ℕ),
  (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b) =
      (∑ a ∈ Finset.range na,
        ActuarialValuation.poissonCountMass (lengthRate A * A.I.length u v) a) *
      (∑ b ∈ Finset.range nb,
        ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.2.1.1

theorem edgeMass_rectangle_nonneg :
  ∀ (A : InnerInput) (u v na nb : ℕ),
  0 ≤ ∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.2.1.2.1

theorem edgeMass_rectangle_le_one :
  ∀ (A : InnerInput) (u v na nb : ℕ),
  (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b) ≤ 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.2.1.2.2

theorem edgeMass_sum_le_one :
  ∀ (A : InnerInput) (u v i j : ℕ),
  (∑ a ∈ Finset.range (tickLimit A - i),
      ∑ b ∈ Finset.range (tickLimit A - j), edgeMass A u v a b) ≤ 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.2.2.1.1

end RSP.PoissonBridge
end

set_option autoImplicit false
section
namespace NearLinearRSP.TwoResources
open scoped BigOperators

theorem standalone_RSP_TableBounds__foldl_invariant :
  ∀ {α β : Type u_1} (f : β → α → β) (P : β → Prop)
    (xs : List α) (b : β) (hb : P b)
    (hf : ∀ b a, P b → P (f b a)),
  P (xs.foldl f b) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).1.1.2.2.1.2.2.2.1.2

theorem putCell_range :
  ∀ (T : Table) (v i j : ℕ) (c : Cell)
    (hT : TableRange T) (hc : 0 ≤ c.value ∧ c.value ≤ 1),
  TableRange (putCell T v i j c) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.2.2.2.1

theorem dpValue_range :
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (v i j : ℕ),
  0 ≤ dpValue A T v i j ∧ dpValue A T v i j ≤ 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.2.2.2.2

theorem edgeExpectation_range :
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (u v i j : ℕ),
  0 ≤ edgeExpectation A T u v i j ∧ edgeExpectation A T u v i j ≤ 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.1.1.1

theorem initLayer_range :
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (i j : ℕ),
  LayerRange (initLayer A T i j) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.1.1.2.1

theorem relaxEdge_range :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerRange S),
  LayerRange (relaxEdge A i j u S e) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.1.1.2.2

theorem popLayer_range :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hS : LayerRange S),
  LayerRange (popLayer A i j S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.1.2.1

theorem buildLayer_range :
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (i j : ℕ),
  TableRange (buildLayer A T i j) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.1.2.2.1

theorem buildTable_range :
  ∀ (A : InnerInput),
  TableRange (buildTable A) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.1.2.2.2

theorem dpValue_buildTable_nonneg :
  ∀ (A : InnerInput) (v i j : ℕ),
  0 ≤ dpValue A (buildTable A) v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.1.1

theorem dpValue_buildTable_le_one :
  ∀ (A : InnerInput) (v i j : ℕ),
  dpValue A (buildTable A) v i j ≤ 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem activeVertices_edge_left :
  ∀ (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges),
  u ∈ activeVertices I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.1.2.2

theorem activeVertices_edge_right :
  ∀ (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges),
  v ∈ activeVertices I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.1.1

@[simp] theorem putCell_same :
  ∀ (T : Table) (v i j : ℕ) (c : Cell),
  putCell T v i j c v i j = c :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.1.2

theorem putCell_other_vertex :
  ∀ (T : Table) (v w i j : ℕ) (c : Cell) (h : w ≠ v),
  putCell T v i j c w i j = T w i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.2.1

theorem putCell_other_layer :
  ∀ (T : Table) (v w i j a b : ℕ) (c : Cell)
    (h : a ≠ i ∨ b ≠ j),
  putCell T v i j c w a b = T w a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.2.2

@[simp] theorem relaxEdge_table :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).table = S.table :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.1.1

@[simp] theorem relaxEdge_queue :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).queue = S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.1.2.1

@[simp] theorem relaxEdge_nextRank :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).nextRank = S.nextRank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.1.2.2

theorem relaxEdge_keys_outside :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hv : v ∉ S.queue),
  (relaxEdge A i j u S e).keys v = S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.2.1.1

theorem relaxEdge_parents_outside :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hv : v ∉ S.queue),
  (relaxEdge A i j u S e).parents v = S.parents v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.2.1.2

theorem relaxEdge_keys_le :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).keys v ≤ S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.2.2.1

theorem standalone_Mission_QueueStructure__fold_preserves :
  ∀ {α β γ : Type u_1} (f : β → α → β) (p : β → γ)
    (hf : ∀ s a, p (f s a) = p s) (xs : List α) (s : β),
  p (xs.foldl f s) = p s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).1.1.2.2.2.2.1.2.2.2

@[simp] theorem relaxAll_table :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).table = S.table :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.1.1

@[simp] theorem relaxAll_queue :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).queue = S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.1.2.1

@[simp] theorem relaxAll_nextRank :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).nextRank = S.nextRank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.1.2.2

theorem relaxAll_keys_outside :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue),
  (relaxAll A i j u S).keys v = S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.2.1.1

theorem relaxAll_parents_outside :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue),
  (relaxAll A i j u S).parents v = S.parents v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.2.1.2

theorem popLayer_queue_length :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState),
  (popLayer A i j S).queue.length = S.queue.length - 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.2.2.1

theorem popLayer_queue_subset :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState),
  (popLayer A i j S).queue ⊆ S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.2.2.2

theorem popLayer_other_layer :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (v a b : ℕ) (h : a ≠ i ∨ b ≠ j),
  (popLayer A i j S).table v a b = S.table v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.1.1.1

@[simp] theorem queueRun_zero :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState),
  queueRun A i j 0 S = S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.1.1.2.1

@[simp] theorem queueRun_succ :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  queueRun A i j (n + 1) S = popLayer A i j (queueRun A i j n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.1.1.2.2

theorem queueRun_queue_length :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  (queueRun A i j n S).queue.length = S.queue.length - n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.1.2.1

theorem queueRun_queue_subset :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  (queueRun A i j n S).queue ⊆ S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.1.2.2.1

theorem queueRun_other_layer :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (v a b : ℕ) (h : a ≠ i ∨ b ≠ j),
  (queueRun A i j n S).table v a b = S.table v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.1.2.2.2

theorem buildLayer_other_layer :
  ∀ (A : InnerInput) (T : Table) (i j v a b : ℕ)
    (h : a ≠ i ∨ b ≠ j),
  buildLayer A T i j v a b = T v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.1.1

theorem buildLayer_queue_exhausted :
  ∀ (A : InnerInput) (T : Table) (i j : ℕ),
  (queueRun A i j (activeVertices A.I).length (initLayer A T i j)).queue = [] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.1.2.1

theorem popLayer_queue_nodup :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (h : S.queue.Nodup),
  (popLayer A i j S).queue.Nodup :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.1.2.2

theorem queueRun_queue_nodup :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (h : S.queue.Nodup),
  (queueRun A i j n S).queue.Nodup :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.2.1.1

theorem popLayer_sync :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (hS : PoppedSync A i j S),
  PoppedSync A i j (popLayer A i j S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.2.1.2

theorem queueRun_sync :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (hS : PoppedSync A i j S),
  PoppedSync A i j (queueRun A i j n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.2.2.1

theorem relaxEdge_zero_key :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerRange S) (hz : S.keys v = 0),
  (relaxEdge A i j u S e).keys v = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.2.2.2

theorem relaxAll_zero_key :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0),
  (relaxAll A i j u S).keys v = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.1.1.1

theorem popLayer_zero_key :
  ∀ (A : InnerInput) (i j v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0),
  (popLayer A i j S).keys v = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.1.1.2.1

theorem queueRun_range :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hS : LayerRange S),
  LayerRange (queueRun A i j n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.1.1.2.2

theorem queueRun_zero_key :
  ∀ (A : InnerInput) (i j n v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0),
  (queueRun A i j n S).keys v = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.1.2.1

theorem buildLayer_source_zero :
  ∀ (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableRange T),
  (buildLayer A T i j A.I.source i j).value = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.1.2.2.1

theorem edgeExpectation_congr :
  ∀ (A : InnerInput) (T U : Table) (u v i j : ℕ)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        dpValue A T u (i + a) (j + b) = dpValue A U u (i + a) (j + b)),
  edgeExpectation A T u v i j = edgeExpectation A U u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.1.2.2.2

theorem edgeExpectation_mono :
  ∀ (A : InnerInput) (T U : Table) (u v i j : ℕ)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        dpValue A T u (i + a) (j + b) ≤ dpValue A U u (i + a) (j + b)),
  edgeExpectation A T u v i j ≤ edgeExpectation A U u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.1.1

theorem edgeExpectation_extensive :
  ∀ (A : InnerInput) (T : Table) (u v i j : ℕ)
    (baseline : ℝ) (hb : baseline ≤ 1)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        baseline ≤ dpValue A T u (i + a) (j + b)),
  baseline ≤ edgeExpectation A T u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.1.2.1

theorem dpValue_congr_at :
  ∀ (A : InnerInput) (T U : Table) (v i j : ℕ)
    (h : T v i j = U v i j),
  dpValue A T v i j = dpValue A U v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.1.2.2

theorem relaxEdge_futureBound :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (relaxEdge A i j u S e) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.2.1.1

theorem relaxAll_keys_le :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState),
  (relaxAll A i j u S).keys v ≤ S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.2.1.2

theorem relaxAll_futureBound :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (relaxAll A i j u S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.2.2.1

theorem popLayer_keys_le :
  ∀ (A : InnerInput) (i j v : ℕ) (S : LayerState),
  (popLayer A i j S).keys v ≤ S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.2.2.2

theorem popLayer_future_dpValue :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (v a b : ℕ) (hab : a ≠ 0 ∨ b ≠ 0),
  dpValue A (popLayer A i j S).table v (i + a) (j + b) =
      dpValue A S.table v (i + a) (j + b) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.1.1.1

theorem popLayer_futureBound :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (popLayer A i j S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.1.1.2.1

theorem queueRun_futureBound :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (queueRun A i j n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.1.1.2.2

theorem settleState_expectation_ge :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hu : u ∈ S.queue)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S) (v : ℕ),
  S.keys u ≤ edgeExpectation A (settleState S i j u).table u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.1.2.1

theorem relaxEdge_keys_ge :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (baseline : ℝ)
    (hkeys : ∀ v ∈ S.queue, baseline ≤ S.keys v)
    (hexpect : ∀ v, baseline ≤ edgeExpectation A S.table u v i j),
  ∀ v ∈ (relaxEdge A i j u S e).queue,
      baseline ≤ (relaxEdge A i j u S e).keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.1.2.2.1

theorem relaxAll_keys_ge :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (baseline : ℝ) (hkeys : ∀ v ∈ S.queue, baseline ≤ S.keys v)
    (hexpect : ∀ v, baseline ≤ edgeExpectation A S.table u v i j),
  ∀ v ∈ (relaxAll A i j u S).queue, baseline ≤ (relaxAll A i j u S).keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.1.2.2.2

theorem pickedVertex_mem :
  ∀ (S : LayerState) (hne : S.queue ≠ []),
  pickedVertex S ∈ S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.1.1

theorem pickedVertex_le :
  ∀ (S : LayerState) (v : ℕ) (hv : v ∈ S.queue),
  S.keys (pickedVertex S) ≤ S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.1.2.1

theorem popLayer_eq_relaxAll :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []),
  popLayer A i j S =
      relaxAll A i j (pickedVertex S) (settleState S i j (pickedVertex S)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.1.2.2

theorem popLayer_keys_ge_picked :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ [])
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S),
  ∀ v ∈ (popLayer A i j S).queue,
      S.keys (pickedVertex S) ≤ (popLayer A i j S).keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.1.1

theorem popLayer_picked_key_mono :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ [])
    (hnext : (popLayer A i j S).queue ≠ [])
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S),
  S.keys (pickedVertex S) ≤ (popLayer A i j S).keys (pickedVertex (popLayer A i j S)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.1.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem pathWeight_cons_cons :
  ∀ (w : ℕ → ℕ → ℝ≥0) (a b : ℕ) (P : List ℕ),
  pathWeight w (a :: b :: P) = (w a b : ℝ) + pathWeight w (b :: P) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.2.1

theorem pathWeight_nonneg :
  ∀ (w : ℕ → ℕ → ℝ≥0) (P : List ℕ),
  0 ≤ pathWeight w P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.2.2

theorem pathWeight_tail_le :
  ∀ (w : ℕ → ℕ → ℝ≥0) (a : ℕ) (P : List ℕ),
  pathWeight w P ≤ pathWeight w (a :: P) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.1.1.1

theorem pathWeight_suffix_le :
  ∀ (w : ℕ → ℕ → ℝ≥0) (pre post : List ℕ),
  pathWeight w post ≤ pathWeight w (pre ++ post) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.1.1.2.1

theorem exists_pathReduction :
  ∀ (P : List ℕ),
  ∃ Q, PathReduction P Q :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.1.1.2.2

theorem isChain_vertices_lt :
  ∀ (G : Digraph) (P : List ℕ)
    (hchain : P.IsChain (fun u v => (u, v) ∈ G.edges))
    (hhead : ∀ v ∈ P.head?, v < G.n),
  ∀ v ∈ P, v < G.n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.1.2.1

theorem IsPath.vertices_lt :
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n),
  ∀ v ∈ P, v < G.n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.1.2.2.1

theorem IsPath.length_le_of_nodup :
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) (hnd : P.Nodup),
  P.length ≤ G.n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.1.2.2.2

theorem IsPath.exists_simple :
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n),
  ∃ Q : List ℕ, IsPath G s t Q ∧ Q.Nodup ∧ Q.length ≤ G.n ∧
      Q ⊆ P ∧ ∀ w : ℕ → ℕ → ℝ≥0, pathWeight w Q ≤ pathWeight w P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.1.1

theorem Feasible.exists_simple :
  ∀ (I : Instance) (t : ℕ) (P : List ℕ)
    (hP : Feasible I t P),
  ∃ Q : List ℕ, Feasible I t Q ∧ Q.Nodup ∧ Q.length ≤ I.graph.n ∧
      pathWeight I.length Q ≤ pathWeight I.length P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.1.2.1

theorem pathWeight_le_length_mul :
  ∀ (G : Digraph) (w : ℕ → ℕ → ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ u v, (u, v) ∈ G.edges → (w u v : ℝ) ≤ M)
    (P : List ℕ) (hP : P.IsChain (fun u v => (u, v) ∈ G.edges)),
  pathWeight w P ≤ (P.length : ℝ) * M :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.1.2.2

theorem IsPath.weight_le_n_mul :
  ∀ (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) (hnd : P.Nodup)
    (w : ℕ → ℕ → ℝ≥0) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ u v, (u, v) ∈ G.edges → (w u v : ℝ) ≤ M),
  pathWeight w P ≤ (G.n : ℝ) * M :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem distanceLess_iff :
  ∀ (x y : Option ℝ),
  distanceLess x y = true ↔ optionDist x < optionDist y :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.2.1.2

theorem standalone_Mission_ShortestTreeStructure__treeFold_mem :
  ∀ (T : ShortestTree) (xs : List ℕ) (P : ℕ → Prop)
    (x : ℕ) (hx : P x) (hall : ∀ y ∈ xs, P y),
  P (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.2.2.1

theorem treePick_mem :
  ∀ (S : TreeQueue) (hne : S.queue ≠ []),
  treePick S ∈ S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.2.2.2.2.2

theorem standalone_Mission_ShortestTreeStructure__treeFold_le_seed :
  ∀ (T : ShortestTree) (xs : List ℕ) (x : ℕ),
  treeDist T (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x) ≤ treeDist T x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.1.1.1

theorem standalone_Mission_ShortestTreeStructure__treeFold_le_mem :
  ∀ (T : ShortestTree) (xs : List ℕ) (x y : ℕ)
    (hy : y ∈ xs),
  treeDist T (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x) ≤ treeDist T y :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.1.1.2.1

theorem treePick_le :
  ∀ (S : TreeQueue) (v : ℕ) (hv : v ∈ S.queue),
  treeDist S.tree (treePick S) ≤ treeDist S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.1.1.2.2

@[simp] theorem treeRelax_queue :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ),
  (treeRelax I allow w u S e).queue = S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.1.2.1

@[simp] theorem treeRelax_rank :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ),
  (treeRelax I allow w u S e).rank = S.rank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.1.2.2.1

theorem treeRelax_outside :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (hv : v ∉ S.queue),
  (treeRelax I allow w u S e).tree v = S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.1.2.2.2

theorem treeRelax_dist_le :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (e : ℕ × ℕ),
  treeDist (treeRelax I allow w u S e).tree v ≤ treeDist S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.2.1.1

theorem standalone_Mission_ShortestTreeStructure__treeFold_preserves :
  ∀ {α β γ : Type u_1} (f : β → α → β) (p : β → γ)
    (hf : ∀ s a, p (f s a) = p s) (xs : List α) (s : β),
  p (xs.foldl f s) = p s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).1.2.1.2.1.1.2.1.2.1

@[simp] theorem treeRelaxAll_queue :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue),
  (treeRelaxAll I allow w u S).queue = S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.2.1.2.2

@[simp] theorem treeRelaxAll_rank :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue),
  (treeRelaxAll I allow w u S).rank = S.rank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.2.2.1.1

theorem treeRelaxFold_outside :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ))
    (hv : v ∉ S.queue),
  (es.foldl (treeRelax I allow w u) S).tree v = S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.2.2.1.2

theorem treeRelaxAll_outside :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (hv : v ∉ S.queue),
  (treeRelaxAll I allow w u S).tree v = S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.2.2.2.1

theorem treeRelaxFold_dist_le :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ)),
  treeDist (es.foldl (treeRelax I allow w u) S).tree v ≤ treeDist S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.1.2.2.2.2

theorem treeRelaxAll_dist_le :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue),
  treeDist (treeRelaxAll I allow w u S).tree v ≤ treeDist S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.1.1.1

@[simp] theorem treeSettle_dist :
  ∀ (S : TreeQueue) (u v : ℕ),
  treeDist (treeSettle S u).tree v = treeDist S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.1.1.2.1

theorem treePop_eq_relaxAll :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []),
  treePop I allow w S = treeRelaxAll I allow w (treePick S) (treeSettle S (treePick S)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.1.1.2.2

theorem treePop_queue_length :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue),
  (treePop I allow w S).queue.length = S.queue.length - 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.1.2.1

theorem treePop_queue_subset :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue),
  (treePop I allow w S).queue ⊆ S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.1.2.2.1

theorem treePop_queue_nodup :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hS : S.queue.Nodup),
  (treePop I allow w S).queue.Nodup :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.1.2.2.2

@[simp] theorem treeRun_zero :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue),
  treeRun I allow w 0 S = S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.1.1

theorem treeRun_succ :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue),
  treeRun I allow w (n + 1) S = treePop I allow w (treeRun I allow w n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.1.2.1

theorem treeRun_queue_length :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue),
  (treeRun I allow w n S).queue.length = S.queue.length - n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.1.2.2

theorem treeRun_queue_nodup :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (hS : S.queue.Nodup),
  (treeRun I allow w n S).queue.Nodup :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.2.1.1

theorem shortestTree_eq_treeRun :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ),
  shortestTree I allow w = (treeRun I allow w (activeVertices I).length (treeInitial I)).tree :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.2.1.2

theorem shortestTree_queue_exhausted :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ),
  (treeRun I allow w (activeVertices I).length (treeInitial I)).queue = [] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.2.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem treeInitial_policy :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ),
  TreePolicy I allow w (treeInitial I) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.2.2.2

theorem treeSettle_policy :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (u : ℕ) (hu : u ∈ S.queue)
    (h : TreePolicy I allow w S),
  TreePolicy I allow w (treeSettle S u) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.1.1.1

theorem treeRelax_policy :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : e ∈ I.graph.edges) (hu : u ∉ S.queue)
    (hur : (S.tree u).rank < S.rank) (h : TreePolicy I allow w S),
  TreePolicy I allow w (treeRelax I allow w u S e) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.1.1.2.1

theorem treeRelaxFold_policy :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ))
    (hes : ∀ e ∈ es, e ∈ I.graph.edges) (hu : u ∉ S.queue)
    (hur : (S.tree u).rank < S.rank) (h : TreePolicy I allow w S),
  TreePolicy I allow w (es.foldl (treeRelax I allow w u) S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.1.1.2.2

theorem treePop_policy :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hdup : S.queue.Nodup)
    (h : TreePolicy I allow w S),
  TreePolicy I allow w (treePop I allow w S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.1.2.1

theorem treeRun_policy :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (hdup : S.queue.Nodup)
    (h : TreePolicy I allow w S),
  TreePolicy I allow w (treeRun I allow w n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.1.2.2.1

theorem shortestTree_finite_rank :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d),
  (shortestTree I allow w v).rank < (activeVertices I).length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.1.2.2.2

theorem shortestTree_finite_parent :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ) (hv : v ≠ I.source)
    (hd : (shortestTree I allow w v).distance = some d),
  ∃ u a, (shortestTree I allow w v).parent = some u ∧
      (shortestTree I allow w u).distance = some a ∧ d = a + w u v ∧
      (u,v) ∈ I.graph.edges ∧ allow u v = true ∧
      (shortestTree I allow w u).rank < (shortestTree I allow w v).rank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem treePop_dist_le :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (v : ℕ),
  treeDist (treePop I allow w S).tree v ≤ treeDist S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.1.2.1

theorem treePop_outside :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (v : ℕ) (hv : v ∉ S.queue),
  (treePop I allow w S).tree v = S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.1.2.2

theorem treePop_dist_picked :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ [])
    (hdup : S.queue.Nodup),
  treeDist (treePop I allow w S).tree (treePick S) = treeDist S.tree (treePick S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.2.1.1

theorem treeRelax_dist_ge :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (baseline : WithTop ℝ) (hkeys : ∀ v ∈ S.queue, baseline ≤ treeDist S.tree v)
    (hu : baseline ≤ treeDist S.tree u) (hw : 0 ≤ w e.1 e.2),
  ∀ v ∈ (treeRelax I allow w u S e).queue,
      baseline ≤ treeDist (treeRelax I allow w u S e).tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.2.1.2

theorem treeRelaxFold_dist_ge :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (es : List (ℕ × ℕ)) (baseline : WithTop ℝ)
    (hkeys : ∀ v ∈ S.queue, baseline ≤ treeDist S.tree v)
    (hu : baseline ≤ treeDist S.tree u) (huq : u ∉ S.queue),
  ∀ v ∈ (es.foldl (treeRelax I allow w u) S).queue,
      baseline ≤ treeDist (es.foldl (treeRelax I allow w u) S).tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.2.2.1

theorem treePop_dist_ge_picked :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hne : S.queue ≠ []) (hdup : S.queue.Nodup),
  ∀ v ∈ (treePop I allow w S).queue,
      treeDist S.tree (treePick S) ≤ treeDist (treePop I allow w S).tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.2.2.2

theorem treeRelax_edge_bound :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue)
    (huv : u ≠ v) (hv : v ∈ S.queue) (ha : allow u v = true),
  treeDist (treeRelax I allow w u S (u,v)).tree v ≤
      treeDist S.tree u + (w u v : WithTop ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.1.1.1

theorem treeRelaxAll_edge_bound :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue)
    (huv : u ≠ v) (hv : v ∈ S.queue) (hu : u ∉ S.queue)
    (ha : allow u v = true) (hedge : (u,v) ∈ I.graph.edges),
  treeDist (treeRelaxAll I allow w u S).tree v ≤
      treeDist S.tree u + (w u v : WithTop ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.1.1.2.1

theorem treePop_separation :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S),
  TreeSeparation I (treePop I allow w S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.1.1.2.2

theorem treePop_bellman :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S)
    (hbell : TreeBellman I allow w S),
  TreeBellman I allow w (treePop I allow w S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.1.2.1.1

theorem treeRun_bellman_separation :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (n : ℕ) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S) (hbell : TreeBellman I allow w S),
  TreeSeparation I (treeRun I allow w n S) ∧ TreeBellman I allow w (treeRun I allow w n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.1.2.1.2

theorem shortestTree_bellman :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u v : ℕ)
    (he : (u,v) ∈ I.graph.edges) (ha : allow u v = true),
  treeDist (shortestTree I allow w) v ≤
      treeDist (shortestTree I allow w) u + (w u v : WithTop ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.1.2.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem treeRelax_dist_nonneg :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v) (e : ℕ × ℕ),
  ∀ v, 0 ≤ treeDist (treeRelax I allow w u S e).tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.1.2.2.2

theorem treeRelaxAll_dist_nonneg :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v),
  ∀ v, 0 ≤ treeDist (treeRelaxAll I allow w u S).tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.2.1.1

theorem treePop_dist_nonneg :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v),
  ∀ v, 0 ≤ treeDist (treePop I allow w S).tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.2.1.2.1

theorem treeRun_dist_nonneg :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (n : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v),
  ∀ v, 0 ≤ treeDist (treeRun I allow w n S).tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.2.1.2.2

theorem treeRun_dist_le :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (v : ℕ),
  treeDist (treeRun I allow w n S).tree v ≤ treeDist S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.2.2.1.1

theorem shortestTree_dist_nonneg :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (v : ℕ),
  0 ≤ treeDist (shortestTree I allow w) v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.2.2.1.2

theorem shortestTree_source_zero :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v),
  (shortestTree I allow w I.source).distance = some 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.2.2.2.1

theorem shortestTree_distance_nonneg :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d),
  0 ≤ d :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.2.2.2.2.2

theorem treeDist_chain_bound :
  ∀ (I : Instance) (T : ShortestTree)
    (allow : ℕ → ℕ → Bool) (w : ℕ → ℕ → ℝ≥0)
    (hbell : ∀ u v, (u,v) ∈ I.graph.edges → allow u v = true →
      treeDist T v ≤ treeDist T u + ((w u v : ℝ) : WithTop ℝ))
    (P : List ℕ) (s t : ℕ) (hp : IsPath I.graph s t P)
    (ha : P.IsChain (fun u v => allow u v = true)),
  treeDist T t ≤ treeDist T s + ((pathWeight w P : ℝ) : WithTop ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.1.1.1

theorem shortestTree_path_bound :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P)
    (ha : P.IsChain (fun u v => allow u v = true)),
  ∃ d : ℝ, (shortestTree I allow (fun u v => w u v) t).distance = some d ∧
      d ≤ pathWeight w P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.1.1.2.1

theorem pathWeight_zero_chain :
  ∀ (w : ℕ → ℕ → ℝ≥0) (P : List ℕ)
    (h : pathWeight w P = 0),
  P.IsChain (fun u v => w u v = 0) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.1.1.2.2

theorem zeroLengthTree_path_bound :
  ∀ (I : Instance) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P) (hz : pathWeight I.length P = 0),
  ∃ d : ℝ, (zeroLengthTree I t).distance = some d ∧ d ≤ pathWeight I.cost P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.1.2.1

theorem zeroBudgetTree_path_bound :
  ∀ (I : Instance) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P) (hz : pathWeight I.cost P = 0),
  ∃ d : ℝ, (zeroBudgetTree I t).distance = some d ∧ d ≤ pathWeight I.length P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.1.2.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem activeVertices_length_le_edges :
  ∀ (I : Instance),
  (activeVertices I).length ≤ 2 * I.graph.edges.length + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.1.2.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem edgeWeightSum_nonneg :
  ∀ (I : Instance) (w : ℕ → ℕ → ℝ≥0),
  0 ≤ edgeWeightSum I w :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.2.1.1

theorem weight_le_edgeWeightSum :
  ∀ (I : Instance) (w : ℕ → ℕ → ℝ≥0) (u v : ℕ)
    (he : (u,v) ∈ I.graph.edges),
  (w u v : ℝ) ≤ edgeWeightSum I w :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.2.1.2.1

theorem treePolicy_distance_bound :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (h : TreePolicy I allow w S)
    (hs : (S.tree I.source).distance = some 0) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ u v, (u,v) ∈ I.graph.edges → w u v ≤ W)
    (v : ℕ) (d : ℝ) (hd : (S.tree v).distance = some d),
  d ≤ (S.rank : ℝ) * W :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.2.1.2.2

theorem treeRun_source_zero :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (k : ℕ),
  ((treeRun I allow w k (treeInitial I)).tree I.source).distance = some 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.2.2.1.1

theorem treeRun_sentinel_bound :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (k v : ℕ) (d : ℝ)
    (hd : ((treeRun I allow (fun u v => (w u v : ℝ)) k (treeInitial I)).tree v).distance = some d),
  d < ((I.graph.n : ℝ) + 1) * (1 + edgeWeightSum I w) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.2.2.1.2

theorem distanceLess_eq_sentinel :
  ∀ (top : ℝ) (x y : Option ℝ)
    (hx : ∀ d, x = some d → d < top) (hy : ∀ d, y = some d → d < top),
  distanceLess x y = decide (x.getD top < y.getD top) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.2.2.2.1

theorem treePick_eq_sentinel_firstMin :
  ∀ (top : ℝ) (S : TreeQueue)
    (hfinite : ∀ v d, (S.tree v).distance = some d → d < top),
  treePick S = firstMin (sentinelKey top S.tree) S.queue 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.1.2.2.2.2

theorem treeRun_pick_sentinel :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (k : ℕ),
  let S := treeRun I allow (fun u v => (w u v : ℝ)) k (treeInitial I)
  treePick S = firstMin
    (sentinelKey (((I.graph.n : ℝ)+1)*(1+edgeWeightSum I w)) S.tree) S.queue 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.1.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

theorem activeLeaf_at :
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ)
    (hk : k<xs.length),
  activeLeaf xs q key B (B+k) =
      ⟨if slotVertex xs k∈q then k+1 else 0,key (slotVertex xs k)⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.1.1.2.1

theorem activeLeaf_outside :
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B node : ℕ)
    (h : node<B ∨ B+xs.length≤node),
  activeLeaf xs q key B node=⟨0,0⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.1.1.2.2

theorem slotVertex_injective :
  ∀ (xs : List ℕ) (hxs : xs.Nodup) (i j : ℕ)
    (hi : i<xs.length) (hj : j<xs.length),
  slotVertex xs i=slotVertex xs j ↔ i=j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.1.2.1

theorem slotVertex_idxOf :
  ∀ (xs : List ℕ) (hxs : xs.Nodup) (k : ℕ) (hk : k<xs.length),
  xs.idxOf (slotVertex xs k)=k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.1.2.2.1

theorem activeLeaf_single_change :
  ∀ (xs q q' : List ℕ) (key key' : ℕ → ℝ)
    (B k : ℕ) (hxs : xs.Nodup) (hk : k<xs.length)
    (hkey : ∀ v, v≠slotVertex xs k → key' v=key v)
    (hq : ∀ v, v≠slotVertex xs k → (v∈q' ↔ v∈q)),
  activeLeaf xs q' key' B = Function.update (activeLeaf xs q key B) (B+k)
      ⟨if slotVertex xs k∈q' then k+1 else 0,key' (slotVertex xs k)⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.1.2.2.2

theorem activeLeaf_delete :
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ)
    (hxs : xs.Nodup) (hq : q.Nodup) (hk : k<xs.length),
  activeLeaf xs (q.erase (slotVertex xs k)) key B =
      Function.update (activeLeaf xs q key B) (B+k) ⟨0,key (slotVertex xs k)⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.1.1

theorem activeLeaf_update_key :
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ) (value : ℝ)
    (hxs : xs.Nodup) (hk : k<xs.length) (hq : slotVertex xs k∈q),
  activeLeaf xs q (Function.update key (slotVertex xs k) value) B =
      Function.update (activeLeaf xs q key B) (B+k) ⟨k+1,value⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.1.2.1

theorem slotVertex_idxOf_eq :
  ∀ (xs : List ℕ) (u : ℕ) (hu : u∈xs),
  slotVertex xs (xs.idxOf u)=u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.1.2.2

theorem activeLeaf_delete_vertex :
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (B u : ℕ)
    (hxs : xs.Nodup) (hq : q.Nodup) (hu : u∈xs),
  activeLeaf xs (q.erase u) key B =
      Function.update (activeLeaf xs q key B) (B+xs.idxOf u) ⟨0,key u⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.2.1.1

theorem activeLeaf_update_vertex :
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (B u : ℕ) (value : ℝ)
    (hxs : xs.Nodup) (hu : u∈xs) (huq : u∈q),
  activeLeaf xs q (Function.update key u value) B =
      Function.update (activeLeaf xs q key B) (B+xs.idxOf u) ⟨xs.idxOf u+1,value⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.2.1.2

theorem standalone_Mission_QueueLeaves__getD_map_range :
  ∀ (xs : List ℕ),
  (List.range xs.length).map (slotVertex xs)=xs :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.2.2.1

theorem standalone_Mission_QueueLeaves__filterMap_live :
  ∀ (xs q : List ℕ) (f : ℕ→Record),
  xs.filterMap (fun v=>if v∈q then some (f v) else none) =
      (xs.filter (fun v=>decide (v∈q))).map f :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.2.2.2

theorem filter_sublist_members :
  ∀ (xs q : List ℕ) (hxs : xs.Nodup) (hq : q.Sublist xs),
  xs.filter (fun v=>decide (v∈q))=q :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.1.1.1

theorem activeLeaf_records :
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (B : ℕ)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length≤B),
  leafRecords (activeLeaf xs q key B) B B = q.map (vertexRecord xs key) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.1.1.2.1

theorem activeLeaf_firstMin :
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (height : ℕ)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length≤2^height)
    (fallback : ℕ) (hne : q≠[]),
  (heapTruth (2^height) (activeLeaf xs q key (2^height)) 1).decode =
      some (vertexRecord xs key (firstMin key q fallback)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.1.1.2.2

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

theorem popLayer_queue_sublist :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState),
  (popLayer A i j S).queue.Sublist S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.1.2.1

theorem queueRun_queue_sublist :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  (queueRun A i j n S).queue.Sublist S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.1.2.2.1

theorem treePop_queue_sublist :
  ∀ (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ) (S : TreeQueue),
  (treePop I allow w S).queue.Sublist S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.1.2.2.2

theorem treeRun_queue_sublist :
  ∀ (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ) (n : ℕ) (S : TreeQueue),
  (treeRun I allow w n S).queue.Sublist S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

theorem initPrefix_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input initPrefix s = prefixed s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.2.1.2.1

theorem initPair_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input initPair s = paired s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.2.1.2.2

theorem empty_coherent :
  ∀ (capacity : ℕ),
  Coherent capacity (fun _ => (⟨0, 0⟩ : Record)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.2.2.1.1

theorem prefixed_inv :
  ∀ (W P B : ℕ) (s : Store) (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1),
  InitInv W P B (B - 1) (prefixed s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.2.2.1.2

theorem paired_inv :
  ∀ (W P B k : ℕ) (s : Store) (hspace : W + 2 * B ≤ P)
    (hk : 0 < k) (hkB : k < B) (h : InitInv W P B k s),
  InitInv W P B (k - 1) (paired s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.2.2.2.1

theorem initLoop_run :
  ∀ (input : RAMInput) (W P B k : ℕ) (s : Store)
    (hspace : W + 2 * B ≤ P) (hkB : k < B) (h : InitInv W P B k s),
  ∃ out, Run input (.loop (.nat .lt 3 0) (atoms initPair)) s out (15 * k + 1) ∧
      InitInv W P B 0 out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.2.2.2.2

theorem initializeEmpty_correct :
  ∀ (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1),
  ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      out.nr 0 = 0 ∧ out.nr 1 = W ∧ out.nr 2 = P ∧ out.nr 3 = 0 ∧ out.nr 4 = 1 ∧
      ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, readRecord out (W + v) = ⟨0, 0⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.1.1.1

theorem InitFrame.refl :
  ∀ (W P B : ℕ) (s : Store),
  InitFrame W P B s s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.1.1.2.1

theorem InitFrame.trans :
  ∀ (W P B : ℕ) (s u t : Store)
    (h : InitFrame W P B s u) (h' : InitFrame W P B u t),
  InitFrame W P B s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.1.1.2.2

theorem prefixed_frame :
  ∀ (W P B : ℕ) (s : Store) (hB : 0 < B)
    (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h4 : s.nr 4 = 1),
  InitFrame W P B s (prefixed s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.1.2.1.1

theorem paired_frame :
  ∀ (W P B k : ℕ) (s : Store) (hkB : k < B)
    (h0 : s.nr 0 = k) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h4 : s.nr 4 = 1),
  InitFrame W P B s (paired s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.1.2.1.2

theorem initLoop_run_framed :
  ∀ (input : RAMInput) (W P B k : ℕ) (s : Store)
    (hspace : W + 2 * B ≤ P) (hkB : k < B) (h : InitInv W P B k s),
  ∃ out, Run input (.loop (.nat .lt 3 0) (atoms initPair)) s out (15 * k + 1) ∧
      InitInv W P B 0 out ∧ InitFrame W P B s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.1.2.2.1

theorem initializeEmpty_framed :
  ∀ (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1),
  ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      InitInv W P B 0 out ∧ InitFrame W P B s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.1.2.2.2

theorem updateLeaf_refines :
  ∀ (input : RAMInput) (B : ℕ) (leaf : ℕ → Record) (s : Store)
    (hparent : ParentLayout (2 * B) s) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hleaf : B ≤ s.nr 0)
    (hrep : Represents B (s.nr 1) leaf s),
  ∃ out k, Run input updateLeaf s out k ∧ k ≤ 19 * Nat.clog 2 (2 * B) + 6 ∧
      out.nr 0 = 0 ∧ (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout (2 * B) out ∧
      Represents B (s.nr 1) (Function.update leaf (s.nr 0) ⟨s.nr 10, s.rr 2⟩) out ∧
      WinnerFrame (s.nr 1) (2 * B) s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.2.1.1

theorem initializeEmpty_represents :
  ∀ (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1),
  ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      InitInv W P B 0 out ∧ Represents B W (fun _ => ⟨0, 0⟩) out ∧ InitFrame W P B s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.2.1.2.1

theorem represented_root_firstMin :
  ∀ (h W : ℕ) (leaf : ℕ → Record) (s : Store)
    (hrep : Represents (2 ^ h) W leaf s) (xs : List ℕ) (encode : ℕ → Record)
    (hslots : leafRecords leaf (2 ^ h) (2 ^ h) = xs.map encode)
    (fallback : ℕ) (hne : xs ≠ []),
  (readRecord s (W + 1)).decode =
      some (encode (firstMin (fun v => (encode v).key) xs fallback)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.2.1.2.2

theorem prefixLeaf_zero :
  ∀ (B : ℕ) (key : ℕ → ℝ),
  prefixLeaf B key 0 = fun _ => ⟨0, 0⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.2.2.1.1

theorem prefixLeaf_succ :
  ∀ (B k : ℕ) (key : ℕ → ℝ),
  Function.update (prefixLeaf B key k) (B + k) ⟨k + 1, key k⟩ = prefixLeaf B key (k + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.2.2.1.2

theorem buildSetup_eval :
  ∀ (input : RAMInput) (s : Store),
  Queue.evalAtoms input buildSetup s = buildSetupState s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.2.2.2.1

theorem prepareInsert_eval :
  ∀ (input : RAMInput) (s : Store),
  Queue.evalAtoms input prepareInsert s = preparedInsert s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.2.2.2.2

theorem insertIncrement_eval :
  ∀ (input : RAMInput) (s : Store),
  insertIncrement.eval input s = inserted s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.1.1.1

theorem initializeEmpty_high_register :
  ∀ {input : RAMInput} {s t : Store} {k r : ℕ}
    (h : Run input initializeEmpty s t k) (hr : 10 ≤ r),
  t.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.1.1.2.1

theorem updateLeaf_high_register :
  ∀ {input : RAMInput} {s t : Store} {k r : ℕ}
    (h : Run input updateLeaf s t k) (hr : 10 ≤ r),
  t.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.1.1.2.2

theorem WinnerFrame.initFrame :
  ∀ (W P B : ℕ) (s t : Store)
    (h : WinnerFrame W (2 * B) s t),
  InitFrame W P B s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.1.2.1

theorem insertBody_run :
  ∀ (input : RAMInput) (B N W P R k : ℕ) (initial s : Store)
    (hB : 0 < B) (hN : N ≤ B) (hk : k < N)
    (hkeys : ∀ i < N, R + i < W ∨ W + 2 * B ≤ R + i)
    (h : BuildInv B N W P R initial k s),
  ∃ out cost, Run input insertBody s out cost ∧ BuildInv B N W P R initial (k + 1) out ∧
      cost ≤ 19 * Nat.clog 2 (2 * B) + 11 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.1.2.2.1

theorem buildQueue_run :
  ∀ (input : RAMInput) (B N W P R : ℕ) (s : Store)
    (hB : 0 < B) (hN : N ≤ B) (hspace : W + 2 * B ≤ P)
    (hkeys : ∀ i < N, R + i < W ∨ W + 2 * B ≤ R + i)
    (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1)
    (h11 : s.nr 11 = B) (h12 : s.nr 12 = N) (h13 : s.nr 13 = R),
  ∃ out cost, Run input buildQueue s out cost ∧ BuildInv B N W P R s N out ∧
      cost ≤ 15 * B + (19 * Nat.clog 2 (2 * B) + 13) * N + 3 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.1.2.2.2

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

theorem activeLeaf_initial :
  ∀ (xs : List ℕ) (key : ℕ → ℝ) (B : ℕ),
  activeLeaf xs xs key B =
      prefixLeaf B (fun k => key (slotVertex xs k)) xs.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.1.1

theorem prefixLeaf_records :
  ∀ (B N : ℕ) (key : ℕ → ℝ) (hN : N ≤ B),
  leafRecords (prefixLeaf B key N) B B =
      (List.range N).map (fun k => (⟨k+1,key k⟩ : Record)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.1.2.1

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem seed_prefixLeaf :
  ∀ (xs : List ℕ) (A R source off B : ℕ) (top : ℝ) (s : Store)
    (h : TreeSeedInv xs A R source off top xs.length s),
  Queue.prefixLeaf B (fun k => s.rm (R+k)) xs.length =
      Queue.activeLeaf xs xs (fun v => if v=source then 0 else top) B :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.1.2.2

theorem treeInitializeQueue_run :
  ∀ (input : RAMInput) (xs : List ℕ)
    (A R source off B W P : ℕ) (top : ℝ) (s : Store)
    (hB : 0 < B) (hfit : xs.length ≤ B) (hWP : W+2*B ≤ P) (hPR : P+2*B ≤ R)
    (hAW : A+xs.length ≤ W)
    (hW : s.nr 1 = W) (hP : s.nr 2 = P) (hz : s.nr 3 = 0) (hone : s.nr 4 = 1)
    (hcapacity : s.nr 11 = B) (hlen : s.nr 12 = xs.length)
    (hA : s.nr 171 = A) (hR : s.nr 13 = R) (hsource : s.nr 123 = source)
    (hoff : s.nr 173 = off) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A+j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A),
  ∃ out steps, Run input treeInitializeQueue s out steps ∧
      steps ≤ 15*B + (19*Nat.clog 2 (2*B)+31)*xs.length + 5 ∧
      TreeSeedInv xs A R source off top xs.length out ∧
      Queue.ParentLayout (2*B) out ∧
      Queue.Represents B W
        (Queue.activeLeaf xs xs (fun v => if v=source then 0 else top) B) out ∧
      (∀ a, (∀ v ∈ xs, a ≠ targetAddress v + off) →
        (a < R ∨ R+xs.length ≤ a) →
        (a < W ∨ W+2*B ≤ a) → (a < P ∨ P+2*B ≤ a) →
        out.nm a = s.nm a ∧ out.rm a = s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.2.1.1

theorem activeProbe_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input activeProbe s = activeProbed s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.2.1.2

theorem activeAppend_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input activeAppend s = activeAppended s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.2.2.1

theorem activeInsert_run :
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 125 = 0),
  ∃ steps ≤ 8, Run input activeInsert s (activeResult s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.2.2.2

theorem activeResult_frame_register :
  ∀ (s : Store) (r : ℕ)
    (h143 : r ≠ 143) (h144 : r ≠ 144) (h145 : r ≠ 145) (h146 : r ≠ 146),
  (activeResult s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.1.1.1

theorem activeResult_frame_memory :
  ∀ (s : Store) (a : ℕ)
    (hflag : a ≠ s.nr 141 + s.nr 140) (hlist : a ≠ s.nr 142 + s.nr 143),
  (activeResult s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.1.1.2.1

theorem activeResult_frame_reals :
  ∀ (s : Store),
  (activeResult s).rr = s.rr ∧ (activeResult s).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.1.1.2.2

theorem activeResult_present :
  ∀ (s : Store) (hm : s.nm (s.nr 141 + s.nr 140) ≠ 0),
  (activeResult s).nm = s.nm ∧ (activeResult s).nr 143 = s.nr 143 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.1.2.1

theorem activeResult_absent :
  ∀ (s : Store) (hm : s.nm (s.nr 141 + s.nr 140) = 0)
    (hone : s.nr 126 = 1)
    (hsep : s.nr 141 + s.nr 140 ≠ s.nr 142 + s.nr 143),
  (activeResult s).nr 143 = s.nr 143 + 1 ∧
    (activeResult s).nm (s.nr 141 + s.nr 140) = s.nr 143 + 1 ∧
    (activeResult s).nm (s.nr 142 + s.nr 143) = s.nr 140 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.1.2.2.1

theorem active_regions_disjoint :
  ∀ (base n v count : ℕ) (hv : v < n),
  base + v ≠ (base + 2 * n) + count :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.1.2.2.2

theorem stableInsert_mem :
  ∀ (xs : List ℕ) (v x : ℕ),
  x ∈ stableInsert xs v ↔ x ∈ xs ∨ x = v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.1.1

theorem stableInsert_nodup :
  ∀ (xs : List ℕ) (v : ℕ) (hx : xs.Nodup),
  (stableInsert xs v).Nodup :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.1.2.1

theorem standalone_Mission_RAMActiveList__stableFold_loop :
  ∀ (xs acc : List ℕ),
  xs.foldl stableInsert acc.reverse = List.eraseDupsBy.loop (· == ·) xs acc :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.1.2.2

theorem stableFold_eq_eraseDups :
  ∀ (xs : List ℕ),
  xs.foldl stableInsert [] = xs.eraseDups :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.2.1.1

theorem activeVertices_eq_stableFold :
  ∀ (I : Instance),
  activeVertices I = (I.source :: I.graph.edges.flatMap (fun e => [e.1,e.2])).foldl
      stableInsert [] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.2.1.2

theorem ActiveRep.flag_zero_iff :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v < n),
  s.nm (base + v) = 0 ↔ v ∉ xs :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.2.2.1

theorem ActiveRep.empty :
  ∀ (n base array : ℕ) (s : Store)
    (hb : s.nr 141 = base) (ha : s.nr 142 = array) (hc : s.nr 143 = 0)
    (hsep : base + n ≤ array) (hz : ∀ v < n, s.nm (base + v) = 0),
  ActiveRep n base array [] s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.2.2.2

theorem ActiveRep.insert :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (hv : s.nr 140 < n) (hone : s.nr 126 = 1),
  ActiveRep n base array (stableInsert xs (s.nr 140)) (activeResult s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.1.1

theorem ActiveRep.indexOf :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs),
  s.nm (base + v) = xs.idxOf v + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.1.2.1

theorem ActiveRep.index_bounds :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs),
  0 < s.nm (base + v) ∧ s.nm (base + v) ≤ xs.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.1.2.2

theorem ActiveRep.inverse :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs),
  s.nm (array + (s.nm (base + v) - 1)) = v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.2.1

theorem ActiveRep.vertex_at :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (k : ℕ) (hk : k < xs.length),
  s.nm (array + k) = xs[k]?.getD 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.2.2.1

theorem ActiveRep.length_le :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s),
  xs.length ≤ n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.2.2.2

theorem ActiveRep.congr :
  ∀ {n base array : ℕ} {xs : List ℕ} {s t : Store}
    (h : ActiveRep n base array xs s)
    (hb : t.nr 141 = s.nr 141) (ha : t.nr 142 = s.nr 142) (hc : t.nr 143 = s.nr 143)
    (hmap : ∀ v < n, t.nm (base + v) = s.nm (base + v))
    (harray : ∀ k < xs.length, t.nm (array + k) = s.nm (array + k)),
  ActiveRep n base array xs t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.1.1

theorem TreeMode.weight_nonneg :
  ∀ (mode : TreeMode) (I : Instance) (u v : ℕ),
  0 ≤ mode.weight I u v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.1.2.1

theorem TreeMode.top_pos :
  ∀ (mode : TreeMode) (I : Instance),
  0 < mode.top I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.1.2.2

theorem TreeMode.offset_lt_four :
  ∀ (mode : TreeMode),
  mode.offset < 4 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.2.1.1

theorem TreeAllocation.capacity_pos :
  ∀ {I : Instance} (E : TreeAllocation I),
  0 < E.B :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.2.1.2

theorem TreeAllocation.target_lt_map :
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (v : ℕ) (hv : v < I.graph.n),
  targetAddress v + mode.offset < E.map :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.2.2.1

theorem TreeAllocation.map_le_array :
  ∀ {I : Instance} (E : TreeAllocation I),
  E.map ≤ E.array :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.2.2.2

theorem TreeAllocation.array_end_le_winner :
  ∀ {I : Instance} (E : TreeAllocation I),
  E.array + I.graph.n ≤ E.W :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.1.1.1

theorem TreeAllocation.target_lt_winner :
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (v : ℕ) (hv : v < I.graph.n),
  targetAddress v + mode.offset < E.W :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.1.1.2.1

theorem TreeRegisters.transfer :
  ∀ {I : Instance} {B W P R map array heads links off mode : ℕ}
    {top : ℝ} {s t : Store} (h : TreeRegisters I B W P R map array heads links off mode top s)
    (hn : ∀ r ∈ treeNatConstants, t.nr r = s.nr r) (hr : t.rr 170 = s.rr 170),
  TreeRegisters I B W P R map array heads links off mode top t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.1.1.2.2

theorem TreeRegisters.after_run :
  ∀ {I : Instance} {B W P R map array heads links off mode : ℕ}
    {top : ℝ} {s t : Store} (h : TreeRegisters I B W P R map array heads links off mode top s)
    {input : RAMInput} {cmd : Cmd} {steps : ℕ} (hrun : Run input cmd s t steps)
    (hn : Disjoint treeNatConstants cmd.natWrites) (hr : 170 ∉ cmd.realWrites),
  TreeRegisters I B W P R map array heads links off mode top t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.1.2.1.1

theorem treeInitializeQueue_rep :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s : Store) (hr : E.Registers mode s)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s),
  ∃ out steps, Run input treeInitializeQueue s out steps ∧
      E.Registers mode out ∧ E.Memory mode (treeInitial I) out ∧
      steps ≤ 15*E.B + (19*Nat.clog 2 (2*E.B)+31)*(activeVertices I).length + 5 ∧
      (∀ a, (∀ v ∈ activeVertices I, a ≠ targetAddress v + mode.offset) →
        (a < E.R ∨ E.R+(activeVertices I).length ≤ a) →
        (a < E.W ∨ E.W+2*E.B ≤ a) → (a < E.P ∨ E.P+2*E.B ≤ a) →
        out.nm a = s.nm a ∧ out.rm a = s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.1.2.1.2

theorem treeExtractAtoms_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeExtractAtoms s = treeExtractPrepared s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.1.2.2.1

theorem treeExtractPrepared_values :
  ∀ (s : Store) (hone : s.nr 4 = 1),
  (treeExtractPrepared s).nr 0 = s.nr 170 + (s.nm (s.nr 1 + 1) - 1) ∧
    (treeExtractPrepared s).nr 10 = 0 ∧
    (treeExtractPrepared s).nr 260 = s.nm (s.nr 1 + 1) ∧
    (treeExtractPrepared s).nr 261 = s.nm (s.nr 1 + 1) - 1 ∧
    (treeExtractPrepared s).nr 262 = s.nm (s.nr 171 + (s.nm (s.nr 1 + 1) - 1)) ∧
    (treeExtractPrepared s).rr 260 = s.rm (s.nr 1 + 1) ∧
    (treeExtractPrepared s).rr 2 = s.rm (s.nr 1 + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.1.2.2.2

theorem treeExtractPrepared_header :
  ∀ (s : Store) (r : ℕ) (hr : 0 < r) (hr' : r < 5),
  (treeExtractPrepared s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.2.1.1

theorem standalone_Mission_RAMTreeExtract__updateLeaf_nat_frame :
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input Queue.updateLeaf s out steps) (hr : 11 ≤ r),
  out.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.2.1.2.1

theorem standalone_Mission_RAMTreeExtract__updateLeaf_real_frame :
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input Queue.updateLeaf s out steps) (hr : 2 ≤ r),
  out.rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.2.1.2.2

theorem treeExtract_run :
  ∀ (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeExtractPrepared s))
    (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 170 + (s.nm (s.nr 1 + 1) - 1))
    (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeExtractPrepared s))
    (hnew : truth (s.nr 170 + (s.nm (s.nr 1 + 1) - 1)) = ⟨0, s.rm (s.nr 1 + 1)⟩),
  ∃ out steps, Run input treeExtract s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 15 ∧
      Queue.ParentLayout (2 * B) out ∧
      (∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v) ∧
      out.nr 260 = s.nm (s.nr 1 + 1) ∧
      out.nr 261 = s.nm (s.nr 1 + 1) - 1 ∧
      out.nr 262 = s.nm (s.nr 171 + (s.nm (s.nr 1 + 1) - 1)) ∧
      out.rr 260 = s.rm (s.nr 1 + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.2.2.1.1

theorem treeRecordDistance_run :
  ∀ (input : RAMInput) (s : Store),
  Run input (.atoms treeRecordDistanceAtoms) s (treeRecordedDistance s) 6 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.2.2.1.2

theorem treeRecordedDistance_value :
  ∀ (s : Store),
  (treeRecordedDistance s).rm (targetAddress (s.nr 262) + s.nr 173) = s.rr 260 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.2.2.2.1

theorem treeRecordedDistance_frame :
  ∀ (s : Store) (a : ℕ)
    (ha : a ≠ targetAddress (s.nr 262) + s.nr 173),
  (treeRecordedDistance s).nm = s.nm ∧ (treeRecordedDistance s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.2.2.2.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem encodeInput_edge_left :
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).naturals (3+2*k) = e.1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.1.1

theorem encodeInput_edge_right :
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).naturals (3+2*k+1) = e.2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.1.2.1

theorem encodeInput_length :
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).reals (2+2*k) = (I.length e.1 e.2 : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.1.2.2

theorem encodeInput_cost :
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).reals (2+2*k+1) = (I.cost e.1 e.2 : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem treeEdgeAtoms_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeEdgeAtoms s = treeEdgeLoaded input s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.2.2.1

theorem treeEdgeLoaded_values :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (e : ℕ × ℕ)
    (he : I.graph.edges[s.nr 265]? = some e) (hone : s.nr 4 = 1),
  (treeEdgeLoaded (encodeInput I ε) s).nr 268 = e.2 ∧
    (treeEdgeLoaded (encodeInput I ε) s).rr 261 = (I.length e.1 e.2 : ℝ) ∧
    (treeEdgeLoaded (encodeInput I ε) s).rr 262 = (I.cost e.1 e.2 : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.2.2.2

theorem treeTargetAtoms_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeTargetAtoms s = treeTargetLoaded s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.2.1.1

theorem treeDecreaseAtoms_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input treeDecreaseAtoms s = treeDecreased s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.2.1.2.1

theorem treeDecreased_header :
  ∀ (s : Store) (r : ℕ) (hr : r < 11),
  (treeDecreased s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.2.1.2.2

theorem treeApplyDecrease_run :
  ∀ (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeDecreased s)) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeDecreased s))
    (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 264⟩),
  ∃ out steps, Run input treeApplyDecrease s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 14 ∧
      Queue.ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.2.2.1.1

theorem adjacencyAtoms_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input adjacencyAtoms s = adjacencyResult s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.2.2.1.2

theorem adjacencyInsert_run :
  ∀ (input : RAMInput) (s : Store),
  Run input adjacencyInsert s (adjacencyResult s) 6 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.2.2.2.1

theorem adjacencyResult_head :
  ∀ (s : Store) (hone : s.nr 126 = 1),
  (adjacencyResult s).nm (s.nr 163 + s.nr 161) = s.nr 160 + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.2.2.2.2

theorem adjacencyResult_link :
  ∀ (s : Store)
    (hsep : s.nr 164 + s.nr 160 ≠ s.nr 163 + s.nr 161),
  (adjacencyResult s).nm (s.nr 164 + s.nr 160) = s.nm (s.nr 163 + s.nr 161) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.1.1.1

theorem adjacencyResult_memory_frame :
  ∀ (s : Store) (a : ℕ)
    (hh : a ≠ s.nr 163 + s.nr 161) (hl : a ≠ s.nr 164 + s.nr 160),
  (adjacencyResult s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.1.1.2.1

theorem adjacencyResult_register_frame :
  ∀ (s : Store) (r : ℕ)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168),
  (adjacencyResult s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.1.1.2.2

theorem adjacencyResult_real_frame :
  ∀ (s : Store),
  (adjacencyResult s).rr = s.rr ∧ (adjacencyResult s).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.1.2.1

theorem AdjacencyChain.frame :
  ∀ {mem mem' : ℕ → ℕ} {links token : ℕ} {es : List ℕ}
    (h : AdjacencyChain mem links token es)
    (hf : ∀ e ∈ es, mem' (links + e) = mem (links + e)),
  AdjacencyChain mem' links token es :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.1.2.2.1

theorem adjacencyInsert_chain :
  ∀ (s : Store) (es : List ℕ)
    (hone : s.nr 126 = 1)
    (hold : AdjacencyChain s.nm (s.nr 164) (s.nm (s.nr 163 + s.nr 161)) es)
    (hfresh : s.nr 160 ∉ es)
    (hsep : ∀ e, s.nr 164 + e ≠ s.nr 163 + s.nr 161),
  AdjacencyChain (adjacencyResult s).nm (s.nr 164)
      ((adjacencyResult s).nm (s.nr 163 + s.nr 161)) (s.nr 160 :: es) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.1.2.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem treeAdjacencyPrepared_scratch :
  ∀ (input : RAMInput) (s : Store),
  TreeIteratorScratch s (treeAdjacencyPrepared input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.2.1.1

theorem treeAdjacencyAdvanced_scratch :
  ∀ (input : RAMInput) (s : Store),
  TreeIteratorScratch s (treeAdjacencyAdvanced input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.2.1.2.1

theorem treeAdjacencyPrepared_values :
  ∀ (input : RAMInput) (s : Store),
  (treeAdjacencyPrepared input s).nr 265 = s.nr 278-s.nr 4 ∧
    (treeAdjacencyPrepared input s).nr 279 = s.nm (s.nr 139+(s.nr 278-s.nr 4)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.2.1.2.2

theorem treeAdjacencyLoop_run_of_edge_contract :
  ∀ {α : Type u_1}
    (input : RAMInput) (links C : ℕ) (valid protect : ℕ → Prop)
    (step : α → ℕ → α) (Inv : α → Store → Prop)
    (htransfer : ∀ S s t, Inv S s → TreeIteratorScratch s t → Inv S t)
    (hedge : ∀ S e s, valid e → Inv S s → s.nr 265 = e →
      ∃ t n, Run input treeRelaxEdgeCmd s t n ∧ Inv (step S e) t ∧ n ≤ C ∧
        (∀ k, valid k → t.nm (links+k) = s.nm (links+k)) ∧
        (∀ a, protect a → t.nm a = s.nm a ∧ t.rm a = s.rm a))
    (es : List ℕ) (S : α) (s : Store) (token : ℕ)
    (hchain : AdjacencyChain s.nm links token es)
    (hvalid : ∀ e ∈ es, valid e) (hInv : Inv S s)
    (hz : s.nr 3 = 0) (ho : s.nr 4 = 1) (hl : s.nr 139 = links)
    (htoken : s.nr 278 = token),
  ∃ out n, Run input treeAdjacencyLoop s out n ∧ Inv (es.foldl step S) out ∧
      out.nr 278 = 0 ∧ n ≤ (C+6)*es.length+1 ∧
      (∀ a, protect a → out.nm a = s.nm a ∧ out.rm a = s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).2.1.1.1.1.2.2.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem treeCheckTarget_run :
  ∀ (input : RAMInput) (B : ℕ) (leaf : ℕ → Queue.Record)
    (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeTargetLoaded s)) (hone : s.nr 4 = 1)
    (hpositive : 0 < (treeTargetLoaded s).nr 0) (hleaf : B ≤ (treeTargetLoaded s).nr 0)
    (hrep : Queue.Represents B ((treeTargetLoaded s).nr 1) leaf (treeTargetLoaded s))
    (hparent : targetAddress ((treeTargetLoaded s).nr 268) + (treeTargetLoaded s).nr 173 < (treeTargetLoaded s).nr 1),
  ∃ out steps, Run input treeCheckTarget s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 25 ∧
      Queue.ParentLayout (2 * B) out ∧
      Queue.Represents B ((treeTargetLoaded s).nr 1) (treeCheckedLeaf leaf (treeTargetLoaded s)) out ∧
      (∀ a, a < (treeTargetLoaded s).nr 1 ∨ (treeTargetLoaded s).nr 1 + 2 * B ≤ a →
        out.nm a = treeCheckedNatMemory (treeTargetLoaded s) a ∧ out.rm a = (treeTargetLoaded s).rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.2.2.1.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem treePolicy_candidate_sentinel :
  ∀ (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ≥0) (S : TreeQueue)
    (h : TreePolicy I allow (fun u v=>(w u v:ℝ)) S)
    (hs : (S.tree I.source).distance=some 0) (u v : ℕ) (d : ℝ)
    (hd : (S.tree u).distance=some d) (he : (u,v)∈I.graph.edges),
  d+(w u v:ℝ) < ((I.graph.n:ℝ)+1)*(1+edgeWeightSum I w) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.2.2.2.1

theorem sentinelKey_le :
  ∀ (top : ℝ) (T : ShortestTree) (v : ℕ)
    (h : ∀ d, (T v).distance=some d → d<top),
  sentinelKey top T v≤top :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.2.2.2.2

theorem sentinel_source_none_no_decrease :
  ∀ (top : ℝ) (T : ShortestTree) (u v : ℕ)
    (hu : (T u).distance=none) (weight : ℝ) (hw : 0≤weight)
    (hv : ∀ d, (T v).distance=some d → d<top),
  ¬ sentinelKey top T u+weight < sentinelKey top T v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.1.1.1

theorem sentinel_finite_candidate_comparison :
  ∀ (top : ℝ) (T : ShortestTree) (v : ℕ)
    (candidate : ℝ) (hc : candidate<top)
    (hv : ∀ d, (T v).distance=some d → d<top),
  distanceLess (some candidate) (T v).distance = decide (candidate<sentinelKey top T v) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.1.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem treeRelax_eq_real_test :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (u v : ℕ) (top : ℝ)
    (hu : u ∉ S.queue) (hw : 0 ≤ w u v)
    (hfinite : ∀ x d, (S.tree x).distance = some d → d < top)
    (hcandidate : ∀ d, (S.tree u).distance = some d → d + w u v < top),
  treeRelax I allow w u S (u,v) =
      if v ∈ S.queue ∧ allow u v = true ∧
          sentinelKey top S.tree u + w u v < sentinelKey top S.tree v then
        { S with tree := Function.update S.tree v ⟨some (sentinelKey top S.tree u + w u v), some u, 0⟩ }
      else S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.1.1.2.2

theorem sentinelKey_update :
  ∀ (top : ℝ) (T : ShortestTree) (v : ℕ) (d : ℝ)
    (parent rank : ℕ),
  sentinelKey top (Function.update T v ⟨some d, some parent, rank⟩) =
      Function.update (sentinelKey top T) v d :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem TreeMemoryRep.congr :
  ∀ {I : Instance} {B W P map array off : ℕ} {top : ℝ}
    {S : TreeQueue} {s t : Store} (h : TreeMemoryRep I B W P map array off top S s)
    (hmap : t.nr 141 = s.nr 141) (harray : t.nr 142 = s.nr 142)
    (hcount : t.nr 143 = s.nr 143) (hn : t.nm = s.nm) (hr : t.rm = s.rm),
  TreeMemoryRep I B W P map array off top S t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.1.2.2.1

theorem TreeMemoryRep.after_readonly :
  ∀ {I : Instance} {B W P map array off : ℕ} {top : ℝ}
    {S : TreeQueue} {s t : Store} (h : TreeMemoryRep I B W P map array off top S s)
    {input : RAMInput} {cmd : Cmd} {steps : ℕ} (hrun : Run input cmd s t steps)
    (h141 : 141 ∉ cmd.natWrites) (h142 : 142 ∉ cmd.natWrites) (h143 : 143 ∉ cmd.natWrites)
    (hn : cmd.writesNatMemory = false) (hr : cmd.writesRealMemory = false),
  TreeMemoryRep I B W P map array off top S t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.1.2.2.2

theorem treeTarget_values :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (s : Store) (v : ℕ) (hm : E.Memory mode S s)
    (hr : E.Registers mode s) (hv : v ∈ activeVertices I) (hhead : s.nr 268 = v),
  let k := (activeVertices I).idxOf v
  let p := treeTargetLoaded s
  p.nr 0 = E.B+k ∧ p.nr 10 = (if v ∈ S.queue then k+1 else 0) ∧
  p.rr 265 = sentinelKey (mode.top I) S.tree v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.2.1.1

theorem treeTarget_correct :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (input : RAMInput) (s : Store) (u v : ℕ) (d : ℝ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (hv : v ∈ activeVertices I) (hu : s.nr 262 = u) (hhead : s.nr 268 = v)
    (hd : s.rr 264 = d),
  ∃ out steps, Run input treeCheckTarget s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+25 ∧
      E.Memory mode (treeTargetState (mode.top I) S u v d) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.2.1.2.1

theorem TreeMode.sentinel_bounds :
  ∀ (mode : TreeMode) (I : Instance) (S : TreeQueue)
    (h : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0) (u v : ℕ) (he : (u,v) ∈ I.graph.edges),
  (∀ x d, (S.tree x).distance = some d → d < mode.top I) ∧
    (∀ d, (S.tree u).distance = some d → d + mode.weight I u v < mode.top I) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.2.1.2.2

theorem standalone_Mission_RAMTreeEdge__edgeGuard_value :
  ∀ (I : Instance) (mode : TreeMode) (s : Store) (u v : ℕ)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v) (hz : s.rr 263 = 0),
  (standalone_Mission_RAMTreeEdge__edgeGuard mode).eval s = mode.allow I u v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.2.2.1.1

theorem standalone_Mission_RAMTreeEdge__candidate_value :
  ∀ (I : Instance) (mode : TreeMode) (input : RAMInput)
    (s : Store) (u v : ℕ) (key : ℝ) (hkey : s.rr 260 = key)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v),
  ((standalone_Mission_RAMTreeEdge__candidateAtom mode).eval input s).rr 264 = key + mode.weight I u v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.2.2.1.2

theorem standalone_Mission_RAMTreeEdge__modeBody_correct :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (input : RAMInput) (s : Store) (u v : ℕ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (he : (u,v) ∈ I.graph.edges) (huq : u ∉ S.queue)
    (hpolicy : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0)
    (hu : s.nr 262 = u) (hv : s.nr 268 = v)
    (hkey : s.rr 260 = sentinelKey (mode.top I) S.tree u)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v) (hz : s.rr 263 = 0),
  ∃ out steps, Run input (standalone_Mission_RAMTreeEdge__modeBody mode) s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+28 ∧
      E.Memory mode (treeRelax I (mode.allow I) (mode.weight I) u S (u,v)) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.2.2.2.1

theorem treeEdge_correct :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (ε : ℝ) (s : Store) (u v : ℕ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (he : I.graph.edges[s.nr 265]? = some (u,v)) (huq : u ∉ S.queue)
    (hpolicy : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0)
    (hu : s.nr 262 = u) (hkey : s.rr 260 = sentinelKey (mode.top I) S.tree u),
  ∃ out steps, Run (encodeInput I ε) treeRelaxEdgeCmd s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+40 ∧
      E.Memory mode (treeRelax I (mode.allow I) (mode.weight I) u S (u,v)) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.1.2.2.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem treeRelax_source_zero :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ) (S : TreeQueue)
    (hn : ∀ v, 0 ≤ treeDist S.tree v) (hs : (S.tree I.source).distance = some 0)
    (e : ℕ × ℕ),
  ((treeRelax I allow w u S e).tree I.source).distance = some 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.1.1.1

theorem TreeScanMath.step :
  ∀ {I : Instance} {allow : ℕ → ℕ → Bool} {w : ℕ → ℕ → ℝ}
    {u : ℕ} {S : TreeQueue} (h : TreeScanMath I allow w u S)
    (hw : ∀ u v, 0 ≤ w u v) (e : ℕ × ℕ) (he : e ∈ I.graph.edges),
  TreeScanMath I allow w u (treeRelax I allow w u S e) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.1.1.2.1

theorem TreeScanMath.start :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool) (w : ℕ → ℕ → ℝ)
    (S : TreeQueue) (u : ℕ) (hu : u ∈ S.queue) (hq : S.queue.Nodup)
    (hp : TreePolicy I allow w S) (hn : ∀ v, 0 ≤ treeDist S.tree v)
    (hs : (S.tree I.source).distance = some 0),
  TreeScanMath I allow w u (treeSettle S u) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.1.1.2.2

theorem relaxEdge_nonoutgoing :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (he : e.1 ≠ u),
  relaxEdge A i j u S e = S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.1.2.1

theorem relaxFold_filter_outgoing :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (es : List (ℕ × ℕ)),
  (es.filter (fun e => e.1 == u)).foldl (relaxEdge A i j u) S =
      es.foldl (relaxEdge A i j u) S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.1.2.2.1

theorem relaxAll_eq_outgoingFold :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  relaxAll A i j u S = (outgoingEdges A.I u).foldl (relaxEdge A i j u) S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.1.2.2.2

theorem treeRelax_nonoutgoing :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : e.1 ≠ u),
  treeRelax I allow w u S e = S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.2.1.1

theorem treeRelaxFold_filter_outgoing :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ)),
  (es.filter (fun e => e.1 == u)).foldl (treeRelax I allow w u) S =
      es.foldl (treeRelax I allow w u) S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.2.1.2.1

theorem treeRelaxAll_eq_outgoingFold :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue),
  treeRelaxAll I allow w u S =
      (outgoingEdges I u).foldl (treeRelax I allow w u) S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.2.1.2.2

theorem relaxEdge_disabled :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (he : ¬ (e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue)),
  relaxEdge A i j u S e = S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.2.2.1.1

theorem treeRelax_disabled :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : ¬ (e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue ∧ allow e.1 e.2 = true)),
  treeRelax I allow w u S e = S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.2.2.1.2

theorem relaxEdge_comm :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e f : ℕ × ℕ),
  relaxEdge A i j u (relaxEdge A i j u S e) f =
      relaxEdge A i j u (relaxEdge A i j u S f) e :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.2.2.2.1

theorem relaxFold_perm :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (es fs : List (ℕ × ℕ)) (h : es.Perm fs),
  es.foldl (relaxEdge A i j u) S = fs.foldl (relaxEdge A i j u) S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.2.2.2.2.2.2

theorem relaxAll_eq_reversedOutgoingFold :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  relaxAll A i j u S = (outgoingEdges A.I u).reverse.foldl (relaxEdge A i j u) S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.1.1.1

theorem treeRelax_comm :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (weight : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e f : ℕ × ℕ),
  treeRelax I allow weight u (treeRelax I allow weight u S e) f =
      treeRelax I allow weight u (treeRelax I allow weight u S f) e :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.1.1.2.1

theorem treeRelaxFold_perm :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue)
    (es fs : List (ℕ × ℕ)) (h : es.Perm fs),
  es.foldl (treeRelax I allow w u) S = fs.foldl (treeRelax I allow w u) S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.1.1.2.2

theorem treeRelaxAll_eq_reversedOutgoingFold :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue),
  treeRelaxAll I allow w u S =
      (outgoingEdges I u).reverse.foldl (treeRelax I allow w u) S :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.1.2.1

theorem popLayer_reversed_refinement :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []),
  popLayer A i j S = (outgoingEdges A.I (pickedVertex S)).reverse.foldl
      (relaxEdge A i j (pickedVertex S)) (settleState S i j (pickedVertex S)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.1.2.2.1

theorem treePop_reversed_refinement :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []),
  treePop I allow w S = (outgoingEdges I (treePick S)).reverse.foldl
      (treeRelax I allow w (treePick S)) (treeSettle S (treePick S)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.1.2.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

@[simp] theorem adjacencyStep_index :
  ∀ (input : RAMInput) (s : Store),
  (adjacencyStep input s).nr 160 = s.nr 160 + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.1.1

@[simp] theorem adjacencyStep_inputPointer :
  ∀ (input : RAMInput) (s : Store),
  (adjacencyStep input s).nr 162 = s.nr 162 + 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.1.2.1

theorem adjacencyStep_register :
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (h160 : r ≠ 160) (h161 : r ≠ 161) (h162 : r ≠ 162)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168),
  (adjacencyStep input s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.1.2.2

theorem adjacencyScanBody_run :
  ∀ (input : RAMInput) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2),
  Run input adjacencyScanBody s (adjacencyStep input s) 9 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.2.1.1

theorem adjacencyScanLoop_run :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2)
    (hend : s.nr 160 + remaining = s.nr 122),
  Run input adjacencyScanLoop s (adjacencyScanResult input remaining s) (11*remaining+1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.2.1.2

theorem adjacencyScanCmd_run :
  ∀ (input : RAMInput) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2),
  Run input adjacencyScanCmd s
      (adjacencyScanResult input (s.nr 122) (adjacencyPrepared s)) (11*s.nr 122+3) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.2.2.1

theorem outgoingIndices_lt :
  ∀ (I : Instance) (count v e : ℕ)
    (he : e ∈ outgoingIndices I count v),
  e < count :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.2.2.2

theorem outgoingIndices_succ :
  ∀ (I : Instance) (count v : ℕ),
  outgoingIndices I (count+1) v =
      if (edgeAt I count).1 = v then count :: outgoingIndices I count v
      else outgoingIndices I count v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.1.1.1

theorem adjacencyPrefix_zero :
  ∀ (I : Instance) (heads links : ℕ) (mem : ℕ → ℕ)
    (hz : ∀ v<I.graph.n, mem (heads+v)=0),
  AdjacencyPrefix I 0 heads links mem :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.1.1.2.1

theorem edgeAt_valid :
  ∀ (I : Instance) (e : ℕ) (he : e < I.graph.edges.length),
  (edgeAt I e).1 < I.graph.n ∧ (edgeAt I e).2 < I.graph.n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.1.1.2.2

theorem adjacencyStep_prefix :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (count heads links : ℕ)
    (hone : s.nr 126=1) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hvalid : count<I.graph.edges.length)
    (hsep : heads+I.graph.n ≤ links) (h : AdjacencyPrefix I count heads links s.nm),
  AdjacencyPrefix I (count+1) heads links (adjacencyStep (encodeInput I ε) s).nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.1.2.1

theorem adjacencyScanResult_register :
  ∀ (input : RAMInput) (n : ℕ) (s : Store) (r : ℕ)
    (h160 : r ≠ 160) (h161 : r ≠ 161) (h162 : r ≠ 162)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168),
  (adjacencyScanResult input n s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.1.2.2.1

theorem adjacencyScanResult_reals :
  ∀ (input : RAMInput) (n : ℕ) (s : Store),
  (adjacencyScanResult input n s).rr = s.rr ∧
      (adjacencyScanResult input n s).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.1.2.2.2

theorem adjacencyScanResult_prefix :
  ∀ (I : Instance) (ε : ℝ) (remaining : ℕ)
    (s : Store) (count heads links : ℕ)
    (hone : s.nr 126=1) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links)
    (hvalid : count+remaining≤I.graph.edges.length)
    (hsep : heads+I.graph.n≤links) (h : AdjacencyPrefix I count heads links s.nm),
  AdjacencyPrefix I (count+remaining) heads links
      (adjacencyScanResult (encodeInput I ε) remaining s).nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.1.1

theorem adjacencyStep_memory_outside :
  ∀ (I : Instance) (ε : ℝ) (s : Store)
    (count heads links a : ℕ) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hk : count<I.graph.edges.length)
    (hahead : a<heads ∨ heads+I.graph.n≤a)
    (halink : a<links ∨ links+I.graph.edges.length≤a),
  (adjacencyStep (encodeInput I ε) s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.1.2.1

theorem adjacencyScanResult_memory_outside :
  ∀ (I : Instance) (ε : ℝ) (remaining : ℕ)
    (s : Store) (count heads links a : ℕ)
    (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links)
    (hvalid : count+remaining≤I.graph.edges.length)
    (hahead : a<heads ∨ heads+I.graph.n≤a)
    (halink : a<links ∨ links+I.graph.edges.length≤a),
  (adjacencyScanResult (encodeInput I ε) remaining s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.1.2.2

theorem adjacencyScanCmd_correct :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (heads links : ℕ)
    (hm : s.nr 122=I.graph.edges.length) (hone : s.nr 126=1) (htwo : s.nr 127=2)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hsep : heads+I.graph.n≤links)
    (hzero : ∀ v<I.graph.n, s.nm (heads+v)=0),
  ∃ out, Run (encodeInput I ε) adjacencyScanCmd s out (11*I.graph.edges.length+3) ∧
      AdjacencyPrefix I I.graph.edges.length heads links out.nm ∧
      out.rr=s.rr ∧ out.rm=s.rm ∧
      (∀ a, (a<heads ∨ heads+I.graph.n≤a) →
        (a<links ∨ links+I.graph.edges.length≤a) → out.nm a=s.nm a) ∧
      (∀ r, r≠160 → r≠161 → r≠162 → r≠165 → r≠166 → r≠167 → r≠168 → out.nr r=s.nr r) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.2.1.1

theorem standalone_Mission_RAMAdjacencyScan__map_filter_compat :
  ∀ {α β : Type} (f : α→β) (p : β→Bool) (xs : List α),
  (xs.filter (fun x=>p (f x))).map f = (xs.map f).filter p :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.2.1.2

theorem edgeAt_map_range :
  ∀ (I : Instance),
  (List.range I.graph.edges.length).map (edgeAt I) = I.graph.edges :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.2.2.1

theorem outgoingIndices_edges :
  ∀ (I : Instance) (v : ℕ),
  (outgoingIndices I I.graph.edges.length v).map (edgeAt I) = (outgoingEdges I v).reverse :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.2.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem TreeScanInvariant.transfer :
  ∀ {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {u : ℕ} {S : TreeQueue} {s t : Store} (h : TreeScanInvariant E mode u S s)
    (hf : TreeIteratorScratch s t),
  TreeScanInvariant E mode u S t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.1.1.1

theorem TreeAllocation.link_protected :
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (k : ℕ) (hk : k < I.graph.edges.length),
  TreeProtected E mode (E.links+k) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.1.1.2.1

theorem TreeAllocation.graph_protected :
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (a : ℕ) (hlo : E.map ≤ a) (hhi : a < E.W),
  TreeProtected E mode a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.1.1.2.2

theorem AdjacencyPrefix.protected_frame :
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) {s t : Store}
    (h : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm)
    (hf : ∀ a, TreeProtected E mode a → t.nm a = s.nm a),
  AdjacencyPrefix I I.graph.edges.length E.heads E.links t.nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.1.2.1

theorem outgoingIndices_valid :
  ∀ (I : Instance) (u e : ℕ)
    (he : e ∈ outgoingIndices I I.graph.edges.length u),
  ∃ v, I.graph.edges[e]? = some (u,v) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.1.2.2.1

theorem treeScan_run :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (u : ℕ) (S : TreeQueue) (s : Store) (es : List ℕ) (token : ℕ)
    (hchain : AdjacencyChain s.nm E.links token es)
    (hvalid : ∀ e ∈ es, ∃ v, I.graph.edges[e]? = some (u,v))
    (hInv : TreeScanInvariant E mode u S s) (htoken : s.nr 278 = token),
  ∃ out steps, Run (encodeInput I ε) treeAdjacencyLoop s out steps ∧
      TreeScanInvariant E mode u
        (es.foldl (fun T e => treeRelax I (mode.allow I) (mode.weight I) u T (edgeAt I e)) S) out ∧
      out.nr 278 = 0 ∧ steps ≤ (19*Nat.clog 2 (2*E.B)+46)*es.length+1 ∧
      (∀ a, TreeProtected E mode a → out.nm a = s.nm a ∧ out.rm a = s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.1.2.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured Queue

theorem standalone_Mission_RAMTreeExtractRefinement__queue_update_nat_high :
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input updateLeaf s out steps) (hr : 11 ≤ r),
  out.nr r=s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.2.1.1

theorem standalone_Mission_RAMTreeExtractRefinement__queue_update_real_high :
  ∀ {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input updateLeaf s out steps) (hr : 2 ≤ r),
  out.rr r=s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.2.1.2.1

theorem treeExtract_refines :
  ∀ (input : RAMInput) (B height : ℕ)
    (xs q : List ℕ) (key : ℕ→ℝ) (s : Store)
    (hB : B=2^height) (hfit : xs.length ≤ B)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hne : q ≠ [])
    (hp : s.nr 1+2*B ≤ s.nr 2 ∧ s.nr 3=0 ∧
      ∀ node < 2*B,s.nm (s.nr 2+node)=node/2)
    (hone : s.nr 4=1) (hbase : s.nr 170=B)
    (harray : ∀ k v, xs[k]?=some v → s.nm (s.nr 171+k)=v)
    (hrep : Represents B (s.nr 1) (activeLeaf xs q key B) s),
  let u := firstMin key q 0
  ∃ out cost, Run input treeExtract s out cost ∧
    cost ≤ 19*Nat.clog 2 (2*B)+15 ∧ ParentLayout (2*B) out ∧
    Represents B (s.nr 1) (activeLeaf xs (q.erase u) key B) out ∧
    WinnerFrame (s.nr 1) (2*B) s out ∧
    out.nr 0=0 ∧ (∀ r,0 < r → r < 5 → out.nr r=s.nr r) ∧
    out.nr 260=xs.idxOf u+1 ∧ out.nr 261=xs.idxOf u ∧
    out.nr 262=u ∧ out.rr 260=key u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.2.1.2.2

theorem treeExtract_high_register :
  ∀ (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input treeExtract s out cost) (hr : 11 ≤ r)
    (h260 : r ≠ 260) (h261 : r ≠ 261) (h262 : r ≠ 262),
  out.nr r=s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.2.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem sentinelKey_treeSettle :
  ∀ (top : ℝ) (S : TreeQueue) (u : ℕ),
  sentinelKey top (treeSettle S u).tree=sentinelKey top S.tree :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.2.2.1.2

theorem treeSettle_parent_unchanged :
  ∀ (S : TreeQueue) (u v : ℕ),
  ((treeSettle S u).tree v).parent=(S.tree v).parent :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.2.2.2.1

theorem treeExtract_registers :
  ∀ (I : Instance) (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s out : Store) (cost : ℕ)
    (hR : E.Registers mode s) (h : Run input treeExtract s out cost),
  E.Registers mode out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.2.2.2.2

theorem treeSettle_registers :
  ∀ (I : Instance) (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s out : Store) (cost : ℕ)
    (hR : E.Registers mode s) (h : Run input treeSettleCmd s out cost),
  E.Registers mode out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.1.1

theorem treeSettle_run :
  ∀ (input : RAMInput) (I : Instance) (E : TreeAllocation I)
    (mode : TreeMode) (S : TreeQueue) (s : Store)
    (hM : E.Memory mode S s) (hR : E.Registers mode s) (hne : S.queue ≠ [])
    (hfinite : ∀ v d,(S.tree v).distance=some d → d < mode.top I),
  ∃ out cost, Run input treeSettleCmd s out cost ∧
      cost ≤ 19*Nat.clog 2 (2*E.B)+21 ∧
      E.Memory mode (treeSettle S (treePick S)) out ∧ E.Registers mode out ∧
      out.nr 262=treePick S ∧ out.rr 260=sentinelKey (mode.top I) S.tree (treePick S) ∧
      (∀ a,(a < E.W ∨ E.W+2*E.B ≤ a) → out.nm a=s.nm a) ∧
      (∀ a,(a < E.W ∨ E.W+2*E.B ≤ a) →
        a ≠ targetAddress (treePick S)+mode.offset → out.rm a=s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.1.2.1

theorem treeSettle_counter277 :
  ∀ (input : RAMInput) (s out : Store) (cost : ℕ)
    (h : Run input treeSettleCmd s out cost),
  out.nr 277=s.nr 277 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.1.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

theorem outgoingWork_erase :
  ∀ (I : Instance) (vertices : List ℕ) (u : ℕ) (hu : u ∈ vertices),
  (outgoingEdges I u).length + outgoingWork I (vertices.erase u) = outgoingWork I vertices :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.2.1.1

theorem standalone_Mission_OutgoingWork__indicator_sum :
  ∀ (xs : List ℕ) (u : ℕ),
  (xs.map (fun v => if u = v then 1 else 0)).sum = xs.count u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.2.1.2

theorem standalone_Mission_OutgoingWork__outgoing_filter_count :
  ∀ (edges : List (ℕ × ℕ)) (vertices : List ℕ)
    (hnd : vertices.Nodup) (hs : ∀ e ∈ edges, e.1 ∈ vertices),
  (vertices.map (fun u => (edges.filter (fun e => e.1 == u)).length)).sum = edges.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.2.2.1

theorem outgoingWork_active :
  ∀ (I : Instance),
  outgoingWork I (activeVertices I) = I.graph.edges.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.2.2.2

theorem outgoingWork_settle :
  ∀ (I : Instance) (S : LayerState) (i j u : ℕ) (hu : u ∈ S.queue),
  (outgoingEdges I u).length + outgoingWork I (settleState S i j u).queue =
      outgoingWork I S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.2.1.1

theorem queueRun_succ_front :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  queueRun A i j (n+1) S = queueRun A i j n (popLayer A i j S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.2.1.2.1

theorem popLayer_nextRank_of_ne :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue≠[]),
  (popLayer A i j S).nextRank=S.nextRank+1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.2.1.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem standalone_Mission_RAMTreePop__seq_attach :
  ∀ {input : RAMInput} {a b c : Cmd} {s t out : Store} {n m : ℕ}
    (hab : Run input (.seq a b) s t n) (hc : Run input c t out m),
  Run input (.seq a (.seq b c)) s out (n+m) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.2.2.1.1

theorem treeHeadStore_token :
  ∀ (input : RAMInput) (s : Store),
  (treeHeadStore input s).nr 278 = s.nm (s.nr 137+s.nr 262) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.2.2.1.2

theorem treePopCmd_run :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (S : TreeQueue) (s : Store)
    (hm : E.Memory mode S s) (hr : E.Registers mode s) (hne : S.queue ≠ [])
    (hp : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hn : ∀ v, 0 ≤ treeDist S.tree v) (hs : (S.tree I.source).distance = some 0)
    (hfinite : ∀ v d, (S.tree v).distance=some d → d < mode.top I)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm),
  ∃ out steps, Run (encodeInput I ε) treePopCmd s out steps ∧
      E.Memory mode (treePop I (mode.allow I) (mode.weight I) S) out ∧
      E.Registers mode out ∧ out.nr 277 = s.nr 277+1 ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+25 +
        (19*Nat.clog 2 (2*E.B)+46)*(outgoingEdges I (treePick S)).length ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.2.2.2.1

theorem treePop_outgoingWork :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []),
  (outgoingEdges I (treePick S)).length + outgoingWork I (treePop I allow w S).queue =
      outgoingWork I S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.2.2.2.2

theorem treeLoop_run :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (remaining k : ℕ) (s : Store)
    (hend : k+remaining=(activeVertices I).length)
    (hm : E.Memory mode (treeState I mode k) s) (hr : E.Registers mode s)
    (hcounter : s.nr 277=k)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm),
  ∃ out steps, Run (encodeInput I ε) treeLoopCmd s out steps ∧
      E.Memory mode (treeState I mode (activeVertices I).length) out ∧
      E.Registers mode out ∧ out.nr 277=(activeVertices I).length ∧
      steps ≤ (19*Nat.clog 2 (2*E.B)+27)*remaining +
        (19*Nat.clog 2 (2*E.B)+46)*outgoingWork I (treeState I mode k).queue+1 ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.1.1.1

theorem standalone_Mission_RAMTreeRun__seq_attach :
  ∀ {input : RAMInput} {a b c : Cmd} {s t out : Store} {n m : ℕ}
    (hab : Run input (.seq a b) s t n) (hc : Run input c t out m),
  Run input (.seq a (.seq b c)) s out (n+m) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.1.1.2.1

theorem treeCmd_run :
  ∀ {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (s : Store) (hr : E.Registers mode s)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm),
  ∃ out steps, Run (encodeInput I ε) treeCmd s out steps ∧
      E.Memory mode (treeState I mode (activeVertices I).length) out ∧
      E.Registers mode out ∧
      steps ≤ 15*E.B+(38*Nat.clog 2 (2*E.B)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*E.B)+46)*I.graph.edges.length+7 ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeWholeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.1.1.2.2

theorem treeState_final_tree :
  ∀ (I : Instance) (mode : TreeMode),
  (treeState I mode (activeVertices I).length).tree =
      shortestTree I (mode.allow I) (mode.weight I) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.1.2.1

theorem treeState_final_queue :
  ∀ (I : Instance) (mode : TreeMode),
  (treeState I mode (activeVertices I).length).queue=[] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.1.2.2.1

theorem TreeMemoryRep.final_distances :
  ∀ {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {s : Store} (h : E.Memory mode (treeState I mode (activeVertices I).length) s)
    (v : ℕ) (hv : v ∈ activeVertices I),
  s.rm (targetAddress v+mode.offset) =
      sentinelKey (mode.top I) (shortestTree I (mode.allow I) (mode.weight I)) v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.1.2.2.2

theorem TreeMemoryRep.final_parents :
  ∀ {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {s : Store} (h : E.Memory mode (treeState I mode (activeVertices I).length) s)
    (v : ℕ) (hv : v ∈ activeVertices I),
  s.nm (targetAddress v+mode.offset) =
      (((shortestTree I (mode.allow I) (mode.weight I)) v).parent.map (·+1)).getD 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.2.1.1

theorem zeroTreeSetup_run :
  ∀ (input : RAMInput) (mode : TreeMode) (s : Store),
  Run input (zeroTreeSetup mode) s (zeroTreePrepared mode s) 3 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.2.1.2.1

theorem TreeRegisters.prepare :
  ∀ {I : Instance} {E : TreeAllocation I} {old : TreeMode}
    {s : Store} (h : E.Registers old s) (mode : TreeMode)
    (hs : s.rr mode.sentinelRegister=mode.top I),
  E.Registers mode (zeroTreePrepared mode s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.2.1.2.2

theorem TreeAllocation.length_field_protected :
  ∀ {I : Instance} (E : TreeAllocation I)
    (v : ℕ) (hv : v < I.graph.n),
  TreeWholeProtected E .zeroBudget (targetAddress v+2) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.2.2.1.1

theorem TreeMode.zeroLength_tree :
  ∀ (I : Instance),
  shortestTree I (TreeMode.zeroLength.allow I) (TreeMode.zeroLength.weight I) = zeroLengthTree I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.2.2.1.2

theorem TreeMode.zeroBudget_tree :
  ∀ (I : Instance),
  shortestTree I (TreeMode.zeroBudget.allow I) (TreeMode.zeroBudget.weight I) = zeroBudgetTree I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.2.2.2.1

theorem zeroTreesCmd_run :
  ∀ {I : Instance} (E : TreeAllocation I) (ε : ℝ) (s : Store)
    (hstart : E.Registers .zeroLength (zeroTreePrepared .zeroLength s))
    (hsentinel : s.rr 281=TreeMode.zeroBudget.top I)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm),
  ∃ out steps, Run (encodeInput I ε) zeroTreesCmd s out steps ∧
      ZeroTreeMemory I out ∧ E.Registers .zeroBudget out ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      steps ≤ 2*(15*E.B+(38*Nat.clog 2 (2*E.B)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*E.B)+46)*I.graph.edges.length+7)+6 ∧
      (∀ a, TreeWholeProtected E .zeroLength a → TreeWholeProtected E .zeroBudget a →
        out.nm a=s.nm a ∧ out.rm a=s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.1.2.2.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem standalone_Mission_Guesses__min_fold_le_seed :
  ∀ (xs : List ℝ) (a : ℝ),
  xs.foldl min a ≤ a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.1.1.1

theorem standalone_Mission_Guesses__min_fold_le_member :
  ∀ (xs : List ℝ) (a x : ℝ) (hx : x ∈ xs),
  xs.foldl min a ≤ x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.1.1.2.1

theorem standalone_Mission_Guesses__seed_le_max_fold :
  ∀ (xs : List ℝ) (a : ℝ),
  a ≤ xs.foldl max a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.1.1.2.2

theorem standalone_Mission_Guesses__member_le_max_fold :
  ∀ (xs : List ℝ) (a x : ℝ) (hx : x ∈ xs),
  x ≤ xs.foldl max a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.1.2.1

theorem firstPositiveLength_le_member :
  ∀ (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I),
  firstPositiveLength I ≤ x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.1.2.2.1

theorem member_le_largestLength :
  ∀ (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I),
  x ≤ largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.1.2.2.2

theorem largestLength_nonneg :
  ∀ (I : Instance),
  0 ≤ largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.1.1

theorem firstPositiveLength_le_largestLength :
  ∀ (I : Instance)
    (h : positiveLengths I ≠ []),
  firstPositiveLength I ≤ largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.1.2.1

theorem largestLength_pos :
  ∀ (I : Instance) (h : positiveLengths I ≠ []),
  0 < largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.1.2.2

theorem one_le_aspectRatio :
  ∀ (I : Instance),
  1 ≤ aspectRatio I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.2.1.1

theorem crossing_exists :
  ∀ (a r top : ℝ) (ha : 0 < a) (hr : 1 < r),
  ∃ k : ℕ, top ≤ a * r ^ k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.2.1.2

theorem firstCrossing_spec :
  ∀ (a r top : ℝ) (ha : 0 < a) (hr : 1 < r),
  top ≤ a * r ^ firstCrossing a r top :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.2.2.1

theorem firstCrossing_minimal :
  ∀ (a r top : ℝ) (ha : 0 < a) (hr : 1 < r)
    (i : ℕ) (hi : i < firstCrossing a r top),
  a * r ^ i < top :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.2.2.2

theorem firstCrossing_le :
  ∀ (a r top : ℝ) (ha : 0 < a) (hr : 1 < r)
    (i : ℕ) (hi : top ≤ a * r ^ i),
  firstCrossing a r top ≤ i :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.1.1.1

theorem firstCrossing_mono_top :
  ∀ (a r x y : ℝ) (ha : 0 < a) (hr : 1 < r)
    (hxy : x ≤ y),
  firstCrossing a r x ≤ firstCrossing a r y :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.1.1.2.1

theorem firstCrossing_approx :
  ∀ (a r x : ℝ) (ha : 0 < a) (hr : 1 < r)
    (hax : a ≤ x),
  a * r ^ firstCrossing a r x ≤ r * x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.1.1.2.2

theorem geometricGuesses_cover :
  ∀ (I : Instance) (ε x : ℝ)
    (hε : 0 < ε) (hne : positiveLengths I ≠ [])
    (hlo : firstPositiveLength I ≤ x)
    (hhi : x ≤ I.graph.n * largestLength I),
  ∃ L ∈ geometricGuesses I ε, x ≤ L ∧ L ≤ (1 + ε / 4) * x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.GuessLoop
open Structured

theorem step_run :
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  Run input (.atoms stepOps) (gridState s k) (gridState s (k+1)) 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.1.2.2.1

theorem loop_run :
  ∀ (input : RAMInput) (s : Store)
    (ha : 0 < s.rr 70) (hr : 1 < s.rr 71) (j d : ℕ)
    (hk : j+d = firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)),
  Run input loopCmd (gridState s j) (gridState s (j+d)) (4*d+1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.1.2.2.2

theorem crossingCmd_run :
  ∀ (input : RAMInput) (s : Store)
    (ha : 0 < s.rr 70) (hr : 1 < s.rr 71),
  Run input crossingCmd s
      (gridState s (firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)))
      (4*firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)+4) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.2.1.1

theorem crossing_result :
  ∀ (s : Store) (k : ℕ),
  (gridState s k).nr 70 = k ∧ (gridState s k).rr 73 = s.rr 70*s.rr 71^k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.2.1.2.1

theorem crossing_frame :
  ∀ (s : Store) (k : ℕ),
  (∀ r, r ≠ 70 → r ≠ 71 → (gridState s k).nr r = s.nr r) ∧
    (∀ r, r ≠ 73 → (gridState s k).rr r = s.rr r) ∧
    (gridState s k).nm = s.nm ∧ (gridState s k).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.2.1.2.2

end NearLinearRSP.TwoResources.Mission.GuessLoop
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

theorem acceptedIndex_spec :
  ∀ (I : Instance) (ε : ℝ) (t r : ℕ)
    (h : acceptedIndex I ε t = some r),
  ∃ A, (outerInputs I ε)[r]? = some A ∧ accepted A t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.2.2.1.1

theorem acceptedIndex_le :
  ∀ (I : Instance) (ε : ℝ) (t r s : ℕ) (A : InnerInput)
    (hr : acceptedIndex I ε t = some r)
    (hs : (outerInputs I ε)[s]? = some A) (ha : accepted A t),
  r ≤ s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.2.2.1.2

theorem acceptedIndex_exists :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ) (A : InnerInput)
    (hA : A ∈ outerInputs I ε) (ha : accepted A t),
  ∃ r, acceptedIndex I ε t = some r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.2.2.2.1

theorem answerBranch_inner_iff :
  ∀ (I : Instance) (ε : ℝ) (t r : ℕ),
  answerBranch I ε t = .inner r ↔
      t ≠ I.source ∧
      (∀ d, (zeroLengthTree I t).distance = some d → (I.budget : ℝ) < d) ∧
      I.budget ≠ 0 ∧ acceptedIndex I ε t = some r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.1.2.2.2.2

theorem answerBranch_inner_input :
  ∀ (I : Instance) (ε : ℝ) (t r : ℕ)
    (h : answerBranch I ε t = .inner r),
  ∃ A, (outerInputs I ε)[r]? = some A ∧ accepted A t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.1.1.1

theorem answerBranch_zeroLength_spec :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t = .zeroLength),
  t = I.source ∨ ∃ d, (zeroLengthTree I t).distance = some d ∧ d ≤ I.budget :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.1.1.2.1

theorem answerBranch_zeroBudget_spec :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t = .zeroBudget),
  I.budget = 0 ∧ (zeroBudgetTree I t).distance.isSome = true :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.1.1.2.2

theorem outerInputs_mem_fields :
  ∀ (I : Instance) (ε : ℝ) (A : InnerInput)
    (hA : A ∈ outerInputs I ε),
  A.I = I ∧ A.δ = ε / 4 ∧ A.L ∈ geometricGuesses I ε :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.1.2.1

theorem geometricGuesses_ordered :
  ∀ (I : Instance) (ε : ℝ) (hε : 0 ≤ ε),
  (geometricGuesses I ε).Pairwise (· ≤ ·) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.1.2.2.1

theorem outerInputs_ordered :
  ∀ (I : Instance) (ε : ℝ) (hε : 0 ≤ ε),
  (outerInputs I ε).Pairwise (fun A B => A.L ≤ B.L) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.1.2.2.2

theorem outerInputs_get_length_le :
  ∀ (I : Instance) (ε : ℝ) (hε : 0 ≤ ε)
    (r s : ℕ) (A B : InnerInput) (hr : (outerInputs I ε)[r]? = some A)
    (hs : (outerInputs I ε)[s]? = some B) (hrs : r ≤ s),
  A.L ≤ B.L :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.2.1.1

theorem answerDistance_eq_none_iff :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ),
  answerDistance I ε t = none ↔ answerBranch I ε t = .absent :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.2.1.2.1

theorem EncodesOutput.readDistance_eq :
  ∀ (I : Instance) (ε : ℝ) (S : RAMState)
    (h : EncodesOutput I ε S) (t : ℕ) (ht : t < I.graph.n),
  readDistance S t = answerDistance I ε t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.2.1.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem outerInputs_length_exact :
  ∀ (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1),
  (outerInputs I ε).length = if (positiveLengths I).isEmpty ∨ I.budget = 0 then 0
      else firstCrossing (firstPositiveLength I) (1+ε/4) (I.graph.n * largestLength I)+1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem countCmd_run :
  ∀ (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (s : Store) (hs : CountReady I ε s),
  ∃ out steps, Run (encodeInput I ε) countCmd s out steps ∧
      out.nr 132 = (outerInputs I ε).length ∧
      steps ≤ 4*(outerInputs I ε).length+13 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.2.2.1.2

theorem countCmd_nat_frame :
  ∀ {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k) (r : ℕ)
    (h70 : r ≠ 70) (h71 : r ≠ 71) (h132 : r ≠ 132),
  out.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.2.2.2.1

theorem countCmd_real_frame :
  ∀ {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k) (r : ℕ) (hr : r < 70 ∨ 74 < r),
  out.rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.2.2.2.2.2.2

theorem countCmd_memory_frame :
  ∀ {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k),
  out.nm = s.nm ∧ out.rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.1.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission
namespace Preprocess
open Structured

theorem headerPrepared_values :
  ∀ (input : RAMInput) (s : Store),
  (headerPrepared input s).nr 121 = input.naturals 0 ∧
    (headerPrepared input s).nr 122 = input.naturals 1 ∧
    (headerPrepared input s).nr 123 = input.naturals 2 ∧
    (headerPrepared input s).nr 124 = 0 ∧
    (headerPrepared input s).nr 126 = 1 ∧
    (headerPrepared input s).nr 129 = 4 * input.naturals 0 ∧
    (headerPrepared input s).nr 130 = 16 + 4 * input.naturals 0 ∧
    (headerPrepared input s).rr 120 = input.reals 0 ∧
    (headerPrepared input s).rr 121 = input.reals 1 ∧
    (headerPrepared input s).rr 123 = 1 + input.reals 0 / 4 ∧
    (headerPrepared input s).rr 124 = 512 / (input.reals 0 / 4) ^ 2 ∧
    (headerPrepared input s).rr 125 = 1 ∧
    (headerPrepared input s).rr 127 = 0 ∧
    (headerPrepared input s).rr 128 = (1 + input.reals 0 / 8) / (1 + input.reals 0 / 4) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.1.1.2.1

theorem headerLoopStore_zero :
  ∀ (input : RAMInput) (s : Store),
  headerLoopStore (headerPrepared input s) 0 = headerPrepared input s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.1.1.2.2

theorem headerBody_run :
  ∀ (input : RAMInput) (s : Store) (k : ℕ)
    (hone : s.nr 126 = 1) (hrone : s.rr 125 = 1),
  Run input headerBody (headerLoopStore s k) (headerLoopStore s (k + 1)) 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.1.2.1

theorem headerLoop_run :
  ∀ (input : RAMInput) (s : Store) (x : ℝ)
    (hone : s.nr 126 = 1) (hrone : s.rr 125 = 1) (hx : s.rr 124 = x)
    (k remaining : ℕ) (hcount : k + remaining = Nat.ceil x),
  Run input headerLoop (headerLoopStore s k)
      (headerLoopStore s (Nat.ceil x)) (4 * remaining + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.1.2.2.1

theorem headerCmd_run :
  ∀ (input : RAMInput) (s : Store),
  Run input headerCmd s (headerResult input s)
      (37 + 4 * Nat.ceil (512 / (input.reals 0 / 4) ^ 2)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.1.2.2.2

theorem headerResult_header :
  ∀ (I : Instance) (ε : ℝ) (s : Store),
  (headerResult (encodeInput I ε) s).nm 0 = outerQ ε ∧
    (headerResult (encodeInput I ε) s).nm 1 = I.source ∧
    (headerResult (encodeInput I ε) s).nm 2 = I.graph.n ∧
    (headerResult (encodeInput I ε) s).rm 0 = (1 + ε / 8) / (1 + ε / 4) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.2.1.1

theorem headerResult_memory_frame :
  ∀ (input : RAMInput) (s : Store) (a : ℕ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) (h2 : a ≠ 2),
  (headerResult input s).nm a = s.nm a ∧ (headerResult input s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.2.1.2.1

end Preprocess
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.NatToReal
open Structured

theorem run_atoms :
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (atoms as) s (evalAtoms input as s) as.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.2.1.2.2

theorem powerBody_run :
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  Run input powerBody (powerState s k) (powerState s (k+1)) 3 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.2.2.1.1

theorem powerLoop_run :
  ∀ (input : RAMInput) (s : Store) (n k d : ℕ)
    (hn : s.nr 66 = n+1) (hlo : 2 ^ (k+d) ≤ n) (hhi : n < 2 ^ (k+d+1)),
  Run input powerLoop (powerState s k) (powerState s (k+d)) (5*d+1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.2.2.1.2

theorem convertBody_run :
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 65 = 1)
    (hpos : 0 < s.nr 61),
  Run input convertBody s (bodyResult s (Nat.log 2 (s.nr 61)))
      (7 + 5 * Nat.log 2 (s.nr 61)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.2.2.2.1

theorem Frame.refl :
  ∀ (s : Store),
  Frame s s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.1.2.2.2.2

theorem Frame.trans :
  ∀ {s t u : Store} (h : Frame s t) (h' : Frame t u),
  Frame s u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.1.1.1

theorem bodyResult_frame :
  ∀ (s : Store) (k : ℕ),
  Frame s (bodyResult s k) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.1.1.2.1

theorem convertLoop_run :
  ∀ (input : RAMInput) (h : ℕ) (s : Store)
    (hz : s.nr 64 = 0) (hone : s.nr 65 = 1) (hb : s.nr 61 < 2 ^ h),
  ∃ (t : Store) (steps : ℕ), Run input convertLoop s t steps ∧
      t.nr 61 = 0 ∧ t.rr 60 = s.rr 60 + s.nr 61 ∧
      steps ≤ 14 * h ^ 2 + 1 ∧ Frame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.1.1.2.2

theorem convertCmd_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ (t : Store) (steps : ℕ), Run input convertCmd s t steps ∧
      t.rr 60 = (s.nr 60 : ℝ) ∧
      steps ≤ 14 * (Nat.log 2 (s.nr 60) + 1) ^ 2 + 5 ∧ Frame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.1.2.1

end NearLinearRSP.TwoResources.Mission.NatToReal
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Scan

theorem positives_append :
  ∀ (xs ys : List (ℝ × ℝ)),
  positives (xs++ys) = positives xs ++ positives ys :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.1.2.2.1

theorem minimum_append :
  ∀ (xs : List ℝ) (x : ℝ),
  (xs++[x]).foldl min ((xs++[x]).headD 1) =
      if xs.isEmpty then x else min (xs.foldl min (xs.headD 1)) x :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.1.2.2.2

theorem addSample_summarize :
  ∀ (xs : List (ℝ × ℝ)) (x : ℝ × ℝ),
  addSample (summarize xs) x = summarize (xs++[x]) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.1.1

theorem prefixSummary_succ :
  ∀ (input : RAMInput) (k : ℕ),
  prefixSummary input (k+1) = addSample (prefixSummary input k) (sample input k) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.1.2.1

theorem encoded_samples :
  ∀ (I : Instance) (ε : ℝ),
  (List.range I.graph.edges.length).map (sample (encodeInput I ε)) = edgeSamples I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.1.2.2

theorem max_fold_filter_positive :
  ∀ (xs : List ℝ) (a : ℝ) (ha : 0 ≤ a),
  xs.foldl max a = (xs.filter (0 < ·)).foldl max a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.2.1.1

theorem summarize_edgeSamples :
  ∀ (I : Instance),
  (summarize (edgeSamples I)).found = !(positiveLengths I).isEmpty ∧
    (summarize (edgeSamples I)).minimum = firstPositiveLength I ∧
    (summarize (edgeSamples I)).maximum = largestLength I ∧
    (summarize (edgeSamples I)).sumLength =
      (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum ∧
    (summarize (edgeSamples I)).sumCost =
      (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.2.1.2

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Scan
open Structured

theorem minCmd_run :
  ∀ (input : RAMInput) (s : Store) (dst src : ℕ),
  ∃ n ≤ 3, Run input (minCmd dst src) s (minResult s dst src) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.2.2.1

theorem maxCmd_run :
  ∀ (input : RAMInput) (s : Store) (dst src : ℕ),
  ∃ n ≤ 3, Run input (maxCmd dst src) s (maxResult s dst src) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.2.2.2

theorem positiveCmd_run :
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 153 = 0) (hrz : s.rr 156 = 0),
  ∃ n ≤ 6, Run input positiveCmd s (positiveResult input s) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.1.1.1

theorem scanBody_run :
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 153 = 0) (hrz : s.rr 156 = 0),
  ∃ n ≤ 16, Run input scanBody s (scanBodyResult input s) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.1.1.2.1

theorem scanBody_values :
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 154 = 1)
    (hflag : s.nr 150 = 0 ∨ s.nr 150 = 1),
  let t := scanBodyResult input s
  let l := input.reals (s.nr 151)
  let c := input.reals (s.nr 151+1)
  t.nr 151 = s.nr 151+2 ∧ t.nr 152 = s.nr 152+1 ∧
  t.nr 150 = (if 0 < l then 1 else s.nr 150) ∧
  t.rr 150 = (if 0 < l then if s.nr 150 = 0 then l else min (s.rr 150) l else s.rr 150) ∧
  t.rr 151 = max (s.rr 151) l ∧ t.rr 152 = s.rr 152+l ∧ t.rr 153 = s.rr 153+c :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.1.1.2.2

theorem scan_init_rep :
  ∀ (input : RAMInput) (s : Store),
  ScanRep input (input.naturals 1) 0 (evalAtoms input scanInitOps s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.1.2.1

theorem scan_step_rep :
  ∀ (input : RAMInput) (m k : ℕ) (s : Store)
    (h : ScanRep input m k s),
  ∃ n ≤ 16, Run input scanBody s (scanBodyResult input s) n ∧
      ScanRep input m (k+1) (scanBodyResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.1.2.2.1

theorem scanCmd_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ out steps, Run input scanCmd s out steps ∧
      ScanRep input (input.naturals 1) (input.naturals 1) out ∧
      steps ≤ 18*input.naturals 1+13 ∧ out.nm = s.nm ∧ out.rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.1.2.2.2

theorem scan_encoded_correct :
  ∀ (I : Instance) (ε : ℝ) (s : Store),
  ∃ out steps, Run (encodeInput I ε) scanCmd s out steps ∧
      out.rr 150 = firstPositiveLength I ∧ out.rr 151 = largestLength I ∧
      out.rr 152 = (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum ∧
      out.rr 153 = (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum ∧
      out.nr 150 = (if (positiveLengths I).isEmpty then 0 else 1) ∧
      steps ≤ 20*(I.graph.edges.length+1) ∧ out.nm = s.nm ∧ out.rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Scan
open Structured

theorem scan_nat_frame :
  ∀ (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input scanCmd s t steps) (hr : r < 150 ∨ 159 < r),
  t.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.2.1.2.1

theorem scan_real_frame :
  ∀ (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input scanCmd s t steps) (hr : r < 150 ∨ 156 < r),
  t.rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.2.1.2.2

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem CoreRegs.transfer :
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : CoreRegs I ε s)
    (hn : ∀r, 121 ≤ r → r ≤ 130 → t.nr r = s.nr r)
    (hr : ∀r, 121 ≤ r → r ≤ 128 → t.rr r = s.rr r),
  CoreRegs I ε t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.2.2.1.1

theorem headerResult_core :
  ∀ (I : Instance) (ε : ℝ) (s : Store),
  CoreRegs I ε (headerResult (encodeInput I ε) s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.2.2.1.2

theorem scalarCmd_run :
  ∀ (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1),
  ∃ out steps, Run (encodeInput I ε) scalarCmd initialStore out steps ∧
      ScalarReady I ε out ∧
      steps ≤ 4*outerQ ε + 14*(Nat.log 2 I.graph.n+1)^2 +
        20*I.graph.edges.length + 4*(outerInputs I ε).length + 80 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.2.2.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Address
open Structured

theorem standalone_Mission_RAMAddress__store_eq :
  ∀ (s t : Store) (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm),
  s = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.2.2.2.2

theorem standalone_Mission_RAMAddress__body_run :
  ∀ (input : RAMInput) (s : Store) (addr k : ℕ)
    (hone : s.nr 47 = 1),
  Run input addressBody (loopStore s addr (k + 1))
      (loopStore s (addr + s.nr 41) k) 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.1.1.1

theorem loop_run :
  ∀ (input : RAMInput) (s : Store) (addr k : ℕ)
    (hone : s.nr 47 = 1) (hzero : s.nr 48 = 0),
  Run input addressLoop (loopStore s addr k)
      (loopStore s (addr + s.nr 41 * k) 0) (4 * k + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.1.1.2.1

theorem addressCmd_run :
  ∀ (input : RAMInput) (s : Store),
  Run input addressCmd s (addressResult s) (8 + 4 * s.nr 42) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.1.1.2.2

theorem addressResult_value :
  ∀ (s : Store),
  (addressResult s).nr 44 = s.nr 40 + s.nr 41 * s.nr 42 + 4 * s.nr 43 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.1.2.1.1

theorem addressResult_frame :
  ∀ (s : Store) (r : ℕ)
    (h44 : r ≠ 44) (h45 : r ≠ 45) (h46 : r ≠ 46)
    (h47 : r ≠ 47) (h48 : r ≠ 48),
  (addressResult s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.1.2.1.2

theorem addressResult_memory :
  ∀ (s : Store),
  (addressResult s).rr = s.rr ∧ (addressResult s).nm = s.nm ∧
      (addressResult s).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.1.2.2.1

theorem rectangle_index_lt :
  ∀ (q i j : ℕ) (hi : i < q) (hj : j < q),
  i * q + j < q ^ 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.1.2.2.2

theorem address_cost_le_rectangle :
  ∀ (q i j : ℕ) (hi : i < q) (hj : j < q),
  8 + 4 * (i * q + j) ≤ 8 + 4 * q ^ 2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.2.1.1

theorem tableAddress_stride :
  ∀ (I : Instance) (ε : ℝ) (r v i j : ℕ),
  tableAddress I ε r v i j = tableBase I ε r +
      (4 * I.graph.n) * (i * outerQ ε + j) + 4 * v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.2.1.2.1

theorem tableAddress_next_cost :
  ∀ (I : Instance) (ε : ℝ) (r v i j : ℕ),
  tableAddress I ε r v i (j + 1) = tableAddress I ε r v i j + 4 * I.graph.n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.2.1.2.2

theorem tableAddress_next_length :
  ∀ (I : Instance) (ε : ℝ) (r v i j : ℕ),
  tableAddress I ε r v (i + 1) j = tableAddress I ε r v i j +
      4 * I.graph.n * outerQ ε :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.2.2.1.1

theorem tableAddress_change_vertex :
  ∀ (I : Instance) (ε : ℝ) (r v u i j : ℕ),
  tableAddress I ε r v i j - 4 * v + 4 * u = tableAddress I ε r u i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.2.2.1.2

end Address
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem layoutFirst_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input layoutFirst s = layoutFirstResult s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.2.2.2.1

theorem layoutSecond_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input layoutSecond s = layoutSecondResult s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.2.2.2.2.2

theorem layoutThird_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input layoutThird s = layoutThirdResult s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.1.1.1

theorem layoutFinish_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input layoutFinish s = layoutFinishResult s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.1.1.2.1

theorem layout_counts :
  ∀ (input : RAMInput) (s : Store),
  (layoutState1 input s).nr 42 = s.nr 124 ∧
    (layoutState2 input s).nr 42 = s.nr 124 ∧
    (layoutState3 input s).nr 42 = s.nr 132 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.1.1.2.2

theorem layoutCmd_run :
  ∀ (input : RAMInput) (s : Store),
  Run input layoutCmd s (layoutResult input s)
      (55 + 8 * s.nr 124 + 4 * s.nr 132) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.1.2.1

theorem layoutResult_values :
  ∀ (input : RAMInput) (s : Store),
  (layoutResult input s).nr 133 = s.nr 129 * s.nr 124 ^ 2 ∧
    (layoutResult input s).nr 134 = s.nr 130 + s.nr 129 * s.nr 124 ^ 2 * s.nr 132 ∧
    (layoutResult input s).nr 135 = (layoutResult input s).nr 134 ∧
    (layoutResult input s).nr 141 = (layoutResult input s).nr 134 + s.nr 124 + 64 ∧
    (layoutResult input s).nr 137 = (layoutResult input s).nr 141 + s.nr 121 ∧
    (layoutResult input s).nr 142 = (layoutResult input s).nr 141 + 2 * s.nr 121 ∧
    (layoutResult input s).nr 139 = (layoutResult input s).nr 141 + 3 * s.nr 121 ∧
    (layoutResult input s).nm 6 = (layoutResult input s).nr 135 ∧
    (layoutResult input s).nm 7 = (layoutResult input s).nr 141 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.1.2.2.1

theorem layoutResult_headers :
  ∀ (input : RAMInput) (s : Store),
  (layoutResult input s).nr 138 = s.nr 129 * s.nr 124 ∧
    (layoutResult input s).nm 4 = s.nr 129 ∧
    (layoutResult input s).nm 5 = s.nr 129 * s.nr 124 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.1.2.2.2

theorem layoutResult_memory_frame :
  ∀ (input : RAMInput) (s : Store) (a : ℕ)
    (h4 : a ≠ 4) (h5 : a ≠ 5) (h6 : a ≠ 6) (h7 : a ≠ 7),
  (layoutResult input s).nm a = s.nm a ∧ (layoutResult input s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem powerCacheBody_eval :
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  evalAtoms input powerCacheBodyOps (powerCacheState s k) = powerCacheState s (k+1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.2.1.2.1

theorem powerCacheBody_run :
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  Run input (.atoms powerCacheBodyOps) (powerCacheState s k) (powerCacheState s (k+1)) 4 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.2.1.2.2

theorem powerCacheLoop_run :
  ∀ (input : RAMInput) (s : Store) (k d : ℕ)
    (he : k+d = s.nr 124),
  Run input powerCacheLoop (powerCacheState s k) (powerCacheState s (k+d)) (6*d+1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.2.2.1.1

theorem powerCacheCmd_run :
  ∀ (input : RAMInput) (s : Store),
  Run input powerCacheCmd s (powerCacheState s (s.nr 124)) (6*s.nr 124+5) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.2.2.1.2

theorem powerCache_values :
  ∀ (s : Store) (a : ℕ) (ha : a < s.nr 124),
  (powerCacheState s (s.nr 124)).rm (s.nr 135+a) = s.rr 128^a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.2.2.2.1

theorem powerCache_frame :
  ∀ (s : Store) (a : ℕ)
    (ha : a < s.nr 135 ∨ s.nr 135+s.nr 124 ≤ a),
  (powerCacheState s (s.nr 124)).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.1.2.2.2.2

theorem powerCache_natMemory :
  ∀ (s : Store),
  (powerCacheState s (s.nr 124)).nm = s.nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

theorem prepend_run :
  ∀ (input : RAMInput) (s : Store) (hone : s.nr 31 = 1),
  Run input prependCmd s (prependResult s) 3 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.1.2.1

theorem storesList_cons :
  ∀ (mem : ℕ → ℕ) (base u : ℕ) (xs : List ℕ)
    (hb : 0 < base) (h : StoresList mem base xs),
  StoresList (Function.update mem (base - 1) u) (base - 1) (u :: xs) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.1.2.2

theorem storesList_map :
  ∀ (mem : ℕ → ℕ) (base : ℕ) (xs : List ℕ)
    (h : StoresList mem base xs),
  (List.range xs.length).map (fun k => mem (base + k)) = xs :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.2.1

theorem prepend_stores :
  ∀ (s : Store) (xs : List ℕ)
    (hlen : s.nr 2 = xs.length) (hbase : 0 < s.nr 3)
    (hmem : StoresList s.nm (s.nr 3) xs),
  (prependResult s).nr 2 = (s.nr 0 :: xs).length ∧
    StoresList (prependResult s).nm ((prependResult s).nr 3) (s.nr 0 :: xs) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.2.2.1

theorem prepend_memory_frame :
  ∀ (s : Store) (a : ℕ) (ha : a < s.nr 3 - 1),
  (prependResult s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.1.2.2.2

theorem score_run :
  ∀ (input : RAMInput) (s : Store),
  Run input scoreCmd s (scoreResult input s) 13 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.2.1.1

theorem score_value :
  ∀ (input : RAMInput) (s : Store),
  (scoreResult input s).rr 5 =
      (1 - s.rm (s.nr 27)) +
        s.rm (s.nr 21 + s.nr 16) * s.rr 1 / s.rr 3 +
        s.rm (s.nr 21 + s.nr 17) * s.rr 2 / s.rr 4 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.2.1.2.1

theorem score_nat_frame :
  ∀ (input : RAMInput) (s : Store) (r : ℕ) (h : r ≠ 39),
  (scoreResult input s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.2.1.2.2

theorem score_real_frame :
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (h5 : r ≠ 5) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9)
    (h10 : r ≠ 10) (h13 : r ≠ 13) (h14 : r ≠ 14),
  (scoreResult input s).rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.2.2.1.1

theorem score_memory_frame :
  ∀ (input : RAMInput) (s : Store),
  (scoreResult input s).nm = s.nm ∧ (scoreResult input s).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.2.2.1.2

theorem choose_run :
  ∀ (input : RAMInput) (s : Store),
  Run input chooseCmd s (chooseResult input s) (chooseCost s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.2.2.2.1

theorem choose_cost_le :
  ∀ (s : Store),
  chooseCost s ≤ 6 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.1.2.2.2.2.2

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query

theorem header_lt_outputEnd :
  ∀ (I : Instance) (ε : ℝ) (a : ℕ) (ha : a < 16),
  a < outputEnd I ε :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.1.1.1

theorem target_lt_outputEnd :
  ∀ (I : Instance) (ε : ℝ) (v off : ℕ)
    (hv : v < I.graph.n) (hoff : off < 4),
  targetAddress v + off < outputEnd I ε :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.1.1.2.1

theorem table_lt_outputEnd :
  ∀ (I : Instance) (ε : ℝ) (r v i j off : ℕ)
    (hr : r < (outerInputs I ε).length) (hv : v < I.graph.n)
    (hi : i < outerQ ε) (hj : j < outerQ ε) (hoff : off < 4),
  tableAddress I ε r v i j + off < outputEnd I ε :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.1.1.2.2

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem ScalarReady.numeric :
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : ScalarReady I ε s),
  NumericRegs I ε s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.1.2.1

theorem NumericRegs.transfer :
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : NumericRegs I ε s)
    (hn : ∀r, (121 ≤ r ∧ r ≤ 132) ∨ r = 150 → t.nr r = s.nr r)
    (hr : ∀r, 121 ≤ r → r ≤ 153 → t.rr r = s.rr r),
  NumericRegs I ε t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.1.2.2.1

theorem layoutResult_numeric :
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : NumericRegs I ε s),
  NumericRegs I ε (layoutResult (encodeInput I ε) s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.1.2.2.2

theorem layoutResult_layout :
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : NumericRegs I ε s),
  LayoutRegs I ε (layoutResult (encodeInput I ε) s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.2.1.1

theorem layoutCacheCmd_run :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hs : ScalarReady I ε s),
  ∃ out steps, Run (encodeInput I ε) layoutCacheCmd s out steps ∧
      LayoutReady I ε out ∧ steps = 60+14*outerQ ε+4*(outerInputs I ε).length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.2.1.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem activeStep_register :
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (h140 : r ≠ 140) (h143 : r ≠ 143) (h144 : r ≠ 144)
    (h145 : r ≠ 145) (h146 : r ≠ 146) (h147 : r ≠ 147),
  (activeStep input s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.2.1.2.2

@[simp] theorem activeStep_pointer :
  ∀ (input : RAMInput) (s : Store),
  (activeStep input s).nr 147 = s.nr 147 + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.2.2.1.1

theorem activeScanBody_run :
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1),
  ∃ steps ≤ 10, Run input activeScanBody s (activeStep input s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.2.2.1.2

theorem activeScan_run :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1)
    (hend : s.nr 147 + remaining = s.nr 148),
  ∃ steps ≤ 12 * remaining + 1,
      Run input activeScan s (activeScanResult input remaining s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.2.2.2.1

theorem ActiveRep.loaded :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (input : RAMInput),
  ActiveRep n base array xs (activeLoaded input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.2.2.2.2

theorem ActiveRep.step :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (input : RAMInput)
    (hv : input.naturals (s.nr 147) < n) (hone : s.nr 126 = 1),
  ActiveRep n base array (stableInsert xs (input.naturals (s.nr 147))) (activeStep input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.1.1.1

theorem activeScan_rep :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (n base array : ℕ) (xs : List ℕ) (h : ActiveRep n base array xs s)
    (hone : s.nr 126 = 1)
    (hv : ∀ v ∈ scannedVertices input (s.nr 147) remaining, v < n),
  ActiveRep n base array
      ((scannedVertices input (s.nr 147) remaining).foldl stableInsert xs)
      (activeScanResult input remaining s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.1.1.2.1

theorem scannedVertices_pairs :
  ∀ (input : RAMInput) (start : ℕ) (edges : List (ℕ × ℕ))
    (hinput : ∀ k e, edges[k]? = some e →
      input.naturals (start + 2 * k) = e.1 ∧ input.naturals (start + 2 * k + 1) = e.2),
  scannedVertices input start (2 * edges.length) = edges.flatMap (fun e => [e.1,e.2]) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.1.1.2.2

theorem encoded_scannedVertices :
  ∀ (I : Instance) (ε : ℝ),
  scannedVertices (encodeInput I ε) 3 (2 * I.graph.edges.length) =
      I.graph.edges.flatMap (fun e => [e.1,e.2]) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.1.2.1

theorem activeInitAtoms_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input activeInitAtoms s = activeInitPrepared s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.1.2.2.1

theorem activeInit_run :
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1),
  ∃ steps ≤ 24 * s.nr 122 + 14,
      Run input activeInit s (activeInitResult input s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.1.2.2.2

theorem activeInit_rep :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (base array : ℕ)
    (hm : s.nr 122 = I.graph.edges.length) (hsource : s.nr 123 = I.source)
    (hbase : s.nr 141 = base) (harray : s.nr 142 = array)
    (hsep : base + I.graph.n ≤ array) (hone : s.nr 126 = 1)
    (hzero : ∀ v < I.graph.n, s.nm (base + v) = 0),
  ActiveRep I.graph.n base array (activeVertices I)
      (activeInitResult (encodeInput I ε) s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.1.1

theorem ActiveRep.insert_memory_frame :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (hv : s.nr 140 < n) (hone : s.nr 126 = 1)
    (a : ℕ) (hb : a < base ∨ base + n ≤ a) (ha : a < array ∨ array + n ≤ a),
  (activeResult s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.1.2.1

theorem activeScan_memory_frame :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (n base array : ℕ) (xs : List ℕ) (h : ActiveRep n base array xs s)
    (hone : s.nr 126 = 1)
    (hv : ∀ v ∈ scannedVertices input (s.nr 147) remaining, v < n)
    (a : ℕ) (hb : a < base ∨ base + n ≤ a) (ha : a < array ∨ array + n ≤ a),
  (activeScanResult input remaining s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.1.2.2

theorem activeInit_memory_frame :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (base array : ℕ)
    (hm : s.nr 122 = I.graph.edges.length) (hsource : s.nr 123 = I.source)
    (hbase : s.nr 141 = base) (harray : s.nr 142 = array)
    (hsep : base + I.graph.n ≤ array) (hone : s.nr 126 = 1)
    (hzero : ∀ v < I.graph.n, s.nm (base + v) = 0)
    (a : ℕ) (hb : a < base ∨ base + I.graph.n ≤ a)
    (ha : a < array ∨ array + I.graph.n ≤ a),
  (activeInitResult (encodeInput I ε) s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.2.1.1

theorem activeInit_register_frame :
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1) (r : ℕ)
    (hr : r ∉ ({140, 143, 144, 145, 146, 147, 148} : Finset ℕ)),
  (activeInitResult input s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.2.1.2

theorem activeInit_real_frame :
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1),
  (activeInitResult input s).rr = s.rr ∧ (activeInitResult input s).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.2.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem LayoutRegs.transfer :
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : LayoutRegs I ε s)
    (hn : ∀r, r ∈ ({133,134,135,137,138,139,141,142} : Finset ℕ) → t.nr r=s.nr r),
  LayoutRegs I ε t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.2.2.2

theorem OutputHeaders.transfer :
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : OutputHeaders I ε s)
    (hn : ∀a, a<8 → a≠3 → t.nm a=s.nm a) (hr : t.rm 0=s.rm 0),
  OutputHeaders I ε t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.1.1.1

theorem graphCmd_run :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hs : LayoutReady I ε s),
  ∃ out steps, Run (encodeInput I ε) graphCmd s out steps ∧
      GraphReady I ε out ∧ steps ≤ 35*I.graph.edges.length+21 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.1.1.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

theorem capacityStart_eval :
  ∀ (input : RAMInput) (s : Store),
  capacityStart.eval input s = capacityState s 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.1.1.2.2

theorem capacityDouble_eval :
  ∀ (input : RAMInput) (s : Store) (k : ℕ),
  capacityDouble.eval input (capacityState s k) = capacityState s (k + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.1.2.1

theorem chooseCapacity_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2,
      Run input chooseCapacity s (capacityState s (Nat.clog 2 (s.nr 10))) k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.1.2.2.1

theorem chooseCapacity_bounds :
  ∀ (input : RAMInput) (s : Store) (hn : 0 < s.nr 10),
  ∃ out k, Run input chooseCapacity s out k ∧ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2 ∧
      s.nr 10 ≤ out.nr 11 ∧ out.nr 11 < 2 * s.nr 10 ∧
      out.nm = s.nm ∧ out.rm = s.rm ∧ out.rr = s.rr ∧
      ∀ a, a ≠ 11 → out.nr a = s.nr a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.1.2.2.2

theorem chooseCapacity_exact :
  ∀ (input : RAMInput) (s : Store),
  ∃ out k, Run input chooseCapacity s out k ∧ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2 ∧
      out.nr 11 = 2 ^ Nat.clog 2 (s.nr 10) ∧
      out.nm = s.nm ∧ out.rm = s.rm ∧ out.rr = s.rr ∧
      ∀ a, a ≠ 11 → out.nr a = s.nr a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem GraphReady.transfer :
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : GraphReady I ε s)
    (hn : ∀r, 121≤r → r≤153 → t.nr r=s.nr r)
    (hr : ∀r, 121≤r → r≤153 → t.rr r=s.rr r)
    (hm : t.nm=s.nm) (hrm : t.rm=s.rm),
  GraphReady I ε t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.1.2.1

theorem heapCmd_run :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hs : GraphReady I ε s),
  ∃ out steps, Run (encodeInput I ε) heapCmd s out steps ∧ SetupReady I ε out ∧
      steps≤3*Nat.clog 2 (activeVertices I).length+21 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.1.2.2

theorem setupCmd_run :
  ∀ (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1),
  ∃ out steps, Run (encodeInput I ε) setupCmd initialStore out steps ∧ SetupReady I ε out ∧
      steps≤18*outerQ ε+14*(Nat.log 2 I.graph.n+1)^2+55*I.graph.edges.length+
        8*(outerInputs I ε).length+3*Nat.clog 2 (activeVertices I).length+182 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.2.1.1

theorem SetupReady.capacity_bounds :
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : SetupReady I ε s),
  (activeVertices I).length ≤ s.nr 11 ∧ s.nr 11 < 2*(activeVertices I).length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.2.1.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem GraphReady.runtime :
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : GraphReady I ε s),
  RuntimeReady I ε s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.2.2.1

theorem SetupReady.runtime :
  ∀ {I : Instance} {ε : ℝ} {s : Store} (h : SetupReady I ε s),
  RuntimeReady I ε s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.2.2.2

theorem RuntimeReady.transfer :
  ∀ {I : Instance} {ε : ℝ} {s t : Store} (h : RuntimeReady I ε s)
    (hn : ∀r, 121≤r → r≤153 → t.nr r=s.nr r)
    (hr : ∀r, 121≤r → r≤153 → t.rr r=s.rr r)
    (hhead : ∀a, a<8 → t.nm a=s.nm a)
    (hgraph : ∀a, graphBase I ε≤a → a<linksBase I ε+I.graph.edges.length → t.nm a=s.nm a)
    (hz : t.rm 0=s.rm 0)
    (hcache : ∀a<outerQ ε, t.rm (Query.outputEnd I ε+a)=s.rm (Query.outputEnd I ε+a)),
  RuntimeReady I ε t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.1.1.1

theorem SetupReady.costSentinel_mode :
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s),
  s.rr 280=TreeMode.zeroLength.top I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.1.1.2.1

theorem SetupReady.lengthSentinel_mode :
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s),
  s.rr 281=TreeMode.zeroBudget.top I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.1.1.2.2

theorem RuntimeReady.treeActive :
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : RuntimeReady I ε s),
  ActiveRep I.graph.n (treeAllocation I ε).map (treeAllocation I ε).array (activeVertices I) s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.1.2.1

theorem RuntimeReady.treeAdjacency :
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : RuntimeReady I ε s),
  AdjacencyPrefix I I.graph.edges.length (treeAllocation I ε).heads
      (treeAllocation I ε).links s.nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.1.2.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

theorem run_acyclic :
  ∀ (input : RAMInput) (c : Cmd) (h : c.acyclic = true) (s : Store),
  ∃ n ≤ c.size, Run input c s (c.evalAcyclic input s) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.1.2.2.2

theorem Cmd.atoms_evalAcyclic :
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  (Cmd.atoms as).evalAcyclic input s = evalAtoms input as s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.2.1.1

@[simp] theorem Cmd.atoms_acyclic :
  ∀ (as : List Atom),
  (Cmd.atoms as).acyclic = true :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.2.1.2.1

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

theorem markAccepted_fold :
  ∀ (p : ℕ → Bool) (xs : List ℕ) (b : AnswerBranch),
  xs.foldl (markAccepted p) b =
      if b = .absent then branchFromIndex (xs.find? p) else b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.2.1.2.2

theorem acceptedIndex_zero_budget :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (hC : I.budget = 0),
  acceptedIndex I ε t = none :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.2.2.1.1

theorem acceptedIndex_zero_accuracy :
  ∀ (I : Instance) (t : ℕ),
  acceptedIndex I 0 t = none :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.2.2.1.2

theorem answerBranch_seed_find :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ),
  answerBranch I ε t =
      if answerBranch I 0 t = .absent then branchFromIndex (acceptedIndex I ε t)
      else answerBranch I 0 t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.2.2.2.1

theorem answerBranch_incremental :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ),
  (List.range (outerInputs I ε).length).foldl
      (markAccepted (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A t))))
      (answerBranch I 0 t) = answerBranch I ε t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.2.2.2.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

theorem seedCmd_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ n ≤ 40, Run input seedCmd s (seedResult input s) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.1.1.1

theorem seedResult_values :
  ∀ (input : RAMInput) (s : Store),
  (seedResult input s).nm (s.nr 300) = seedTag s ∧
    (seedTag s = 1 → (seedResult input s).rm (s.nr 300) = 0) ∧
    (seedTag s = 2 → (seedResult input s).rm (s.nr 300) = s.rr 301) ∧
    (∀ a, a ≠ s.nr 300 → (seedResult input s).nm a = s.nm a ∧
      (seedResult input s).rm a = s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.1.1.2.1

theorem markCmd_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ n ≤ 15, Run input markCmd s (markResult input s) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.1.1.2.2

theorem markResult_values :
  ∀ (input : RAMInput) (s : Store),
  (markResult input s).nm (s.nr 300) =
      (if s.nm (s.nr 300) = 0 ∧ (3/4 : ℝ) ≤ s.rr 305 then 3 else s.nm (s.nr 300)) ∧
    (s.nm (s.nr 300) = 0 → (3/4 : ℝ) ≤ s.rr 305 →
      (markResult input s).nm (s.nr 300+1) = s.nr 301 ∧
      (markResult input s).rm (s.nr 300) = s.rr 304) ∧
    (∀ a, a ≠ s.nr 300 → a ≠ s.nr 300+1 →
      (markResult input s).nm a = s.nm a) ∧
    (∀ a, a ≠ s.nr 300 → (markResult input s).rm a = s.rm a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.1.2.1

theorem markResult_unchanged :
  ∀ (input : RAMInput) (s : Store)
    (h : s.nm (s.nr 300) ≠ 0 ∨ s.rr 305 < (3/4 : ℝ)),
  (markResult input s).nm = s.nm ∧ (markResult input s).rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.1.2.2.1

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

theorem LabelRep.finite_iff :
  ∀ {d : Option ℝ} {sentinel value : ℝ}
    (h : LabelRep d sentinel value),
  value < sentinel ↔ d.isSome = true :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.1.2.2.2

theorem seedTag_correct :
  ∀ (I : Instance) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (hsource : s.nr 123 = I.source)
    (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)),
  seedTag s = branchTag (answerBranch I 0 v) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.2.1.1

theorem seedResult_correct :
  ∀ (input : RAMInput) (I : Instance) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (hsource : s.nr 123 = I.source)
    (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)),
  (seedResult input s).nm (s.nr 300) = branchTag (answerBranch I 0 v) ∧
    (∀ d, answerDistance I 0 v = some d → (seedResult input s).rm (s.nr 300) = d) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.2.1.2.1

theorem mark_acceptance :
  ∀ (A : InnerInput) (v : ℕ) (s : Store)
    (h : s.rr 305 = 1 - dpValue A (buildTable A) v 0 0),
  (3/4 : ℝ) ≤ s.rr 305 ↔ accepted A v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.2.1.2.2

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

theorem selectedDistance_answer :
  ∀ (I : Instance) (ε : ℝ) (v : ℕ),
  selectedDistance I ε v (answerBranch I ε v) = answerDistance I ε v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.2.2.1.1

theorem selectedDistance_seed :
  ∀ (I : Instance) (ε : ℝ) (v : ℕ),
  selectedDistance I ε v (answerBranch I 0 v) = answerDistance I 0 v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.2.2.1.2

theorem seed_record :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (ha : s.nr 300 = targetAddress v)
    (hsource : s.nr 123 = I.source) (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)),
  RecordRep I ε v (answerBranch I 0 v) (seedResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.2.2.2.1

theorem mark_record :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (v r : ℕ)
    (A : InnerInput) (b : AnswerBranch) (s : Store)
    (hrec : RecordRep I ε v b s)
    (ha : s.nr 300 = targetAddress v) (hbase : s.nr 301 = tableBase I ε r)
    (hd : s.rr 304 = (1+A.δ)*A.L)
    (hsuccess : (3/4 : ℝ) ≤ s.rr 305 ↔ accepted A v)
    (hA : (outerInputs I ε)[r]? = some A),
  RecordRep I ε v
      (markAccepted (fun j => ((outerInputs I ε)[j]?).any (fun B => decide (accepted B v))) b r)
      (markResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.2.2.2.2

theorem branchesAfter_zero :
  ∀ (I : Instance) (ε : ℝ) (v : ℕ),
  branchesAfter I ε 0 v = answerBranch I 0 v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.1.1.1

theorem branchesAfter_succ :
  ∀ (I : Instance) (ε : ℝ) (k v : ℕ),
  branchesAfter I ε (k+1) v =
      markAccepted (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A v)))
        (branchesAfter I ε k v) k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.1.1.2.1

theorem branchesAfter_end :
  ∀ (I : Instance) (ε : ℝ) (v : ℕ),
  branchesAfter I ε (outerInputs I ε).length v = answerBranch I ε v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.1.1.2.2

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

theorem seedVisitor_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ n ≤ 46, Run input seedVisitor s (seedVisitorResult input s) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.1.2.1.1

theorem seedVisitor_correct :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (ha : s.nr 300 = targetAddress v)
    (hsource : s.nr 123 = I.source) (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rm (targetAddress v+2)))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rm (targetAddress v+3))),
  RecordRep I ε v (answerBranch I 0 v) (seedVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.1.2.1.2

theorem seedVisitor_memory_frame :
  ∀ (input : RAMInput) (s : Store) (a : ℕ)
    (ha : a ≠ s.nr 300),
  (seedVisitorResult input s).nm a = s.nm a ∧
    (seedVisitorResult input s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.1.2.2.1

theorem markVisitor_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ n ≤ 19, Run input markVisitor s (markVisitorResult input s) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.1.2.2.2

theorem markVisitor_correct :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (v r : ℕ)
    (A : InnerInput) (b : AnswerBranch) (s : Store)
    (hrec : RecordRep I ε v b s) (hv : s.nr 307 = v)
    (ha : s.nr 300 = targetAddress v) (hbase : s.nr 301 = tableBase I ε r)
    (hd : s.rr 304 = (1+A.δ)*A.L)
    (hmass : s.rm (tableBase I ε r+4*v) = 1-dpValue A (buildTable A) v 0 0)
    (hA : (outerInputs I ε)[r]? = some A),
  RecordRep I ε v
      (markAccepted (fun j => ((outerInputs I ε)[j]?).any (fun B => decide (accepted B v))) b r)
      (markVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.2.1.1

theorem markVisitor_memory_frame :
  ∀ (input : RAMInput) (s : Store) (a : ℕ)
    (ha : a ≠ s.nr 300) (ha1 : a ≠ s.nr 300+1),
  (markVisitorResult input s).nm a = s.nm a ∧
    (markVisitorResult input s).rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.2.1.2.1

theorem RecordRep.memory_congr :
  ∀ (I : Instance) (ε : ℝ) (v : ℕ) (b : AnswerBranch)
    (s t : Store) (htag : t.nm (targetAddress v) = s.nm (targetAddress v))
    (hbase : t.nm (targetAddress v+1) = s.nm (targetAddress v+1))
    (hd : t.rm (targetAddress v) = s.rm (targetAddress v))
    (h : RecordRep I ε v b s),
  RecordRep I ε v b t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.2.1.2.2

theorem target_record_separate :
  ∀ (v w a b : ℕ) (hvw : v ≠ w) (ha : a < 4) (hb : b < 4),
  targetAddress v+a ≠ targetAddress w+b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.2.2.1.1

theorem seedVisitor_nat_frame :
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [302,304,308,309]),
  (seedVisitorResult input s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.2.2.1.2

theorem seedVisitor_real_frame :
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [300,301,302]),
  (seedVisitorResult input s).rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.2.2.2.1

theorem markVisitor_nat_frame :
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [302,303,304,306,308,309]),
  (markVisitorResult input s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.2.2.2.2.2

theorem markVisitor_real_frame :
  ∀ (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [303,305,306]),
  (markVisitorResult input s).rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.1.1.1

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.ActiveIterator
open Structured

theorem setup_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input setupAtoms s=setup s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.1.1.2.1

theorem prepared_eval :
  ∀ (input : RAMInput) (s : Store),
  evalAtoms input prepareAtoms s=prepared s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.1.1.2.2

theorem advanced_eval :
  ∀ (input : RAMInput) (s : Store),
  incrementAtom.eval input s=advanced s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.1.2.1

theorem setup_state :
  ∀ (array : ℕ) (xs : List ℕ) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj),
  State array xs 0 (setup s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.1.2.2.1

theorem prepared_state :
  ∀ (array : ℕ) (xs : List ℕ) (k : ℕ) (s : Store)
    (h : State array xs k s),
  State array xs k (prepared s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.1.2.2.2

theorem prepared_values :
  ∀ (array : ℕ) (xs : List ℕ) (k : ℕ) (s : Store)
    (h : State array xs k s) (hk : k<xs.length),
  (prepared s).nr 307=xs[k] ∧ (prepared s).nr 300=16+4*xs[k] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.2.1.1

theorem advanced_state :
  ∀ (array : ℕ) (xs : List ℕ) (k : ℕ) (s out : Store)
    (h : State array xs k s) (hf : Frame array xs s out),
  State array xs (k+1) (advanced out) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.2.1.2.1

theorem command_run :
  ∀ (input : RAMInput) (visitor : Cmd) (array : ℕ) (xs : List ℕ)
    (bound : ℕ) (P : ℕ → Store → Prop) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj)
    (hstart : P 0 (setup s))
    (hvisit : ∀ k t, k<xs.length → State array xs k t → P k t →
      ∃ out cost, Run input visitor (prepared t) out cost ∧ cost≤bound ∧
        Frame array xs (prepared t) out ∧ P (k+1) (advanced out)),
  ∃ out cost, Run input (command visitor) s out cost ∧
      State array xs xs.length out ∧ P xs.length out ∧
      cost≤(bound+8)*xs.length+4 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.2.1.2.2

theorem prefixFold_succ :
  ∀ {α : Type} (step : α→ℕ→α) (initial : α)
    (xs : List ℕ) (k : ℕ) (hk : k<xs.length),
  prefixFold step initial xs (k+1)=step (prefixFold step initial xs k) xs[k] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.2.2.1.1

theorem command_fold :
  ∀ {α : Type} (input : RAMInput) (visitor : Cmd) (array : ℕ)
    (xs : List ℕ) (bound : ℕ) (step : α→ℕ→α) (initial : α)
    (Rep : α→Store→Prop) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj)
    (hstart : Rep initial (setup s))
    (hvisit : ∀ k t (hk : k<xs.length), State array xs k t →
      Rep (prefixFold step initial xs k) t →
      ∃ out cost, Run input visitor (prepared t) out cost ∧ cost≤bound ∧
        Frame array xs (prepared t) out ∧
        Rep (step (prefixFold step initial xs k) xs[k]) (advanced out)),
  ∃ out cost, Run input (command visitor) s out cost ∧
      State array xs xs.length out ∧ Rep (xs.foldl step initial) out ∧
      cost≤(bound+8)*xs.length+4 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.2.2.1.2

theorem command_nat_frame :
  ∀ (input : RAMInput) (visitor : Cmd) (s out : Store) (cost r : ℕ)
    (h : Run input (command visitor) s out cost)
    (hv : r∉visitor.natWrites)
    (hr : r∉[300,307,320,321,322,323,324,325]),
  out.nr r=s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.2.2.2.1

theorem command_real_frame :
  ∀ (input : RAMInput) (visitor : Cmd) (s out : Store) (cost r : ℕ)
    (h : Run input (command visitor) s out cost)
    (hv : r∉visitor.realWrites),
  out.rr r=s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.1.2.2.2.2

end NearLinearRSP.TwoResources.Mission.ActiveIterator
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem standalone_Mission_QueueSource__fold_keeps :
  ∀ {α β : Type u_1} (f : β → α → β) (Inv : β → Prop)
    (xs : List α) (s : β) (hs : Inv s) (hstep : ∀ s a, Inv s → Inv (f s a)),
  Inv (xs.foldl f s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).2.2.2.1.1.2.1.1.1

theorem standalone_Mission_QueueSource__fold_sets :
  ∀ {α β : Type u_1} (f : β → α → β) (Inv P : β → Prop)
    (xs : List α) (a : α) (ha : a ∈ xs) (s : β) (hs : Inv s)
    (hInv : ∀ s b, Inv s → Inv (f s b))
    (hset : ∀ s, Inv s → P (f s a))
    (hkeep : ∀ s b, Inv s → P s → P (f s b)),
  P (xs.foldl f s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).2.2.2.1.1.2.1.1.2.1

theorem buildRow_range :
  ∀ (A : InnerInput) (T : Table) (i : ℕ) (hT : TableRange T),
  TableRange (buildRow A T i) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.1.1.2.2

theorem buildRow_other_row :
  ∀ (A : InnerInput) (T : Table) (i v a b : ℕ)
    (h : a ≠ i),
  buildRow A T i v a b = T v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.1.2.1

theorem buildRow_source_zero :
  ∀ (A : InnerInput) (T : Table) (i j : ℕ)
    (hj : j < tickLimit A) (hT : TableRange T),
  (buildRow A T i A.I.source i j).value = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.1.2.2.1

theorem buildTable_source_value :
  ∀ (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A),
  (buildTable A A.I.source i j).value = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.1.2.2.2

theorem dpValue_buildTable_source :
  ∀ (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A),
  dpValue A (buildTable A) A.I.source i j = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.2.1.1

theorem popLayer_inactive_frame :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hsub : S.queue ⊆ activeVertices A.I) (v a b : ℕ) (hv : v ∉ activeVertices A.I),
  (popLayer A i j S).table v a b = S.table v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.2.1.2.1

theorem queueRun_inactive_frame :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hsub : S.queue ⊆ activeVertices A.I) (v a b : ℕ) (hv : v ∉ activeVertices A.I),
  (queueRun A i j n S).table v a b = S.table v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.2.1.2.2

theorem buildLayer_inactive_frame :
  ∀ (A : InnerInput) (T : Table) (i j v a b : ℕ)
    (hv : v ∉ activeVertices A.I),
  buildLayer A T i j v a b = T v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.2.2.1.1

theorem standalone_Mission_QueueInactive__fold_const :
  ∀ {α β γ : Type u_1} (f : β → α → β) (p : β → γ)
    (xs : List α) (s : β) (h : ∀ s a, p (f s a) = p s),
  p (xs.foldl f s) = p s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{u_1}).2.2.2.1.1.2.2.2.1.2

theorem buildRow_inactive_frame :
  ∀ (A : InnerInput) (T : Table) (i v a b : ℕ)
    (hv : v ∉ activeVertices A.I),
  buildRow A T i v a b = T v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.2.2.2.1

theorem buildTable_inactive :
  ∀ (A : InnerInput) (v i j : ℕ) (hv : v ∉ activeVertices A.I),
  buildTable A v i j = ⟨1, .lengthTick, 0⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.2.2.2.2

theorem dpValue_buildTable_inactive :
  ∀ (A : InnerInput) (v i j : ℕ)
    (hv : v ∉ activeVertices A.I),
  dpValue A (buildTable A) v i j = 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.1.1.1

theorem accepted_active :
  ∀ (A : InnerInput) (v : ℕ) (h : accepted A v),
  v ∈ activeVertices A.I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.1.1.2.1

theorem shortestTree_finite_active :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d),
  v ∈ activeVertices I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.1.1.2.2

theorem shortestTree_inactive_distance :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (hv : v ∉ activeVertices I),
  (shortestTree I allow w v).distance = none :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.1.2.1

theorem answerBranch_active :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t ≠ .absent),
  t ∈ activeVertices I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.1.2.2.1

theorem answerBranch_inactive :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I),
  answerBranch I ε t = .absent :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.1.2.2.2

theorem answerDistance_inactive :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I),
  answerDistance I ε t = none :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.2.1.1

theorem answerPath_inactive :
  ∀ (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I),
  answerPath I ε t = none :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.2.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

theorem TargetFrame.refl :
  ∀ (I : Instance) (s : Store),
  TargetFrame I s s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.2.1.2.2

theorem TargetFrame.trans :
  ∀ {I : Instance} {s t u : Store}
    (h : TargetFrame I s t) (h' : TargetFrame I t u),
  TargetFrame I s u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.2.2.1.1

theorem TargetFrame.outside :
  ∀ {I : Instance} {s t : Store} (h : TargetFrame I s t)
    (a : ℕ) (ha : a < 16 ∨ 16+4*I.graph.n ≤ a),
  t.nm a = s.nm a ∧ t.rm a = s.rm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.2.2.1.2

theorem TargetFrame.treeParents :
  ∀ {I : Instance} {s t : Store} (h : TargetFrame I s t)
    (v : ℕ),
  t.nm (targetAddress v+2) = s.nm (targetAddress v+2) ∧
      t.nm (targetAddress v+3) = s.nm (targetAddress v+3) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.2.2.2.1

theorem seedVisitor_targetFrame :
  ∀ (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v),
  TargetFrame I s (seedVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.2.2.2.2

theorem markVisitor_targetFrame :
  ∀ (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v),
  TargetFrame I s (markVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.1.1.1

theorem setAnswer_fold_apply :
  ∀ (xs : List ℕ) (f value : ℕ → AnswerBranch) (v : ℕ),
  (xs.foldl (setAnswer value) f) v = if v ∈ xs then value v else f v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.1.1.2.1

theorem updateAnswer_fold_apply :
  ∀ (xs : List ℕ) (hxs : xs.Nodup)
    (f : ℕ → AnswerBranch) (change : ℕ → AnswerBranch → AnswerBranch) (v : ℕ),
  (xs.foldl (updateAnswer change) f) v = if v ∈ xs then change v (f v) else f v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.1.1.2.2

theorem RecordMap.initial_absent :
  ∀ (I : Instance) (ε : ℝ) (s : Store)
    (h : ∀ v < I.graph.n, s.nm (targetAddress v) = 0),
  RecordMap I ε (fun _ => .absent) s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.1.2.1.1

theorem RecordMap.seed_step :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (f : ℕ → AnswerBranch)
    (v : ℕ) (s : Store) (ha : s.nr 300 = targetAddress v)
    (h : RecordMap I ε f s)
    (hnew : RecordRep I ε v (answerBranch I 0 v) (seedVisitorResult input s)),
  RecordMap I ε (setAnswer (answerBranch I 0) f v) (seedVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.1.2.1.2

theorem RecordMap.mark_step :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (f : ℕ → AnswerBranch)
    (v : ℕ) (change : ℕ → AnswerBranch → AnswerBranch) (s : Store)
    (ha : s.nr 300 = targetAddress v) (h : RecordMap I ε f s)
    (hnew : RecordRep I ε v (change v (f v)) (markVisitorResult input s)),
  RecordMap I ε (updateAnswer change f v) (markVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.1.2.2.1

theorem seed_fold_exact :
  ∀ (I : Instance) (v : ℕ),
  ((activeVertices I).foldl (setAnswer (answerBranch I 0)) (fun _ => .absent)) v =
      answerBranch I 0 v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.1.2.2.2

theorem mark_fold_exact :
  ∀ (I : Instance) (ε : ℝ) (r v : ℕ),
  ((activeVertices I).foldl
      (updateAnswer (fun w b => markAccepted
        (fun j => ((outerInputs I ε)[j]?).any (fun A => decide (accepted A w))) b r))
      (branchesAfter I ε r)) v = branchesAfter I ε (r+1) v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.2.1.1

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

theorem seedVisitor_world :
  ∀ (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (ha : s.nr 300 = targetAddress v) (h : SeedWorld I s),
  SeedWorld I (seedVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.2.1.2.1

theorem seedVisitor_iteratorFrame :
  ∀ (input : RAMInput) (I : Instance) (array : ℕ) (s : Store)
    (v : ℕ) (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v)
    (hspace : 16+4*I.graph.n ≤ array),
  ActiveIterator.Frame array (activeVertices I) s (seedVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.2.1.2.2

theorem seedRecords_run :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (array : ℕ) (s : Store)
    (hworld : SeedWorld I s)
    (ha : s.nr 142 = array) (hn : s.nr 143 = (activeVertices I).length)
    (hmem : ∀ k (hk : k < (activeVertices I).length), s.nm (array+k) = (activeVertices I)[k])
    (hspace : 16+4*I.graph.n ≤ array)
    (hzero : ∀ v < I.graph.n, s.nm (targetAddress v) = 0),
  ∃ out cost, Run input seedRecordsCmd s out cost ∧
      SeedWorld I out ∧ RecordMap I ε (answerBranch I 0) out ∧
      TargetFrame I s out ∧ cost ≤ 54*(activeVertices I).length+4 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.2.2.1.1

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem runtime_outputs_queryReady :
  ∀ (I : Instance) (ε : ℝ) (s : Store)
    (h : RuntimeReady I ε s) (hp : OutputParents I s)
    (hr : TargetRecords.RecordMap I ε (answerBranch I ε) s)
    (ht : CompletedTables I ε (outerInputs I ε).length s) (pc : ℕ),
  Query.QueryReady I ε (s.at pc) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.2.2.1.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem SetupReady.treeStart :
  ∀ {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s),
  (treeAllocation I ε).Registers .zeroLength (zeroTreePrepared .zeroLength s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.2.2.2.1

theorem TreeAllocation.protected_before_winner :
  ∀ {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (a : ℕ) (ha : a < E.W)
    (hfields : ∀ v ∈ activeVertices I,a ≠ targetAddress v+mode.offset),
  TreeWholeProtected E mode a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.2.2.2.2.2

theorem treeAllocation_protected_before_map :
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < graphBase I ε)
    (hfields : ∀ v ∈ activeVertices I,a ≠ targetAddress v+mode.offset),
  TreeWholeProtected (treeAllocation I ε) mode a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.1.1.1

theorem treeAllocation_header_protected :
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < 8),
  TreeWholeProtected (treeAllocation I ε) mode a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.1.1.2.1

theorem treeAllocation_graph_protected :
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (hlo : graphBase I ε ≤ a)
    (hhi : a < linksBase I ε+I.graph.edges.length),
  TreeWholeProtected (treeAllocation I ε) mode a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.1.1.2.2

theorem treeAllocation_post_targets_protected :
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (hlo : 16+4*I.graph.n ≤ a) (hhi : a < graphBase I ε),
  TreeWholeProtected (treeAllocation I ε) mode a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.1.2.1

theorem treeAllocation_cache_protected :
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < outerQ ε),
  TreeWholeProtected (treeAllocation I ε) mode (Query.outputEnd I ε+a) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.1.2.2.1

theorem treeAllocation_tag_protected :
  ∀ (I : Instance) (ε : ℝ) (mode : TreeMode)
    (v : ℕ) (hv : v < I.graph.n),
  TreeWholeProtected (treeAllocation I ε) mode (targetAddress v) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.1.2.2.2

theorem zeroTrees_nat_scalar_frame :
  ∀ (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input zeroTreesCmd s out cost) (hlo : 121 ≤ r) (hhi : r ≤ 153),
  out.nr r=s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.2.1.1

theorem zeroTrees_real_scalar_frame :
  ∀ (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input zeroTreesCmd s out cost) (hlo : 121 ≤ r) (hhi : r ≤ 153),
  out.rr r=s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.2.1.2.1

theorem ZeroTreeMemory.seedWorld :
  ∀ (I : Instance) (s : Store) (h : ZeroTreeMemory I s)
    (hs : s.nr 123=I.source) (hb : s.rr 121=I.budget)
    (hL : s.rr 280=TreeMode.zeroLength.top I)
    (hC : s.rr 281=TreeMode.zeroBudget.top I),
  TargetRecords.SeedWorld I s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.2.1.2.2

theorem zeroTrees_ready :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hSetup : SetupReady I ε s),
  ∃ out steps, Run (encodeInput I ε) zeroTreesCmd s out steps ∧
      RuntimeReady I ε out ∧ OutputParents I out ∧ TargetRecords.SeedWorld I out ∧
      FutureZero I ε 0 out ∧
      (∀ v < I.graph.n,out.nm (targetAddress v)=0) ∧ out.nr 11=queueCapacity I ∧
      steps ≤ 2*(15*queueCapacity I+
        (38*Nat.clog 2 (2*queueCapacity I)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*queueCapacity I)+46)*I.graph.edges.length+7)+6 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.2.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

theorem markVisitor_world :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (r : ℕ)
    (A : InnerInput) (s : Store) (v : ℕ) (hv : v < I.graph.n)
    (ha : s.nr 300 = targetAddress v) (h : MarkWorld I ε r A s),
  MarkWorld I ε r A (markVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.2.2.1.2

theorem markVisitor_iteratorFrame :
  ∀ (input : RAMInput) (I : Instance) (array : ℕ) (s : Store)
    (v : ℕ) (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v)
    (hspace : 16+4*I.graph.n ≤ array),
  ActiveIterator.Frame array (activeVertices I) s (markVisitorResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.2.2.2.1

theorem markRecords_run :
  ∀ (input : RAMInput) (I : Instance) (ε : ℝ) (r : ℕ) (A : InnerInput)
    (hA : (outerInputs I ε)[r]? = some A) (array : ℕ) (s : Store)
    (hworld : MarkWorld I ε r A s) (hrecords : RecordMap I ε (branchesAfter I ε r) s)
    (ha : s.nr 142 = array) (hn : s.nr 143 = (activeVertices I).length)
    (hmem : ∀ k (hk : k < (activeVertices I).length), s.nm (array+k) = (activeVertices I)[k])
    (hspace : 16+4*I.graph.n ≤ array),
  ∃ out cost, Run input markRecordsCmd s out cost ∧ MarkWorld I ε r A out ∧
      RecordMap I ε (branchesAfter I ε (r+1)) out ∧ TargetFrame I s out ∧
      cost ≤ 27*(activeVertices I).length+4 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.2.2.2.2

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured

theorem prepared_values :
  ∀ (input : RAMInput) (s : Store),
  (prepared input s).nr 200 = s.nr 244 ∧ (prepared input s).nr 201 = s.nr 124 ∧
    (prepared input s).nr 202 = s.nr 125 ∧ (prepared input s).nr 203 = s.nr 244+s.nr 133 ∧
    (prepared input s).nr 204 = s.nr 143 ∧ (prepared input s).nr 205 = s.nr 247 ∧
    (prepared input s).nr 206 = s.nr 248 ∧ (prepared input s).nr 207 = s.nr 249 ∧
    (prepared input s).nr 208 = s.nr 250 ∧ (prepared input s).nr 209 = s.nr 138 ∧
    (prepared input s).rr 200 = s.rr 127/(s.rr 244*s.rr 243) ∧
    (prepared input s).rr 201 = s.rr 245 ∧ (prepared input s).rr 202 = s.rr 128 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.1.1.1

theorem markPrepared_values :
  ∀ (input : RAMInput) (s : Store),
  (markPrepared input s).nr 301 = s.nr 244 ∧
    (markPrepared input s).rr 304 = s.rr 123*s.rr 243 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.1.1.2.1

theorem advanced_values :
  ∀ (input : RAMInput) (s : Store),
  (advanced input s).nr 243 = s.nr 243+s.nr 126 ∧
    (advanced input s).nr 244 = s.nr 244+s.nr 133 ∧
    (advanced input s).rr 243 = s.rr 243*s.rr 123 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.1.1.2.2

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
namespace Mission

theorem poissonCountMass_recurrence :
  ∀ (μ : ℝ) (k : ℕ),
  ActuarialValuation.poissonCountMass μ (k + 1) =
      ActuarialValuation.poissonCountMass μ k * μ / ((k : ℝ) + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.1.2.1

theorem poisson_prefix :
  ∀ (input : RAMInput),
  execute poissonProgram input 10 initialState =
      poissonLoopState (input.reals 0) (input.naturals 0) 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.1.2.2.1

theorem poisson_iteration :
  ∀ (input : RAMInput) (μ : ℝ) (n k : ℕ)
    (hk : k < n),
  execute poissonProgram input 6 (poissonLoopState μ n k) =
      poissonLoopState μ n (k + 1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.1.2.2.2

theorem poisson_iterations :
  ∀ (input : RAMInput) (μ : ℝ) (n k : ℕ)
    (hk : k ≤ n),
  execute poissonProgram input (6 * k) (poissonLoopState μ n 0) =
      poissonLoopState μ n k :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.2.1.1

theorem poisson_exit :
  ∀ (input : RAMInput) (μ : ℝ) (n : ℕ),
  execute poissonProgram input 4 (poissonLoopState μ n n) =
      poissonFinalState μ n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.2.1.2.1

theorem poisson_evaluation :
  ∀ (input : RAMInput),
  execute poissonProgram input (14 + 6 * input.naturals 0) initialState =
      poissonFinalState (input.reals 0) (input.naturals 0) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.2.1.2.2

theorem poissonProgram_correct :
  ∀ (input : RAMInput),
  ∃ (steps : ℕ) (out : RAMState),
      Execution poissonProgram input initialState out steps ∧
      steps ≤ 14 + 6 * input.naturals 0 ∧
      out.rm 0 = ActuarialValuation.poissonCountMass (input.reals 0) (input.naturals 0) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.2.2.1.1

end Mission
end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped BigOperators
namespace NearLinearRSP.TwoResources.Mission.Expectation
open Structured

theorem run_atoms :
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (atoms as) s (evalAtoms input as s) as.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.2.2.1.2

theorem Frame.refl :
  ∀ (s : Store),
  Frame s s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.2.2.2.1

theorem Frame.trans :
  ∀ {s t u : Store} (h : Frame s t) (g : Frame t u),
  Frame s u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.2.2.2.2.2

theorem ColumnFrame.refl :
  ∀ (s : Store),
  ColumnFrame s s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.1.1.1

theorem ColumnFrame.trans :
  ∀ {s t u : Store} (h : ColumnFrame s t)
    (g : ColumnFrame t u),
  ColumnFrame s u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.1.1.2.1

theorem ColumnFrame.frame :
  ∀ {s t : Store} (h : ColumnFrame s t),
  Frame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.1.1.2.2

theorem columnBody_inv :
  ∀ (input : RAMInput) (c : ColumnContext) (k : ℕ)
    (total : ℝ) (s : Store) (h : ColumnInv c k total s),
  ColumnInv c (k + 1) (total + c.term k) (evalAtoms input columnAtoms s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.1.2.1

theorem columnBody_frame :
  ∀ (input : RAMInput) (s : Store),
  ColumnFrame s (evalAtoms input columnAtoms s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.1.2.2.1

theorem columnLoop_run :
  ∀ (input : RAMInput) (c : ColumnContext) (k d : ℕ)
    (total : ℝ) (s : Store) (h : ColumnInv c k total s) (hend : c.count = k + d),
  ∃ t : Store, Run input columnLoop s t (11 * d + 1) ∧
      ColumnInv c (k + d) (total + ∑ b ∈ Finset.range d, c.term (k + b)) t ∧
      ColumnFrame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.1.2.2.2

theorem rowPrepare_inv :
  ∀ (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s),
  ColumnInv (c.column a) 0 total (evalAtoms input rowPrepare s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.2.1.1

theorem rowPrepare_frame :
  ∀ (input : RAMInput) (s : Store),
  ColumnFrame s (evalAtoms input rowPrepare s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.2.1.2.1

theorem RowInv.afterColumn :
  ∀ (c : RectangleContext) (a : ℕ) (total next : ℝ)
    (s t : Store) (h : RowInv c a total s) (hf : ColumnFrame s t)
    (htotal : t.rr 82 = next),
  RowInv c a next t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.2.1.2.2

theorem rowFinish_inv :
  ∀ (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s),
  RowInv c (a + 1) total (evalAtoms input rowFinish s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.2.2.1.1

theorem rowFinish_frame :
  ∀ (input : RAMInput) (s : Store),
  Frame s (evalAtoms input rowFinish s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.2.2.1.2

theorem rowBody_run :
  ∀ (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s),
  ∃ t : Store, Run input rowBody s t (10 + 11 * c.cols) ∧
      RowInv c (a + 1) (total + c.row a) t ∧ Frame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.2.2.2.1

theorem rowLoop_run :
  ∀ (input : RAMInput) (c : RectangleContext) (a d : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s) (hend : c.rows = a + d),
  ∃ t : Store, Run input rowLoop s t ((12 + 11 * c.cols) * d + 1) ∧
      RowInv c (a + d) (total + ∑ k ∈ Finset.range d, c.row (a + k)) t ∧ Frame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.1.2.2.2.2

theorem corePrepare_inv :
  ∀ (input : RAMInput) (s : Store),
  RowInv (contextOf s) 0 0 (evalAtoms input corePrepare s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.1.1.1

theorem corePrepare_frame :
  ∀ (input : RAMInput) (s : Store),
  Frame s (evalAtoms input corePrepare s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.1.1.2.1

theorem coreFinish_frame :
  ∀ (input : RAMInput) (s : Store),
  Frame s (evalAtoms input coreFinish s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.1.1.2.2

theorem coreCmd_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ t : Store, Run input coreCmd s t (13 + (12 + 11 * s.nr 87) * s.nr 86) ∧
      t.rr 82 = 1 - ∑ a ∈ Finset.range (s.nr 86),
        ∑ b ∈ Finset.range (s.nr 87),
          mass (s.rr 80) a * mass (s.rr 81) b *
            s.rm (s.nr 88 + s.nr 90 * a + s.nr 89 * b) ∧ Frame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.1.2.1.1

theorem setupCmd_run :
  ∀ (input : RAMInput) (s : Store),
  Run input setupCmd s (setupResult input s)
      (41 + 4 * s.nr 81 + 4 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 80) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.1.2.1.2

theorem setupResult_values :
  ∀ (input : RAMInput) (s : Store),
  (setupResult input s).nr 86 = s.nr 80 - s.nr 81 ∧
    (setupResult input s).nr 87 = s.nr 80 - s.nr 82 ∧
    (setupResult input s).nr 88 = s.nr 84 + s.nr 85 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 83 ∧
    (setupResult input s).nr 89 = s.nr 85 ∧
    (setupResult input s).nr 90 = s.nr 85 * s.nr 80 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.1.2.2.1

theorem FullFrame.refl :
  ∀ (s : Store),
  FullFrame s s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.1.2.2.2

theorem FullFrame.trans :
  ∀ {s t u : Store} (h : FullFrame s t) (g : FullFrame t u),
  FullFrame s u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.2.1.1

theorem Frame.full :
  ∀ {s t : Store} (h : Frame s t),
  FullFrame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.2.1.2.1

theorem setupResult_frame :
  ∀ (input : RAMInput) (s : Store),
  FullFrame s (setupResult input s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.2.1.2.2

theorem nonsaturatedCmd_run :
  ∀ (input : RAMInput) (s : Store)
    (hi : s.nr 81 < s.nr 80) (hj : s.nr 82 < s.nr 80),
  ∃ t : Store, Run input nonsaturatedCmd s t
      (54 + 4 * s.nr 81 + 4 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 80 +
        (12 + 11 * (s.nr 80 - s.nr 82)) * (s.nr 80 - s.nr 81)) ∧
      t.rr 82 = expectedResult s ∧ FullFrame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.2.2.1.1

theorem expectationCmd_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ (t : Store) (steps : ℕ), Run input expectationCmd s t steps ∧
      steps ≤ 100 * (s.nr 80 + 1) ^ 2 ∧
      t.rr 82 = expectedResult s ∧ FullFrame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.2.2.1.2

theorem expectedResult_eq_edgeExpectation :
  ∀ (A : InnerInput) (T : Table)
    (u v i j : ℕ) (s : Store)
    (hq : s.nr 80 = tickLimit A) (hi : s.nr 81 = i) (hj : s.nr 82 = j)
    (hμ : s.rr 80 = lengthRate A * A.I.length u v)
    (hν : s.rr 81 = costRate A * A.I.cost u v)
    (hmem : ∀ a < tickLimit A - i, ∀ b < tickLimit A - j,
      s.rm (s.nr 84 + s.nr 85 * ((i + a) * tickLimit A + (j + b)) + 4 * s.nr 83) =
        1 - (T u (i + a) (j + b)).value),
  expectedResult s = edgeExpectation A T u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.2.2.2.1

theorem edgeExpectation_run :
  ∀ (input : RAMInput) (A : InnerInput) (T : Table)
    (u v i j : ℕ) (s : Store)
    (hq : s.nr 80 = tickLimit A) (hi : s.nr 81 = i) (hj : s.nr 82 = j)
    (hμ : s.rr 80 = lengthRate A * A.I.length u v)
    (hν : s.rr 81 = costRate A * A.I.cost u v)
    (hmem : ∀ a < tickLimit A - i, ∀ b < tickLimit A - j,
      s.rm (s.nr 84 + s.nr 85 * ((i + a) * tickLimit A + (j + b)) + 4 * s.nr 83) =
        1 - (T u (i + a) (j + b)).value),
  ∃ (t : Store) (steps : ℕ), Run input expectationCmd s t steps ∧
      steps ≤ 100 * (tickLimit A + 1) ^ 2 ∧
      t.rr 82 = edgeExpectation A T u v i j ∧ FullFrame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.2.2.2.2.2.2

end NearLinearRSP.TwoResources.Mission.Expectation
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem outerLayout_address (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) (v i j : ℕ) :
    (outerLayout I ε hε hε1 r A hA).address v i j=tableAddress I ε r v i j := by
  obtain ⟨hI,_,_,hq⟩ := outerInputs_get_parameters I ε hε hε1 r A hA
  change tableBase I ε r+4*((i*tickLimit A+j)*A.I.graph.n+v)=_
  rw [hI,hq]
  rfl

private theorem SetupReady.target_nat_zero {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) (v off : ℕ) (hv : v<I.graph.n) (hoff : off<4) :
    s.nm (targetAddress v+off)=0 := by
  have ht := Query.target_lt_outputEnd I ε v off hv hoff
  apply h.graph.naturalZero
  · unfold targetAddress; omega
  · unfold graphBase; omega

private theorem SetupReady.target_real_zero {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) (v off : ℕ) (hv : v<I.graph.n) (hoff : off<4) :
    s.rm (targetAddress v+off)=0 := by
  apply h.graph.realZero
  · unfold targetAddress; omega
  · exact Or.inl (Query.target_lt_outputEnd I ε v off hv hoff)

private theorem SetupReady.table_real_zero {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) (r v i j off : ℕ) (hr : r<(outerInputs I ε).length)
    (hv : v<I.graph.n) (hi : i<outerQ ε) (hj : j<outerQ ε) (hoff : off<4) :
    s.rm (tableAddress I ε r v i j+off)=0 := by
  apply h.graph.realZero
  · unfold tableAddress tableBase; omega
  · exact Or.inl (Query.table_lt_outputEnd I ε r v i j off hr hv hi hj hoff)

private theorem SetupReady.outerGraphMemory {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) :
    DP.GraphMemory (outerLayout I ε hε hε1 r A hA) s := by
  obtain ⟨hI,_,_,_⟩ := outerInputs_get_parameters I ε hε hε1 r A hA
  intro k v hv
  rw [hI] at hv
  exact ⟨h.graph.active.index k v hv,h.graph.active.value k v hv⟩

private theorem SetupReady.outerInitialTable {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) :
    DP.TableValues (outerLayout I ε hε hε1 r A hA) (fun _ _ _=>⟨1,.lengthTick,0⟩) s := by
  obtain ⟨hI,_,_,hq⟩ := outerInputs_get_parameters I ε hε hε1 r A hA
  have hr := (List.getElem?_eq_some_iff.mp hA).1
  intro v hv i hi j hj
  rw [hI] at hv
  rw [hq] at hi hj
  rw [outerLayout_address]
  simpa only [Nat.add_zero,sub_self] using
    h.table_real_zero r v i j 0 hr (activeVertices_valid I v hv) hi hj (by omega)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured Preprocess

private theorem initialized_registers (input : RAMInput) (I : Instance) (ε : ℝ) (s : Store)
    (h : RuntimeReady I ε s) (hB : s.nr 11 = queueCapacity I) :
    Registers I ε 0 (initialized input s) := by
  refine ⟨rfl,?_,?_,?_,hB,?_,?_,?_,?_⟩
  · change s.nr 130 = tableBase I ε 0
    simpa [tableBase] using h.numeric.targetEnd
  · change s.nr 139+s.nr 122+16 = queueWinnerBase I ε
    rw [h.layout.links,h.numeric.edges]
    rfl
  · change s.nr 139+s.nr 122+16+(s.nr 11+s.nr 11) = queueParentBase I ε
    rw [h.layout.links,h.numeric.edges,hB]
    simp [queueParentBase,queueWinnerBase,two_mul]
  · change s.nr 139+s.nr 122+16+(s.nr 11+s.nr 11)+(s.nr 11+s.nr 11) = queueTempBase I ε
    rw [h.layout.links,h.numeric.edges,hB]
    simp [queueTempBase,queueParentBase,queueWinnerBase,two_mul]
  · change s.rr 150 = firstPositiveLength I*(1+ε/4)^0
    simpa using h.numeric.minimum
  · change (s.rr 123+s.rr 125)/2 = 1+ε/8
    rw [h.numeric.ratio,h.numeric.realOne]
    ring
  · change s.rr 127/(((s.rr 123+s.rr 125)/2)*s.rr 121) = _
    rw [h.numeric.realQ,h.numeric.ratio,h.numeric.realOne,h.numeric.budget]
    congr 2
    ring

private theorem advanced_registers (input : RAMInput) (I : Instance) (ε : ℝ) (k : ℕ) (s : Store)
    (h : RuntimeReady I ε s) (hk : Registers I ε k s) :
    Registers I ε (k+1) (advanced input s) := by
  refine ⟨?_,?_,hk.winner,hk.parent,hk.capacity,hk.temporary,?_,hk.factor,hk.costRate⟩
  · change s.nr 243+s.nr 126 = k+1
    rw [hk.index,h.numeric.one]
  · change s.nr 244+s.nr 133 = tableBase I ε (k+1)
    rw [hk.table,h.layout.span]
    unfold tableBase
    ring
  · change s.rr 243*s.rr 123 = firstPositiveLength I*(1+ε/4)^(k+1)
    rw [hk.length,h.numeric.ratio,pow_succ]
    ring

private theorem Registers.transfer {I : Instance} {ε : ℝ} {k : ℕ} {s t : Store}
    (h : Registers I ε k s)
    (hn : ∀ r, 243 ≤ r → r ≤ 250 → t.nr r = s.nr r)
    (hr : ∀ r, 243 ≤ r → r ≤ 245 → t.rr r = s.rr r) : Registers I ε k t := by
  exact ⟨(hn 243 (by omega) (by omega)).trans h.index,
    (hn 244 (by omega) (by omega)).trans h.table,
    (hn 247 (by omega) (by omega)).trans h.winner,
    (hn 248 (by omega) (by omega)).trans h.parent,
    (hn 249 (by omega) (by omega)).trans h.capacity,
    (hn 250 (by omega) (by omega)).trans h.temporary,
    (hr 243 (by omega) (by omega)).trans h.length,
    (hr 244 (by omega) (by omega)).trans h.factor,
    (hr 245 (by omega) (by omega)).trans h.costRate⟩

private theorem prepared_constants (input : RAMInput) (I : Instance) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (r : ℕ) (A : InnerInput)
    (hA : (outerInputs I ε)[r]? = some A) (s : Store)
    (h : RuntimeReady I ε s) (hk : Registers I ε r s) :
    DP.Constants (outerLayout I ε hε hε1 r A hA) (tickLimit A) 0 (prepared input s) := by
  obtain ⟨hI,hδ,hL,hq⟩ := outerInputs_get_parameters I ε hε hε1 r A hA
  have hv := prepared_values input s
  simp only [DP.Constants,outerLayout,DP.Layout.address,hI,hq]
  refine ⟨h.numeric.vertices,h.numeric.source,h.numeric.q,h.numeric.zero,h.numeric.one,
    h.numeric.vertexStride,h.layout.heads,h.layout.links,h.layout.map,h.layout.array,
    hk.table,?_,h.numeric.zero,?_,h.active.count_reg,hk.winner,hk.parent,hk.capacity,
    hk.temporary,h.layout.rowStride,?_,?_,?_⟩
  · exact h.numeric.q
  · change s.nr 244+s.nr 133 = _
    rw [hk.table,h.layout.span]
    ring
  · change s.rr 127/(s.rr 244*s.rr 243) = lengthRate A
    rw [h.numeric.realQ,hk.factor,hk.length]
    simp only [lengthRate,hq,hδ,hL]
    congr 2
    ring
  · change s.rr 245 = costRate A
    rw [hk.costRate]
    simp only [costRate,hq,hδ,hI]
    congr 2
    ring
  · change s.rr 128 = zValue A
    rw [h.numeric.z]
    simp only [zValue,hδ]
    congr 2 <;> ring

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured Preprocess

private theorem runtime_of_readonly {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (hrun : Run input c s t n) (I : Instance) (ε : ℝ) (h : RuntimeReady I ε s)
    (hn : ∀r, 121 ≤ r → r ≤ 153 → r ∉ c.natWrites)
    (hr : ∀r, 121 ≤ r → r ≤ 153 → r ∉ c.realWrites)
    (hN : c.writesNatMemory = false) (hR : c.writesRealMemory = false) :
    RuntimeReady I ε t := by
  have hnm := hrun.natMemory_frame hN
  have hrm := hrun.realMemory_frame hR
  exact h.transfer (fun r h1 h2 => hrun.nat_frame r (hn r h1 h2))
    (fun r h1 h2 => hrun.real_frame r (hr r h1 h2))
    (fun a _ => congrFun hnm a) (fun a _ _ => congrFun hnm a)
    (congrFun hrm 0) (fun a _ => congrFun hrm _)

private theorem initialized_runtime (input : RAMInput) (I : Instance) (ε : ℝ) (s : Store)
    (h : RuntimeReady I ε s) : RuntimeReady I ε (initialized input s) := by
  apply runtime_of_readonly (run_atoms input initOps s) I ε h
  · intro r h1 h2
    simp [Cmd.atoms,initOps,Cmd.natWrites,Atom.natWrites]
    omega
  · intro r h1 h2
    simp [Cmd.atoms,initOps,Cmd.realWrites,Atom.realWrites]
    omega
  · rfl
  · rfl

private theorem prepared_runtime (input : RAMInput) (I : Instance) (ε : ℝ) (s : Store)
    (h : RuntimeReady I ε s) : RuntimeReady I ε (prepared input s) := by
  apply runtime_of_readonly (run_atoms input prepareOps s) I ε h
  · intro r h1 h2
    simp [Cmd.atoms,prepareOps,Cmd.natWrites,Atom.natWrites]
    omega
  · intro r h1 h2
    simp [Cmd.atoms,prepareOps,Cmd.realWrites,Atom.realWrites]
    omega
  · rfl
  · rfl

private theorem markPrepared_runtime (input : RAMInput) (I : Instance) (ε : ℝ) (s : Store)
    (h : RuntimeReady I ε s) : RuntimeReady I ε (markPrepared input s) := by
  apply runtime_of_readonly (run_atoms input markOps s) I ε h
  · intro r h1 h2
    simp [Cmd.atoms,markOps,Cmd.natWrites,Atom.natWrites]
    omega
  · intro r h1 h2
    simp [Cmd.atoms,markOps,Cmd.realWrites,Atom.realWrites]
    omega
  · rfl
  · rfl

private theorem advanced_runtime (input : RAMInput) (I : Instance) (ε : ℝ) (s : Store)
    (h : RuntimeReady I ε s) : RuntimeReady I ε (advanced input s) := by
  apply runtime_of_readonly (run_atoms input advanceOps s) I ε h
  · intro r h1 h2
    simp [Cmd.atoms,advanceOps,Cmd.natWrites,Atom.natWrites]
    omega
  · intro r h1 h2
    simp [Cmd.atoms,advanceOps,Cmd.realWrites,Atom.realWrites]
    omega
  · rfl
  · rfl

private theorem prepared_registers (input : RAMInput) (I : Instance) (ε : ℝ) (k : ℕ) (s : Store)
    (h : Registers I ε k s) : Registers I ε k (prepared input s) := by
  apply h.transfer
  · intro r h1 h2
    apply (run_atoms input prepareOps s).nat_frame
    simp [Cmd.atoms,prepareOps,Cmd.natWrites,Atom.natWrites]
    omega
  · intro r h1 h2
    apply (run_atoms input prepareOps s).real_frame
    simp [Cmd.atoms,prepareOps,Cmd.realWrites,Atom.realWrites]
    omega

private theorem markPrepared_registers (input : RAMInput) (I : Instance) (ε : ℝ) (k : ℕ) (s : Store)
    (h : Registers I ε k s) : Registers I ε k (markPrepared input s) := by
  apply h.transfer
  · intro r h1 h2
    apply (run_atoms input markOps s).nat_frame
    simp [Cmd.atoms,markOps,Cmd.natWrites,Atom.natWrites]
    omega
  · intro r h1 h2
    apply (run_atoms input markOps s).real_frame
    simp [Cmd.atoms,markOps,Cmd.realWrites,Atom.realWrites]
    omega

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP

private theorem Layout.capacity_pos {A : InnerInput} (E : Layout A) : 0 < E.capacity := by
  rw [E.capacity_eq]
  positivity

private theorem Layout.table_end_le_winner {A : InnerInput} (E : Layout A) :
    E.base + 4 * A.I.graph.n * tickLimit A ^ 2 ≤ E.winner := by
  have ha := E.table_before_array
  have hb := E.array_before_winner
  omega

private theorem Layout.address_lt_end {A : InnerInput} (E : Layout A) (v i j off : ℕ)
    (hv : v < A.I.graph.n) (hi : i < tickLimit A) (hj : j < tickLimit A) (hoff : off < 4) :
    E.address v i j + off < E.base + 4 * A.I.graph.n * tickLimit A ^ 2 := by
  have hrect := Address.rectangle_index_lt (tickLimit A) i j hi hj
  have hm := Nat.mul_le_mul_right A.I.graph.n
    (show i * tickLimit A + j + 1 ≤ tickLimit A ^ 2 by omega)
  unfold Layout.address
  nlinarith

private theorem Layout.address_lt_winner {A : InnerInput} (E : Layout A) (v i j off : ℕ)
    (hv : v < A.I.graph.n) (hi : i < tickLimit A) (hj : j < tickLimit A) (hoff : off < 4) :
    E.address v i j + off < E.winner :=
  (E.address_lt_end v i j off hv hi hj hoff).trans_le E.table_end_le_winner

private theorem Layout.winner_le_temp {A : InnerInput} (E : Layout A) : E.winner ≤ E.temp := by
  have h1 := E.winner_before_parent
  have h2 := E.parent_before_temp
  omega

private theorem Layout.address_lt_temp {A : InnerInput} (E : Layout A) (v i j off : ℕ)
    (hv : v < A.I.graph.n) (hi : i < tickLimit A) (hj : j < tickLimit A) (hoff : off < 4) :
    E.address v i j + off < E.temp :=
  (E.address_lt_winner v i j off hv hi hj hoff).trans_le E.winner_le_temp

private theorem Layout.address_injective {A : InnerInput} (E : Layout A) (v u i j a b : ℕ)
    (hv : v < A.I.graph.n) (hu : u < A.I.graph.n)
    (hj : j < tickLimit A) (hb : b < tickLimit A)
    (he : E.address v i j = E.address u a b) : v = u ∧ i = a ∧ j = b := by
  have hpack : (i * tickLimit A + j) * A.I.graph.n + v =
      (a * tickLimit A + b) * A.I.graph.n + u := by
    unfold Layout.address at he
    omega
  have hvertex : v = u := by
    have h := congrArg (fun x => x % A.I.graph.n) hpack
    simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hu] using h
  have hindex : i * tickLimit A + j = a * tickLimit A + b := by
    apply Nat.mul_right_cancel (show 0 < A.I.graph.n by omega)
    omega
  have hcost : j = b := by
    have h := congrArg (fun x => x % tickLimit A) hindex
    simpa [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hb] using h
  have hlength : i = a := by
    apply Nat.mul_right_cancel (show 0 < tickLimit A by omega)
    omega
  exact ⟨hvertex, hlength, hcost⟩

private theorem Layout.address_block_separated {A : InnerInput} (E : Layout A)
    (v u i j a b off off' : ℕ)
    (hv : v < A.I.graph.n) (hu : u < A.I.graph.n)
    (hj : j < tickLimit A) (hb : b < tickLimit A)
    (hoff : off < 4) (hoff' : off' < 4)
    (hne : ¬ (v = u ∧ i = a ∧ j = b)) :
    E.address v i j + off ≠ E.address u a b + off' := by
  intro he
  have ha : E.address v i j = E.address u a b := by
    unfold Layout.address at he ⊢
    omega
  exact hne (E.address_injective v u i j a b hv hu hj hb ha)

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem Constants.transfer {A : InnerInput} (E : Layout A) (i j : ℕ)
    (s t : Store) (h : Constants E i j s)
    (hn : ∀ r ∈ constantNatRegisters, t.nr r = s.nr r)
    (hr : ∀ r ∈ constantRealRegisters, t.rr r = s.rr r) : Constants E i j t := by
  simpa only [Constants,
    hn 121 (by decide),hn 123 (by decide),hn 124 (by decide),hn 125 (by decide),
    hn 126 (by decide),hn 129 (by decide),hn 137 (by decide),hn 139 (by decide),
    hn 141 (by decide),hn 142 (by decide),hn 200 (by decide),hn 201 (by decide),
    hn 202 (by decide),hn 203 (by decide),hn 204 (by decide),hn 205 (by decide),
    hn 206 (by decide),hn 207 (by decide),hn 208 (by decide),hn 209 (by decide),
    hr 200 (by decide),hr 201 (by decide),hr 202 (by decide)] using h

private theorem Constants.after_run {A : InnerInput} (E : Layout A) (i j : ℕ)
    (input : RAMInput) (c : Cmd) (s t : Store) (n : ℕ)
    (h : Constants E i j s) (hrun : Run input c s t n)
    (hn : Disjoint constantNatRegisters c.natWrites)
    (hr : Disjoint constantRealRegisters c.realWrites) : Constants E i j t := by
  apply Constants.transfer E i j s t h
  · intro r hmem
    exact hrun.nat_frame r (fun hw => Finset.disjoint_left.mp hn hmem hw)
  · intro r hmem
    exact hrun.real_frame r (fun hw => Finset.disjoint_left.mp hr hmem hw)

private theorem BelowFrame.refl (cutoff : ℕ) (s : Store) : BelowFrame cutoff s s :=
  fun _ _ => ⟨rfl,rfl⟩

private theorem BelowFrame.trans {cutoff : ℕ} {s t u : Store}
    (h : BelowFrame cutoff s t) (g : BelowFrame cutoff t u) : BelowFrame cutoff s u :=
  fun a ha => ⟨(g a ha).1.trans (h a ha).1,(g a ha).2.trans (h a ha).2⟩

private theorem belowFrame_of_run (input : RAMInput) (c : Cmd) (s t : Store) (n cutoff : ℕ)
    (h : Run input c s t n) (hn : c.writesNatMemory = false)
    (hr : c.writesRealMemory = false) : BelowFrame cutoff s t :=
  fun a _ => ⟨congrFun (h.natMemory_frame hn) a,congrFun (h.realMemory_frame hr) a⟩

private theorem GraphMemory.transfer {A : InnerInput} (E : Layout A) (s t : Store)
    (h : GraphMemory E s) (hf : BelowFrame E.winner s t) : GraphMemory E t := by
  intro k v hv
  have hvn := activeVertices_valid A.I v (List.mem_of_getElem? hv)
  obtain ⟨hkn,_⟩ := List.getElem?_eq_some_iff.mp hv
  have hm := E.map_before_winner
  have ha := E.array_before_winner
  exact ⟨(hf _ (by omega)).1.trans (h k v hv).1,
    (hf _ (by omega)).1.trans (h k v hv).2⟩

private theorem TableValues.transfer {A : InnerInput} (E : Layout A) (T : Table) (s t : Store)
    (h : TableValues E T s) (hf : BelowFrame E.winner s t) : TableValues E T t := by
  intro v hv i hi j hj
  have ha : E.address v i j < E.winner := by
    simpa using E.address_lt_winner v i j 0 (activeVertices_valid A.I v hv) hi hj (by omega)
  exact (hf _ ha).2.trans (h v hv i hi j hj)

private theorem StoredCell.transfer {A : InnerInput} (E : Layout A) (T : Table)
    (v i j : ℕ) (s t : Store) (hv : v < A.I.graph.n)
    (hi : i < tickLimit A) (hj : j < tickLimit A)
    (h : StoredCell E T v i j s) (hf : BelowFrame E.winner s t) :
    StoredCell E T v i j t := by
  have h0 := hf _ (E.address_lt_winner v i j 0 hv hi hj (by omega))
  have h1 := hf _ (E.address_lt_winner v i j 1 hv hi hj (by omega))
  have h2 := hf _ (E.address_lt_winner v i j 2 hv hi hj (by omega))
  simp only [Nat.add_zero] at h0
  rcases h with ⟨hv0,hn0,hn1,hn2,hpgf⟩
  exact ⟨h0.2.trans hv0,h0.1.trans hn0,h1.1.trans hn1,h2.1.trans hn2,
    fun u hu => ⟨h1.2.trans (hpgf u hu).1,h2.2.trans (hpgf u hu).2⟩⟩

private theorem Heap.transfer_below_temp {A : InnerInput} (E : Layout A) (S : LayerState)
    (s t : Store) (h : Heap E S s) (hf : BelowFrame E.temp s t) : Heap E S t := by
  constructor
  · intro node hn
    have hsep := E.winner_before_parent
    have htemp := E.parent_before_temp
    have ha : E.winner + node < E.temp := by omega
    have hm := hf _ ha
    simpa only [Queue.readRecord,hm.1,hm.2] using h.1 node hn
  · intro node hn
    have htemp := E.parent_before_temp
    exact (hf _ (by omega)).1.trans (h.2 node hn)

private theorem Arrays.transfer_winner_frame {A : InnerInput} (E : Layout A) (S : LayerState)
    (s t : Store) (h : Arrays E S s)
    (hf : Queue.WinnerFrame E.winner (2 * E.capacity) s t) : Arrays E S t := by
  intro k v hv
  have hs := E.winner_before_parent
  have ht := E.parent_before_temp
  have h0 := hf (E.temp + k) (Or.inr (by omega))
  have h1 := hf (E.temp + (activeVertices A.I).length + k) (Or.inr (by omega))
  have h2 := hf (E.temp + 2 * (activeVertices A.I).length + k) (Or.inr (by omega))
  obtain ⟨hk,hp,hu,hpgf⟩ := h k v hv
  exact ⟨h0.2.trans hk,h0.1.trans hp,h1.1.trans hu,
    fun u hu => ⟨h1.2.trans (hpgf u hu).1,h2.2.trans (hpgf u hu).2⟩⟩

private theorem Arrays.transfer_above_temp {A : InnerInput} (E : Layout A) (S : LayerState)
    (s t : Store) (h : Arrays E S s)
    (hf : ∀ a, E.temp ≤ a → t.nm a = s.nm a ∧ t.rm a = s.rm a) : Arrays E S t := by
  intro k v hv
  have h0 := hf (E.temp + k) (by omega)
  have h1 := hf (E.temp + (activeVertices A.I).length + k) (by omega)
  have h2 := hf (E.temp + 2 * (activeVertices A.I).length + k) (by omega)
  obtain ⟨hk,hp,hu,hpgf⟩ := h k v hv
  exact ⟨h0.2.trans hk,h0.1.trans hp,h1.1.trans hu,
    fun u hu => ⟨h1.2.trans (hpgf u hu).1,h2.2.trans (hpgf u hu).2⟩⟩

private theorem winnerFrame_below {A : InnerInput} (E : Layout A) (s t : Store)
    (h : Queue.WinnerFrame E.winner (2 * E.capacity) s t) : BelowFrame E.winner s t :=
  fun a ha => h a (Or.inl ha)

private theorem LayerRep.transfer_readonly {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (s t : Store) (h : LayerRep E i j S s)
    (hc : Constants E i j t) (hn : t.nm = s.nm) (hr : t.rm = s.rm)
    (h210 : t.nr 210 = s.nr 210) : LayerRep E i j S t := by
  rcases h with ⟨_,hg,hh,ha,hT,hsub,hrank⟩
  refine ⟨hc,?_,?_,?_,?_,hsub,h210.trans hrank⟩
  · simpa only [GraphMemory,hn] using hg
  · simpa only [Heap,Queue.Represents,Queue.readRecord,hn,hr] using hh
  · simpa only [Arrays,hn,hr] using ha
  · simpa only [TableValues,hr] using hT

private theorem LayerRep.after_readonly {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (input : RAMInput) (c : Cmd) (s t : Store) (n : ℕ)
    (h : LayerRep E i j S s) (hrun : Run input c s t n)
    (hn : Disjoint constantNatRegisters c.natWrites)
    (hr : Disjoint constantRealRegisters c.realWrites)
    (hnm : c.writesNatMemory = false) (hrm : c.writesRealMemory = false)
    (hrank : 210 ∉ c.natWrites) : LayerRep E i j S t :=
  LayerRep.transfer_readonly E i j S s t h
    (Constants.after_run E i j input c s t n h.1 hrun hn hr)
    (hrun.natMemory_frame hnm) (hrun.realMemory_frame hrm) (hrun.nat_frame 210 hrank)

private theorem OutsideTableFrame.refl {A : InnerInput} (E : Layout A) (s : Store) :
    OutsideTableFrame E s s := fun _ _ _ => ⟨rfl,rfl⟩

private theorem OutsideTableFrame.trans {A : InnerInput} {E : Layout A} {s t u : Store}
    (h : OutsideTableFrame E s t) (g : OutsideTableFrame E t u) : OutsideTableFrame E s u :=
  fun a ha hb => ⟨(g a ha hb).1.trans (h a ha hb).1,(g a ha hb).2.trans (h a ha hb).2⟩

private theorem outsideTableFrame_readonly {A : InnerInput} (E : Layout A) (s t : Store)
    (hn : t.nm = s.nm) (hr : t.rm = s.rm) : OutsideTableFrame E s t :=
  fun a _ _ => ⟨congrFun hn a,congrFun hr a⟩

private theorem OutsideTableFrame.adjacency {A : InnerInput} (E : Layout A) (s t : Store)
    (hf : OutsideTableFrame E s t)
    (h : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm) :
    Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links t.nm := by
  intro v hv
  have hhead := E.heads_before_winner
  have hheadTable := E.table_before_heads
  have hlinks := E.links_before_winner
  have hlinksTable := E.table_before_links
  rw [(hf (E.heads+v) (by omega) (Or.inr (by omega))).1]
  apply (h v hv).frame
  intro e he
  have he' := Preprocess.outgoingIndices_lt A.I A.I.graph.edges.length v e he
  exact (hf (E.links+e) (by omega) (Or.inr (by omega))).1

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem tableBase_succ (I : Instance) (ε : ℝ) (r : ℕ) :
    tableBase I ε (r+1)=tableBase I ε r+4*I.graph.n*outerQ ε^2 := by
  unfold tableBase
  ring

private theorem tableBase_mono (I : Instance) (ε : ℝ) {r k : ℕ} (h : r≤k) :
    tableBase I ε r≤tableBase I ε k :=
  Nat.add_le_add_left (Nat.mul_le_mul_left (4*I.graph.n*outerQ ε^2) h) _

private theorem outerTable_address_bounds (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A)
    (v i j off : ℕ) (hv : v∈activeVertices I) (hi : i<tickLimit A)
    (hj : j<tickLimit A) (hoff : off<4) :
    tableBase I ε r≤tableAddress I ε r v i j+off ∧
      tableAddress I ε r v i j+off<tableBase I ε (r+1) := by
  have hp := outerInputs_get_parameters I ε hε hε1 r A hA
  have hI := hp.1
  have hq := hp.2.2.2
  constructor
  · unfold tableAddress; omega
  · have hb := (outerLayout I ε hε hε1 r A hA).address_lt_end v i j off
      (hI.symm ▸ activeVertices_valid I v hv) hi hj hoff
    rw [outerLayout_address] at hb
    change tableAddress I ε r v i j+off < tableBase I ε r+4*A.I.graph.n*tickLimit A^2 at hb
    simpa only [tableBase_succ,hI,hq] using hb

private theorem outerStored_outputTable (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) (s : Store)
    (h : ∀v∈activeVertices A.I, ∀i<tickLimit A, ∀j<tickLimit A,
      DP.StoredCell (outerLayout I ε hε hε1 r A hA) (buildTable A) v i j s) :
    OutputTable I ε r A s := by
  have hI := (outerInputs_get_parameters I ε hε hε1 r A hA).1
  intro v hv i hi j hj
  have hh := h v (hI.symm ▸ hv) i hi j hj
  simpa only [DP.StoredCell,outerLayout_address] using hh

private theorem OutputTable.congr {I : Instance} {ε : ℝ} {r : ℕ} {A : InnerInput} {s t : Store}
    (h : OutputTable I ε r A s) (hε : 0<ε) (hε1 : ε<1)
    (hA : (outerInputs I ε)[r]?=some A)
    (hf : ∀a, tableBase I ε r≤a → a<tableBase I ε (r+1) → t.nm a=s.nm a ∧ t.rm a=s.rm a) :
    OutputTable I ε r A t := by
  intro v hv i hi j hj
  have h0 := outerTable_address_bounds I ε hε hε1 r A hA v i j 0 hv hi hj (by omega)
  have h1 := outerTable_address_bounds I ε hε hε1 r A hA v i j 1 hv hi hj (by omega)
  have h2 := outerTable_address_bounds I ε hε hε1 r A hA v i j 2 hv hi hj (by omega)
  simp only [Nat.add_zero] at h0
  have hf0 := hf _ h0.1 h0.2
  have hf1 := hf _ h1.1 h1.2
  have hf2 := hf _ h2.1 h2.2
  have hh := h v hv i hi j hj
  exact ⟨hf0.2.trans hh.1,hf0.1.trans hh.2.1,hf1.1.trans hh.2.2.1,
    hf2.1.trans hh.2.2.2.1,fun u hu =>
      ⟨hf1.2.trans ((hh.2.2.2.2 u hu).1),hf2.2.trans ((hh.2.2.2.2 u hu).2)⟩⟩

private theorem outsideTableFrame_outer (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) (s t : Store)
    (h : DP.OutsideTableFrame (outerLayout I ε hε hε1 r A hA) s t) :
    OuterTableFrame I ε r s t := by
  have hp := outerInputs_get_parameters I ε hε hε1 r A hA
  intro a ha hb
  apply h a ha
  change a<tableBase I ε r ∨ tableBase I ε r+4*A.I.graph.n*tickLimit A^2≤a
  simpa only [tableBase_succ,hp.1,hp.2.2.2] using hb

private theorem tableBase_le_winner (I : Instance) (ε : ℝ) (r : ℕ)
    (hr : r≤(outerInputs I ε).length) : tableBase I ε r≤queueWinnerBase I ε := by
  have hm := tableBase_mono I ε hr
  change tableBase I ε r≤Query.outputEnd I ε at hm
  unfold queueWinnerBase linksBase graphBase
  omega

private theorem OuterTableFrame.below {I : Instance} {ε : ℝ} {r : ℕ} {s t : Store}
    (h : OuterTableFrame I ε r s t) (hr : r≤(outerInputs I ε).length)
    (a : ℕ) (ha : a<tableBase I ε r) : t.nm a=s.nm a ∧ t.rm a=s.rm a :=
  h a (ha.trans_le (tableBase_le_winner I ε r hr)) (Or.inl ha)

private theorem OuterTableFrame.runtime {I : Instance} {ε : ℝ} {r : ℕ} {s t : Store}
    (h : OuterTableFrame I ε r s t) (hr : r<(outerInputs I ε).length)
    (hs : RuntimeReady I ε s)
    (hn : ∀a, 121≤a → a≤153 → t.nr a=s.nr a)
    (hreal : ∀a, 121≤a → a≤153 → t.rr a=s.rr a) : RuntimeReady I ε t := by
  have he : tableBase I ε (r+1)≤Query.outputEnd I ε := by
    rw [tableBase_succ]
    exact tableEnd_le_outputEnd I ε r hr
  apply hs.transfer hn hreal
  · intro a ha
    exact (h.below (by omega) a (by unfold tableBase; omega)).1
  · intro a hlo hhi
    exact (h a (by unfold queueWinnerBase; omega) (Or.inr (by unfold graphBase at hlo; omega))).1
  · exact (h.below (by omega) 0 (by unfold tableBase; omega)).2
  · intro a ha
    apply (h (Query.outputEnd I ε+a) ?_ (Or.inr (by omega))).2
    unfold queueWinnerBase linksBase graphBase
    omega

private theorem OuterTableFrame.parents {I : Instance} {ε : ℝ} {r : ℕ} {s t : Store}
    (h : OuterTableFrame I ε r s t) (hr : r≤(outerInputs I ε).length)
    (hs : OutputParents I s) : OutputParents I t := by
  intro v hv
  have hvalid := activeVertices_valid I v hv
  have h2 := h.below hr (targetAddress v+2) (by unfold targetAddress tableBase; omega)
  have h3 := h.below hr (targetAddress v+3) (by unfold targetAddress tableBase; omega)
  exact ⟨h2.1.trans (hs v hv).1,h3.1.trans (hs v hv).2⟩

private theorem OuterTableFrame.records {I : Instance} {ε : ℝ} {r : ℕ} {s t : Store}
    (h : OuterTableFrame I ε r s t) (hr : r≤(outerInputs I ε).length)
    (f : ℕ→AnswerBranch) (hs : TargetRecords.RecordMap I ε f s) :
    TargetRecords.RecordMap I ε f t := by
  intro v hv
  have h0 := h.below hr (targetAddress v) (by unfold targetAddress tableBase; omega)
  have h1 := h.below hr (targetAddress v+1) (by unfold targetAddress tableBase; omega)
  exact ⟨h0.1.trans (hs v hv).1,fun d hd=>h0.2.trans ((hs v hv).2.1 d hd),
    fun k hk=>h1.1.trans ((hs v hv).2.2 k hk)⟩

private theorem OuterTableFrame.completed {I : Instance} {ε : ℝ} {r : ℕ} {s t : Store}
    (h : OuterTableFrame I ε r s t) (hr : r≤(outerInputs I ε).length)
    (hε : 0<ε) (hε1 : ε<1) (hs : CompletedTables I ε r s) : CompletedTables I ε r t := by
  intro k hk A hA
  apply (hs k hk A hA).congr hε hε1 hA
  intro a hlo hhi
  exact h.below hr a (hhi.trans_le (tableBase_mono I ε (by omega)))

private theorem OuterTableFrame.future {I : Instance} {ε : ℝ} {r : ℕ} {s t : Store}
    (h : OuterTableFrame I ε r s t) (hs : FutureZero I ε r s) : FutureZero I ε (r+1) t := by
  intro a hlo hhi
  have haW : a<queueWinnerBase I ε := by unfold queueWinnerBase linksBase graphBase; omega
  exact (h a haW (Or.inr hlo)).2.trans
    (hs a ((tableBase_mono I ε (by omega : r≤r+1)).trans hlo) hhi)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured Preprocess

private theorem TargetFrame.parents {I : Instance} {s t : Store}
    (h : TargetFrame I s t) (hs : OutputParents I s) : OutputParents I t := by
  intro v hv
  exact ⟨(h.treeParents v).1.trans (hs v hv).1,(h.treeParents v).2.trans (hs v hv).2⟩

private theorem TargetFrame.table {I : Instance} {ε : ℝ} {r : ℕ} {A : InnerInput} {s t : Store}
    (h : TargetFrame I s t) (hs : OutputTable I ε r A s)
    (hε : 0<ε) (hε1 : ε<1) (hA : (outerInputs I ε)[r]?=some A) : OutputTable I ε r A t := by
  apply hs.congr hε hε1 hA
  intro a hlo hhi
  apply h.outside a (Or.inr ?_)
  unfold tableBase at hlo
  omega

private theorem TargetFrame.completed {I : Instance} {ε : ℝ} {k : ℕ} {s t : Store}
    (h : TargetFrame I s t) (hs : CompletedTables I ε k s)
    (hε : 0<ε) (hε1 : ε<1) : CompletedTables I ε k t := by
  intro r hr A hA
  exact h.table (hs r hr A hA) hε hε1 hA

private theorem TargetFrame.future {I : Instance} {ε : ℝ} {k : ℕ} {s t : Store}
    (h : TargetFrame I s t) (hs : FutureZero I ε k s) : FutureZero I ε k t := by
  intro a hlo hhi
  have hf := h.outside a (Or.inr (by unfold tableBase at hlo; omega))
  exact hf.2.trans (hs a hlo hhi)

private theorem TargetFrame.runtime {I : Instance} {ε : ℝ} {s t : Store}
    (h : TargetFrame I s t) (hs : RuntimeReady I ε s)
    (hn : ∀a, 121≤a → a≤153 → t.nr a=s.nr a)
    (hr : ∀a, 121≤a → a≤153 → t.rr a=s.rr a) : RuntimeReady I ε t := by
  apply hs.transfer hn hr
  · intro a ha
    exact (h.outside a (Or.inl (by omega))).1
  · intro a hlo hhi
    exact (h.outside a (Or.inr (by unfold graphBase Query.outputEnd at hlo; omega))).1
  · exact (h.outside 0 (Or.inl (by omega))).2
  · intro a ha
    exact (h.outside _ (Or.inr (by unfold Query.outputEnd; omega))).2

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem SetupReady.futureZero {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) (k : ℕ) : FutureZero I ε k s := by
  intro a hlo hhi
  apply h.graph.realZero a (by unfold tableBase at hlo; omega) (Or.inl hhi)

private theorem CompletedTables.succ {I : Instance} {ε : ℝ} {r : ℕ} {A : InnerInput} {s : Store}
    (h : CompletedTables I ε r s) (hA : (outerInputs I ε)[r]?=some A)
    (hnew : OutputTable I ε r A s) : CompletedTables I ε (r+1) s := by
  intro k hk B hB
  by_cases hkr : k<r
  · exact h k hkr B hB
  · have he : k=r := by omega
    subst k
    have heB : A=B := Option.some.inj (hA.symm.trans hB)
    subst B
    exact hnew

private theorem FutureZero.congr {I : Instance} {ε : ℝ} {k : ℕ} {s t : Store}
    (h : FutureZero I ε k s)
    (hf : ∀a, tableBase I ε k≤a → a<Query.outputEnd I ε → t.rm a=s.rm a) :
    FutureZero I ε k t := by
  intro a hlo hhi
  exact (hf a hlo hhi).trans (h a hlo hhi)

private theorem completedTables_zero (I : Instance) (ε : ℝ) (s : Store) : CompletedTables I ε 0 s := by
  intro r hr
  omega

private theorem RuntimeReady.outerGraphMemory {I : Instance} {ε : ℝ} {s : Store}
    (h : RuntimeReady I ε s) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) :
    DP.GraphMemory (outerLayout I ε hε hε1 r A hA) s := by
  have hI := (outerInputs_get_parameters I ε hε hε1 r A hA).1
  intro k v hv
  rw [hI] at hv
  exact ⟨h.active.index k v hv,h.active.value k v hv⟩

private theorem RuntimeReady.outerAdjacency {I : Instance} {ε : ℝ} {s : Store}
    (h : RuntimeReady I ε s) (hε : 0<ε) (hε1 : ε<1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) :
    AdjacencyPrefix A.I A.I.graph.edges.length (outerLayout I ε hε hε1 r A hA).heads
      (outerLayout I ε hε hε1 r A hA).links s.nm := by
  have hI := (outerInputs_get_parameters I ε hε hε1 r A hA).1
  change AdjacencyPrefix A.I A.I.graph.edges.length (headsBase I ε) (linksBase I ε) s.nm
  rw [hI]
  exact h.adjacency

private theorem FutureZero.outerInitialTable {I : Instance} {ε : ℝ} {r : ℕ} {s : Store}
    (h : FutureZero I ε r s) (hε : 0<ε) (hε1 : ε<1)
    (A : InnerInput) (hA : (outerInputs I ε)[r]?=some A) :
    DP.TableValues (outerLayout I ε hε hε1 r A hA) (fun _ _ _=>⟨1,.lengthTick,0⟩) s := by
  have hp := outerInputs_get_parameters I ε hε hε1 r A hA
  have hr := (List.getElem?_eq_some_iff.mp hA).1
  intro v hv i hi j hj
  rw [hp.1] at hv
  rw [hp.2.2.2] at hi hj
  change s.rm ((outerLayout I ε hε hε1 r A hA).address v i j)=1-(1:ℝ)
  rw [sub_self,outerLayout_address]
  apply h
  · unfold tableAddress
    omega
  · simpa only [Nat.add_zero] using
      Query.table_lt_outputEnd I ε r v i j 0 hr (activeVertices_valid I v hv) hi hj (by omega)

private theorem OutputTable.zero_mass {I : Instance} {ε : ℝ} {r : ℕ} {A : InnerInput} {s : Store}
    (h : OutputTable I ε r A s) (v : ℕ) (hv : v∈activeVertices I) :
    s.rm (tableBase I ε r+4*v)=1-dpValue A (buildTable A) v 0 0 := by
  have hq : 0<tickLimit A := by
    unfold tickLimit
    apply Nat.ceil_pos.mpr
    exact div_pos (by norm_num) (sq_pos_of_pos A.accuracy_pos)
  have hh := (h v hv 0 hq 0 hq).1
  simpa [tableAddress,dpValue,Nat.not_le.mpr hq] using hh

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured Preprocess TargetRecords

private theorem Invariant.readonly {I : Instance} {ε : ℝ} {k : ℕ} {s t : Store}
    (h : Invariant I ε k s) (hrt : RuntimeReady I ε t) (hreg : Registers I ε k t)
    (hn : t.nm = s.nm) (hr : t.rm = s.rm) : Invariant I ε k t := by
  refine ⟨hrt,hreg,?_,?_,?_,?_⟩
  · simpa only [OutputParents,hn] using h.parents
  · simpa only [RecordMap,RecordRep,hn,hr] using h.records
  · simpa only [CompletedTables,OutputTable,hn,hr] using h.tables
  · simpa only [FutureZero,hr] using h.future

private theorem initialized_invariant (input : RAMInput) (I : Instance) (ε : ℝ) (s : Store)
    (hrt : RuntimeReady I ε s) (hB : s.nr 11 = queueCapacity I)
    (hp : OutputParents I s) (hrec : RecordMap I ε (answerBranch I 0) s)
    (hf : FutureZero I ε 0 s) : Invariant I ε 0 (initialized input s) := by
  refine ⟨initialized_runtime input I ε s hrt,initialized_registers input I ε s hrt hB,
    hp,hrec,completedTables_zero I ε _,hf⟩

private theorem Invariant.finished {I : Instance} {ε : ℝ} {s : Store}
    (h : Invariant I ε (outerInputs I ε).length s) (pc : ℕ) :
    Query.QueryReady I ε (s.at pc) := by
  apply runtime_outputs_queryReady I ε s h.runtime h.parents _ h.tables pc
  intro v hv
  have hh := h.records v hv
  simpa only [branchesAfter_end] using hh

private theorem loop_run_of_body (input : RAMInput) (I : Instance) (ε : ℝ)
    (table : Cmd) (bound : ℕ)
    (hbody : ∀ k s, k < (outerInputs I ε).length → Invariant I ε k s →
      ∃ t n, Run input (body table) s t n ∧ Invariant I ε (k+1) t ∧ n ≤ bound)
    (s : Store) (hs : Invariant I ε 0 s) :
    ∃ t n, Run input (loopCmd table) s t n ∧
      Invariant I ε (outerInputs I ε).length t ∧
      n ≤ (bound+2)*(outerInputs I ε).length+1 := by
  apply run_bounded_loop input (.nat .lt 243 132) (body table)
    (outerInputs I ε).length bound (Invariant I ε) _ hbody 0 s (by omega) hs
  intro k t hk ht
  simp only [Guard.eval,natTest,ht.registers.index,ht.runtime.numeric.count]

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

private theorem seedRecords_nat_disjoint : Disjoint persistentRegisters seedRecordsCmd.natWrites := by decide

private theorem seedRecords_real_disjoint : Disjoint persistentRegisters seedRecordsCmd.realWrites := by decide

private theorem markRecords_nat_disjoint : Disjoint persistentRegisters markRecordsCmd.natWrites := by decide

private theorem markRecords_real_disjoint : Disjoint persistentRegisters markRecordsCmd.realWrites := by decide

private theorem seedRecords_persistent (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input seedRecordsCmd s t steps)
    (hr : (121 ≤ r ∧ r ≤ 153) ∨ (243 ≤ r ∧ r ≤ 259)) :
    t.nr r = s.nr r ∧ t.rr r = s.rr r := by
  have hm : r ∈ persistentRegisters := by simpa [persistentRegisters] using hr
  exact ⟨h.nat_frame r (fun hw => Finset.disjoint_left.mp seedRecords_nat_disjoint hm hw),
    h.real_frame r (fun hw => Finset.disjoint_left.mp seedRecords_real_disjoint hm hw)⟩

private theorem markRecords_persistent (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input markRecordsCmd s t steps)
    (hr : (121 ≤ r ∧ r ≤ 153) ∨ (243 ≤ r ∧ r ≤ 259)) :
    t.nr r = s.nr r ∧ t.rr r = s.rr r := by
  have hm : r ∈ persistentRegisters := by simpa [persistentRegisters] using hr
  exact ⟨h.nat_frame r (fun hw => Finset.disjoint_left.mp markRecords_nat_disjoint hm hw),
    h.real_frame r (fun hw => Finset.disjoint_left.mp markRecords_real_disjoint hm hw)⟩

private theorem seedRecords_capacity (input : RAMInput) (s t : Store) (steps : ℕ)
    (h : Run input seedRecordsCmd s t steps) : t.nr 11 = s.nr 11 := by
  exact h.nat_frame 11 (by decide)

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem Constants.recounter {A : InnerInput} (E : Layout A) (i j a b : ℕ)
    (s t : Store) (h : Constants E i j s)
    (hn : ∀ r, r ≠ 201 → r ≠ 202 → r ≠ 203 → t.nr r = s.nr r)
    (hr : t.rr = s.rr) (ha : t.nr 201 = a) (hb : t.nr 202 = b)
    (hab : t.nr 203 = E.address 0 a b) : Constants E a b t := by
  rcases h with ⟨hn0,hs,hq,hz,ho,hcs,hh,hl,hm,harr,hbase,_,_,_,hcount,hw,hp,hcap,hR,hls,
    hLength,hCost,hZ⟩
  exact ⟨(hn 121 (by decide) (by decide) (by decide)).trans hn0,
    (hn 123 (by decide) (by decide) (by decide)).trans hs,
    (hn 124 (by decide) (by decide) (by decide)).trans hq,
    (hn 125 (by decide) (by decide) (by decide)).trans hz,
    (hn 126 (by decide) (by decide) (by decide)).trans ho,
    (hn 129 (by decide) (by decide) (by decide)).trans hcs,
    (hn 137 (by decide) (by decide) (by decide)).trans hh,
    (hn 139 (by decide) (by decide) (by decide)).trans hl,
    (hn 141 (by decide) (by decide) (by decide)).trans hm,
    (hn 142 (by decide) (by decide) (by decide)).trans harr,
    (hn 200 (by decide) (by decide) (by decide)).trans hbase,ha,hb,hab,
    (hn 204 (by decide) (by decide) (by decide)).trans hcount,
    (hn 205 (by decide) (by decide) (by decide)).trans hw,
    (hn 206 (by decide) (by decide) (by decide)).trans hp,
    (hn 207 (by decide) (by decide) (by decide)).trans hcap,
    (hn 208 (by decide) (by decide) (by decide)).trans hR,
    (hn 209 (by decide) (by decide) (by decide)).trans hls,
    (congrFun hr 200).trans hLength,(congrFun hr 201).trans hCost,(congrFun hr 202).trans hZ⟩

private theorem tableColumnStore_constants {A : InnerInput} (E : Layout A) (i j : ℕ)
    (input : RAMInput) (s : Store) (h : Constants E i (j+1) s) :
    Constants E i j (tableColumnStore input s) := by
  have hcopy := h
  rcases hcopy with ⟨_,_,_,_,hone,hstride,_,_,_,_,_,hi,hj,haddr,_⟩
  apply Constants.recounter E i (j+1) i j s (tableColumnStore input s) h
  · intro r _ h2 h3
    simp [tableColumnStore,evalAtoms,tableColumnPrepare,Atom.eval,Store.ofRAM,Store.at,
      ramStep,evalNat,h2,h3]
  · rfl
  · simp [tableColumnStore,evalAtoms,tableColumnPrepare,Atom.eval,Store.ofRAM,Store.at,ramStep,hi]
  · simp [tableColumnStore,evalAtoms,tableColumnPrepare,Atom.eval,Store.ofRAM,Store.at,
      ramStep,evalNat,hj,hone]
  · have haddress : E.address 0 i (j+1) = E.address 0 i j+4*A.I.graph.n := by
      unfold Layout.address
      ring
    simp [tableColumnStore,evalAtoms,tableColumnPrepare,Atom.eval,Store.ofRAM,Store.at,
      ramStep,evalNat,haddr,hstride,haddress]

private theorem tableRowStore_constants {A : InnerInput} (E : Layout A) (i : ℕ)
    (input : RAMInput) (s : Store) (h : Constants E (i+1) 0 s) :
    Constants E i (tickLimit A) (tableRowStore input s) := by
  have hcopy := h
  rcases hcopy with ⟨_,_,hq,_,hone,_,_,_,_,_,_,hi,_,haddr,_⟩
  apply Constants.recounter E (i+1) 0 i (tickLimit A) s (tableRowStore input s) h
  · intro r h1 h2 _
    simp [tableRowStore,evalAtoms,tableRowPrepare,Atom.eval,Store.ofRAM,Store.at,
      ramStep,evalNat,h1,h2]
  · rfl
  · simp [tableRowStore,evalAtoms,tableRowPrepare,Atom.eval,Store.ofRAM,Store.at,
      ramStep,evalNat,hi,hone]
  · simp [tableRowStore,evalAtoms,tableRowPrepare,Atom.eval,Store.ofRAM,Store.at,ramStep,hq]
  · have haddress : E.address 0 (i+1) 0 = E.address 0 i (tickLimit A) := by
      unfold Layout.address
      ring
    simp [tableRowStore,evalAtoms,tableRowPrepare,Atom.eval,Store.ofRAM,Store.at,
      ramStep,haddr,haddress]

private theorem rowTable_zero (A : InnerInput) (T : Table) (i : ℕ) : rowTable A T i 0 = T := rfl

private theorem rowTable_succ (A : InnerInput) (T : Table) (i j : ℕ) :
    rowTable A T i (j+1) = rowTable A (buildLayer A T i j) i j := by
  simp [rowTable,List.range_succ,List.reverse_append]

private theorem rowsTable_zero (A : InnerInput) (T : Table) : rowsTable A T 0 = T := rfl

private theorem rowsTable_succ (A : InnerInput) (T : Table) (i : ℕ) :
    rowsTable A T (i+1) = rowsTable A (rowTable A T i (tickLimit A)) i := by
  simp [rowsTable,List.range_succ,List.reverse_append]

private theorem rowsTable_eq_buildTable (A : InnerInput) :
    rowsTable A (fun _ _ _ => ⟨1,.lengthTick,0⟩) (tickLimit A) = buildTable A := rfl

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem Constants.column_guard {A : InnerInput} (E : Layout A) (i j : ℕ)
    (s : Store) (h : Constants E i j s) :
    (Guard.nat .lt 125 202).eval s = decide (0 < j) := by
  rcases h with ⟨_,_,_,hz,_,_,_,_,_,_,_,_,hj,_⟩
  simp [Guard.eval,natTest,hz,hj]

private theorem Constants.row_guard {A : InnerInput} (E : Layout A) (i j : ℕ)
    (s : Store) (h : Constants E i j s) :
    (Guard.nat .lt 125 201).eval s = decide (0 < i) := by
  rcases h with ⟨_,_,_,hz,_,_,_,_,_,_,_,hi,_⟩
  simp [Guard.eval,natTest,hz,hi]

private theorem tableRow_run_of_layer_contract {A : InnerInput} (E : Layout A) (ε : ℝ)
    (layer : Cmd) (bound : ℕ) (hLayer : LayerContract E ε layer bound)
    (T : Table) (i count : ℕ) (s : Store)
    (hi : i < tickLimit A) (hcount : count ≤ tickLimit A)
    (hc : Constants E i count s) (hg : GraphMemory E s) (ht : TableValues E T s)
    (hadj : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm) :
    ∃ out n, Run (encodeInput A.I ε) (tableRowCmd layer) s out n ∧
      n ≤ (bound+4)*count+1 ∧ RowResult E T (rowTable A T i count) i count s out := by
  induction count generalizing T s with
  | zero =>
      refine ⟨s,1,Run.loopFalse ?_,by simp,?_⟩
      · simpa using Constants.column_guard E i 0 s hc
      · refine ⟨hc,hg,ht,hadj,?_,OutsideTableFrame.refl E s,?_⟩
        · intro v hv b hb
          omega
        · intro v hv a ha b hb _ hcell
          exact hcell
  | succ count ih =>
      let p := tableColumnStore (encodeInput A.I ε) s
      have hprep : Run (encodeInput A.I ε) (.atoms tableColumnPrepare) s p 2 :=
        run_atoms _ tableColumnPrepare s
      have hpc := tableColumnStore_constants E i count (encodeInput A.I ε) s hc
      obtain ⟨t,nL,hL,hnL,hcL,hgL,htL,hsL,hfL,hkeepL⟩ :=
        hLayer T i count p hi (by omega) hpc hg ht hadj
      have hadjL := OutsideTableFrame.adjacency E p t hfL hadj
      obtain ⟨out,nT,hT,hnT,hout⟩ := ih (T := buildLayer A T i count) (s := t)
        (by omega) hcL hgL htL hadjL
      refine ⟨out,1+(2+nL)+1+nT,Run.loopTrue ?_ (Run.seq hprep hL) hT,?_,?_⟩
      · simpa using Constants.column_guard E i (count+1) s hc
      · rw [Nat.mul_succ]
        omega
      · rw [rowTable_succ]
        refine ⟨hout.constants,hout.graph,hout.table,hout.adjacency,?_,?_,?_⟩
        · intro v hv b hb
          by_cases hbc : b < count
          · exact hout.stored v hv b hbc
          · have he : b = count := by omega
            subst b
            exact hout.kept v hv i hi count (by omega) (Or.inr le_rfl) (hsL v hv)
        · exact (outsideTableFrame_readonly E s p rfl rfl).trans (hfL.trans hout.frame)
        · intro v hv a ha b hb houtside hcell
          exact hout.kept v hv a ha b hb (by omega)
            (hkeepL v hv a ha b hb (by omega) hcell)

private theorem table_run_of_layer_contract {A : InnerInput} (E : Layout A) (ε : ℝ)
    (layer : Cmd) (bound : ℕ) (hLayer : LayerContract E ε layer bound)
    (T : Table) (count : ℕ) (s : Store) (hcount : count ≤ tickLimit A)
    (hc : Constants E count 0 s) (hg : GraphMemory E s) (ht : TableValues E T s)
    (hadj : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm) :
    ∃ out n, Run (encodeInput A.I ε) (tableCmd layer) s out n ∧
      n ≤ ((bound+4)*tickLimit A+5)*count+1 ∧
      RowsResult E T (rowsTable A T count) count s out := by
  induction count generalizing T s with
  | zero =>
      refine ⟨s,1,Run.loopFalse ?_,by simp,?_⟩
      · simpa using Constants.row_guard E 0 0 s hc
      · refine ⟨hc,hg,ht,hadj,?_,OutsideTableFrame.refl E s,?_⟩
        · intro v hv a ha
          omega
        · intro v hv a ha b hb _ hcell
          exact hcell
  | succ count ih =>
      let p := tableRowStore (encodeInput A.I ε) s
      have hprep : Run (encodeInput A.I ε) (.atoms tableRowPrepare) s p 2 :=
        run_atoms _ tableRowPrepare s
      have hpc := tableRowStore_constants E count (encodeInput A.I ε) s hc
      obtain ⟨t,nR,hR,hnR,hrow⟩ := tableRow_run_of_layer_contract E ε layer bound hLayer T
        count (tickLimit A) p (by omega) le_rfl hpc hg ht hadj
      obtain ⟨out,nT,hT,hnT,hout⟩ := ih (T := rowTable A T count (tickLimit A)) (s := t)
        (by omega) hrow.constants hrow.graph hrow.table hrow.adjacency
      refine ⟨out,1+(2+nR)+1+nT,Run.loopTrue ?_ (Run.seq hprep hR) hT,?_,?_⟩
      · simpa using Constants.row_guard E (count+1) 0 s hc
      · rw [Nat.mul_succ]
        omega
      · rw [rowsTable_succ]
        refine ⟨hout.constants,hout.graph,hout.table,hout.adjacency,?_,?_,?_⟩
        · intro v hv a ha b hb
          by_cases hac : a < count
          · exact hout.stored v hv a hac b hb
          · have he : a = count := by omega
            subst a
            exact hout.kept v hv count (by omega) b hb le_rfl (hrow.stored v hv b hb)
        · exact (outsideTableFrame_readonly E s p rfl rfl).trans (hrow.frame.trans hout.frame)
        · intro v hv a ha b hb houtside hcell
          exact hout.kept v hv a ha b hb (by omega)
            (hrow.kept v hv a ha b hb (Or.inl (by omega)) hcell)

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem writeCell_run (input : RAMInput) (s : Store) :
    Run input writeCellCmd s (writtenCell input s) 12 := run_atoms input writeCellAtoms s

private theorem writtenCell_natural (input : RAMInput) (s : Store) :
    (writtenCell input s).nm =
      Function.update (Function.update (Function.update s.nm
        (s.nr 230) (s.nr 231)) (s.nr 230 + 1) (s.nr 232))
        (s.nr 230 + 2) (s.nr 233) := by
  simp [writtenCell, evalAtoms, writeCellAtoms, Atom.eval, Store.ofRAM, ramStep,
    Store.at, evalNat]

private theorem writtenCell_real (input : RAMInput) (s : Store) :
    (writtenCell input s).rm =
      Function.update (Function.update (Function.update s.rm
        (s.nr 230) (1 - s.rr 230)) (s.nr 230 + 1) (s.rr 231))
        (s.nr 230 + 2) (s.rr 232) := by
  simp [writtenCell, evalAtoms, writeCellAtoms, Atom.eval, Store.ofRAM, ramStep,
    Store.at, evalNat, evalReal]

private theorem writtenCell_values (input : RAMInput) (s : Store) :
    (writtenCell input s).rm (s.nr 230) = 1 - s.rr 230 ∧
    (writtenCell input s).nm (s.nr 230) = s.nr 231 ∧
    (writtenCell input s).nm (s.nr 230 + 1) = s.nr 232 ∧
    (writtenCell input s).nm (s.nr 230 + 2) = s.nr 233 ∧
    (writtenCell input s).rm (s.nr 230 + 1) = s.rr 231 ∧
    (writtenCell input s).rm (s.nr 230 + 2) = s.rr 232 := by
  simp [writtenCell_natural, writtenCell_real]

private theorem writtenCell_frame (input : RAMInput) (s : Store) (a : ℕ)
    (ha0 : a ≠ s.nr 230) (ha1 : a ≠ s.nr 230 + 1) (ha2 : a ≠ s.nr 230 + 2) :
    (writtenCell input s).nm a = s.nm a ∧ (writtenCell input s).rm a = s.rm a := by
  simp [writtenCell_natural, writtenCell_real, ha0, ha1, ha2]

private theorem writtenCell_above_table {A : InnerInput} (E : Layout A) (input : RAMInput)
    (u i j : ℕ) (s : Store) (hu : u < A.I.graph.n) (hi : i < tickLimit A)
    (hj : j < tickLimit A) (haddr : s.nr 230 = E.address u i j)
    (a : ℕ) (ha : E.base + 4 * A.I.graph.n * tickLimit A ^ 2 ≤ a) :
    (writtenCell input s).nm a = s.nm a ∧ (writtenCell input s).rm a = s.rm a := by
  have h0 := E.address_lt_end u i j 0 hu hi hj (by omega)
  have h1 := E.address_lt_end u i j 1 hu hi hj (by omega)
  have h2 := E.address_lt_end u i j 2 hu hi hj (by omega)
  apply writtenCell_frame <;> rw [haddr] <;> omega

private theorem writtenCell_tableValues {A : InnerInput} (E : Layout A) (input : RAMInput)
    (T : Table) (u i j : ℕ) (c : Cell) (s : Store)
    (hT : TableValues E T s) (hu : u ∈ activeVertices A.I) (hj : j < tickLimit A)
    (haddr : s.nr 230 = E.address u i j) (hkey : s.rr 230 = c.value) :
    TableValues E (putCell T u i j c) (writtenCell input s) := by
  intro v hv a ha b hb
  by_cases he : v = u ∧ a = i ∧ b = j
  · rcases he with ⟨rfl, rfl, rfl⟩
    simpa [putCell, haddr, hkey] using (writtenCell_values input s).1
  · have hne (off : ℕ) (hoff : off < 4) :
        E.address v a b ≠ E.address u i j + off := by
      simpa only [Nat.add_zero] using
        E.address_block_separated v u a b i j 0 off
          (activeVertices_valid A.I v hv) (activeVertices_valid A.I u hu) hb hj
          (by omega) hoff he
    have hf := (writtenCell_frame input s (E.address v a b)
      (by simpa [haddr] using hne 0 (by omega))
      (by simpa [haddr] using hne 1 (by omega))
      (by simpa [haddr] using hne 2 (by omega))).2
    rw [hf]
    simpa [putCell, he] using hT v hv a ha b hb

private theorem writtenCell_stored {A : InnerInput} (E : Layout A) (input : RAMInput)
    (T : Table) (u i j : ℕ) (c : Cell) (s : Store)
    (haddr : s.nr 230 = E.address u i j) (hkey : s.rr 230 = c.value)
    (htag : s.nr 231 = parentTag c.parent) (hparent : s.nr 232 = parentVertex c.parent)
    (hrank : s.nr 233 = c.rank)
    (hpgf : ∀ v, c.parent = .edge v →
      s.rr 231 = lengthPGF A v u ∧ s.rr 232 = costPGF A v u) :
    StoredCell E (putCell T u i j c) u i j (writtenCell input s) := by
  have h := writtenCell_values input s
  simp only [StoredCell, putCell, true_and, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [haddr, hkey] using h.1
  · simpa [haddr, htag] using h.2.1
  · simpa [haddr, hparent] using h.2.2.1
  · simpa [haddr, hrank] using h.2.2.2.1
  · intro v hv
    rcases hpgf v hv with ⟨hl, hc⟩
    constructor
    · simpa [haddr, hl] using h.2.2.2.2.1
    · simpa [haddr, hc] using h.2.2.2.2.2

private theorem writtenCell_stored_other {A : InnerInput} (E : Layout A) (input : RAMInput)
    (T : Table) (v u i j a b : ℕ) (c : Cell) (s : Store)
    (hT : StoredCell E T v a b s) (hv : v ∈ activeVertices A.I)
    (hu : u ∈ activeVertices A.I) (hb : b < tickLimit A) (hj : j < tickLimit A)
    (hne : ¬ (v = u ∧ a = i ∧ b = j)) (haddr : s.nr 230 = E.address u i j) :
    StoredCell E (putCell T u i j c) v a b (writtenCell input s) := by
  have hf (off : ℕ) (hoff : off < 4) :
      (writtenCell input s).nm (E.address v a b + off) = s.nm (E.address v a b + off) ∧
      (writtenCell input s).rm (E.address v a b + off) = s.rm (E.address v a b + off) := by
    apply writtenCell_frame
    all_goals
      rw [haddr]
      first
      | exact E.address_block_separated v u a b i j off 0
          (activeVertices_valid A.I v hv) (activeVertices_valid A.I u hu) hb hj hoff (by omega) hne
      | exact E.address_block_separated v u a b i j off 1
          (activeVertices_valid A.I v hv) (activeVertices_valid A.I u hu) hb hj hoff (by omega) hne
      | exact E.address_block_separated v u a b i j off 2
          (activeVertices_valid A.I v hv) (activeVertices_valid A.I u hu) hb hj hoff (by omega) hne
  have hf0 := hf 0 (by omega)
  simp only [Nat.add_zero] at hf0
  have hf1 := hf 1 (by omega)
  have hf2 := hf 2 (by omega)
  simpa only [StoredCell, putCell, if_neg hne, Nat.add_zero, hf0.1, hf0.2,
    hf1.1, hf1.2, hf2.1, hf2.2] using hT

private theorem Heap.delete_run {A : InnerInput} (E : Layout A) (S : LayerState) (i j u : ℕ)
    (input : RAMInput) (s : Store) (hheap : Heap E S s)
    (hsub : S.queue.Sublist (activeVertices A.I)) (hu : u ∈ S.queue)
    (h0 : s.nr 0 = E.capacity + (activeVertices A.I).idxOf u)
    (h1 : s.nr 1 = E.winner) (h2 : s.nr 2 = E.parent) (h3 : s.nr 3 = 0)
    (h4 : s.nr 4 = 1) (h10 : s.nr 10 = 0) (hkey : s.rr 2 = S.keys u) :
    ∃ out steps, Run input Queue.updateLeaf s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * E.capacity) + 6 ∧
      Heap E (settleState S i j u) out ∧
      Queue.WinnerFrame E.winner (2 * E.capacity) s out := by
  have hua : u ∈ activeVertices A.I := hsub.subset hu
  have hindex := List.idxOf_lt_length_of_mem hua
  have hcap : 0 < E.capacity := by rw [E.capacity_eq]; positivity
  have hparent : Queue.ParentLayout (2 * E.capacity) s := by
    refine ⟨?_, ?_, h3, ?_⟩
    · rw [h0]
      have := E.active_fit
      omega
    · simpa only [h1, h2] using E.winner_before_parent
    · intro v hv
      simpa only [h2] using hheap.2 v hv
  obtain ⟨out, steps, hrun, hsteps, hz, hheader, hparents, hrecords, hframe⟩ :=
    Queue.updateLeaf_refines input E.capacity (layerLeaf E S) s hparent h4
      (by rw [h0]; omega) (by rw [h0]; omega) (by simpa only [h1] using hheap.1)
  have hleaf : Function.update (layerLeaf E S) (s.nr 0) ⟨s.nr 10, s.rr 2⟩ =
      layerLeaf E (settleState S i j u) := by
    rw [h0, h10, hkey]
    change Function.update (Queue.activeLeaf (activeVertices A.I) S.queue S.keys E.capacity)
      (E.capacity + (activeVertices A.I).idxOf u) ⟨0, S.keys u⟩ =
      Queue.activeLeaf (activeVertices A.I) (S.queue.erase u) S.keys E.capacity
    exact (Queue.activeLeaf_delete_vertex (activeVertices A.I) S.queue S.keys E.capacity u
      (activeVertices_nodup A.I) ((activeVertices_nodup A.I).sublist hsub) hua).symm
  rw [hleaf] at hrecords
  have hp2 : out.nr 2 = E.parent := (hheader 2 (by omega) (by omega)).trans h2
  refine ⟨out, steps, hrun, hsteps, ⟨?_, ?_⟩, ?_⟩
  · simpa only [h1] using hrecords
  · intro v hv
    simpa only [hp2] using hparents.2.2.2 v hv
  · simpa only [h1] using hframe

private theorem Heap.root_record {A : InnerInput} (E : Layout A) (S : LayerState) (s : Store)
    (hheap : Heap E S s) (hsub : S.queue.Sublist (activeVertices A.I)) (hne : S.queue ≠ []) :
    Queue.readRecord s (E.winner + 1) =
      Queue.vertexRecord (activeVertices A.I) S.keys (pickedVertex S) := by
  have hd : (Queue.readRecord s (E.winner + 1)).decode =
      some (Queue.vertexRecord (activeVertices A.I) S.keys (pickedVertex S)) := by
    rw [hheap.1 1 (by have := E.capacity_pos; omega)]
    change (Queue.heapTruth E.capacity
      (Queue.activeLeaf (activeVertices A.I) S.queue S.keys E.capacity) 1).decode = _
    rw [E.capacity_eq]
    exact Queue.activeLeaf_firstMin (activeVertices A.I) S.queue S.keys E.height
      (activeVertices_nodup A.I) hsub (by simpa [E.capacity_eq] using E.active_fit)
      (S.queue.headD 0) hne
  unfold Queue.Record.decode at hd
  split at hd
  · contradiction
  · exact Option.some.inj hd

private theorem popLoaded_values {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (input : RAMInput) (s : Store) (h : LayerRep E i j S s)
    (hne : S.queue ≠ []) :
    let u := pickedVertex S
    let k := (activeVertices A.I).idxOf u
    let t := popLoaded input s
    t.nr 211 = u ∧ t.nr 212 = k + 1 ∧ t.nr 224 = k ∧
    t.nr 230 = E.address u i j ∧ t.rr 230 = S.keys u ∧
    t.nr 231 = parentTag (S.parents u) ∧ t.nr 232 = parentVertex (S.parents u) ∧
    t.nr 233 = S.nextRank ∧
    ∀ v, S.parents u = .edge v → t.rr 231 = lengthPGF A v u ∧ t.rr 232 = costPGF A v u := by
  let u := pickedVertex S
  let k := (activeVertices A.I).idxOf u
  have huq := pickedVertex_mem S hne
  have hu : u ∈ activeVertices A.I := h.2.2.2.2.2.1.subset huq
  have hk : (activeVertices A.I)[k]? = some u := List.getElem?_idxOf hu
  have hr := Heap.root_record E S s h.2.2.1 h.2.2.2.2.2.1 hne
  have htoken : s.nm (E.winner + 1) = k + 1 := congrArg Queue.Record.token hr
  have hkey : s.rm (E.winner + 1) = S.keys u := congrArg Queue.Record.key hr
  have harray := (h.2.1 k u hk).2
  rcases h.2.2.2.1 k u hk with ⟨hkkey, htag, hparent, hpgf⟩
  rcases h.1 with ⟨hn, hsource, hq, hz, hone, hcol, hheads, hlinks, hmap, harr,
    hbase, hi, hj, hlayer, hN, hW, hP, hB, hR, hrow, hμ, hν, hratio⟩
  have hrank := h.2.2.2.2.2.2
  have haddr : E.address 0 i j + 4 * u = E.address u i j := by
    unfold Layout.address
    ring
  simp only
  simp [popLoaded, evalAtoms, popLoadAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
    evalNat, hone, hW, htoken, hkey, harr, harray, hR, hN, htag, hparent,
    hlayer, hrank, Nat.add_assoc, haddr, show u + u + (u + u) = 4 * u by omega]
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hparent
  · intro v hv
    simpa only [Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hpgf v hv

private theorem writtenCell_graph {A : InnerInput} (E : Layout A) (i j u : ℕ)
    (input : RAMInput) (s : Store) (hg : GraphMemory E s)
    (hu : u < A.I.graph.n) (hi : i < tickLimit A) (hj : j < tickLimit A)
    (haddr : s.nr 230 = E.address u i j) : GraphMemory E (writtenCell input s) := by
  intro k v hv
  have hm := writtenCell_above_table E input u i j s hu hi hj haddr
    (E.ordinalMap + v) (by have := E.table_before_map; omega)
  have ha := writtenCell_above_table E input u i j s hu hi hj haddr
    (E.activeArray + k) (by have := E.table_before_array; omega)
  exact ⟨hm.1.trans (hg k v hv).1, ha.1.trans (hg k v hv).2⟩

private theorem writtenCell_heap {A : InnerInput} (E : Layout A) (i j u : ℕ)
    (S : LayerState) (input : RAMInput) (s : Store) (hh : Heap E S s)
    (hu : u < A.I.graph.n) (hi : i < tickLimit A) (hj : j < tickLimit A)
    (haddr : s.nr 230 = E.address u i j) : Heap E S (writtenCell input s) := by
  have hw := E.table_end_le_winner
  constructor
  · intro node hn
    have hf := writtenCell_above_table E input u i j s hu hi hj haddr
      (E.winner + node) (by omega)
    simpa only [Queue.readRecord, hf.1, hf.2] using hh.1 node hn
  · intro node hn
    have hp := E.winner_before_parent
    have hf := writtenCell_above_table E input u i j s hu hi hj haddr
      (E.parent + node) (by omega)
    exact hf.1.trans (hh.2 node hn)

private theorem writtenCell_arrays {A : InnerInput} (E : Layout A) (i j u : ℕ)
    (S : LayerState) (input : RAMInput) (s : Store) (ha : Arrays E S s)
    (hu : u < A.I.graph.n) (hi : i < tickLimit A) (hj : j < tickLimit A)
    (haddr : s.nr 230 = E.address u i j) : Arrays E S (writtenCell input s) := by
  apply Arrays.transfer_above_temp E S s (writtenCell input s) ha
  intro a hab
  apply writtenCell_above_table E input u i j s hu hi hj haddr a
  have h1 := E.table_end_le_winner
  have h2 := E.winner_le_temp
  omega

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem pop_correct {A : InnerInput} (E : Layout A) (i j : ℕ) (S : LayerState)
    (input : RAMInput) (s : Store) (hS : LayerRep E i j S s)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ []) :
    ∃ out steps, Run input popCmd s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * E.capacity) + 43 ∧
      LayerRep E i j (settleState S i j (pickedVertex S)) out ∧
      out.nr 211 = pickedVertex S ∧
      StoredCell E (settleState S i j (pickedVertex S)).table (pickedVertex S) i j out ∧
      (∀ a, a < E.winner →
        (a < E.base ∨ E.base + 4 * A.I.graph.n * tickLimit A ^ 2 ≤ a) →
        out.nm a = s.nm a ∧ out.rm a = s.rm a) ∧
      (∀ v a b, v ∈ activeVertices A.I → a < tickLimit A → b < tickLimit A →
        ¬ (v = pickedVertex S ∧ a = i ∧ b = j) →
        StoredCell E S.table v a b s →
        StoredCell E (settleState S i j (pickedVertex S)).table v a b out) := by
  let u := pickedVertex S
  let k := (activeVertices A.I).idxOf u
  let c : Cell := ⟨S.keys u, S.parents u, S.nextRank⟩
  have huq : u ∈ S.queue := pickedVertex_mem S hne
  have hua : u ∈ activeVertices A.I := hS.2.2.2.2.2.1.subset huq
  have hun : u < A.I.graph.n := activeVertices_valid A.I u hua
  let p := popLoaded input s
  have hload : Run input (.atoms popLoadAtoms) s p 17 := run_atoms input popLoadAtoms s
  have hp : LayerRep E i j S p := LayerRep.after_readonly E i j S input _ s p 17 hS hload
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hu, htoken, hk, haddr, hkey, htag, hparent, hrank, hpgf⟩ :=
    popLoaded_values E i j S input s hS hne
  let w := writtenCell input p
  have hwrite : Run input writeCellCmd p w 12 := writeCell_run input p
  have hwc : Constants E i j w := Constants.after_run E i j input _ p w 12 hp.1 hwrite
    (by decide) (by decide)
  have hwg : GraphMemory E w := writtenCell_graph E i j u input p hp.2.1 hun hi hj haddr
  have hwh : Heap E S w := writtenCell_heap E i j u S input p hp.2.2.1 hun hi hj haddr
  have hwa : Arrays E S w := writtenCell_arrays E i j u S input p hp.2.2.2.1 hun hi hj haddr
  have hwT : TableValues E (settleState S i j u).table w :=
    writtenCell_tableValues E input S.table u i j c p hp.2.2.2.2.1 hua hj haddr hkey
  have hwcell : StoredCell E (settleState S i j u).table u i j w :=
    writtenCell_stored E input S.table u i j c p haddr hkey htag hparent hrank hpgf
  let q := evalAtoms input deletePrepareAtoms w
  have hprep : Run input (.atoms deletePrepareAtoms) w q 7 := run_atoms input deletePrepareAtoms w
  have hqc : Constants E i j q := Constants.after_run E i j input _ w q 7 hwc hprep
    (by decide) (by decide)
  have hqnm : q.nm = w.nm := hprep.natMemory_frame (by decide)
  have hqrm : q.rm = w.rm := hprep.realMemory_frame (by decide)
  have hqh : Heap E S q := by
    simpa only [Heap, Queue.Represents, Queue.readRecord, hqnm, hqrm] using hwh
  have hqg : GraphMemory E q := by simpa only [GraphMemory, hqnm] using hwg
  have hqa : Arrays E S q := by simpa only [Arrays, hqnm, hqrm] using hwa
  have hqT : TableValues E (settleState S i j u).table q := by
    simpa only [TableValues, hqrm] using hwT
  have hqcell : StoredCell E (settleState S i j u).table u i j q := by
    simpa only [StoredCell, hqnm, hqrm] using hwcell
  have hwk : w.nr 224 = k := (hwrite.nat_frame 224 (by decide)).trans hk
  have hwkey : w.rr 230 = S.keys u := (hwrite.real_frame 230 (by decide)).trans hkey
  obtain ⟨_, _, _, _, hwone, _, _, _, _, _, _, _, _, _, _, hwW, hwP, hwB, _, _, _, _, _⟩ := hwc
  have hq0 : q.nr 0 = E.capacity + k := by
    simp [q, evalAtoms, deletePrepareAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
      evalNat, hwB, hwk]
  have hq1 : q.nr 1 = E.winner := by
    simp [q, evalAtoms, deletePrepareAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, hwW]
  have hq2 : q.nr 2 = E.parent := by
    simp [q, evalAtoms, deletePrepareAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, hwP]
  have hq3 : q.nr 3 = 0 := by
    simp [q, evalAtoms, deletePrepareAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at]
  have hq4 : q.nr 4 = 1 := by
    simp [q, evalAtoms, deletePrepareAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at]
  have hq10 : q.nr 10 = 0 := by
    simp [q, evalAtoms, deletePrepareAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at]
  have hqkey : q.rr 2 = S.keys u := by
    simp [q, evalAtoms, deletePrepareAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, hwkey]
  obtain ⟨x, n, hdelete, hdeletecost, hxheap, hxframe⟩ :=
    Heap.delete_run E S i j u input q hqh hS.2.2.2.2.2.1 huq hq0 hq1 hq2 hq3 hq4 hq10 hqkey
  have hxc : Constants E i j x := Constants.after_run E i j input _ q x n hqc hdelete
    (by decide) (by decide)
  have hxg : GraphMemory E x := GraphMemory.transfer E q x hqg (winnerFrame_below E q x hxframe)
  have hxa : Arrays E (settleState S i j u) x :=
    Arrays.transfer_winner_frame E S q x hqa hxframe
  have hxT : TableValues E (settleState S i j u).table x :=
    TableValues.transfer E _ q x hqT (winnerFrame_below E q x hxframe)
  have hxcell : StoredCell E (settleState S i j u).table u i j x :=
    StoredCell.transfer E _ u i j q x hun hi hj hqcell (winnerFrame_below E q x hxframe)
  let out := popFinish.eval input x
  have hfinish : Run input (.atom popFinish) x out 1 := Run.atom popFinish x
  have houtc : Constants E i j out := Constants.after_run E i j input _ x out 1 hxc hfinish
    (by decide) (by decide)
  have houtnm : out.nm = x.nm := hfinish.natMemory_frame (by decide)
  have houtrm : out.rm = x.rm := hfinish.realMemory_frame (by decide)
  have htail : Run input (.seq writeCellCmd (.seq (.atoms deletePrepareAtoms)
      (.seq Queue.updateLeaf (.atom popFinish)))) p out (12 + (7 + (n + 1))) :=
    Run.seq hwrite (Run.seq hprep (Run.seq hdelete hfinish))
  have hprefix : Run input (.seq (.atoms popLoadAtoms) (.seq writeCellCmd
      (.seq (.atoms deletePrepareAtoms) Queue.updateLeaf))) s x (17 + (12 + (7 + n))) :=
    Run.seq hload (Run.seq hwrite (Run.seq hprep hdelete))
  have hxrank : x.nr 210 = S.nextRank :=
    (hprefix.nat_frame 210 (by decide)).trans hS.2.2.2.2.2.2
  have hxone : x.nr 126 = 1 := hxc.2.2.2.2.1
  have houtrank : out.nr 210 = (settleState S i j u).nextRank := by
    simp [out, popFinish, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat,
      hxrank, hxone, settleState]
  refine ⟨out, 17 + (12 + (7 + (n + 1))), Run.seq hload htail,
    by omega, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨houtc, ?_, ?_, ?_, ?_, ?_, houtrank⟩
    · simpa only [GraphMemory, houtnm] using hxg
    · simpa only [Heap, Queue.Represents, Queue.readRecord, houtnm, houtrm] using hxheap
    · simpa only [Arrays, houtnm, houtrm] using hxa
    · simpa only [TableValues, houtrm] using hxT
    · exact (List.erase_sublist (l := S.queue) (a := u)).trans hS.2.2.2.2.2.1
  · exact (htail.nat_frame 211 (by decide)).trans hu
  · simpa only [StoredCell, houtnm, houtrm] using hxcell
  · intro a haw hab
    have hloadnm := congrFun (hload.natMemory_frame (by decide)) a
    have hloadrm := congrFun (hload.realMemory_frame (by decide)) a
    have hwframe : w.nm a = p.nm a ∧ w.rm a = p.rm a := by
      rcases hab with hab | hab
      · have hlow : E.base ≤ p.nr 230 := by rw [haddr]; unfold Layout.address; omega
        apply writtenCell_frame <;> omega
      · exact writtenCell_above_table E input u i j p hun hi hj haddr a hab
    have hqueue := hxframe a (Or.inl haw)
    exact ⟨(congrFun houtnm a).trans (hqueue.1.trans
      ((congrFun hqnm a).trans (hwframe.1.trans hloadnm))),
      (congrFun houtrm a).trans (hqueue.2.trans
        ((congrFun hqrm a).trans (hwframe.2.trans hloadrm)))⟩
  · intro v a b hv ha hb hneq hprev
    have hpStored : StoredCell E S.table v a b p := by
      simpa only [StoredCell, hload.natMemory_frame (by decide),
        hload.realMemory_frame (by decide)] using hprev
    have hwStored : StoredCell E (settleState S i j u).table v a b w :=
      writtenCell_stored_other E input S.table v u i j a b c p hpStored hv hua hb hj hneq haddr
    have hqStored : StoredCell E (settleState S i j u).table v a b q := by
      simpa only [StoredCell, hqnm, hqrm] using hwStored
    have hxStored := StoredCell.transfer E _ v a b q x (activeVertices_valid A.I v hv)
      ha hb hqStored (winnerFrame_below E q x hxframe)
    simpa only [StoredCell, houtnm, houtrm] using hxStored

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem relaxOrdinal_run (input : RAMInput) (s : Store) :
    Run input (.atoms relaxOrdinalOps) s (relaxOrdinalResult input s) 6 :=
  run_atoms input relaxOrdinalOps s

private theorem relaxExpectationPrepared_run (input : RAMInput) (s : Store) :
    Run input (.atoms relaxExpectationOps) s (relaxExpectationPrepared input s) 8 :=
  run_atoms input relaxExpectationOps s

private theorem relaxOldKey_run (input : RAMInput) (s : Store) :
    Run input (.atoms relaxOldKeyOps) s (relaxOldKeyResult input s) 2 :=
  run_atoms input relaxOldKeyOps s

private theorem relaxCommitPrepared_run (input : RAMInput) (s : Store) :
    Run input (.atoms relaxCommitOps) s (relaxCommitPrepared input s) 22 :=
  run_atoms input relaxCommitOps s

private theorem relaxCommit_natural_memory (input : RAMInput) (s : Store) :
    (relaxCommitPrepared input s).nm =
      Function.update (Function.update s.nm (s.nr 335) 3)
        (s.nr 208 + s.nr 204 + s.nr 332) (s.nr 211) := by
  simp [relaxCommitPrepared,evalAtoms,relaxCommitOps,Atom.eval,ramStep,
    Store.at,Store.ofRAM,evalNat]

private theorem relaxCommit_real_memory (input : RAMInput) (s : Store) :
    (relaxCommitPrepared input s).rm =
      Function.update (Function.update (Function.update s.rm (s.nr 335) (s.rr 82))
        (s.nr 208 + s.nr 204 + s.nr 332) (Real.exp (s.rr 80 * (s.rr 202 - 1))))
        (s.nr 208 + s.nr 204 + s.nr 332 + s.nr 204)
          (Real.exp (s.rr 81 * (s.rr 202 - 1))) := by
  simp [relaxCommitPrepared,evalAtoms,relaxCommitOps,Atom.eval,ramStep,
    Store.at,Store.ofRAM,evalNat,evalReal]

private theorem relaxCommit_header (input : RAMInput) (s : Store) :
    (relaxCommitPrepared input s).nr 0 = s.nr 333 ∧
    (relaxCommitPrepared input s).nr 1 = s.nr 205 ∧
    (relaxCommitPrepared input s).nr 2 = s.nr 206 ∧
    (relaxCommitPrepared input s).nr 3 = s.nr 125 ∧
    (relaxCommitPrepared input s).nr 4 = s.nr 126 ∧
    (relaxCommitPrepared input s).nr 10 = s.nr 331 ∧
    (relaxCommitPrepared input s).rr 2 = s.rr 82 := by
  simp [relaxCommitPrepared,evalAtoms,relaxCommitOps,Atom.eval,ramStep,Store.at,Store.ofRAM]

private theorem relaxCommit_below_temp {A : InnerInput} (E : Layout A)
    (input : RAMInput) (s : Store) (k : ℕ)
    (htemp : s.nr 208 = E.temp) (hkey : s.nr 335 = E.temp + k) :
    BelowFrame E.temp s (relaxCommitPrepared input s) := by
  intro a ha
  have h0 : a ≠ s.nr 335 := by omega
  have h1 : a ≠ s.nr 208 + s.nr 204 + s.nr 332 := by omega
  have h2 : a ≠ s.nr 208 + s.nr 204 + s.nr 332 + s.nr 204 := by omega
  simp [relaxCommit_natural_memory,relaxCommit_real_memory,h0,h1,h2]

private theorem layerLeaf_updated {A : InnerInput} (E : Layout A) (S : LayerState)
    (k u v : ℕ) (value : ℝ) (hk : (activeVertices A.I)[k]? = some v)
    (hvq : v ∈ S.queue) :
    layerLeaf E (updatedLayer S u v value) =
      Function.update (layerLeaf E S) (E.capacity + k) ⟨k+1,value⟩ := by
  have hkn := (List.getElem?_eq_some_iff.mp hk).choose
  have hv : Queue.slotVertex (activeVertices A.I) k = v := by simp [Queue.slotVertex,hk]
  have h := Queue.activeLeaf_single_change (activeVertices A.I) S.queue S.queue
    S.keys (Function.update S.keys v value) E.capacity k (activeVertices_nodup A.I) hkn
    (by intro w hw; exact Function.update_of_ne (by simpa [hv] using hw) _ _)
    (by intro w hw; rfl)
  change Queue.activeLeaf (activeVertices A.I) S.queue (Function.update S.keys v value) E.capacity =
    Function.update (Queue.activeLeaf (activeVertices A.I) S.queue S.keys E.capacity)
      (E.capacity+k) ⟨k+1,value⟩
  simpa only [hv,if_pos hvq,Function.update_self] using h

private theorem arrays_after_edge_write {A : InnerInput} (E : Layout A) (S : LayerState)
    (k u v : ℕ) (value : ℝ) (s t : Store)
    (hk : (activeVertices A.I)[k]? = some v) (h : Arrays E S s)
    (hn : t.nm = Function.update (Function.update s.nm (E.temp + k) 3)
      (E.temp + (activeVertices A.I).length + k) u)
    (hr : t.rm = Function.update (Function.update (Function.update s.rm
      (E.temp + k) value) (E.temp + (activeVertices A.I).length + k) (lengthPGF A u v))
      (E.temp + 2 * (activeVertices A.I).length + k) (costPGF A u v)) :
    Arrays E (updatedLayer S u v value) t := by
  have hkn := (List.getElem?_eq_some_iff.mp hk).choose
  intro l w hl
  have hln := (List.getElem?_eq_some_iff.mp hl).choose
  by_cases hw : w = v
  · subst w
    have hlk : l = k := by
      apply (Queue.slotVertex_injective (activeVertices A.I) (activeVertices_nodup A.I)
        l k hln hkn).mp
      simp [Queue.slotVertex,hl,hk]
    subst l
    have h01 : E.temp + k ≠ E.temp + (activeVertices A.I).length + k := by omega
    have h02 : E.temp + k ≠ E.temp + 2 * (activeVertices A.I).length + k := by omega
    have h12 : E.temp + (activeVertices A.I).length + k ≠
        E.temp + 2 * (activeVertices A.I).length + k := by omega
    simp only [updatedLayer,hn,hr,Function.update_of_ne h01,Function.update_of_ne h02,
      Function.update_of_ne h12,Function.update_self]
    simp [parentTag,parentVertex]
  · have hlk : l ≠ k := by
      intro heq
      subst l
      have heq' : v = w := Option.some.inj (hk.symm.trans hl)
      exact hw heq'.symm
    have h00 : E.temp + l ≠ E.temp + k := by omega
    have h01 : E.temp + l ≠ E.temp + (activeVertices A.I).length + k := by omega
    have h02 : E.temp + l ≠ E.temp + 2 * (activeVertices A.I).length + k := by omega
    have h10 : E.temp + (activeVertices A.I).length + l ≠ E.temp + k := by omega
    have h11 : E.temp + (activeVertices A.I).length + l ≠
        E.temp + (activeVertices A.I).length + k := by omega
    have h12 : E.temp + (activeVertices A.I).length + l ≠
        E.temp + 2 * (activeVertices A.I).length + k := by omega
    have h20 : E.temp + 2 * (activeVertices A.I).length + l ≠ E.temp + k := by omega
    have h21 : E.temp + 2 * (activeVertices A.I).length + l ≠
        E.temp + (activeVertices A.I).length + k := by omega
    have h22 : E.temp + 2 * (activeVertices A.I).length + l ≠
        E.temp + 2 * (activeVertices A.I).length + k := by omega
    simpa only [updatedLayer,hn,hr,Function.update_of_ne hw,
      Function.update_of_ne h00,Function.update_of_ne h01,Function.update_of_ne h02,
      Function.update_of_ne h10,Function.update_of_ne h11,Function.update_of_ne h12,
      Function.update_of_ne h20,Function.update_of_ne h21,Function.update_of_ne h22] using h l w hl

private theorem relaxCommit_arrays {A : InnerInput} (E : Layout A) (S : LayerState)
    (k u v : ℕ) (value : ℝ) (input : RAMInput) (s : Store)
    (hk : (activeVertices A.I)[k]? = some v) (ha : Arrays E S s)
    (htemp : s.nr 208 = E.temp) (hN : s.nr 204 = (activeVertices A.I).length)
    (hkreg : s.nr 332 = k) (hkey : s.nr 335 = E.temp + k) (hu : s.nr 211 = u)
    (hvalue : s.rr 82 = value) (hz : s.rr 202 = zValue A)
    (hL : s.rr 80 = lengthRate A * A.I.length u v)
    (hC : s.rr 81 = costRate A * A.I.cost u v) :
    Arrays E (updatedLayer S u v value) (relaxCommitPrepared input s) := by
  apply arrays_after_edge_write E S k u v value s _ hk ha
  · simp only [relaxCommit_natural_memory,htemp,hN,hkreg,hkey,hu]
  · rw [relaxCommit_real_memory,htemp,hN,hkreg,hkey,hvalue,hz,hL,hC]
    have haddr : E.temp + (activeVertices A.I).length + k + (activeVertices A.I).length =
        E.temp + 2 * (activeVertices A.I).length + k := by omega
    rw [haddr]
    rfl

private theorem relaxCommit_correct {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (input : RAMInput) (s : Store) (k u v : ℕ) (value : ℝ)
    (hrep : LayerRep E i j S s) (hk : (activeVertices A.I)[k]? = some v)
    (hvq : v ∈ S.queue) (hu : s.nr 211 = u)
    (htoken : s.nr 331 = k + 1) (hkreg : s.nr 332 = k)
    (hleaf : s.nr 333 = E.capacity + k) (hkey : s.nr 335 = E.temp + k)
    (hvalue : s.rr 82 = value)
    (hL : s.rr 80 = lengthRate A * A.I.length u v)
    (hC : s.rr 81 = costRate A * A.I.cost u v) :
    ∃ t steps, Run input relaxCommitCmd s t steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * E.capacity) + 28 ∧
      LayerRep E i j (updatedLayer S u v value) t ∧ BelowFrame E.winner s t := by
  have hc0 := hrep.1
  obtain ⟨hc,hgraph,hheap,harrays,hvalues,hsub,hrank⟩ := hrep
  obtain ⟨hn,hsource,hq,hzero,hone,hstride,hheads,hlinks,hmap,hactive,
    hbase,hi,hj,hlayer,hN,hW,hP,hB,hR,hrow,hLengthRate,hμ,hz⟩ := hc
  have hc : Constants E i j s := hc0
  obtain ⟨hkn,_⟩ := List.getElem?_eq_some_iff.mp hk
  have hfit := E.active_fit
  have hBpos := E.capacity_pos
  let prepared := relaxCommitPrepared input s
  have hp := relaxCommitPrepared_run input s
  have hpframe : BelowFrame E.temp s prepared := relaxCommit_below_temp E input s k hR hkey
  have hpreheap := Heap.transfer_below_temp E S s prepared hheap hpframe
  have hprearrays := relaxCommit_arrays E S k u v value input s hk harrays
    hR hN hkreg hkey hu hvalue hz hL hC
  obtain ⟨hp0,hp1,hp2,hp3,hp4,hp10,hpr2⟩ := relaxCommit_header input s
  have hparent : Queue.ParentLayout (2 * E.capacity) prepared := by
    refine ⟨?_,?_,?_,?_⟩
    · dsimp [prepared]; rw [hp0,hleaf]; omega
    · dsimp [prepared]; rw [hp1,hp2,hW,hP]; exact E.winner_before_parent
    · dsimp [prepared]; rw [hp3,hzero]
    · intro node hn
      dsimp [prepared]; rw [hp2,hP]
      exact hpreheap.2 node hn
  obtain ⟨t,n,hrun,hcost,hend,hheader,hparents,hh,hframe⟩ :=
    Queue.updateLeaf_refines input E.capacity (layerLeaf E S) prepared hparent
      (by dsimp [prepared]; rw [hp4,hone])
      (by dsimp [prepared]; rw [hp0,hleaf]; omega)
      (by dsimp [prepared]; rw [hp0,hleaf]; omega)
      (by dsimp [prepared]; rw [hp1,hW]; exact hpreheap.1)
  have hframe' : Queue.WinnerFrame E.winner (2 * E.capacity) prepared t := by
    simpa only [prepared,hp1,hW] using hframe
  have hwhole : Run input relaxCommitCmd s t (22+n) := Run.seq hp hrun
  have hlow : BelowFrame E.winner s prepared :=
    fun a ha => hpframe a (ha.trans_le E.winner_le_temp)
  have hbelow : BelowFrame E.winner s t :=
    hlow.trans (winnerFrame_below E prepared t hframe')
  refine ⟨t,22+n,hwhole,by omega,?_,hbelow⟩
  refine ⟨Constants.after_run E i j input relaxCommitCmd s t (22+n) hc hwhole
      (by decide) (by decide),GraphMemory.transfer E s t hgraph hbelow,?_,?_,
    TableValues.transfer E S.table s t hvalues hbelow,hsub,?_⟩
  · constructor
    · have he := layerLeaf_updated E S k u v value hk hvq
      rw [he]
      simpa only [prepared,hp0,hleaf,hp1,hW,hp10,htoken,hpr2,hvalue] using hh
    · intro node hn
      have hn2 : t.nr 2 = E.parent := (hheader 2 (by omega) (by omega)).trans (hp2.trans hP)
      simpa only [hn2] using hparents.2.2.2 node hn
  · exact Arrays.transfer_winner_frame E (updatedLayer S u v value) prepared t hprearrays hframe'
  · exact (hwhole.nat_frame 210 (by decide)).trans hrank

private theorem relaxExpectationPrepared_values (input : RAMInput) (s : Store) :
    let p := relaxExpectationPrepared input s
    p.nr 80 = s.nr 124 ∧ p.nr 81 = s.nr 201 ∧ p.nr 82 = s.nr 202 ∧
    p.nr 83 = s.nr 211 ∧ p.nr 84 = s.nr 200 ∧ p.nr 85 = s.nr 129 ∧
    p.rr 80 = s.rr 200 * s.rr 330 ∧ p.rr 81 = s.rr 201 * s.rr 331 := by
  simp [relaxExpectationPrepared,evalAtoms,relaxExpectationOps,Atom.eval,ramStep,
    Store.at,Store.ofRAM,evalReal]

private theorem relaxOldKey_values (input : RAMInput) (s : Store) :
    (relaxOldKeyResult input s).nr 335 = s.nr 208 + s.nr 332 ∧
    (relaxOldKeyResult input s).rr 332 = s.rm (s.nr 208 + s.nr 332) := by
  simp [relaxOldKeyResult,evalAtoms,relaxOldKeyOps,Atom.eval,ramStep,
    Store.at,Store.ofRAM,evalNat]

private theorem relaxCompute_correct {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (input : RAMInput) (s : Store) (k u v : ℕ)
    (hrep : LayerRep E i j S s) (hk : (activeVertices A.I)[k]? = some v)
    (hua : u ∈ activeVertices A.I) (hu : s.nr 211 = u) (hkreg : s.nr 332 = k)
    (hL : s.rr 330 = A.I.length u v) (hC : s.rr 331 = A.I.cost u v) :
    ∃ t steps, Run input relaxComputeCmd s t steps ∧
      steps ≤ 100 * (tickLimit A + 1) ^ 2 + 10 ∧ LayerRep E i j S t ∧
      t.rr 82 = edgeExpectation A S.table u v i j ∧ t.rr 332 = S.keys v ∧
      t.nr 335 = E.temp + k ∧
      t.rr 80 = lengthRate A * A.I.length u v ∧
      t.rr 81 = costRate A * A.I.cost u v := by
  obtain ⟨hn,hsource,hq,hzero,hone,hstride,hheads,hlinks,hmap,hactive,
    hbase,hi,hj,hlayer,hN,hW,hP,hB,hR,hrow,hLengthRate,hμ,hz⟩ := hrep.1
  let prepared := relaxExpectationPrepared input s
  have hp := relaxExpectationPrepared_run input s
  obtain ⟨hpq,hpi,hpj,hpu,hpb,hps,hpl,hpc⟩ := relaxExpectationPrepared_values input s
  have hmem : ∀ a < tickLimit A - i, ∀ b < tickLimit A - j,
      prepared.rm (prepared.nr 84 + prepared.nr 85 *
          ((i+a)*tickLimit A+(j+b)) + 4*prepared.nr 83) =
        1 - (S.table u (i+a) (j+b)).value := by
    intro a ha b hb
    have he : prepared.nr 84 + prepared.nr 85 *
        ((i+a)*tickLimit A+(j+b)) + 4*prepared.nr 83 = E.address u (i+a) (j+b) := by
      dsimp [prepared]; rw [hpb,hps,hpu,hbase,hstride,hu]; unfold Layout.address; ring
    rw [he,hp.realMemory_frame (by decide)]
    exact hrep.2.2.2.2.1 u hua (i+a) (by omega) (j+b) (by omega)
  obtain ⟨middle,n,hrun,hncost,hvalue,hframe⟩ :=
    Expectation.edgeExpectation_run input A S.table u v i j prepared
      (hpq.trans hq) (hpi.trans hi) (hpj.trans hj)
      (by rw [hpl,hLengthRate,hL]) (by rw [hpc,hμ,hC]) hmem
  let out := relaxOldKeyResult input middle
  have ho := relaxOldKey_run input middle
  have hall : Run input relaxComputeCmd s out (8+(n+2)) := Run.seq hp (Run.seq hrun ho)
  have hRmid : middle.nr 208 = E.temp :=
    (hframe.natural 208 (by omega) (by omega)).trans ((hp.nat_frame 208 (by decide)).trans hR)
  have hkmid : middle.nr 332 = k :=
    (hframe.natural 332 (by omega) (by omega)).trans ((hp.nat_frame 332 (by decide)).trans hkreg)
  have hm : middle.rm = s.rm := hframe.realMemory.trans (hp.realMemory_frame (by decide))
  obtain ⟨hoaddr,hokey⟩ := relaxOldKey_values input middle
  refine ⟨out,8+(n+2),hall,by omega,?_,?_,?_,?_,?_,?_⟩
  · exact LayerRep.after_readonly E i j S input relaxComputeCmd s out _ hrep hall
      (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact (ho.real_frame 82 (by decide)).trans hvalue
  · rw [hokey,hRmid,hkmid,hm]
    exact (hrep.2.2.2.1 k v hk).1
  · rw [hoaddr,hRmid,hkmid]
  · rw [ho.real_frame 80 (by decide),hframe.real 80 (by omega),hpl,hLengthRate,hL]
  · rw [ho.real_frame 81 (by decide),hframe.real 81 (by omega),hpc,hμ,hC]

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem relaxOrdinal_values {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (input : RAMInput) (s : Store) (k v : ℕ)
    (hrep : LayerRep E i j S s) (hk : (activeVertices A.I)[k]? = some v)
    (hv : s.nr 330 = v) :
    let t := relaxOrdinalResult input s
    t.nr 331 = k+1 ∧ t.nr 332 = k ∧ t.nr 333 = E.capacity+k ∧
    t.nr 338 = if v ∈ S.queue then k+1 else 0 := by
  obtain ⟨hkn,_⟩ := List.getElem?_eq_some_iff.mp hk
  obtain ⟨hn,hsource,hq,hzero,hone,hstride,hheads,hlinks,hmap,hactive,
    hbase,hi,hj,hlayer,hN,hW,hP,hB,hR,hrow,hLengthRate,hμ,hz⟩ := hrep.1
  have hm := (hrep.2.1 k v hk).1
  have hfit := E.active_fit
  have hh := hrep.2.2.1.1 (E.capacity+k) (by omega)
  rw [Queue.heapTruth_leaf E.capacity (layerLeaf E S) (E.capacity+k) (by omega)] at hh
  have hleaf : layerLeaf E S (E.capacity+k) =
      ⟨if v ∈ S.queue then k+1 else 0,S.keys v⟩ := by
    change Queue.activeLeaf (activeVertices A.I) S.queue S.keys E.capacity (E.capacity+k) = _
    rw [Queue.activeLeaf_at _ _ _ _ _ hkn]
    simp only [Queue.slotVertex,hk,Option.getD_some]
  rw [hleaf] at hh
  have htoken := congrArg Queue.Record.token hh
  change s.nm (E.winner+(E.capacity+k)) = _ at htoken
  simp [relaxOrdinalResult,evalAtoms,relaxOrdinalOps,Atom.eval,ramStep,Store.at,
    Store.ofRAM,evalNat,hmap,hv,hm,hone,hB,hW,htoken]

private theorem relax_correct {A : InnerInput} (E : Layout A) (i j : ℕ)
    (S : LayerState) (input : RAMInput) (s : Store) (u v : ℕ)
    (hrep : LayerRep E i j S s) (he : (u,v) ∈ A.I.graph.edges)
    (hu : s.nr 211 = u) (hv : s.nr 330 = v)
    (hL : s.rr 330 = A.I.length u v) (hC : s.rr 331 = A.I.cost u v) :
    ∃ t steps, Run input relaxCmd s t steps ∧
      steps ≤ 100 * (tickLimit A + 1) ^ 2 + 19 * Nat.clog 2 (2 * E.capacity) + 60 ∧
      LayerRep E i j (relaxEdge A i j u S (u,v)) t ∧ BelowFrame E.winner s t := by
  by_cases huv : u = v
  · refine ⟨s,2,Run.branchTrue ?_ (Run.skip s),by omega,?_,BelowFrame.refl _ _⟩
    · simp [Guard.eval,natTest,hu,hv,huv]
    · simpa [relaxEdge,huv] using hrep
  · have hva := activeVertices_edge_right A.I u v he
    have hua := activeVertices_edge_left A.I u v he
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hva
    let ordinal := relaxOrdinalResult input s
    have hord := relaxOrdinal_run input s
    have hordrep : LayerRep E i j S ordinal :=
      LayerRep.after_readonly E i j S input (.atoms relaxOrdinalOps) s ordinal 6 hrep hord
        (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨htoken,hkreg,hleaf,hmembership⟩ := relaxOrdinal_values E i j S input s k v hrep hk hv
    have hzero : ordinal.nr 125 = 0 := hordrep.1.2.2.2.1
    have houter : (Guard.nat .eq 330 211).eval s = false := by
      simp [Guard.eval,natTest,hu,hv,Ne.symm huv]
    by_cases hvq : v ∈ S.queue
    · have hguard : (Guard.nat .eq 338 125).eval ordinal = false := by
        simp only [Guard.eval,natTest]
        rw [hmembership,hzero]
        simp [hvq]
      obtain ⟨computed,n,hcompute,hn,hcomputed,hvalue,hkey,haddr,hmeanL,hmeanC⟩ :=
        relaxCompute_correct E i j S input ordinal k u v hordrep hk hua
          ((hord.nat_frame 211 (by decide)).trans hu) hkreg
          ((hord.real_frame 330 (by decide)).trans hL)
          ((hord.real_frame 331 (by decide)).trans hC)
      have hprefix : Run input (.seq (.atoms relaxOrdinalOps) relaxComputeCmd) s computed (6+n) :=
        Run.seq hord hcompute
      have hpreframe : BelowFrame E.winner s computed :=
        belowFrame_of_run input _ s computed _ _ hprefix (by decide) (by decide)
      by_cases hbetter : edgeExpectation A S.table u v i j < S.keys v
      · obtain ⟨out,m,hcommit,hm,hout,hframe⟩ := relaxCommit_correct E i j S input computed k u v _
          hcomputed hk hvq ((hprefix.nat_frame 211 (by decide)).trans hu)
          ((hcompute.nat_frame 331 (by decide)).trans htoken)
          ((hcompute.nat_frame 332 (by decide)).trans hkreg)
          ((hcompute.nat_frame 333 (by decide)).trans hleaf) haddr hvalue hmeanL hmeanC
        have hpresent : Run input relaxPresentCmd ordinal out (n+(1+m+1)) :=
          Run.seq hcompute (Run.branchTrue (by simp [Guard.eval,realTest,hvalue,hkey,hbetter]) hcommit)
        have hwhole : Run input relaxCmd s out (1+(6+(1+(n+(1+m+1))))) :=
          Run.branchFalse houter (Run.seq hord (Run.branchFalse hguard hpresent))
        refine ⟨out,_,hwhole,by omega,?_,hpreframe.trans hframe⟩
        simpa [relaxEdge,huv,hvq,hbetter,updatedLayer] using hout
      · have hpresent : Run input relaxPresentCmd ordinal computed (n+1) :=
          Run.seq hcompute (Run.branchFalse (by simp [Guard.eval,realTest,hvalue,hkey,hbetter]) (Run.skip computed))
        have hwhole : Run input relaxCmd s computed (1+(6+(1+(n+1)))) :=
          Run.branchFalse houter (Run.seq hord (Run.branchFalse hguard hpresent))
        refine ⟨computed,_,hwhole,by omega,?_,hpreframe⟩
        simpa [relaxEdge,huv,hvq,hbetter] using hcomputed
    · have hguard : (Guard.nat .eq 338 125).eval ordinal = true := by
        simp only [Guard.eval,natTest]
        rw [hmembership,hzero]
        simp [hvq]
      have hwhole : Run input relaxCmd s ordinal (1+(6+2)) :=
        Run.branchFalse houter (Run.seq hord (Run.branchTrue hguard (Run.skip ordinal)))
      refine ⟨ordinal,_,hwhole,by omega,?_,?_⟩
      · simpa [relaxEdge,hvq] using hordrep
      · exact belowFrame_of_run input _ s ordinal _ _ hord (by decide) (by decide)

private theorem outgoingLoaded_values (I : Instance) (ε : ℝ) (s : Store) (index u v : ℕ)
    (hindex : s.nr 213 = index + 1) (hone : s.nr 126 = 1)
    (he : I.graph.edges[index]? = some (u, v)) :
    let t := outgoingLoaded (encodeInput I ε) s
    t.nr 224 = index ∧ t.nr 330 = v ∧
    t.rr 330 = I.length u v ∧ t.rr 331 = I.cost u v := by
  have hright := encodeInput_edge_right I ε index (u, v) he
  have hlength := encodeInput_length I ε index (u, v) he
  have hcost := encodeInput_cost I ε index (u, v) he
  have ha : index + index + 4 = 3 + 2 * index + 1 := by omega
  have hb : index + index + 4 - 2 = 2 + 2 * index := by omega
  simp [outgoingLoaded, evalAtoms, outgoingLoadAtoms, Atom.eval, Store.ofRAM,
    ramStep, Store.at, evalNat, hindex, hone, ha, hb, hright, hlength, hcost]

private theorem outgoingLoop_correct {A : InnerInput} (E : Layout A) (i j u : ℕ)
    (ε : ℝ) (mem : ℕ → ℕ) (token : ℕ) (es : List ℕ)
    (hchain : Preprocess.AdjacencyChain mem E.links token es)
    (S : LayerState) (s : Store) (hrep : LayerRep E i j S s)
    (hu : s.nr 211 = u) (htoken : s.nr 213 = token)
    (hedges : ∀ e ∈ es, ∃ v, A.I.graph.edges[e]? = some (u,v))
    (hlinks : ∀ e ∈ es, s.nm (E.links+e) = mem (E.links+e)) :
    ∃ t steps, Run (encodeInput A.I ε) outgoingLoop s t steps ∧
      steps ≤ outgoingCost A E * es.length + 1 ∧
      LayerRep E i j ((es.map (Preprocess.edgeAt A.I)).foldl (relaxEdge A i j u) S) t ∧
      BelowFrame E.winner s t := by
  induction hchain generalizing S s with
  | nil =>
      refine ⟨s,1,Run.loopFalse ?_,by simp,?_,BelowFrame.refl _ _⟩
      · simp [Guard.eval,natTest,htoken,hrep.1.2.2.2.1]
      · simpa using hrep
  | @cons e next es hnext htail ih =>
      obtain ⟨v,he⟩ := hedges e (by simp)
      obtain ⟨helt,_⟩ := List.getElem?_eq_some_iff.mp he
      have haem : (u,v) ∈ A.I.graph.edges := List.mem_of_getElem? he
      let loaded := outgoingLoaded (encodeInput A.I ε) s
      have hload : Run (encodeInput A.I ε) (.atoms outgoingLoadAtoms) s loaded 10 :=
        run_atoms _ _ _
      have hloaded : LayerRep E i j S loaded := LayerRep.after_readonly E i j S _ _ _ _ _
        hrep hload (by decide) (by decide) (by decide) (by decide) (by decide)
      obtain ⟨hindex,hv,hL,hC⟩ := outgoingLoaded_values A.I ε s e u v htoken
        hrep.1.2.2.2.2.1 he
      obtain ⟨relaxed,n,hrelax,hn,hrelaxed,hframe⟩ := relax_correct E i j S _ loaded u v
        hloaded haem ((hload.nat_frame 211 (by decide)).trans hu) hv hL hC
      let advanced := evalAtoms (encodeInput A.I ε) outgoingNextAtoms relaxed
      have hadvance : Run (encodeInput A.I ε) (.atoms outgoingNextAtoms) relaxed advanced 2 :=
        run_atoms _ _ _
      have hadvanced : LayerRep E i j (relaxEdge A i j u S (u,v)) advanced :=
        LayerRep.after_readonly E i j _ _ _ _ _ _ hrelaxed hadvance
          (by decide) (by decide) (by decide) (by decide) (by decide)
      have hprefix : Run (encodeInput A.I ε) outgoingBody s advanced (10+(n+2)) :=
        Run.seq hload (Run.seq hrelax hadvance)
      have hprefixFrame : BelowFrame E.winner s advanced :=
        (belowFrame_of_run _ _ _ _ _ _ hload (by decide) (by decide)).trans
          (hframe.trans (belowFrame_of_run _ _ _ _ _ _ hadvance (by decide) (by decide)))
      have hri : relaxed.nr 224 = e := (hrelax.nat_frame 224 (by decide)).trans hindex
      have hrl : relaxed.nr 139 = E.links := hrelaxed.1.2.2.2.2.2.2.2.1
      have hlinklt : E.links+e<E.winner := by have := E.links_before_winner; omega
      have hrlink : relaxed.nm (E.links+e) = next := by
        rw [(hframe _ hlinklt).1,congrFun (hload.natMemory_frame (by decide)) _]
        exact (hlinks e (by simp)).trans hnext
      have hatoken : advanced.nr 213 = next := by
        simp [advanced,evalAtoms,outgoingNextAtoms,Atom.eval,Store.ofRAM,Store.at,
          ramStep,evalNat,hri,hrl,hrlink]
      have hau : advanced.nr 211 = u := (hprefix.nat_frame 211 (by decide)).trans hu
      have heAt : Preprocess.edgeAt A.I e = (u,v) := by simp [Preprocess.edgeAt,he]
      obtain ⟨out,m,hrun,hm,hout,houtFrame⟩ := ih _ advanced hadvanced hau hatoken
        (fun k hk => hedges k (by simp [hk])) (by
          intro k hk
          obtain ⟨w,hw⟩ := hedges k (by simp [hk])
          obtain ⟨hkm,_⟩ := List.getElem?_eq_some_iff.mp hw
          have hkw : E.links+k<E.winner := by have := E.links_before_winner; omega
          exact (hprefixFrame _ hkw).1.trans (hlinks k (by simp [hk])))
      have hguard : (Guard.nat .lt 125 213).eval s = true := by
        simp [Guard.eval,natTest,htoken,hrep.1.2.2.2.1]
      refine ⟨out,_,Run.loopTrue hguard hprefix hrun,?_,?_,hprefixFrame.trans houtFrame⟩
      · simp only [List.length_cons,outgoingCost] at *
        nlinarith
      · simpa only [List.map_cons,List.foldl_cons,heAt] using hout

private theorem outgoingIndices_edge (I : Instance) (u e : ℕ)
    (he : e ∈ Preprocess.outgoingIndices I I.graph.edges.length u) :
    ∃ v, I.graph.edges[e]? = some (u,v) := by
  have hlt := Preprocess.outgoingIndices_lt I I.graph.edges.length u e he
  have hget := List.getElem?_eq_getElem hlt
  have ht : (Preprocess.edgeAt I e).1 = u := by
    have h := he
    simp only [Preprocess.outgoingIndices,List.mem_reverse,List.mem_filter,
      List.mem_range,beq_iff_eq] at h
    exact h.2
  refine ⟨(Preprocess.edgeAt I e).2,?_⟩
  have hpair : Preprocess.edgeAt I e = (u,(Preprocess.edgeAt I e).2) :=
    Prod.ext ht rfl
  simpa only [Preprocess.edgeAt,hget,Option.getD_some] using congrArg some hpair

private theorem outgoing_correct {A : InnerInput} (E : Layout A) (i j u : ℕ) (ε : ℝ)
    (S : LayerState) (s : Store) (hrep : LayerRep E i j S s)
    (hu : s.nr 211 = u) (hun : u < A.I.graph.n)
    (hadj : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm) :
    ∃ t steps, Run (encodeInput A.I ε) outgoingCmd s t steps ∧
      steps ≤ outgoingCost A E * (outgoingEdges A.I u).length + 3 ∧
      LayerRep E i j (relaxAll A i j u S) t ∧ BelowFrame E.winner s t := by
  let prepared := evalAtoms (encodeInput A.I ε) outgoingStartAtoms s
  have hp : Run (encodeInput A.I ε) (.atoms outgoingStartAtoms) s prepared 2 := run_atoms _ _ _
  have hprep : LayerRep E i j S prepared := LayerRep.after_readonly E i j S _ _ _ _ _
    hrep hp (by decide) (by decide) (by decide) (by decide) (by decide)
  have hh : s.nr 137 = E.heads := hrep.1.2.2.2.2.2.2.1
  have htoken : prepared.nr 213 = s.nm (E.heads+u) := by
    simp [prepared,evalAtoms,outgoingStartAtoms,Atom.eval,Store.ofRAM,Store.at,
      ramStep,evalNat,hh,hu]
  obtain ⟨out,n,hrun,hn,hout,hframe⟩ := outgoingLoop_correct E i j u ε s.nm _ _ (hadj u hun)
    S prepared hprep ((hp.nat_frame 211 (by decide)).trans hu) htoken
    (fun e he => outgoingIndices_edge A.I u e he)
    (fun e _ => congrFun (hp.natMemory_frame (by decide)) _)
  have heq := Preprocess.outgoingIndices_edges A.I u
  have hlen : (Preprocess.outgoingIndices A.I A.I.graph.edges.length u).length =
      (outgoingEdges A.I u).length := by
    have := congrArg List.length heq
    simpa using this
  rw [hlen] at hn
  refine ⟨out,2+n,Run.seq hp hrun,by omega,?_,?_⟩
  · rw [heq,←relaxAll_eq_reversedOutgoingFold] at hout
    exact hout
  · exact (belowFrame_of_run _ _ _ _ _ _ hp (by decide) (by decide)).trans hframe

private theorem layerStep_correct {A : InnerInput} (E : Layout A) (i j : ℕ) (ε : ℝ)
    (S : LayerState) (s : Store) (hrep : LayerRep E i j S s)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ [])
    (hpop : poppedCells E i j S s)
    (hadj : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm) :
    ∃ t steps, Run (encodeInput A.I ε) layerStep s t steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * E.capacity) + 46 +
        outgoingCost A E * (outgoingEdges A.I (pickedVertex S)).length ∧
      LayerRep E i j (popLayer A i j S) t ∧
      poppedCells E i j (popLayer A i j S) t ∧
      OutsideTableFrame E s t ∧
      (∀ v a b, v ∈ activeVertices A.I → a < tickLimit A → b < tickLimit A →
        (a ≠ i ∨ b ≠ j) → StoredCell E S.table v a b s →
        StoredCell E (popLayer A i j S).table v a b t) := by
  let u := pickedVertex S
  have huq : u ∈ S.queue := pickedVertex_mem S hne
  have hua : u ∈ activeVertices A.I := hrep.2.2.2.2.2.1.subset huq
  have hun := activeVertices_valid A.I u hua
  obtain ⟨p,np,hp,hnp,hpr,hpu,hpc,hpf,hpp⟩ :=
    pop_correct E i j S (encodeInput A.I ε) s hrep hi hj hne
  have hpadj : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links p.nm := by
    intro v hv
    have hhead : p.nm (E.heads+v) = s.nm (E.heads+v) :=
      (hpf _ (by have := E.heads_before_winner; omega)
        (Or.inr (by have := E.table_before_heads; omega))).1
    rw [hhead]
    apply (hadj v hv).frame
    intro e he
    have hem := Preprocess.outgoingIndices_lt A.I A.I.graph.edges.length v e he
    exact (hpf _ (by have := E.links_before_winner; omega)
      (Or.inr (by have := E.table_before_links; omega))).1
  obtain ⟨out,no,ho,hno,hor,hof⟩ := outgoing_correct E i j u ε
    (settleState S i j u) p hpr hpu hun hpadj
  change no ≤ outgoingCost A E * (outgoingEdges A.I (pickedVertex S)).length + 3 at hno
  have hsame : relaxAll A i j u (settleState S i j u) = popLayer A i j S :=
    (popLayer_eq_relaxAll A i j S hne).symm
  rw [hsame] at hor
  have ht : (popLayer A i j S).table = (settleState S i j u).table := by
    rw [←hsame,relaxAll_table]
  have hq : (popLayer A i j S).queue = S.queue.erase u := by
    rw [←hsame,relaxAll_queue]; rfl
  refine ⟨out,np+no,Run.seq hp ho,by omega,hor,?_,?_,?_⟩
  · intro v hva hvq
    rw [ht]
    apply StoredCell.transfer E _ v i j p out (activeVertices_valid A.I v hva) hi hj _ hof
    by_cases hvu : v = u
    · subst v; exact hpc
    · have hvnot : v ∉ S.queue := by
        intro hvs
        apply hvq
        rw [hq]
        exact (List.mem_erase_of_ne hvu).mpr hvs
      exact hpp v i j hva hi hj (by intro h; exact hvu h.1) (hpop v hva hvnot)
  · intro a ha hb
    exact ⟨(hof a ha).1.trans (hpf a ha hb).1,(hof a ha).2.trans (hpf a ha hb).2⟩
  · intro v a b hva ha hb hab hold
    rw [ht]
    apply StoredCell.transfer E _ v a b p out (activeVertices_valid A.I v hva) ha hb _ hof
    exact hpp v a b hva ha hb (by aesop) hold

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem dpLength_run (input : RAMInput) (s : Store) :
    ∃ n ≤ 6, Run input dpLengthCmd s (dpLengthResult input s) n := by
  let t := evalAtoms input dpLengthPrepare s
  have hp := run_atoms input dpLengthPrepare s
  by_cases h : s.nr 181+s.nr 126 < s.nr 124
  · have hg : (Guard.nat .lt 185 124).eval t = true := by
      simp [t,evalAtoms,dpLengthPrepare,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,Guard.eval,natTest,h]
    refine ⟨6,le_rfl,?_⟩
    simpa only [dpLengthCmd,dpLengthResult,if_pos h,t,dpLengthPrepare,dpLengthLoad,
      List.length_cons,List.length_nil] using
      Run.seq hp (Run.branchTrue hg (run_atoms input dpLengthLoad t))
  · have hg : (Guard.nat .lt 185 124).eval t = false := by
      simp [t,evalAtoms,dpLengthPrepare,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,Guard.eval,natTest,h]
    refine ⟨3,by omega,?_⟩
    simpa only [dpLengthCmd,dpLengthResult,if_neg h,t,dpLengthPrepare,
      List.length_cons,List.length_nil] using
      Run.seq hp (Run.branchFalse hg (Run.skip (input := input) t))

private theorem dpCost_run (input : RAMInput) (s : Store) :
    ∃ n ≤ 6, Run input dpCostCmd s (dpCostResult input s) n := by
  let t := evalAtoms input dpCostPrepare s
  have hp := run_atoms input dpCostPrepare s
  by_cases h : s.nr 182+s.nr 126 < s.nr 124
  · have hg : (Guard.nat .lt 185 124).eval t = true := by
      simp [t,evalAtoms,dpCostPrepare,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,Guard.eval,natTest,h]
    refine ⟨6,le_rfl,?_⟩
    simpa only [dpCostCmd,dpCostResult,if_pos h,t,dpCostPrepare,dpCostLoad,
      List.length_cons,List.length_nil] using
      Run.seq hp (Run.branchTrue hg (run_atoms input dpCostLoad t))
  · have hg : (Guard.nat .lt 185 124).eval t = false := by
      simp [t,evalAtoms,dpCostPrepare,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,Guard.eval,natTest,h]
    refine ⟨3,by omega,?_⟩
    simpa only [dpCostCmd,dpCostResult,if_neg h,t,dpCostPrepare,
      List.length_cons,List.length_nil] using
      Run.seq hp (Run.branchFalse hg (Run.skip (input := input) t))

private theorem dpChoose_run (input : RAMInput) (s : Store) :
    ∃ n ≤ 5, Run input dpChooseCmd s (dpChooseResult input s) n := by
  by_cases h : s.rr 190 < s.rr 191
  · refine ⟨5,le_rfl,?_⟩
    simpa only [dpChooseCmd,dpChooseResult,if_pos h,dpChooseCostOps,
      List.length_cons,List.length_nil] using
      Run.branchTrue (by simp [Guard.eval,realTest,h] : (Guard.real .lt 190 191).eval s = true)
        (run_atoms input dpChooseCostOps s)
  · refine ⟨4,by omega,?_⟩
    simpa only [dpChooseCmd,dpChooseResult,if_neg h,dpChooseLengthOps,
      List.length_cons,List.length_nil] using
      Run.branchFalse (by simp [Guard.eval,realTest,h] : (Guard.real .lt 190 191).eval s = false)
        (run_atoms input dpChooseLengthOps s)

private theorem dpLeaf_run (input : RAMInput) (s : Store) :
    ∃ n ≤ 18, Run input dpLeafCmd s (dpLeafResult input s) n := by
  by_cases h : s.nr 175 = s.nr 123
  · refine ⟨4,by omega,?_⟩
    simpa only [dpLeafCmd,dpLeafResult,if_pos h,dpSourceOps,
      List.length_cons,List.length_nil] using
      Run.branchTrue (by simp [Guard.eval,natTest,h] : (Guard.nat .eq 175 123).eval s = true)
        (run_atoms input dpSourceOps s)
  · obtain ⟨nl,hl,hrl⟩ := dpLength_run input s
    obtain ⟨nc,hc,hrc⟩ := dpCost_run input (dpLengthResult input s)
    obtain ⟨np,hp,hrp⟩ := dpChoose_run input (dpCostResult input (dpLengthResult input s))
    refine ⟨1+(nl+(nc+np)),by omega,?_⟩
    simpa only [dpLeafCmd,dpLeafResult,if_neg h] using
      Run.branchFalse (by simp [Guard.eval,natTest,h] : (Guard.nat .eq 175 123).eval s = false)
        (Run.seq hrl (Run.seq hrc hrp))

private theorem dpFuture_values (input : RAMInput) (s : Store) (hone : s.nr 126 = 1) :
    let t := dpCostResult input (dpLengthResult input s)
    t.rr 190 = (if s.nr 181+1 < s.nr 124 then s.rm (s.nr 180+s.nr 183) else 0) ∧
    t.rr 191 = (if s.nr 182+1 < s.nr 124 then s.rm (s.nr 180+s.nr 129) else 0) := by
  by_cases hl : s.nr 181+1 < s.nr 124 <;> by_cases hc : s.nr 182+1 < s.nr 124 <;>
    simp [dpCostResult,dpLengthResult,evalAtoms,dpLengthPrepare,dpLengthLoad,
      dpCostPrepare,dpCostLoad,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,hone,hl,hc]

private theorem dpChoose_values (input : RAMInput) (s : Store) :
    (dpChooseResult input s).rr 2 = min (1-s.rr 190) (1-s.rr 191) ∧
    (dpChooseResult input s).nr 184 = (if 1-s.rr 190 ≤ 1-s.rr 191 then 1 else 2) := by
  by_cases h : s.rr 190 < s.rr 191
  · have hm : 1-s.rr 191 ≤ 1-s.rr 190 := by linarith
    have hn : ¬1-s.rr 190 ≤ 1-s.rr 191 := by linarith
    simp [dpChooseResult,h,evalAtoms,dpChooseCostOps,Atom.eval,Store.ofRAM,Store.at,
      ramStep,evalReal,min_eq_right hm,hn]
  · have hm : 1-s.rr 190 ≤ 1-s.rr 191 := by linarith
    simp [dpChooseResult,h,evalAtoms,dpChooseLengthOps,Atom.eval,Store.ofRAM,Store.at,
      ramStep,evalReal,min_eq_left hm,hm]

private theorem dpLeaf_correct (input : RAMInput) (A : InnerInput) (T : Table) (v i j : ℕ)
    (s : Store) (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hv : s.nr 175 = v) (hsource : s.nr 123 = A.I.source)
    (hq : s.nr 124 = tickLimit A) (hone : s.nr 126 = 1)
    (hiReg : s.nr 181 = i) (hjReg : s.nr 182 = j)
    (hL : i+1 < tickLimit A → s.rm (s.nr 180+s.nr 183) = 1-dpValue A T v (i+1) j)
    (hC : j+1 < tickLimit A → s.rm (s.nr 180+s.nr 129) = 1-dpValue A T v i (j+1)) :
    ∃ out steps, Run input dpLeafCmd s out steps ∧ steps ≤ 18 ∧
      out.rr 2 = (initLayer A T i j).keys v ∧
      out.nr 184 = parentTag ((initLayer A T i j).parents v) ∧
      out.nm = s.nm ∧ out.rm = s.rm := by
  obtain ⟨n,hn,hrun⟩ := dpLeaf_run input s
  have hvalues : (dpLeafResult input s).rr 2 = (initLayer A T i j).keys v ∧
      (dpLeafResult input s).nr 184 = parentTag ((initLayer A T i j).parents v) := by
    have hf := dpFuture_values input s hone
    rw [hiReg,hjReg,hq] at hf
    have hleft : (dpCostResult input (dpLengthResult input s)).rr 190 =
        1-dpValue A T v (i+1) j := by
      rw [hf.1]
      split
      · exact hL (by assumption)
      · rename_i h
        simp [dpValue,show tickLimit A ≤ i+1 by omega]
    have hright : (dpCostResult input (dpLengthResult input s)).rr 191 =
        1-dpValue A T v i (j+1) := by
      rw [hf.2]
      split
      · exact hC (by assumption)
      · rename_i h
        simp [dpValue,show tickLimit A ≤ j+1 by omega]
    have hc := dpChoose_values input (dpCostResult input (dpLengthResult input s))
    rw [hleft,hright] at hc
    have hsub (x : ℝ) : 1-(1-x)=x := by ring
    simp only [hsub] at hc
    constructor
    all_goals
      by_cases hs : v = A.I.source
      · simp [dpLeafResult,hv,hsource,hs,evalAtoms,dpSourceOps,Atom.eval,Store.ofRAM,
          Store.at,ramStep,initLayer,parentTag]
      · simp only [dpLeafResult,hv,hsource,if_neg hs,initLayer,if_neg hs]
        first
        | exact hc.1
        | by_cases hle : dpValue A T v (i+1) j ≤ dpValue A T v i (j+1)
          · simpa [parentTag,hle] using hc.2
          · simpa [parentTag,hle] using hc.2
  exact ⟨dpLeafResult input s,n,hrun,hn,hvalues.1,hvalues.2,
    hrun.natMemory_frame (by decide),hrun.realMemory_frame (by decide)⟩

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured Preprocess

private theorem fillPrepared_values (input : RAMInput) (s : Store) :
    let v := s.nm (s.nr 142 + s.nr 225)
    let t := fillPrepared input s
    t.nr 175 = v ∧ t.nr 180 = s.nr 203 + 4*v ∧ t.nr 181 = s.nr 201 ∧
      t.nr 182 = s.nr 202 ∧ t.nr 183 = s.nr 209 := by
  simp [fillPrepared,evalAtoms,fillPrepareAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,
    show s.nm (s.nr 142+s.nr 225)+s.nm (s.nr 142+s.nr 225)+
      (s.nm (s.nr 142+s.nr 225)+s.nm (s.nr 142+s.nr 225))=
        4*s.nm (s.nr 142+s.nr 225) by omega]

private theorem fillStored_values (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (ho : s.nr 126 = 1) :
    (fillStored input s).nr 225 = s.nr 225+1 ∧
    (fillStored input s).nm = Function.update
      (Function.update s.nm (s.nr 208+s.nr 225) (s.nr 184))
      (s.nr 208+s.nr 225+s.nr 204) 0 ∧
    (fillStored input s).rm = Function.update s.rm (s.nr 208+s.nr 225) (s.rr 2) := by
  simp [fillStored,evalAtoms,fillStoreAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,hz,ho]

private theorem fillEval_registers (A : InnerInput) (i j array base R lengthStride costStride : ℕ)
    (input : RAMInput) (s t : Store) (n : ℕ) (hrun : Run input fillEvalCmd s t n)
    (h : FillRegisters A i j array base R lengthStride costStride s) :
    FillRegisters A i j array base R lengthStride costStride t := by
  exact ⟨(hrun.nat_frame 123 (by decide)).trans h.source,
    (hrun.nat_frame 124 (by decide)).trans h.limit,
    (hrun.nat_frame 125 (by decide)).trans h.zero,
    (hrun.nat_frame 126 (by decide)).trans h.one,
    (hrun.nat_frame 129 (by decide)).trans h.costStride_eq,
    (hrun.nat_frame 142 (by decide)).trans h.array_eq,
    (hrun.nat_frame 201 (by decide)).trans h.i_eq,
    (hrun.nat_frame 202 (by decide)).trans h.j_eq,
    (hrun.nat_frame 203 (by decide)).trans h.base_eq,
    (hrun.nat_frame 204 (by decide)).trans h.count_eq,
    (hrun.nat_frame 208 (by decide)).trans h.keyBase_eq,
    (hrun.nat_frame 209 (by decide)).trans h.lengthStride_eq⟩

private theorem fillEval_invariant (A : InnerInput) (T : Table)
    (i j array base R lengthStride costStride : ℕ) (initial : Store) (k : ℕ)
    (input : RAMInput) (s t : Store) (n : ℕ) (hrun : Run input fillEvalCmd s t n)
    (h : FillInvariant A T i j array base R lengthStride costStride initial k s) :
    FillInvariant A T i j array base R lengthStride costStride initial k t := by
  have hnm := hrun.natMemory_frame (by decide)
  have hrm := hrun.realMemory_frame (by decide)
  refine ⟨fillEval_registers A i j array base R lengthStride costStride input s t n hrun h.registers,
    (hrun.nat_frame 225 (by decide)).trans h.counter,?_,?_,?_,?_,?_⟩
  · simpa only [hrm] using h.key
  · simpa only [hnm] using h.tag
  · simpa only [hnm] using h.parent
  · simpa only [hnm] using h.naturalFrame
  · simpa only [hrm] using h.realFrame

private theorem fillStore_registers (A : InnerInput) (i j array base R lengthStride costStride : ℕ)
    (input : RAMInput) (s : Store)
    (h : FillRegisters A i j array base R lengthStride costStride s) :
    FillRegisters A i j array base R lengthStride costStride (fillStored input s) := by
  have hrun := run_atoms input fillStoreAtoms s
  exact ⟨(hrun.nat_frame 123 (by decide)).trans h.source,
    (hrun.nat_frame 124 (by decide)).trans h.limit,
    (hrun.nat_frame 125 (by decide)).trans h.zero,
    (hrun.nat_frame 126 (by decide)).trans h.one,
    (hrun.nat_frame 129 (by decide)).trans h.costStride_eq,
    (hrun.nat_frame 142 (by decide)).trans h.array_eq,
    (hrun.nat_frame 201 (by decide)).trans h.i_eq,
    (hrun.nat_frame 202 (by decide)).trans h.j_eq,
    (hrun.nat_frame 203 (by decide)).trans h.base_eq,
    (hrun.nat_frame 204 (by decide)).trans h.count_eq,
    (hrun.nat_frame 208 (by decide)).trans h.keyBase_eq,
    (hrun.nat_frame 209 (by decide)).trans h.lengthStride_eq⟩

private theorem fillStore_invariant (A : InnerInput) (T : Table)
    (i j array base R lengthStride costStride : ℕ) (initial : Store) (k v : ℕ)
    (input : RAMInput) (s : Store)
    (hk : k < (activeVertices A.I).length) (hv : (activeVertices A.I)[k]? = some v)
    (h : FillInvariant A T i j array base R lengthStride costStride initial k s)
    (hkey : s.rr 2 = (initLayer A T i j).keys v)
    (htag : s.nr 184 = parentTag ((initLayer A T i j).parents v)) :
    FillInvariant A T i j array base R lengthStride costStride initial (k+1) (fillStored input s) := by
  obtain ⟨hcounter,hnm,hrm⟩ := fillStored_values input s h.registers.zero h.registers.one
  rw [h.counter] at hcounter
  rw [h.registers.keyBase_eq,h.counter,h.registers.count_eq,htag] at hnm
  rw [h.registers.keyBase_eq,h.counter,hkey] at hrm
  refine ⟨fillStore_registers A i j array base R lengthStride costStride input s h.registers,
    hcounter,?_,?_,?_,?_,?_⟩
  · intro a w ha hw
    rw [hrm]
    by_cases hak : a = k
    · subst a
      have hwv : w = v := Option.some.inj (hw.symm.trans hv)
      simp [hwv]
    · rw [Function.update_of_ne (by omega : R+a ≠ R+k)]
      exact h.key a w (by omega) hw
  · intro a w ha hw
    rw [hnm,Function.update_of_ne (by omega : R+a ≠ R+k+(activeVertices A.I).length)]
    by_cases hak : a = k
    · subst a
      have hwv : w = v := Option.some.inj (hw.symm.trans hv)
      simp [hwv]
    · rw [Function.update_of_ne (by omega : R+a ≠ R+k)]
      exact h.tag a w (by omega) hw
  · intro a ha
    rw [hnm]
    by_cases hak : a = k
    · subst a
      have he : R+(activeVertices A.I).length+k = R+k+(activeVertices A.I).length := by omega
      simp [he]
    · rw [Function.update_of_ne (by omega : R+(activeVertices A.I).length+a ≠ R+k+(activeVertices A.I).length),
        Function.update_of_ne (by omega : R+(activeVertices A.I).length+a ≠ R+k)]
      exact h.parent a (by omega)
  · intro a ha
    rw [hnm,Function.update_of_ne (by omega : a ≠ R+k+(activeVertices A.I).length),
      Function.update_of_ne (by omega : a ≠ R+k)]
    exact h.naturalFrame a ha
  · intro a ha
    rw [hrm,Function.update_of_ne (by omega : a ≠ R+k)]
    exact h.realFrame a ha

private theorem fillEval_correct (A : InnerInput) (T : Table)
    (i j array base R lengthStride costStride : ℕ) (initial : Store) (k v : ℕ)
    (input : RAMInput) (s : Store)
    (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hk : k < (activeVertices A.I).length) (hv : (activeVertices A.I)[k]? = some v)
    (hl : FillLayout A T i j array base R lengthStride costStride initial)
    (h : FillInvariant A T i j array base R lengthStride costStride initial k s) :
    ∃ t n, Run input fillEvalCmd s t n ∧ n ≤ 26 ∧
      FillInvariant A T i j array base R lengthStride costStride initial k t ∧
      t.rr 2 = (initLayer A T i j).keys v ∧
      t.nr 184 = parentTag ((initLayer A T i j).parents v) := by
  let p := fillPrepared input s
  have hp : Run input (.atoms fillPrepareAtoms) s p 8 := run_atoms input fillPrepareAtoms s
  have hpN : p.nm = s.nm := hp.natMemory_frame (by decide)
  have hpR : p.rm = s.rm := hp.realMemory_frame (by decide)
  have hload : s.nm (s.nr 142+s.nr 225) = v := by
    rw [h.registers.array_eq,h.counter,h.naturalFrame _ (Or.inl (hl.activeBelow k hk))]
    exact hl.active k v hv
  obtain ⟨hpv,hpa,hpi,hpj,hpls⟩ := fillPrepared_values input s
  rw [hload] at hpv hpa
  rw [h.registers.base_eq] at hpa
  rw [h.registers.i_eq] at hpi
  rw [h.registers.j_eq] at hpj
  rw [h.registers.lengthStride_eq] at hpls
  have hpcs : p.nr 129 = costStride :=
    (hp.nat_frame 129 (by decide)).trans h.registers.costStride_eq
  have hvm : v ∈ activeVertices A.I := List.mem_of_getElem? hv
  obtain ⟨t,n,hrun,hn,hkey,htag,_,_⟩ := dpLeaf_correct input A T v i j p hi hj hpv
    ((hp.nat_frame 123 (by decide)).trans h.registers.source)
    ((hp.nat_frame 124 (by decide)).trans h.registers.limit)
    ((hp.nat_frame 126 (by decide)).trans h.registers.one) hpi hpj
    (by
      intro hb
      rw [hpa,hpls,hpR,h.realFrame _ (Or.inl (hl.lengthBelow v hvm hb))]
      exact hl.lengthValue v hvm hb)
    (by
      intro hb
      rw [hpa,hpcs,hpR,h.realFrame _ (Or.inl (hl.costBelow v hvm hb))]
      exact hl.costValue v hvm hb)
  have hseq : Run input fillEvalCmd s t (8+n) := Run.seq hp hrun
  exact ⟨t,8+n,hseq,by omega,
    fillEval_invariant A T i j array base R lengthStride costStride initial k input s t
      (8+n) hseq h,hkey,htag⟩

private theorem fillBody_run (A : InnerInput) (T : Table)
    (i j array base R lengthStride costStride : ℕ) (initial : Store)
    (input : RAMInput)
    (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hl : FillLayout A T i j array base R lengthStride costStride initial)
    (k : ℕ) (s : Store) (hk : k < (activeVertices A.I).length)
    (h : FillInvariant A T i j array base R lengthStride costStride initial k s) :
    ∃ t n, Run input fillBody s t n ∧
      FillInvariant A T i j array base R lengthStride costStride initial (k+1) t ∧ n ≤ 32 := by
  let v := (activeVertices A.I)[k]
  have hv : (activeVertices A.I)[k]? = some v := List.getElem?_eq_getElem hk
  obtain ⟨t,n,hrun,hn,ht,hkey,htag⟩ :=
    fillEval_correct A T i j array base R lengthStride costStride initial k v input s
      hi hj hk hv hl h
  have hstore : Run input (.atoms fillStoreAtoms) t (fillStored input t) 6 :=
    run_atoms input fillStoreAtoms t
  exact ⟨fillStored input t,n+6,Run.seq hrun hstore,
    fillStore_invariant A T i j array base R lengthStride costStride initial k v input t
      hk hv ht hkey htag,by omega⟩

private theorem fillInitialKeys_run (A : InnerInput) (T : Table)
    (i j array base R lengthStride costStride : ℕ) (input : RAMInput) (initial : Store)
    (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hl : FillLayout A T i j array base R lengthStride costStride initial)
    (hr : FillRegisters A i j array base R lengthStride costStride initial) :
    ∃ out n, Run input fillInitialKeys initial out n ∧
      FillInvariant A T i j array base R lengthStride costStride initial
        (activeVertices A.I).length out ∧ n ≤ 34*(activeVertices A.I).length+2 := by
  let reset : Atom := ⟨.natConst 225 0,trivial⟩
  let s := reset.eval input initial
  have hreset : Run input (.atom reset) initial s 1 := Run.atom reset initial
  have hnr : FillRegisters A i j array base R lengthStride costStride s := by
    exact ⟨(hreset.nat_frame 123 (by decide)).trans hr.source,
      (hreset.nat_frame 124 (by decide)).trans hr.limit,
      (hreset.nat_frame 125 (by decide)).trans hr.zero,
      (hreset.nat_frame 126 (by decide)).trans hr.one,
      (hreset.nat_frame 129 (by decide)).trans hr.costStride_eq,
      (hreset.nat_frame 142 (by decide)).trans hr.array_eq,
      (hreset.nat_frame 201 (by decide)).trans hr.i_eq,
      (hreset.nat_frame 202 (by decide)).trans hr.j_eq,
      (hreset.nat_frame 203 (by decide)).trans hr.base_eq,
      (hreset.nat_frame 204 (by decide)).trans hr.count_eq,
      (hreset.nat_frame 208 (by decide)).trans hr.keyBase_eq,
      (hreset.nat_frame 209 (by decide)).trans hr.lengthStride_eq⟩
  have hs : FillInvariant A T i j array base R lengthStride costStride initial 0 s := by
    refine ⟨hnr,?_,?_,?_,?_,?_,?_⟩
    · simp [s,reset,Atom.eval,Store.ofRAM,Store.at,ramStep]
    · intro a v ha
      omega
    · intro a v ha
      omega
    · intro a ha
      omega
    · intro a _
      exact congrFun (hreset.natMemory_frame (by decide)) a
    · intro a _
      exact congrFun (hreset.realMemory_frame (by decide)) a
  obtain ⟨out,n,hrun,hout,hn⟩ := run_bounded_loop input (.nat .lt 225 204) fillBody
    (activeVertices A.I).length 32
    (FillInvariant A T i j array base R lengthStride costStride initial)
    (by
      intro k t _ ht
      simp [Guard.eval,natTest,ht.counter,ht.registers.count_eq])
    (fillBody_run A T i j array base R lengthStride costStride initial input hi hj hl)
    0 s (by omega) hs
  refine ⟨out,1+n,Run.seq hreset hrun,hout,?_⟩
  simp only [Nat.sub_zero] at hn
  omega

private theorem initLayer_parentVertex (A : InnerInput) (T : Table) (v i j : ℕ) :
    parentVertex ((initLayer A T i j).parents v) = 0 := by
  by_cases hs : v = A.I.source
  · simp [initLayer,hs,parentVertex]
  · by_cases hle : dpValue A T v (i+1) j ≤ dpValue A T v i (j+1) <;>
      simp [initLayer,hs,hle,parentVertex]

private theorem fillInitialKeys_persistent (input : RAMInput) (s t : Store) (n : ℕ)
    (hrun : Run input fillInitialKeys s t n) (r : ℕ) (hlo : 200 ≤ r) (hhi : r ≤ 224) :
    t.nr r = s.nr r := by
  interval_cases r <;> exact hrun.nat_frame _ (by decide)

private theorem initLayer_parent_ne_edge (A : InnerInput) (T : Table) (v i j u : ℕ) :
    (initLayer A T i j).parents v ≠ .edge u := by
  by_cases hs : v = A.I.source
  · simp [initLayer,hs]
  · by_cases hle : dpValue A T v (i+1) j ≤ dpValue A T v i (j+1) <;>
      simp [initLayer,hs,hle]

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem Layout.winner_lt_temp {A : InnerInput} (E : Layout A) : E.winner < E.temp := by
  have hp := E.capacity_pos
  have hwp := E.winner_before_parent
  have hpt := E.parent_before_temp
  omega

private theorem fill_address_lt_temp {A : InnerInput} (E : Layout A) (v i j : ℕ)
    (hv : v < A.I.graph.n) (hi : i < tickLimit A) (hj : j < tickLimit A) :
    E.address v i j < E.temp := by
  simpa only [Nat.add_zero] using E.address_lt_temp v i j 0 hv hi hj (by decide)

private theorem Constants.fillRegisters {A : InnerInput} (E : Layout A) (i j : ℕ) (s : Store)
    (h : Constants E i j s) :
    FillRegisters A i j E.activeArray (E.address 0 i j) E.temp
      (4*A.I.graph.n*tickLimit A) (4*A.I.graph.n) s := by
  rcases h with ⟨hn,hs,hq,hz,ho,hcs,hh,hl,hm,ha,hbase,hi,hj,haddr,hcount,hw,hp,hb,hr,hls,
    hLength,hCost,hZ⟩
  exact ⟨hs,hq,hz,ho,hcs,ha,hi,hj,haddr,hcount,hr,hls⟩

private theorem fillInitialKeys_constants {A : InnerInput} (E : Layout A) (i j : ℕ)
    (input : RAMInput) (s t : Store) (n : ℕ) (hrun : Run input fillInitialKeys s t n)
    (h : Constants E i j s) : Constants E i j t := by
  rcases h with ⟨hn,hs,hq,hz,ho,hcs,hh,hl,hm,ha,hbase,hi,hj,haddr,hcount,hw,hp,hb,hr,hls,
    hLength,hCost,hZ⟩
  exact ⟨(hrun.nat_frame 121 (by decide)).trans hn,
    (hrun.nat_frame 123 (by decide)).trans hs,
    (hrun.nat_frame 124 (by decide)).trans hq,
    (hrun.nat_frame 125 (by decide)).trans hz,
    (hrun.nat_frame 126 (by decide)).trans ho,
    (hrun.nat_frame 129 (by decide)).trans hcs,
    (hrun.nat_frame 137 (by decide)).trans hh,
    (hrun.nat_frame 139 (by decide)).trans hl,
    (hrun.nat_frame 141 (by decide)).trans hm,
    (hrun.nat_frame 142 (by decide)).trans ha,
    (hrun.nat_frame 200 (by decide)).trans hbase,
    (hrun.nat_frame 201 (by decide)).trans hi,
    (hrun.nat_frame 202 (by decide)).trans hj,
    (hrun.nat_frame 203 (by decide)).trans haddr,
    (hrun.nat_frame 204 (by decide)).trans hcount,
    (hrun.nat_frame 205 (by decide)).trans hw,
    (hrun.nat_frame 206 (by decide)).trans hp,
    (hrun.nat_frame 207 (by decide)).trans hb,
    (hrun.nat_frame 208 (by decide)).trans hr,
    (hrun.nat_frame 209 (by decide)).trans hls,
    (hrun.real_frame 200 (by decide)).trans hLength,
    (hrun.real_frame 201 (by decide)).trans hCost,
    (hrun.real_frame 202 (by decide)).trans hZ⟩

private theorem fillLayout_of_table {A : InnerInput} (E : Layout A) (T : Table) (i j : ℕ)
    (s : Store) (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hg : GraphMemory E s) (ht : TableValues E T s) :
    FillLayout A T i j E.activeArray (E.address 0 i j) E.temp
      (4*A.I.graph.n*tickLimit A) (4*A.I.graph.n) s := by
  have heL (v : ℕ) : E.address 0 i j+4*v+4*A.I.graph.n*tickLimit A =
      E.address v (i+1) j := by unfold Layout.address; ring
  have heC (v : ℕ) : E.address 0 i j+4*v+4*A.I.graph.n =
      E.address v i (j+1) := by unfold Layout.address; ring
  refine ⟨fun k v hv => (hg k v hv).2,?_,?_,?_,?_,?_⟩
  · intro k hk
    have ha := E.array_before_winner
    have hw := E.winner_lt_temp
    omega
  · intro v hv hb
    rw [heL]
    exact fill_address_lt_temp E v (i+1) j (activeVertices_valid A.I v hv) hb hj
  · intro v hv hb
    rw [heL,ht v hv (i+1) hb j hj]
    simp [dpValue,show ¬tickLimit A ≤ i+1 by omega,show ¬tickLimit A ≤ j by omega]
  · intro v hv hb
    rw [heC]
    exact fill_address_lt_temp E v i (j+1) (activeVertices_valid A.I v hv) hi hb
  · intro v hv hb
    rw [heC,ht v hv i hi (j+1) hb]
    simp [dpValue,show ¬tickLimit A ≤ i by omega,show ¬tickLimit A ≤ j+1 by omega]

private theorem fillInitialKeys_layout {A : InnerInput} (E : Layout A) (T : Table) (i j : ℕ)
    (input : RAMInput) (s : Store) (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hc : Constants E i j s) (hg : GraphMemory E s) (ht : TableValues E T s) :
    ∃ out n, Run input fillInitialKeys s out n ∧ Constants E i j out ∧
      GraphMemory E out ∧ Arrays E (initLayer A T i j) out ∧ TableValues E T out ∧
      (∀ a < E.temp, out.nm a = s.nm a ∧ out.rm a = s.rm a) ∧
      n ≤ 34*(activeVertices A.I).length+2 := by
  obtain ⟨out,n,hrun,hout,hn⟩ := fillInitialKeys_run A T i j E.activeArray
    (E.address 0 i j) E.temp (4*A.I.graph.n*tickLimit A) (4*A.I.graph.n) input s hi hj
    (fillLayout_of_table E T i j s hi hj hg ht) (Constants.fillRegisters E i j s hc)
  refine ⟨out,n,hrun,fillInitialKeys_constants E i j input s out n hrun hc,?_,?_,?_,?_,hn⟩
  · intro k v hv
    obtain ⟨hk,_⟩ := List.getElem?_eq_some_iff.mp hv
    have hvm := activeVertices_valid A.I v (List.mem_of_getElem? hv)
    have hm := E.map_before_winner
    have ha := E.array_before_winner
    have hw := E.winner_lt_temp
    rw [hout.naturalFrame _ (Or.inl (by omega : E.ordinalMap+v < E.temp)),
      hout.naturalFrame _ (Or.inl (by omega : E.activeArray+k < E.temp))]
    exact hg k v hv
  · intro k v hv
    obtain ⟨hk,_⟩ := List.getElem?_eq_some_iff.mp hv
    refine ⟨hout.key k v hk hv,hout.tag k v hk hv,?_,?_⟩
    · rw [initLayer_parentVertex]
      exact hout.parent k hk
    · intro u he
      exact False.elim (initLayer_parent_ne_edge A T v i j u he)
  · intro v hv a ha b hb
    rw [hout.realFrame _ (Or.inl (fill_address_lt_temp E v a b (activeVertices_valid A.I v hv) ha hb))]
    exact ht v hv a ha b hb
  · intro a ha
    exact ⟨hout.naturalFrame a (Or.inl ha),hout.realFrame a (Or.inl ha)⟩

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem initialQueueStore_values (input : RAMInput) (s : Store) :
    let t := initialQueueStore input s
    t.nr 1 = s.nr 205 ∧ t.nr 2 = s.nr 206 ∧ t.nr 3 = 0 ∧ t.nr 4 = 1 ∧
      t.nr 11 = s.nr 207 ∧ t.nr 12 = s.nr 204 ∧ t.nr 13 = s.nr 208 ∧ t.nr 210 = 0 := by
  simp [initialQueueStore,evalAtoms,initialQueueSetup,Atom.eval,Store.ofRAM,Store.at,ramStep]

private theorem initializeLayer_persistent (input : RAMInput) (s t : Store) (n : ℕ)
    (hrun : Run input initializeLayer s t n) (r : ℕ)
    (hlo : 200 ≤ r) (hhi : r ≤ 224) (hne : r ≠ 210) : t.nr r = s.nr r := by
  interval_cases r <;> first | omega | exact hrun.nat_frame _ (by decide)

private theorem initializeLayer_constants {A : InnerInput} (E : Layout A) (i j : ℕ)
    (input : RAMInput) (s t : Store) (n : ℕ) (hrun : Run input initializeLayer s t n)
    (h : Constants E i j s) : Constants E i j t := by
  rcases h with ⟨hn,hs,hq,hz,ho,hcs,hh,hl,hm,ha,hbase,hi,hj,haddr,hcount,hw,hp,hb,hr,hls,
    hLength,hCost,hZ⟩
  exact ⟨(hrun.nat_frame 121 (by decide)).trans hn,
    (hrun.nat_frame 123 (by decide)).trans hs,
    (hrun.nat_frame 124 (by decide)).trans hq,
    (hrun.nat_frame 125 (by decide)).trans hz,
    (hrun.nat_frame 126 (by decide)).trans ho,
    (hrun.nat_frame 129 (by decide)).trans hcs,
    (hrun.nat_frame 137 (by decide)).trans hh,
    (hrun.nat_frame 139 (by decide)).trans hl,
    (hrun.nat_frame 141 (by decide)).trans hm,
    (hrun.nat_frame 142 (by decide)).trans ha,
    (hrun.nat_frame 200 (by decide)).trans hbase,
    (hrun.nat_frame 201 (by decide)).trans hi,
    (hrun.nat_frame 202 (by decide)).trans hj,
    (hrun.nat_frame 203 (by decide)).trans haddr,
    (hrun.nat_frame 204 (by decide)).trans hcount,
    (hrun.nat_frame 205 (by decide)).trans hw,
    (hrun.nat_frame 206 (by decide)).trans hp,
    (hrun.nat_frame 207 (by decide)).trans hb,
    (hrun.nat_frame 208 (by decide)).trans hr,
    (hrun.nat_frame 209 (by decide)).trans hls,
    (hrun.real_frame 200 (by decide)).trans hLength,
    (hrun.real_frame 201 (by decide)).trans hCost,
    (hrun.real_frame 202 (by decide)).trans hZ⟩

private theorem prefixLeaf_initLayer {A : InnerInput} (E : Layout A) (T : Table)
    (i j : ℕ) (s : Store) (ha : Arrays E (initLayer A T i j) s) :
    Queue.prefixLeaf E.capacity (fun k => s.rm (E.temp+k)) (activeVertices A.I).length =
      layerLeaf E (initLayer A T i j) := by
  funext node
  by_cases hn : E.capacity ≤ node ∧ node < E.capacity+(activeVertices A.I).length
  · have hk : node-E.capacity < (activeVertices A.I).length := by omega
    let v := (activeVertices A.I)[node-E.capacity]
    have hv : (activeVertices A.I)[node-E.capacity]? = some v := List.getElem?_eq_getElem hk
    have hm : v ∈ activeVertices A.I := List.mem_of_getElem? hv
    simp only [Queue.prefixLeaf,layerLeaf,hn,if_pos,Option.getD_some,hv,initLayer,hm]
    rw [(ha (node-E.capacity) v hv).1]
    rfl
  · simp [Queue.prefixLeaf,layerLeaf,hn]

private theorem queueFrame_graph {A : InnerInput} (E : Layout A) (s t : Store)
    (hf : Queue.InitFrame E.winner E.parent E.capacity s t)
    (hg : GraphMemory E s) : GraphMemory E t := by
  intro k v hv
  obtain ⟨hk,_⟩ := List.getElem?_eq_some_iff.mp hv
  have hvm := activeVertices_valid A.I v (List.mem_of_getElem? hv)
  have hm := E.map_before_winner
  have ha := E.array_before_winner
  have hwp := E.winner_before_parent
  rw [hf.1 _ (Or.inl (by omega : E.ordinalMap+v < E.winner))
      (Or.inl (by omega : E.ordinalMap+v < E.parent)),
    hf.1 _ (Or.inl (by omega : E.activeArray+k < E.winner))
      (Or.inl (by omega : E.activeArray+k < E.parent))]
  exact hg k v hv

private theorem queueFrame_arrays {A : InnerInput} (E : Layout A) (S : LayerState) (s t : Store)
    (hf : Queue.InitFrame E.winner E.parent E.capacity s t)
    (ha : Arrays E S s) : Arrays E S t := by
  have hwp := E.winner_before_parent
  have hpt := E.parent_before_temp
  have hnm (a : ℕ) (h : E.temp ≤ a) : t.nm a = s.nm a :=
    hf.1 a (Or.inr (by omega)) (Or.inr (by omega))
  have hrm (a : ℕ) (h : E.temp ≤ a) : t.rm a = s.rm a :=
    hf.2 a (Or.inr (by omega))
  intro k v hv
  rw [hrm _ (by omega),hnm _ (by omega),hnm _ (by omega)]
  refine ⟨(ha k v hv).1,(ha k v hv).2.1,(ha k v hv).2.2.1,?_⟩
  intro u hu
  rw [hrm _ (by omega),hrm _ (by omega)]
  exact (ha k v hv).2.2.2 u hu

private theorem queueFrame_table {A : InnerInput} (E : Layout A) (T : Table) (s t : Store)
    (hf : Queue.InitFrame E.winner E.parent E.capacity s t)
    (ht : TableValues E T s) : TableValues E T t := by
  intro v hv i hi j hj
  have hb : E.address v i j < E.winner := by
    simpa only [Nat.add_zero] using E.address_lt_winner v i j 0
      (activeVertices_valid A.I v hv) hi hj (by decide)
  rw [hf.2 _ (Or.inl hb)]
  exact ht v hv i hi j hj

private theorem initializeLayer_run {A : InnerInput} (E : Layout A) (T : Table) (i j : ℕ)
    (input : RAMInput) (s : Store) (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hc : Constants E i j s) (hg : GraphMemory E s) (ht : TableValues E T s) :
    ∃ out n, Run input initializeLayer s out n ∧ LayerRep E i j (initLayer A T i j) out ∧
      (∀ a < E.winner, out.nm a = s.nm a ∧ out.rm a = s.rm a) ∧
      n ≤ 15*E.capacity + (19*Nat.clog 2 (2*E.capacity)+47)*(activeVertices A.I).length+13 := by
  obtain ⟨f,nf,hfill,hfc,hfg,hfa,hft,hff,hnf⟩ :=
    fillInitialKeys_layout E T i j input s hi hj hc hg ht
  let p := initialQueueStore input f
  have hp : Run input (.atoms initialQueueSetup) f p 8 := run_atoms input initialQueueSetup f
  have hpn : p.nm = f.nm := hp.natMemory_frame (by decide)
  have hpr : p.rm = f.rm := hp.realMemory_frame (by decide)
  have hpg : GraphMemory E p := by simpa only [GraphMemory,hpn] using hfg
  have hpa : Arrays E (initLayer A T i j) p := by simpa only [Arrays,hpn,hpr] using hfa
  have hpt : TableValues E T p := by simpa only [TableValues,hpr] using hft
  obtain ⟨h1,h2,h3,h4,h11,h12,h13,h210⟩ := initialQueueStore_values input f
  rcases hfc with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hN,hW,hP,hB,hR,_⟩
  rw [hW] at h1
  rw [hP] at h2
  rw [hB] at h11
  rw [hN] at h12
  rw [hR] at h13
  have hspace := E.winner_before_parent
  have htemp := E.parent_before_temp
  obtain ⟨out,nq,hqueue,hq,hnq⟩ := Queue.buildQueue_run input E.capacity
    (activeVertices A.I).length E.winner E.parent E.temp p E.capacity_pos E.active_fit
    E.winner_before_parent (by intro a _; exact Or.inr (by omega)) h1 h2 h3 h4 h11 h12 h13
  have hrun : Run input initializeLayer s out (nf+(8+nq)) :=
    Run.seq hfill (Run.seq hp hqueue)
  have hheap : Heap E (initLayer A T i j) out := by
    refine ⟨?_,?_⟩
    · rw [← prefixLeaf_initLayer E T i j p hpa]
      exact hq.represents
    · intro u hu
      simpa only [hq.hP] using hq.parents.2.2.2 u hu
  refine ⟨out,nf+(8+nq),hrun,?_,?_,?_⟩
  · refine ⟨initializeLayer_constants E i j input s out _ hrun hc,
      queueFrame_graph E p out hq.frame hpg,hheap,queueFrame_arrays E _ p out hq.frame hpa,
      queueFrame_table E T p out hq.frame hpt,?_,?_⟩
    · exact List.Sublist.refl _
    · exact (hqueue.nat_frame 210 (by decide)).trans h210
  · intro a ha
    have hat : a < E.temp := ha.trans E.winner_lt_temp
    have hap : a < E.parent := by omega
    exact ⟨(hq.frame.1 a (Or.inl ha) (Or.inl hap)).trans
        ((congrFun hpn a).trans (hff a hat).1),
      (hq.frame.2 a (Or.inl ha)).trans ((congrFun hpr a).trans (hff a hat).2)⟩
  · nlinarith

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem layerLoop_correct {A : InnerInput} (E : Layout A) (i j : ℕ) (ε : ℝ)
    (remaining : ℕ) (S : LayerState) (s : Store) (hrep : LayerRep E i j S s)
    (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hcount : S.queue.length = remaining)
    (hbalance : S.nextRank + S.queue.length = (activeVertices A.I).length)
    (hpop : poppedCells E i j S s)
    (hadj : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm) :
    ∃ t steps, Run (encodeInput A.I ε) layerLoop s t steps ∧
      steps ≤ (19*Nat.clog 2 (2*E.capacity)+48)*remaining +
        outgoingCost A E * outgoingWork A.I S.queue + 1 ∧
      LayerRep E i j (queueRun A i j remaining S) t ∧
      poppedCells E i j (queueRun A i j remaining S) t ∧
      OutsideTableFrame E s t ∧
      (∀ v ∈ activeVertices A.I, ∀ a < tickLimit A, ∀ b < tickLimit A,
        (a ≠ i ∨ b ≠ j) → StoredCell E S.table v a b s →
        StoredCell E (queueRun A i j remaining S).table v a b t) := by
  induction remaining generalizing S s with
  | zero =>
      have hN : s.nr 204 = (activeVertices A.I).length := hrep.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hrank : s.nr 210 = (activeVertices A.I).length := by
        rw [hrep.2.2.2.2.2.2]; omega
      refine ⟨s,1,Run.loopFalse ?_,by omega,hrep,hpop,OutsideTableFrame.refl _ _,?_⟩
      · simp [Guard.eval,natTest,hrank,hN]
      · intro v hv a ha b hb hab h; exact h
  | succ n ih =>
      have hne : S.queue ≠ [] := by intro h; simp [h] at hcount
      have hu : pickedVertex S ∈ S.queue := pickedVertex_mem S hne
      obtain ⟨p,np,hp,hnp,hpr,hpc,hpf,hpp⟩ :=
        layerStep_correct E i j ε S s hrep hi hj hne hpop hadj
      have hpcount : (popLayer A i j S).queue.length = n := by
        rw [popLayer_queue_length,hcount]; omega
      have hprank : (popLayer A i j S).nextRank = S.nextRank+1 := by
        rw [popLayer_eq_relaxAll A i j S hne,relaxAll_nextRank]; rfl
      have hpbalance : (popLayer A i j S).nextRank + (popLayer A i j S).queue.length =
          (activeVertices A.I).length := by omega
      obtain ⟨out,no,ho,hno,hor,hoc,hof,hop⟩ := ih _ p hpr hpcount hpbalance hpc
        (OutsideTableFrame.adjacency E s p hpf hadj)
      have hN : s.nr 204 = (activeVertices A.I).length := hrep.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hguard : (Guard.nat .lt 210 204).eval s = true := by
        simp only [Guard.eval,natTest,hrep.2.2.2.2.2.2,hN]
        exact decide_eq_true (by omega)
      have hwork : (outgoingEdges A.I (pickedVertex S)).length +
          outgoingWork A.I (popLayer A i j S).queue = outgoingWork A.I S.queue := by
        rw [popLayer_eq_relaxAll A i j S hne,relaxAll_queue]
        exact outgoingWork_settle A.I S i j (pickedVertex S) hu
      have hworkMul := congrArg (fun w => outgoingCost A E*w) hwork
      simp only [Nat.mul_add] at hworkMul
      have hrec : queueRun A i j (n+1) S = queueRun A i j n (popLayer A i j S) :=
        queueRun_succ_front A i j n S
      refine ⟨out,_,Run.loopTrue hguard hp ho,?_,?_,?_,hpf.trans hof,?_⟩
      · nlinarith
      · simpa only [hrec] using hor
      · simpa only [hrec] using hoc
      · intro v hv a ha b hb hab hold
        rw [hrec]
        exact hop v hv a ha b hb hab (hpp v a b hv ha hb hab hold)

private theorem layer_correct {A : InnerInput} (E : Layout A) (T : Table) (i j : ℕ)
    (ε : ℝ) (s : Store) (hi : i < tickLimit A) (hj : j < tickLimit A)
    (hc : Constants E i j s) (hg : GraphMemory E s) (ht : TableValues E T s)
    (hadj : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm) :
    ∃ t steps, Run (encodeInput A.I ε) layerCmd s t steps ∧ steps ≤ layerCost E ∧
      Constants E i j t ∧ GraphMemory E t ∧ TableValues E (buildLayer A T i j) t ∧
      (∀ v ∈ activeVertices A.I, StoredCell E (buildLayer A T i j) v i j t) ∧
      OutsideTableFrame E s t ∧
      (∀ v ∈ activeVertices A.I, ∀ a < tickLimit A, ∀ b < tickLimit A,
        (a ≠ i ∨ b ≠ j) → StoredCell E T v a b s →
        StoredCell E (buildLayer A T i j) v a b t) := by
  obtain ⟨p,np,hp,hpr,hpf,hnp⟩ := initializeLayer_run E T i j (encodeInput A.I ε) s hi hj hc hg ht
  have hpFrame : OutsideTableFrame E s p := fun a ha _ => hpf a ha
  have hpPopped : poppedCells E i j (initLayer A T i j) p := by
    intro v hv hn; exact False.elim (hn hv)
  obtain ⟨out,no,ho,hno,hor,hoc,hof,hop⟩ := layerLoop_correct E i j ε
    (activeVertices A.I).length (initLayer A T i j) p hpr hi hj rfl (by simp [initLayer])
      hpPopped (OutsideTableFrame.adjacency E s p hpFrame hadj)
  have htable : (queueRun A i j (activeVertices A.I).length (initLayer A T i j)).table =
      buildLayer A T i j := rfl
  refine ⟨out,np+no,Run.seq hp ho,?_,hor.1,hor.2.1,?_,?_,hpFrame.trans hof,?_⟩
  · have hw : outgoingWork A.I (initLayer A T i j).queue = A.I.graph.edges.length :=
      outgoingWork_active A.I
    rw [hw] at hno
    unfold layerCost
    nlinarith
  · simpa only [htable] using hor.2.2.2.2.1
  · intro v hv
    have h := hoc v hv (by rw [buildLayer_queue_exhausted]; simp)
    simpa only [htable] using h
  · intro v hv a ha b hb hab hold
    have hpStored : StoredCell E T v a b p :=
      StoredCell.transfer E T v a b s p (activeVertices_valid A.I v hv) ha hb hold hpf
    simpa only [htable] using hop v hv a ha b hb hab hpStored

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem buildTable_run {A : InnerInput} (E : Layout A) (ε : ℝ) (s : Store)
    (hc : Constants E (tickLimit A) 0 s) (hg : GraphMemory E s)
    (ht : TableValues E (fun _ _ _ => ⟨1,.lengthTick,0⟩) s)
    (hadj : Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links s.nm) :
    ∃ out n, Run (encodeInput A.I ε) buildTableCmd s out n ∧ n ≤ tableCost E ∧
      Constants E 0 0 out ∧ GraphMemory E out ∧ TableValues E (buildTable A) out ∧
      (∀ v ∈ activeVertices A.I, ∀ i < tickLimit A, ∀ j < tickLimit A,
        StoredCell E (buildTable A) v i j out) ∧
      OutsideTableFrame E s out ∧
      Preprocess.AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links out.nm := by
  have hLayer : LayerContract E ε layerCmd (layerCost E) := by
    intro T i j t hi hj hc hg ht hadj
    exact layer_correct E T i j ε t hi hj hc hg ht hadj
  obtain ⟨out,n,hrun,hn,hout⟩ := table_run_of_layer_contract E ε layerCmd (layerCost E)
    hLayer (fun _ _ _ => ⟨1,.lengthTick,0⟩) (tickLimit A) s le_rfl hc hg ht hadj
  rw [rowsTable_eq_buildTable] at hout
  exact ⟨out,n,hrun,hn,hout.constants,hout.graph,hout.table,hout.stored,hout.frame,hout.adjacency⟩

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.DP
open Structured

private theorem buildTable_nat_disjoint :
    Disjoint outerPersistentRegisters buildTableCmd.natWrites := by decide

private theorem buildTable_real_disjoint :
    Disjoint outerPersistentRegisters buildTableCmd.realWrites := by decide

private theorem buildTable_persistent (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input buildTableCmd s t steps)
    (hr : (121 ≤ r ∧ r ≤ 153) ∨ (243 ≤ r ∧ r ≤ 259)) :
    t.nr r = s.nr r ∧ t.rr r = s.rr r := by
  have hmem : r ∈ outerPersistentRegisters := by simpa [outerPersistentRegisters] using hr
  exact ⟨h.nat_frame r (fun hw => Finset.disjoint_left.mp buildTable_nat_disjoint hmem hw),
    h.real_frame r (fun hw => Finset.disjoint_left.mp buildTable_real_disjoint hmem hw)⟩

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured Preprocess TargetRecords

private theorem body_run (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (r : ℕ) (A : InnerInput) (hA : (outerInputs I ε)[r]? = some A)
    (s : Store) (hs : Invariant I ε r s) :
    ∃ out n, Run (encodeInput I ε) (body DP.buildTableCmd) s out n ∧
      Invariant I ε (r+1) out ∧
      n ≤ DP.tableCost (outerLayout I ε hε hε1 r A hA) +
        27*(activeVertices I).length+23 := by
  let input := encodeInput I ε
  let E := outerLayout I ε hε hε1 r A hA
  let p := prepared input s
  have hp : Run input (.atoms prepareOps) s p 14 := run_atoms input prepareOps s
  have hpInv : Invariant I ε r p := hs.readonly
    (prepared_runtime input I ε s hs.runtime)
    (prepared_registers input I ε r s hs.registers) rfl rfl
  have hc : DP.Constants E (tickLimit A) 0 p :=
    prepared_constants input I ε hε hε1 r A hA s hs.runtime hs.registers
  have hg : DP.GraphMemory E p := hpInv.runtime.outerGraphMemory hε hε1 r A hA
  have ht : DP.TableValues E (fun _ _ _ => ⟨1,.lengthTick,0⟩) p :=
    hpInv.future.outerInitialTable hε hε1 A hA
  have hadj : AdjacencyPrefix A.I A.I.graph.edges.length E.heads E.links p.nm :=
    hpInv.runtime.outerAdjacency hε hε1 r A hA
  obtain ⟨d,nD,hD,hnD,hcD,hgD,htD,hstored,hframe,hadjD⟩ :=
    DP.buildTable_run E ε p hc hg ht hadj
  obtain ⟨hI,hdelta,hLength,hq⟩ := outerInputs_get_parameters I ε hε hε1 r A hA
  obtain ⟨hr,_⟩ := List.getElem?_eq_some_iff.mp hA
  have hD' : Run input DP.buildTableCmd p d nD := by simpa only [hI] using hD
  have hPersist (a : ℕ) (ha : (121 ≤ a ∧ a ≤ 153) ∨ (243 ≤ a ∧ a ≤ 259)) :
      d.nr a = p.nr a ∧ d.rr a = p.rr a :=
    DP.buildTable_persistent input p d nD a hD' ha
  have hf : OuterTableFrame I ε r p d :=
    outsideTableFrame_outer I ε hε hε1 r A hA p d hframe
  have hRuntimeD : RuntimeReady I ε d := hf.runtime hr hpInv.runtime
    (fun a h1 h2 => (hPersist a (Or.inl ⟨h1,h2⟩)).1)
    (fun a h1 h2 => (hPersist a (Or.inl ⟨h1,h2⟩)).2)
  have hRegistersD : Registers I ε r d := hpInv.registers.transfer
    (fun a h1 h2 => (hPersist a (Or.inr ⟨h1,by omega⟩)).1)
    (fun a h1 h2 => (hPersist a (Or.inr ⟨h1,by omega⟩)).2)
  have hParentsD : OutputParents I d := hf.parents (by omega) hpInv.parents
  have hRecordsD : RecordMap I ε (branchesAfter I ε r) d :=
    hf.records (by omega) _ hpInv.records
  have hOutputD : OutputTable I ε r A d :=
    outerStored_outputTable I ε hε hε1 r A hA d hstored
  have hTablesD : CompletedTables I ε (r+1) d :=
    (hf.completed (by omega) hε hε1 hpInv.tables).succ hA hOutputD
  have hFutureD : FutureZero I ε (r+1) d := hf.future hpInv.future
  let m := markPrepared input d
  have hm : Run input (.atoms markOps) d m 2 := run_atoms input markOps d
  have hRuntimeM : RuntimeReady I ε m := markPrepared_runtime input I ε d hRuntimeD
  have hRegistersM : Registers I ε r m := markPrepared_registers input I ε r d hRegistersD
  have hWorld : MarkWorld I ε r A m := by
    refine ⟨?_,?_,?_⟩
    · exact (markPrepared_values input d).1.trans hRegistersD.table
    · change d.rr 123*d.rr 243 = (1+A.δ)*A.L
      rw [hRuntimeD.numeric.ratio,hRegistersD.length,hdelta,hLength]
    · intro v hv
      exact hOutputD.zero_mass v hv
  obtain ⟨t,nM,hMark,hWorldT,hRecordsT,hTarget,hnM⟩ :=
    markRecords_run input I ε r A hA (arrayBase I ε) m hWorld hRecordsD
      hRuntimeM.active.array_reg hRuntimeM.active.count_reg
      (fun k hk => hRuntimeM.active.value k _ (List.getElem?_eq_getElem hk))
      (by unfold arrayBase graphBase Query.outputEnd; omega)
  have hMarkPersist (a : ℕ) (ha : (121 ≤ a ∧ a ≤ 153) ∨ (243 ≤ a ∧ a ≤ 259)) :
      t.nr a = m.nr a ∧ t.rr a = m.rr a :=
    markRecords_persistent input m t nM a hMark ha
  have hRuntimeT : RuntimeReady I ε t := hTarget.runtime hRuntimeM
    (fun a h1 h2 => (hMarkPersist a (Or.inl ⟨h1,h2⟩)).1)
    (fun a h1 h2 => (hMarkPersist a (Or.inl ⟨h1,h2⟩)).2)
  have hRegistersT : Registers I ε r t := hRegistersM.transfer
    (fun a h1 h2 => (hMarkPersist a (Or.inr ⟨h1,by omega⟩)).1)
    (fun a h1 h2 => (hMarkPersist a (Or.inr ⟨h1,by omega⟩)).2)
  have hParentsT : OutputParents I t := hTarget.parents hParentsD
  have hTablesT : CompletedTables I ε (r+1) t := hTarget.completed hTablesD hε hε1
  have hFutureT : FutureZero I ε (r+1) t := hTarget.future hFutureD
  let out := advanced input t
  have hAdvance : Run input (.atoms advanceOps) t out 3 := run_atoms input advanceOps t
  have hout : Invariant I ε (r+1) out :=
    ⟨advanced_runtime input I ε t hRuntimeT,
      advanced_registers input I ε r t hRuntimeT hRegistersT,
      hParentsT,hRecordsT,hTablesT,hFutureT⟩
  refine ⟨out,14+(nD+(2+(nM+3))),Run.seq hp (Run.seq hD' (Run.seq hm
    (Run.seq hMark hAdvance))),hout,?_⟩
  dsimp only [E] at hnD
  omega

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.DP

private theorem tableCost_with_outer_bound {A : InnerInput} (E : Layout A)
    (hB : E.capacity ≤ 2*(activeVertices A.I).length) :
    tableCost E + 27*(activeVertices A.I).length + 44 ≤
      1000*((activeVertices A.I).length+A.I.graph.edges.length+1)*
        (Nat.clog 2 (2*E.capacity)+1)*(tickLimit A+1)^4 := by
  let N := (activeVertices A.I).length
  let m := A.I.graph.edges.length
  let l := Nat.clog 2 (2*E.capacity)
  let q := tickLimit A
  let p := N+m+1
  let L := l+1
  let t := (q+1)^2
  let F := p*L*t
  have hp : 1 ≤ p := by omega
  have hL : 1 ≤ L := by omega
  have ht : 1 ≤ t := Nat.one_le_pow 2 (q+1) (by omega)
  have hLp : p ≤ p*L := by simpa using Nat.mul_le_mul_left p hL
  have hF : p*L ≤ F := by simpa [F] using Nat.mul_le_mul_left (p*L) ht
  have hpF : p ≤ F := hLp.trans hF
  have hFpos : 1 ≤ F := hp.trans hpF
  have hLt : t ≤ L*t := by simpa using Nat.mul_le_mul_right t hL
  have hLLt : L ≤ L*t := by simpa using Nat.mul_le_mul_left L ht
  have hBterm : 15*E.capacity ≤ 30*F := by
    have : E.capacity ≤ 2*N := hB
    have : N ≤ p := by omega
    omega
  have hNterm : (38*l+100)*N ≤ 138*F := by
    have hcoeff : 38*l+100 ≤ 138*L := by dsimp [L]; omega
    have hN : N ≤ p := by omega
    have hmul := Nat.mul_le_mul hcoeff hN
    nlinarith
  have hcoeff : 100*t+19*l+74 ≤ 193*(L*t) := by
    have hl : l+1=L := rfl
    nlinarith
  have hmterm : (100*t+19*l+74)*m ≤ 193*F := by
    have hm : m ≤ p := by omega
    have hmul := Nat.mul_le_mul hcoeff hm
    dsimp [F]
    nlinarith
  have hlayer : layerCost E ≤ 400*F := by
    change 15*E.capacity+(38*l+100)*N+(100*t+19*l+74)*m+20 ≤ 400*F
    omega
  have hq : q^2 ≤ t := Nat.pow_le_pow_left (by omega : q ≤ q+1) 2
  have hqt : q ≤ t := by dsimp [t]; nlinarith
  have hFt : F ≤ F*t := by simpa using Nat.mul_le_mul_left F ht
  have htFt : t ≤ F*t := by simpa using Nat.mul_le_mul_right t hFpos
  have htable : tableCost E ≤ 410*F*t := by
    have hmul := Nat.mul_le_mul hlayer hq
    change ((layerCost E+4)*q+5)*q+1 ≤ _
    nlinarith
  have hmark : 27*N+44 ≤ 71*F*t := by
    have hN : N ≤ p := by omega
    nlinarith
  calc
    tableCost E+27*N+44 ≤ 481*F*t := by nlinarith
    _ ≤ 1000*F*t := Nat.mul_le_mul_right t (Nat.mul_le_mul_right F (by decide : 481 ≤ 1000))
    _ = 1000*(N+m+1)*(l+1)*(q+1)^4 := by dsimp [F,p,L,t]; ring

end NearLinearRSP.TwoResources.Mission.DP
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured Preprocess TargetRecords

private theorem all_tables_run (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (s : Store) (hs : Invariant I ε 0 s) :
    ∃ out n, Run (encodeInput I ε) (loopCmd DP.buildTableCmd) s out n ∧
      Invariant I ε (outerInputs I ε).length out ∧
      n ≤ iterationBound I ε*(outerInputs I ε).length+1 := by
  have hB : queueCapacity I ≤ 2*(activeVertices I).length :=
    (Queue.capacity_bounds _ (activeVertices_length_pos I)).2.le
  have hb : 2≤ iterationBound I ε := by
    have hx : 1≤((activeVertices I).length+I.graph.edges.length+1)*
        (Nat.clog 2 (2*queueCapacity I)+1)*(outerQ ε+1)^4 := by
      have hp : 0<((activeVertices I).length+I.graph.edges.length+1)*
          (Nat.clog 2 (2*queueCapacity I)+1)*(outerQ ε+1)^4 := by positivity
      omega
    unfold iterationBound
    nlinarith
  have hstep : ∀ k t, k<(outerInputs I ε).length → Invariant I ε k t →
      ∃ u cost, Run (encodeInput I ε) (body DP.buildTableCmd) t u cost ∧
        Invariant I ε (k+1) u ∧ cost ≤  iterationBound I ε-2 := by
    intro k t hk ht
    obtain ⟨hC,hA⟩ := outerInputs_get_grid I ε hε hε1 k hk
    let A := gridInput I ε hε hε1 hC k
    obtain ⟨u,cost,hrun,hu,hcost⟩ := body_run I ε hε hε1 k A hA t ht
    have htable := DP.tableCost_with_outer_bound (outerLayout I ε hε hε1 k A hA) hB
    change DP.tableCost (outerLayout I ε hε hε1 k A hA)+
      27*(activeVertices I).length+44 ≤  iterationBound I ε at htable
    exact ⟨u,cost,hrun,hu,by omega⟩
  obtain ⟨out,n,hrun,hout,hn⟩ := loop_run_of_body (encodeInput I ε) I ε
    DP.buildTableCmd (iterationBound I ε-2) hstep s hs
  refine ⟨out,n,hrun,hout,?_⟩
  simpa only [Nat.sub_add_cancel hb] using hn

private theorem outerCmd_run (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (s : Store) (hrt : RuntimeReady I ε s) (hB : s.nr 11=queueCapacity I)
    (hp : OutputParents I s) (hr : RecordMap I ε (answerBranch I 0) s)
    (hf : FutureZero I ε 0 s) :
    ∃ out n, Run (encodeInput I ε) outerCmd s out n ∧
      (∀ pc, Query.QueryReady I ε (out.at pc)) ∧
      n ≤ iterationBound I ε*((outerInputs I ε).length+1)+16 := by
  let input := encodeInput I ε
  have hinit := run_atoms input initOps s
  have hi := initialized_invariant input I ε s hrt hB hp hr hf
  obtain ⟨out,n,hrun,hout,hn⟩ := all_tables_run I ε hε hε1 _ hi
  refine ⟨out,15+n,Run.seq hinit hrun,fun pc => hout.finished pc,?_⟩
  have hmul : iterationBound I ε*(outerInputs I ε).length ≤
      iterationBound I ε*((outerInputs I ε).length+1) := Nat.mul_le_mul_left _ (by omega)
  omega

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured TargetRecords

private theorem afterTreesCmd_run (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1)
    (s : Store) (hrt : RuntimeReady I ε s) (hB : s.nr 11=queueCapacity I)
    (hp : OutputParents I s) (hw : SeedWorld I s) (hf : FutureZero I ε 0 s)
    (hz : ∀ v<I.graph.n, s.nm (targetAddress v)=0) :
    ∃ out n, Run (encodeInput I ε) afterTreesCmd s out n ∧
      (∀ pc, Query.QueryReady I ε (out.at pc)) ∧
      n ≤ 54*(activeVertices I).length+4+
        (Outer.iterationBound I ε*((outerInputs I ε).length+1)+16) := by
  let input := encodeInput I ε
  have hmem : ∀ k (hk : k<(activeVertices I).length),
      s.nm (arrayBase I ε+k)=(activeVertices I)[k] := by
    intro k hk
    exact hrt.active.value k _ (List.getElem?_eq_getElem hk)
  have hspace : 16+4*I.graph.n≤arrayBase I ε := by
    unfold arrayBase graphBase Query.outputEnd
    omega
  obtain ⟨seeded,sn,hseed,_,hrecords,hframe,hn⟩ := seedRecords_run input I ε
    (arrayBase I ε) s hw hrt.layout.array hrt.active.count_reg hmem hspace hz
  have hseeded := hframe.runtime hrt
    (fun r hlo hhi => (seedRecords_persistent input s seeded sn r hseed (Or.inl ⟨hlo,hhi⟩)).1)
    (fun r hlo hhi => (seedRecords_persistent input s seeded sn r hseed (Or.inl ⟨hlo,hhi⟩)).2)
  have hcapacity := (seedRecords_capacity input s seeded sn hseed).trans hB
  obtain ⟨out,on,hrun,hready,hcost⟩ := Outer.outerCmd_run I ε hε hε1 seeded hseeded hcapacity
    (hframe.parents hp) hrecords (hframe.future hf)
  exact ⟨out,sn+on,Run.seq hseed hrun,hready,by omega⟩

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem length_edge_le_largestLength (I : Instance) (u v : ℕ)
    (he : (u,v) ∈ I.graph.edges) : (I.length u v : ℝ) ≤ largestLength I := by
  by_cases hw : 0 < (I.length u v : ℝ)
  · apply member_le_largestLength I
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_map.mpr ⟨(u,v),he,rfl⟩
    · simpa using hw
  · exact (le_of_not_gt hw).trans (largestLength_nonneg I)

private theorem positive_path_has_positive_edge (I : Instance) (P : List ℕ)
    (hP : P.IsChain (fun u v => (u,v) ∈ I.graph.edges))
    (hpos : 0 < pathWeight I.length P) :
    ∃ u v, (u,v) ∈ I.graph.edges ∧ 0 < (I.length u v : ℝ) ∧
      (I.length u v : ℝ) ≤ pathWeight I.length P := by
  induction P with
  | nil => simp [pathWeight] at hpos
  | cons a P ih =>
      cases P with
      | nil => simp [pathWeight] at hpos
      | cons b P =>
          have htail := pathWeight_nonneg I.length (b::P)
          by_cases hw : 0 < (I.length a b : ℝ)
          · refine ⟨a,b,hP.rel,hw,?_⟩
            rw [pathWeight_cons_cons]
            linarith
          · have hz : (I.length a b : ℝ) = 0 :=
              le_antisymm (le_of_not_gt hw) (I.length a b).coe_nonneg
            have hp : 0 < pathWeight I.length (b::P) := by
              simpa [pathWeight_cons_cons, hz] using hpos
            obtain ⟨u,v,he,hp,hb⟩ := ih hP.tail hp
            exact ⟨u,v,he,hp,by simpa [pathWeight_cons_cons,hz] using hb⟩

private theorem positive_path_length_bounds (I : Instance) (t : ℕ) (P : List ℕ)
    (hP : IsPath I.graph I.source t P) (hpos : 0 < pathWeight I.length P) :
    positiveLengths I ≠ [] ∧ firstPositiveLength I ≤ pathWeight I.length P := by
  obtain ⟨u,v,he,hpos,hbound⟩ := positive_path_has_positive_edge I P hP.2.2 hpos
  have hm : (I.length u v : ℝ) ∈ positiveLengths I := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨(u,v),he,rfl⟩,by simpa using hpos⟩
  exact ⟨List.ne_nil_of_mem hm,(firstPositiveLength_le_member I _ hm).trans hbound⟩

private theorem feasible_zero_or_covered (I : Instance) (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (P : List ℕ) (hP : Feasible I t P) :
    ∃ Q : List ℕ, Feasible I t Q ∧ pathWeight I.length Q ≤ pathWeight I.length P ∧
      (pathWeight I.length Q = 0 ∨
        ∃ L ∈ geometricGuesses I ε,
          pathWeight I.length Q ≤ L ∧ L ≤ (1 + ε / 4) * pathWeight I.length P) := by
  obtain ⟨Q,hQ,hnd,_,hw⟩ := Feasible.exists_simple I t P hP
  refine ⟨Q,hQ,hw,?_⟩
  by_cases hz : pathWeight I.length Q = 0
  · exact Or.inl hz
  · right
    have hp : 0 < pathWeight I.length Q :=
      lt_of_le_of_ne (pathWeight_nonneg _ _) (Ne.symm hz)
    have hbounds := positive_path_length_bounds I t Q hQ.1 hp
    have hupper := IsPath.weight_le_n_mul I.graph I.source t Q hQ.1 I.source_valid hnd
      I.length (largestLength I) (largestLength_nonneg I) (length_edge_le_largestLength I)
    obtain ⟨L,hL,hlo,hhi⟩ := geometricGuesses_cover I ε (pathWeight I.length Q)
      hε hbounds.1 hbounds.2 hupper
    refine ⟨L,hL,hlo,hhi.trans ?_⟩
    exact mul_le_mul_of_nonneg_left hw (by linarith)

private theorem outerInputs_contains_positive_guess (I : Instance) (ε L : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 < (I.budget : ℝ))
    (hL : L ∈ geometricGuesses I ε) (hL0 : 0 < L) :
    ∃ A ∈ outerInputs I ε, A.I = I ∧ A.δ = ε / 4 ∧ A.L = L := by
  let A : InnerInput := {
    I := I
    δ := ε / 4
    accuracy_pos := by linarith
    accuracy_lt_one := by linarith
    L := L
    length_pos := hL0
    budget_pos := hC }
  refine ⟨A,?_,rfl,rfl,rfl⟩
  unfold outerInputs
  simp only [hε,hε1,hC,and_self,↓reduceDIte]
  apply List.mem_filterMap.mpr
  refine ⟨L,hL,?_⟩
  simp [hL0,A]

private theorem firstCrossing_log_bound (a r top : ℝ) (ha : 0 < a) (hr : 1 < r)
    (htop : a ≤ top) :
    (firstCrossing a r top : ℝ) ≤ Real.log (top / a) / Real.log r + 1 := by
  have hr0 : 0 < r := by linarith
  have htop0 : 0 < top := ha.trans_le htop
  have hlogr : 0 < Real.log r := Real.log_pos hr
  cases he : firstCrossing a r top with
  | zero =>
      have hratio : 1 ≤ top / a := (le_div_iff₀ ha).mpr (by simpa using htop)
      have hlog := Real.log_nonneg hratio
      simp only [Nat.cast_zero]
      positivity
  | succ k =>
      have hk : k < firstCrossing a r top := by omega
      have hprev := firstCrossing_minimal a r top ha hr k hk
      have hlog := Real.log_lt_log (mul_pos ha (pow_pos hr0 k)) hprev
      rw [Real.log_mul (ne_of_gt ha) (pow_ne_zero k (ne_of_gt hr0)), Real.log_pow] at hlog
      rw [Real.log_div (ne_of_gt htop0) (ne_of_gt ha)]
      have hdiv : (k : ℝ) ≤ (Real.log top - Real.log a) / Real.log r := by
        apply (le_div_iff₀ hlogr).mpr
        linarith
      push_cast
      linarith

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem graph_n_pos (I : Instance) : 0 < I.graph.n := by
  have := I.source_valid
  omega

private theorem log_size_nonneg (I : Instance) :
    0 ≤ Real.log (max 2 I.graph.n : ℕ) := by
  apply Real.log_nonneg
  have : 1 ≤ max 2 I.graph.n := by omega
  exact_mod_cast this

private theorem log_aspect_size_nonneg (I : Instance) :
    0 ≤ Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I) := by
  apply Real.log_nonneg
  have hN : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by
    exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  nlinarith [one_le_aspectRatio I]

private theorem log_grid_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε / 8 ≤ Real.log (1 + ε / 4) := by
  have hr : 0 < 1 + ε / 4 := by linarith
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
  rw [Real.log_inv] at hh
  have he : ε / 8 ≤ 1 - (1 + ε / 4)⁻¹ := by
    rw [inv_eq_one_div]
    have hi : 1 / (1 + ε / 4) ≤ 1 - ε / 8 := by
      apply (div_le_iff₀ hr).mpr
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hε1)]
    linarith
  linarith

private theorem geometricGuesses_length_bound (I : Instance) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((geometricGuesses I ε).length : ℝ) ≤
      10 * (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) / ε := by
  by_cases he : positiveLengths I = []
  · have hh : (geometricGuesses I ε).length = 0 := by simp [geometricGuesses,he]
    rw [hh]
    have hlog := log_aspect_size_nonneg I
    simp only [Nat.cast_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) hε.le
  · have he' : (positiveLengths I).isEmpty = false := by simpa using he
    have ha := firstPositiveLength_pos I
    have hmax := firstPositiveLength_le_largestLength I he
    have hn : (1 : ℝ) ≤ I.graph.n := by exact_mod_cast graph_n_pos I
    have hnmax : (I.graph.n : ℝ) ≤ (max 2 I.graph.n : ℕ) := by
      exact_mod_cast le_max_right 2 I.graph.n
    have ht : firstPositiveLength I ≤ (I.graph.n : ℝ) * largestLength I := by
      nlinarith [largestLength_nonneg I]
    have hb := firstCrossing_log_bound (firstPositiveLength I) (1 + ε / 4)
      (I.graph.n * largestLength I) ha (by linarith) ht
    have har : aspectRatio I = largestLength I / firstPositiveLength I := by
      simp [aspectRatio,he']
    have hratio : (I.graph.n : ℝ) * largestLength I / firstPositiveLength I =
        I.graph.n * aspectRatio I := by rw [har]; ring
    rw [hratio] at hb
    have harpos : 0 < aspectRatio I := lt_of_lt_of_le (by norm_num) (one_le_aspectRatio I)
    have hlogle : Real.log ((I.graph.n : ℝ) * aspectRatio I) ≤
        Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I) := by
      apply Real.log_le_log (mul_pos (by positivity) harpos)
      exact mul_le_mul_of_nonneg_right hnmax harpos.le
    have hlogr : 0 < Real.log (1 + ε / 4) := Real.log_pos (by linarith)
    have hlow := log_grid_lower ε hε hε1
    have hdiv : Real.log ((I.graph.n : ℝ) * aspectRatio I) / Real.log (1 + ε / 4) ≤
        8 * Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I) / ε := by
      apply (div_le_iff₀ hlogr).mpr
      have hnonneg := log_aspect_size_nonneg I
      have hm := mul_le_mul_of_nonneg_left hlow
        (show 0 ≤ 8 * Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I) / ε by positivity)
      have hid : 8 * Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I) / ε * (ε / 8) =
          Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I) := by field_simp
      rw [hid] at hm
      exact hlogle.trans hm
    have hsum : (firstCrossing (firstPositiveLength I) (1 + ε / 4)
        (I.graph.n * largestLength I) : ℝ) + 1 ≤
        10 * (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) / ε := by
      have haux : 8 * Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I) / ε + 2 ≤
          10 * (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) / ε := by
        apply (le_div_iff₀ hε).mpr
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hε)]
        nlinarith [log_aspect_size_nonneg I]
      linarith
    simpa [geometricGuesses,he'] using hsum

private theorem outerInputs_length_le_guesses (I : Instance) (ε : ℝ) :
    (outerInputs I ε).length ≤ (geometricGuesses I ε).length := by
  unfold outerInputs
  split
  · exact List.length_filterMap_le _ _
  · simp

private theorem outerInputs_length_bound (I : Instance) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((outerInputs I ε).length : ℝ) ≤
      10 * (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) / ε := by
  exact (Nat.cast_le.mpr (outerInputs_length_le_guesses I ε)).trans
    (geometricGuesses_length_bound I ε hε hε1)

private theorem outerQ_add_one_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((outerQ ε + 1 : ℕ) : ℝ) ≤ 8194 / ε ^ 2 := by
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hsq1 : ε ^ 2 ≤ 1 := by nlinarith
  have hq := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 512 / (ε / 4) ^ 2 by positivity)
  have hid : (512 : ℝ) / (ε / 4) ^ 2 = 8192 / ε ^ 2 := by ring
  rw [hid] at hq
  have hout : (outerQ ε : ℝ) < 8192 / ε ^ 2 + 1 := by
    simpa only [outerQ, hid] using hq
  apply (le_div_iff₀ hsq).mpr
  have hm := mul_le_mul_of_nonneg_right hout.le hsq.le
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hsq), one_mul] at hm
  push_cast
  nlinarith

private theorem nat_log_size_bound (n : ℕ) (hn : 0 < n) :
    (Nat.log 2 n : ℝ) + 1 ≤ 2 * (1 + Real.log (max 2 n : ℕ)) := by
  have hb := Real.natLog_le_logb n 2
  simp only [Real.logb, Nat.cast_ofNat] at hb
  have hlogtwo : (1 : ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at hh
    norm_num at hh
    linarith
  have hp : 0 < Real.log 2 := by positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogle : Real.log (n : ℝ) ≤ Real.log (max 2 n : ℕ) :=
    Real.log_le_log hnpos (by exact_mod_cast le_max_right 2 n)
  have hmul := (le_div_iff₀ hp).mp hb
  have hlower := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (Nat.log 2 n) : (0 : ℝ) ≤ _)
  linarith

private theorem tournament_height_bound (I : Instance) (capacity : ℕ)
    (hc : capacity ≤ 4 * (activeVertices I).length) :
    (Nat.clog 2 capacity : ℝ) + 1 ≤ 6 * (1 + Real.log (max 2 I.graph.n : ℕ)) := by
  have ha := activeVertices_length_le_vertices I
  have hn := Nat.lt_pow_succ_log_self (by decide : 1 < 2) I.graph.n
  have hp : capacity ≤ 2 ^ (Nat.log 2 I.graph.n + 3) := by
    have he : 2 ^ (Nat.log 2 I.graph.n + 3) = 4 * 2 ^ (Nat.log 2 I.graph.n + 1) := by
      rw [show Nat.log 2 I.graph.n + 3 = (Nat.log 2 I.graph.n + 1) + 2 by omega,
        pow_add]
      ring
    rw [he]
    omega
  have hh := Nat.clog_le_of_le_pow hp
  have hh' : (Nat.clog 2 capacity : ℝ) ≤ (Nat.log 2 I.graph.n : ℝ) + 3 := by
    exact_mod_cast hh
  have hb := nat_log_size_bound I.graph.n (graph_n_pos I)
  have hz := log_size_nonneg I
  linarith

private theorem log_size_le_log_aspect_size (I : Instance) :
    Real.log (max 2 I.graph.n : ℕ) ≤
      Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I) := by
  have hn : (0 : ℝ) < (max 2 I.graph.n : ℕ) := by positivity
  apply Real.log_le_log hn
  nlinarith [one_le_aspectRatio I]

private theorem nat_conversion_cost_scale (I : Instance) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((14 * (Nat.log 2 I.graph.n + 1)^2 + 5 : ℕ) : ℝ) ≤
      61 * preprocessingScale I ε := by
  have hb := nat_log_size_bound I.graph.n (graph_n_pos I)
  have hn := log_size_nonneg I
  have hW := log_size_le_log_aspect_size I
  have hsq := pow_le_pow_left₀
    (show (0 : ℝ) ≤ (Nat.log 2 I.graph.n : ℝ) + 1 by positivity) hb 2
  have hprod := mul_le_mul_of_nonneg_left hW (show 0 ≤ 1 + Real.log (max 2 I.graph.n : ℕ) by linarith)
  have hlogprod : 1 ≤ (1 + Real.log (max 2 I.graph.n : ℕ)) *
      (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) := by nlinarith
  have hcost : (14 * ((Nat.log 2 I.graph.n : ℝ)+1)^2+5) ≤
      61 * ((1 + Real.log (max 2 I.graph.n : ℕ)) *
        (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I))) := by nlinarith
  have hm : (1 : ℝ) ≤ (max 1 I.graph.edges.length : ℕ) := by
    exact_mod_cast le_max_left 1 I.graph.edges.length
  have he9 : 0 < ε ^ 9 := pow_pos hε 9
  have he91 : ε ^ 9 ≤ 1 := pow_le_one₀ hε.le hε1
  have hscale : (1 + Real.log (max 2 I.graph.n : ℕ)) *
      (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) ≤ preprocessingScale I ε := by
    unfold preprocessingScale
    apply (le_div_iff₀ he9).mpr
    have h1 := mul_le_mul_of_nonneg_left he91 (le_trans (by norm_num) hlogprod)
    have h2 := mul_le_mul_of_nonneg_right hm (le_trans (by norm_num) hlogprod)
    nlinarith
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  exact hcost.trans (mul_le_mul_of_nonneg_left hscale (by norm_num))

private theorem preprocessing_count_scale (I : Instance) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((max 1 I.graph.edges.length : ℕ) : ℝ) *
        (1 + Real.log (max 2 I.graph.n : ℕ)) *
        ((geometricGuesses I ε).length + 1 : ℕ) *
        ((outerQ ε + 1 : ℕ) : ℝ) ^ 4 ≤
      (11 * 8194 ^ 4 : ℝ) * preprocessingScale I ε := by
  have hg := geometricGuesses_length_bound I ε hε hε1
  have hq := outerQ_add_one_bound ε hε hε1
  have hlog := log_aspect_size_nonneg I
  have hg1 : (((geometricGuesses I ε).length + 1 : ℕ) : ℝ) ≤
      11 * (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) / ε := by
    have hm := mul_le_mul_of_nonneg_right hg hε.le
    rw [div_mul_cancel₀ _ (ne_of_gt hε)] at hm
    apply (le_div_iff₀ hε).mpr
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith
  have hq4 := pow_le_pow_left₀ (show (0 : ℝ) ≤ ((outerQ ε + 1 : ℕ) : ℝ) by positivity) hq 4
  have hprod := mul_le_mul hg1 hq4
    (show (0 : ℝ) ≤ ((outerQ ε + 1 : ℕ) : ℝ) ^ 4 by positivity)
    (show 0 ≤ 11 * (1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio I)) / ε by positivity)
  have hsize := log_size_nonneg I
  have htotal := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ ((max 1 I.graph.edges.length : ℕ) : ℝ) *
      (1 + Real.log (max 2 I.graph.n : ℕ)) by positivity)
  calc
    _ = ((max 1 I.graph.edges.length : ℕ) : ℝ) *
        (1 + Real.log (max 2 I.graph.n : ℕ)) *
        ((((geometricGuesses I ε).length + 1 : ℕ) : ℝ) *
          ((outerQ ε + 1 : ℕ) : ℝ)^4) := by ring
    _ ≤ _ := htotal
    _ = _ := by unfold preprocessingScale; field_simp <;> ring

private theorem retrieval_instruction_bound (q p ticks edges overhead : ℕ)
    (ht : ticks ≤ 2*q) (he : edges ≤ p) :
    overhead * (q+1) + overhead * ticks + overhead * (q+1)^2 * edges +
        overhead * (p+1) ≤ 5 * overhead * (q+1)^2 * (p+1) := by
  have hsq : q+1 ≤ (q+1)^2 := by nlinarith
  have ht' := Nat.mul_le_mul_left overhead ht
  have he' := Nat.mul_le_mul_left (overhead * (q+1)^2) he
  have hstart := Nat.mul_le_mul_left overhead hsq
  have hone : 1 ≤ (q+1)^2 := by nlinarith
  have hend := Nat.mul_le_mul_left (overhead*(p+1)) hone
  have hcross : overhead * (q+1)^2 ≤ overhead * (q+1)^2 * (p+1) := by
    simpa using Nat.mul_le_mul_left (overhead*(q+1)^2) (show 1 ≤ p+1 by omega)
  nlinarith [Nat.mul_le_mul_left overhead (show q ≤ (q+1)^2 by nlinarith)]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

private theorem active_edge_work_bound (I : Instance) :
    (activeVertices I).length + I.graph.edges.length + 1 ≤ 5 * max 1 I.graph.edges.length := by
  have h := activeVertices_length_le_edges I
  have hm : I.graph.edges.length ≤ max 1 I.graph.edges.length := le_max_right _ _
  have h1 : 1 ≤ max 1 I.graph.edges.length := le_max_left _ _
  omega

private theorem preprocessing_work_scale (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (B C : ℕ) (hB : B ≤ 2 * (activeVertices I).length) :
    ((C * ((activeVertices I).length + I.graph.edges.length + 1) *
      (Nat.clog 2 (2*B)+1) * ((outerInputs I ε).length+1) * (outerQ ε+1)^4 : ℕ) : ℝ) ≤
      ((330*C*8194^4 : ℕ) : ℝ) * preprocessingScale I ε := by
  have hN : (((activeVertices I).length+I.graph.edges.length+1 : ℕ) : ℝ) ≤
      5 * ((max 1 I.graph.edges.length : ℕ) : ℝ) := by
    exact_mod_cast active_edge_work_bound I
  have hH : ((Nat.clog 2 (2*B)+1 : ℕ) : ℝ) ≤
      6 * (1+Real.log (max 2 I.graph.n : ℕ)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using tournament_height_bound I (2*B) (by omega)
  have hG : (((outerInputs I ε).length+1 : ℕ) : ℝ) ≤
      (((geometricGuesses I ε).length+1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (outerInputs_length_le_guesses I ε) 1
  have hL : 0 ≤ 1+Real.log (max 2 I.graph.n : ℕ) := by
    have h := log_size_nonneg I
    linarith
  have hNH := mul_le_mul hN hH (Nat.cast_nonneg _) (by positivity)
  have hNHG := mul_le_mul hNH hG (Nat.cast_nonneg _) (by positivity)
  have hprod := mul_le_mul_of_nonneg_right hNHG
    (show (0 : ℝ) ≤ ((outerQ ε+1 : ℕ) : ℝ)^4 by positivity)
  have hCprod := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg C : (0 : ℝ) ≤ _)
  have hscale := mul_le_mul_of_nonneg_left (preprocessing_count_scale I ε hε hε1)
    (show (0 : ℝ) ≤ 30*C by positivity)
  push_cast only [Nat.cast_mul,Nat.cast_pow] at hCprod ⊢
  calc
    _ ≤ (C : ℝ) * ((5*((max 1 I.graph.edges.length : ℕ) : ℝ) *
        (6*(1+Real.log (max 2 I.graph.n : ℕ))) *
        (((geometricGuesses I ε).length+1 : ℕ) : ℝ)) *
        ((outerQ ε+1 : ℕ) : ℝ)^4) := by nlinarith [hCprod]
    _ = (30*C) * (((max 1 I.graph.edges.length : ℕ) : ℝ) *
        (1+Real.log (max 2 I.graph.n : ℕ)) *
        (((geometricGuesses I ε).length+1 : ℕ) : ℝ) *
        ((outerQ ε+1 : ℕ) : ℝ)^4) := by ring
    _ ≤ _ := hscale
    _ = _ := by push_cast; ring

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess

private theorem standalone_Mission_RAMPreprocessingCost__preprocessing_arithmetic (N m B H q G Lc conv : ℕ)
    (hB : B ≤ 2*N) (hLc : Lc ≤ H) :
    (18*q+conv+55*m+8*G+3*Lc+182) +
      (2*(15*B+(38*H+58)*N+(19*H+46)*m+7)+6) + (54*N+4) +
      (1000*(N+m+1)*(H+1)*(q+1)^4*(G+1)+16) + 1 ≤
      conv+5+10000*(N+m+1)*(H+1)*(G+1)*(q+1)^4 := by
  let p := N+m+1
  let L := H+1
  let Q := (q+1)^4
  let F := p*L*(G+1)*Q
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hQ : 1 ≤ Q := by
    have hpos : 0 < Q := by dsimp [Q]; positivity
    omega
  have hqQ : q ≤ Q := (show q ≤ q+1 by omega).trans
    (le_self_pow (show 1 ≤ q+1 by omega) (by decide : 4 ≠ 0))
  have hPL : p ≤ p*L := by simpa using Nat.mul_le_mul_left p hL
  have hPLG : p*L ≤ p*L*(G+1) := by
    simpa using Nat.mul_le_mul_left (p*L) (show 1 ≤ G+1 by omega)
  have hPLGF : p*L*(G+1) ≤ F := by
    simpa only [F,Nat.mul_one] using Nat.mul_le_mul_left (p*L*(G+1)) hQ
  have hPLF : p*L ≤ F := hPLG.trans hPLGF
  have hpF : p ≤ F := hPL.trans hPLF
  have hNF : N ≤ F := (show N ≤ p by dsimp [p]; omega).trans hpF
  have hmF : m ≤ F := (show m ≤ p by dsimp [p]; omega).trans hpF
  have hF : 1 ≤ F := hp.trans hpF
  have hLF : L ≤ F :=
    (by simpa using Nat.mul_le_mul_right L hp : L ≤ p*L).trans hPLF
  have hHF : H ≤ F := (show H ≤ L by dsimp [L]; omega).trans hLF
  have hGF : G ≤ F := by
    have hpl : 1 ≤ p*L := hp.trans hPL
    have hG : G+1 ≤ p*L*(G+1) := by
      simpa using Nat.mul_le_mul_right (G+1) hpl
    omega
  have hQF : Q ≤ F := by
    have hplg : 1 ≤ p*L*(G+1) := (hp.trans hPL).trans hPLG
    simpa only [F,one_mul] using Nat.mul_le_mul_right Q hplg
  have hqF : q ≤ F := hqQ.trans hQF
  have hHNF : H*N ≤ F := by
    have hmul := Nat.mul_le_mul (show H ≤ L by dsimp [L]; omega)
      (show N ≤ p by dsimp [p]; omega)
    have hHN : H*N ≤ p*L := by simpa only [Nat.mul_comm L p] using hmul
    exact hHN.trans hPLF
  have hHmF : H*m ≤ F := by
    have hmul := Nat.mul_le_mul (show H ≤ L by dsimp [L]; omega)
      (show m ≤ p by dsimp [p]; omega)
    have hHm : H*m ≤ p*L := by simpa only [Nat.mul_comm L p] using hmul
    exact hHm.trans hPLF
  have houter : 1000*(N+m+1)*(H+1)*(q+1)^4*(G+1) = 1000*F := by
    dsimp [F,p,L,Q]; ring
  have hwork : 10000*(N+m+1)*(H+1)*(G+1)*(q+1)^4 = 10000*F := by
    dsimp [F,p,L,Q]; ring
  rw [houter,hwork]
  nlinarith

private theorem preprocessingInstructionBound_coarse (I : Instance) (ε : ℝ) :
    preprocessingInstructionBound I ε ≤
      14*(Nat.log 2 I.graph.n+1)^2+5+
      10000*((activeVertices I).length+I.graph.edges.length+1)*
        (Nat.clog 2 (2*queueCapacity I)+1)*((outerInputs I ε).length+1)*(outerQ ε+1)^4 := by
  have hb := Queue.capacity_bounds (activeVertices I).length (activeVertices_length_pos I)
  have hB : queueCapacity I ≤ 2*(activeVertices I).length := hb.2.le
  have hN : (activeVertices I).length ≤ 2*queueCapacity I := by
    have hh : (activeVertices I).length ≤ queueCapacity I := hb.1
    omega
  exact standalone_Mission_RAMPreprocessingCost__preprocessing_arithmetic _ _ _ _ _ _ _ _ hB (Nat.clog_mono_right 2 hN)

private theorem preprocessingInstructionBound_scale (I : Instance) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (preprocessingInstructionBound I ε : ℝ) ≤ preprocessingConstant * preprocessingScale I ε := by
  have hB : queueCapacity I ≤ 2*(activeVertices I).length :=
    (Queue.capacity_bounds _ (activeVertices_length_pos I)).2.le
  have hbound := preprocessingInstructionBound_coarse I ε
  have hcast : (preprocessingInstructionBound I ε : ℝ) ≤
      ((14*(Nat.log 2 I.graph.n+1)^2+5 : ℕ) : ℝ) +
      ((10000*((activeVertices I).length+I.graph.edges.length+1)*
        (Nat.clog 2 (2*queueCapacity I)+1)*((outerInputs I ε).length+1)*(outerQ ε+1)^4 : ℕ) : ℝ) := by
    exact_mod_cast hbound
  have hconversion := nat_conversion_cost_scale I ε hε hε1
  have hwork := preprocessing_work_scale I ε hε hε1 (queueCapacity I) 10000 hB
  calc
    _ ≤ _ := hcast
    _ ≤ 61*preprocessingScale I ε + ((330*10000*8194^4 : ℕ) : ℝ)*preprocessingScale I ε :=
      add_le_add hconversion hwork
    _ = _ := by norm_num [preprocessingConstant]; ring

private theorem preprocessingConstant_pos : 0 < preprocessingConstant := by
  norm_num [preprocessingConstant]

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem preprocessingCmd_run (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ∃ out n, Run (encodeInput I ε) preprocessingCmd initialStore out n ∧
      (∀ pc, Query.QueryReady I ε (out.at pc)) ∧
      n+1 ≤ preprocessingInstructionBound I ε := by
  obtain ⟨setup,sn,hsetup,hs,hscost⟩ := setupCmd_run I ε hε hε1
  obtain ⟨trees,tn,htrees,hrt,hparents,hworld,hfuture,hzero,hcapacity,htcost⟩ :=
    zeroTrees_ready I ε setup hs
  obtain ⟨out,on,hout,hready,hocost⟩ := afterTreesCmd_run I ε hε hε1 trees hrt hcapacity
    hparents hworld hfuture hzero
  refine ⟨out,sn+(tn+on),Run.seq hsetup (Run.seq htrees hout),hready,?_⟩
  dsimp only [preprocessingInstructionBound]
  unfold Outer.iterationBound at hocost
  omega

private theorem preprocessingProgram_run (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ∃ steps snapshot,
      Execution preprocessingProgram (encodeInput I ε) initialState snapshot steps ∧
      steps ≤ preprocessingInstructionBound I ε ∧ Query.QueryReady I ε snapshot := by
  obtain ⟨out,n,hrun,hready,hbound⟩ := preprocessingCmd_run I ε hε hε1
  obtain ⟨steps,snapshot,hexec,hsteps,hstore⟩ := compiled_preprocessing hrun
  refine ⟨steps,snapshot,hexec,hsteps.trans hbound,?_⟩
  have hm := congrArg Store.nm hstore
  have hrm := congrArg Store.rm hstore
  have hh := hready 0
  simpa only [Query.QueryReady,EncodesOutput,Store.at,Store.ofRAM,←hm,←hrm] using hh

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem RectConstants.after_score (E : RectParams) (input : RAMInput) (s : Store)
    (h : RectConstants E s) : RectConstants E (scoreResult input s) := by
  rcases h with ⟨h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm⟩
  simp only [RectConstants]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [score_nat_frame input s 21 (by decide)] using h21
  · simpa only [score_nat_frame input s 24 (by decide)] using h24
  · simpa only [score_nat_frame input s 25 (by decide)] using h25
  · simpa only [score_nat_frame input s 28 (by decide)] using h28
  · simpa only [score_nat_frame input s 29 (by decide)] using h29
  · simpa only [score_nat_frame input s 31 (by decide)] using h31
  · simpa only [score_real_frame input s 1 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)] using h1
  · simpa only [score_real_frame input s 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)] using h2
  · simpa only [score_real_frame input s 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)] using h3
  · simpa only [score_real_frame input s 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)] using h4
  · exact (score_memory_frame input s).2.trans hm

private theorem score_of_cell (E : RectParams) (input : RAMInput) (s : Store)
    (a b : ℕ) (best : ℕ × ℕ) (h : RectCell E a b best s) :
    (scoreResult input s).rr 5 = E.score (a, b) := by
  rcases h with ⟨hc, _, ha, hb, _, hp⟩
  rcases hc with ⟨h21, _, _, _, _, _, h1, h2, h3, h4, hm⟩
  rw [score_value, hp, hm, h21, ha, hb, h1, h2, h3, h4]
  rfl

private theorem RectCell.after_score (E : RectParams) (input : RAMInput) (s : Store)
    (a b : ℕ) (best : ℕ × ℕ) (h : RectCell E a b best s) :
    RectCell E a b best (scoreResult input s) := by
  rcases h with ⟨hc, hh, ha, hb, hr, hp⟩
  rcases hh with ⟨h18, h19, h49, h6⟩
  refine ⟨hc.after_score E input s, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa only [score_nat_frame input s 18 (by decide)] using h18
  · simpa only [score_nat_frame input s 19 (by decide)] using h19
  · simpa only [score_nat_frame input s 49 (by decide)] using h49
  · simpa only [score_real_frame input s 6 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)] using h6
  · simpa only [score_nat_frame input s 16 (by decide)] using ha
  · simpa only [score_nat_frame input s 17 (by decide)] using hb
  · simpa only [score_nat_frame input s 26 (by decide)] using hr
  · simpa only [score_nat_frame input s 27 (by decide)] using hp

private theorem RectCell.after_choose (E : RectParams) (input : RAMInput) (s : Store)
    (a b : ℕ) (best : ℕ × ℕ) (h : RectCell E a b best s)
    (hscore : s.rr 5 = E.score (a, b)) :
    RectCell E a b (E.choose best (a, b)) (chooseResult input s) := by
  rcases h with ⟨hc, hh, ha, hb, hr, hp⟩
  rcases hc with ⟨h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm⟩
  rcases hh with ⟨h18, h19, h49, h6⟩
  by_cases hlt : E.score (a, b) < E.score best
  · simp [chooseResult, hscore, h6, hlt, RectParams.choose, RectCell, RectConstants,
      RectBest, evalAtoms, chooseAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
      h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm, ha, hb, hr, hp]
  · simp [chooseResult, hscore, h6, hlt, RectParams.choose, RectCell, RectConstants,
      RectBest, h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm,
      h18, h19, h49, ha, hb, hr, hp]

private theorem RectCell.after_advance (E : RectParams) (input : RAMInput) (s : Store)
    (a b : ℕ) (best : ℕ × ℕ) (h : RectCell E a b best s) :
    RectCell E a (b + 1) best (evalAtoms input cellAdvanceAtoms s) := by
  rcases h with ⟨hc, hh, ha, hb, hr, hp⟩
  rcases hc with ⟨h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm⟩
  rcases hh with ⟨h18, h19, h49, h6⟩
  simp [RectCell, RectConstants, RectBest, evalAtoms, cellAdvanceAtoms,
    Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat,
    h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm,
    h18, h19, h49, h6, ha, hb, hr, hp, RectParams.address, Nat.mul_succ, Nat.add_assoc]

private theorem cell_run (E : RectParams) (input : RAMInput) (s : Store)
    (a b : ℕ) (best : ℕ × ℕ) (h : RectCell E a b best s) :
    ∃ t n, Run input cellCmd s t n ∧
      RectCell E a (b + 1) (E.choose best (a, b)) t ∧ n ≤ 21 := by
  let u := scoreResult input s
  let v := chooseResult input u
  let t := evalAtoms input cellAdvanceAtoms v
  refine ⟨t, 13 + (chooseCost u + 2),
    Run.seq (score_run input s) (Run.seq (choose_run input u)
      (run_atoms input cellAdvanceAtoms v)), ?_, ?_⟩
  · exact RectCell.after_advance E input v a b _
      (RectCell.after_choose E input u a b best (h.after_score E input s a b best)
        (score_of_cell E input s a b best h))
  · have hc := choose_cost_le u
    omega

@[simp] private theorem rowWinner_zero (E : RectParams) (a : ℕ) (best : ℕ × ℕ) :
    rowWinner E a 0 best = best := rfl

private theorem rowWinner_succ (E : RectParams) (a b : ℕ) (best : ℕ × ℕ) :
    rowWinner E a (b + 1) best = E.choose (rowWinner E a b best) (a, b) := by
  simp [rowWinner, List.range_succ, List.foldl_append]

private theorem row_loop_run (E : RectParams) (input : RAMInput) (s : Store)
    (a : ℕ) (best : ℕ × ℕ) (h : RectCell E a 0 best s) :
    ∃ t n, Run input (.loop (.nat .lt 17 29) cellCmd) s t n ∧
      RectCell E a E.cols (rowWinner E a E.cols best) t ∧ n ≤ 23 * E.cols + 1 := by
  suffices hh : ∃ t n, Run input (.loop (.nat .lt 17 29) cellCmd) s t n ∧
      RectCell E a E.cols (rowWinner E a E.cols best) t ∧
      n ≤ (21 + 2) * (E.cols - 0) + 1 by simpa using hh
  refine run_bounded_loop input (.nat .lt 17 29) cellCmd E.cols 21
    (fun b s => RectCell E a b (rowWinner E a b best) s) ?_ ?_ 0 s (by omega) ?_
  · intro b u _ hu
    rcases hu with ⟨hc, _, _, hb, _, _⟩
    have hcols := hc.2.2.2.2.1
    simp [Guard.eval, natTest, hb, hcols]
  · intro b u hb hu
    obtain ⟨t, n, hn, ht, hcost⟩ := cell_run E input u a b _ hu
    exact ⟨t, n, hn, by simpa only [rowWinner_succ] using ht, hcost⟩
  · simpa using h

private theorem row_setup (E : RectParams) (input : RAMInput) (s : Store)
    (a : ℕ) (best : ℕ × ℕ) (h : RectRow E a best s) :
    RectCell E a 0 best (evalAtoms input rowSetupAtoms s) := by
  rcases h with ⟨hc, hh, ha, hr⟩
  rcases hc with ⟨h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm⟩
  rcases hh with ⟨h18, h19, h49, h6⟩
  simp [RectCell, RectConstants, RectBest, evalAtoms, rowSetupAtoms,
    Atom.eval, Store.ofRAM, ramStep, Store.at,
    h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm,
    h18, h19, h49, h6, ha, hr, RectParams.address]

private theorem row_advance (E : RectParams) (input : RAMInput) (s : Store)
    (a b : ℕ) (best : ℕ × ℕ) (h : RectCell E a b best s) :
    RectRow E (a + 1) best (evalAtoms input rowAdvanceAtoms s) := by
  rcases h with ⟨hc, hh, ha, _, hr, _⟩
  rcases hc with ⟨h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm⟩
  rcases hh with ⟨h18, h19, h49, h6⟩
  simp [RectRow, RectConstants, RectBest, evalAtoms, rowAdvanceAtoms,
    Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat,
    h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm,
    h18, h19, h49, h6, ha, hr, Nat.mul_succ, Nat.add_assoc]

private theorem row_run (E : RectParams) (input : RAMInput) (s : Store)
    (a : ℕ) (best : ℕ × ℕ) (h : RectRow E a best s) :
    ∃ t n, Run input rowCmd s t n ∧
      RectRow E (a + 1) (rowWinner E a E.cols best) t ∧ n ≤ 23 * E.cols + 5 := by
  let u := evalAtoms input rowSetupAtoms s
  obtain ⟨v, n, hn, hv, hbound⟩ := row_loop_run E input u a best (row_setup E input s a best h)
  refine ⟨evalAtoms input rowAdvanceAtoms v, 2 + (n + 2),
    Run.seq (run_atoms input rowSetupAtoms s)
      (Run.seq hn (run_atoms input rowAdvanceAtoms v)),
    row_advance E input v a E.cols _ hv, ?_⟩
  omega

@[simp] private theorem rowsWinner_zero (E : RectParams) (best : ℕ × ℕ) :
    rowsWinner E 0 best = best := rfl

private theorem rowsWinner_succ (E : RectParams) (a : ℕ) (best : ℕ × ℕ) :
    rowsWinner E (a + 1) best = rowWinner E a E.cols (rowsWinner E a best) := by
  simp [rowsWinner, List.range_succ, List.foldl_append]

private theorem rows_loop_run (E : RectParams) (input : RAMInput) (s : Store)
    (best : ℕ × ℕ) (h : RectRow E 0 best s) :
    ∃ t n, Run input (.loop (.nat .lt 16 28) rowCmd) s t n ∧
      RectRow E E.rows (rowsWinner E E.rows best) t ∧
      n ≤ (23 * E.cols + 7) * E.rows + 1 := by
  suffices hh : ∃ t n, Run input (.loop (.nat .lt 16 28) rowCmd) s t n ∧
      RectRow E E.rows (rowsWinner E E.rows best) t ∧
      n ≤ (23 * E.cols + 5 + 2) * (E.rows - 0) + 1 by
    simpa [Nat.add_assoc] using hh
  refine run_bounded_loop input (.nat .lt 16 28) rowCmd E.rows (23 * E.cols + 5)
    (fun a s => RectRow E a (rowsWinner E a best) s) ?_ ?_ 0 s (by omega) ?_
  · intro a u _ hu
    rcases hu with ⟨hc, _, ha, _⟩
    have hrows := hc.2.2.2.1
    simp [Guard.eval, natTest, ha, hrows]
  · intro a u ha hu
    obtain ⟨t, n, hn, ht, hcost⟩ := row_run E input u a _ hu
    exact ⟨t, n, hn, by simpa only [rowsWinner_succ] using ht, hcost⟩
  · simpa using h

private theorem rectangle_setup (E : RectParams) (input : RAMInput) (s : Store)
    (h : RectConstants E s) (hbase : s.nr 27 = E.base) :
    RectRow E 0 (0, 0)
      (evalAtoms input chooseAtoms (scoreResult input (evalAtoms input rectangleSetupAtoms s))) := by
  rcases h with ⟨h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm⟩
  simp [RectRow, RectConstants, RectBest, evalAtoms, rectangleSetupAtoms, chooseAtoms,
    scoreResult, scoreAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, evalReal,
    h21, h24, h25, h28, h29, h31, h1, h2, h3, h4, hm, hbase,
    RectParams.address, RectParams.score]

private theorem rectangle_run (E : RectParams) (input : RAMInput) (s : Store)
    (h : RectConstants E s) (hbase : s.nr 27 = E.base) :
    ∃ t n, Run input rectangleCmd s t n ∧
      RectBest E (rowsWinner E E.rows (0, 0)) t ∧
      n ≤ (23 * E.cols + 7) * E.rows + 21 := by
  let u := evalAtoms input rectangleSetupAtoms s
  let v := scoreResult input u
  let w := evalAtoms input chooseAtoms v
  obtain ⟨t, n, hn, ht, hb⟩ := rows_loop_run E input w (0, 0) (rectangle_setup E input s h hbase)
  refine ⟨t, 3 + (13 + (4 + n)),
    Run.seq (run_atoms input rectangleSetupAtoms s)
      (Run.seq (score_run input u) (Run.seq (run_atoms input chooseAtoms v) hn)), ht.2.1, ?_⟩
  omega

private theorem rowsWinner_eq_fold (E : RectParams) (best : ℕ × ℕ) :
    rowsWinner E E.rows best = (rectanglePairs E.rows E.cols).foldl E.choose best := by
  simp [rowsWinner, rowWinner, rectanglePairs, List.foldl_flatMap, List.foldl_map]

private theorem rectanglePairs_head (rows cols : ℕ) (hr : 0 < rows) (hc : 0 < cols) :
    (rectanglePairs rows cols).headD (0, 0) = (0, 0) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rows ≠ 0)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : cols ≠ 0)
  simp [rectanglePairs, List.range_succ_eq_map]

private theorem rowsWinner_eq_firstMin (E : RectParams) (hr : 0 < E.rows) (hc : 0 < E.cols) :
    rowsWinner E E.rows (0, 0) = firstMin E.score (rectanglePairs E.rows E.cols) (0, 0) := by
  rw [rowsWinner_eq_fold]
  simp only [firstMin, rectanglePairs_head E.rows E.cols hr hc, RectParams.choose]
  rfl

private theorem mem_rectanglePairs (rows cols a b : ℕ) :
    (a, b) ∈ rectanglePairs rows cols ↔ a < rows ∧ b < cols := by
  simp [rectanglePairs]

private theorem rectanglePairs_ne_nil (rows cols : ℕ) (hr : 0 < rows) (hc : 0 < cols) :
    rectanglePairs rows cols ≠ [] := by
  have hm : (0, 0) ∈ rectanglePairs rows cols := (mem_rectanglePairs rows cols 0 0).2 ⟨hr, hc⟩
  intro h
  simpa [h] using hm

private theorem rectangle_run_firstMin (E : RectParams) (input : RAMInput) (s : Store)
    (h : RectConstants E s) (hbase : s.nr 27 = E.base)
    (hr : 0 < E.rows) (hc : 0 < E.cols) :
    ∃ t n best, Run input rectangleCmd s t n ∧
      best = firstMin E.score (rectanglePairs E.rows E.cols) (0, 0) ∧
      RectBest E best t ∧ best.1 < E.rows ∧ best.2 < E.cols ∧
      n ≤ (23 * E.cols + 7) * E.rows + 21 := by
  obtain ⟨t, n, hn, ht, hcost⟩ := rectangle_run E input s h hbase
  refine ⟨t, n, rowsWinner E E.rows (0, 0), hn, rowsWinner_eq_firstMin E hr hc,
    ht, ?_, ?_, hcost⟩
  all_goals
    have hm := firstMin_mem E.score (rectanglePairs E.rows E.cols) (0, 0)
      (rectanglePairs_ne_nil E.rows E.cols hr hc)
    rw [← rowsWinner_eq_firstMin E hr hc] at hm
    have hb := (mem_rectanglePairs E.rows E.cols _ _).1 hm
    first | exact hb.1 | exact hb.2

private theorem rectangle_cost_le (q rows cols : ℕ) (hr : rows ≤ q) (hc : cols ≤ q) :
    (23 * cols + 7) * rows + 21 ≤ 51 * (q + 1) ^ 2 := by
  have hm := Nat.mul_le_mul hr hc
  nlinarith

private theorem firstMin_congr_on {α : Type} (f g : α → ℝ) (xs : List α) (fallback : α)
    (hne : xs ≠ []) (h : ∀ x ∈ xs, f x = g x) :
    firstMin f xs fallback = firstMin g xs fallback := by
  have hf : ∀ ys : List α, ∀ start, start ∈ xs → (∀ y ∈ ys, y ∈ xs) →
      ys.foldl (fun a b => if f b < f a then b else a) start =
      ys.foldl (fun a b => if g b < g a then b else a) start := by
    intro ys
    induction ys with
    | nil => intros; rfl
    | cons y ys ih =>
        intro start hs hys
        simp only [List.foldl_cons]
        have hy := hys y (by simp)
        rw [h y hy, h start hs]
        apply ih
        · split_ifs <;> assumption
        · intro z hz
          exact hys z (by simp [hz])
  apply hf xs (xs.headD fallback)
  · cases xs with
    | nil => contradiction
    | cons x xs => simp
  · intro y hy
    exact hy

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace RSP.Barrier

private theorem log_gap_lower {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (1 - z) ^ 2 / 2 ≤ Real.log z + 1 / z - 1 := by
  let f : ℝ → ℝ := fun x => Real.log x + 1 / x - 1 - (1 - x) ^ 2 / 2
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt f (1 / x - 1 / x ^ 2 + (1 - x)) x := by
    have hlog := Real.hasDerivAt_log (ne_of_gt hx)
    have hinv := (hasDerivAt_id x).inv (ne_of_gt hx)
    have hsq := (((hasDerivAt_id x).const_sub 1).pow 2).div_const 2
    convert! ((hlog.add hinv).sub_const 1).sub hsq using 1
    · ext y
      simp [f, one_div]
    · simp [one_div]
      ring
  have hanti : AntitoneOn f (Set.Icc z 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc z 1)
    · intro x hx
      exact (hd x (lt_of_lt_of_le hz hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (lt_of_lt_of_le hz (interior_subset hx).1)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc z 1 := interior_subset hx
      have hx0 : 0 < x := lt_of_lt_of_le hz hx'.1
      rw [(hd x hx0).deriv]
      have heq : (1 / x - 1 / x ^ 2 + (1 - x)) * x ^ 2 =
          -(1 - x) * (1 - x ^ 2) := by
        field_simp [ne_of_gt hx0]
        <;> ring
      have hsq : x ^ 2 ≤ 1 := by nlinarith [hx'.2]
      have hp := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hx'.2))
        (sub_nonneg.mpr hsq)
      rw [← heq] at hp
      nlinarith [sq_pos_of_pos hx0]
  have h := hanti ⟨le_rfl, hz1⟩ ⟨hz1, le_rfl⟩ hz1
  simp only [f, Real.log_one, div_one, sub_self, zero_pow (by decide : 2 ≠ 0),
    zero_div, add_zero, sub_zero] at h
  linarith

private theorem eight_le_clock_barrier {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (q : ℕ) (hq : 512 / δ ^ 2 ≤ (q : ℝ)) :
    let z := (1 + δ / 2) / (1 + δ)
    8 ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) := by
  let z := (1 + δ / 2) / (1 + δ)
  change 8 ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z)
  have hd : 0 < 1 + δ := by linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ hd).mpr
    linarith
  have hgap : δ / 4 ≤ 1 - z := by
    have heq : 1 - z = (δ / 2) / (1 + δ) := by
      dsimp [z]
      field_simp [ne_of_gt hd]
      <;> ring
    rw [heq]
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (le_of_lt hδ) (sub_nonneg.mpr hδ1)]
  have hlog : δ ^ 2 / 32 ≤ Real.log z + 1 / z - 1 := by
    have h := log_gap_lower hz hz1
    nlinarith [sq_nonneg (1 - z - δ / 4)]
  have hqδ : 512 ≤ (q : ℝ) * δ ^ 2 := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hq
  have hq1r : (1 : ℝ) ≤ q := by
    have hd2 : δ ^ 2 ≤ 1 := by nlinarith
    have hn : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hq1 : 1 ≤ q := by exact_mod_cast hq1r
  have hprod : 16 ≤ (q : ℝ) * (Real.log z + 1 / z - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith
  have hlog0 : Real.log z ≤ 0 := Real.log_nonpos (le_of_lt hz) hz1
  have hexp : 16 ≤ ((q - 1 : ℕ) : ℝ) * Real.log z + (q : ℝ) * (1 - z) / z := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
    have heq : ((q : ℝ) - 1) * Real.log z + (q : ℝ) * (1 - z) / z =
        (q : ℝ) * (Real.log z + 1 / z - 1) - Real.log z := by
      field_simp
      <;> ring
    rw [heq]
    linarith
  calc
    (8 : ℝ) ≤ Real.exp (16 : ℝ) := by nlinarith [Real.add_one_le_exp (16 : ℝ)]
    _ ≤ Real.exp (((q - 1 : ℕ) : ℝ) * Real.log z + (q : ℝ) * (1 - z) / z) :=
      Real.exp_le_exp.mpr hexp
    _ = z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hz]

private theorem one_le_resource_term {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (q : ℕ) (hq : 512 / δ ^ 2 ≤ (q : ℝ)) (i : ℕ) (hi : i < q)
    (a : ℝ) (ha : (q : ℝ) / ((1 + δ / 2) / (1 + δ)) ≤ a) :
    let z := (1 + δ / 2) / (1 + δ)
    1 ≤ z ^ i / (8 * Real.exp (a * (z - 1))) := by
  let z := (1 + δ / 2) / (1 + δ)
  change 1 ≤ z ^ i / (8 * Real.exp (a * (z - 1)))
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ (by linarith : 0 < 1 + δ)).mpr
    linarith
  have hp : z ^ (q - 1) ≤ z ^ i :=
    pow_le_pow_of_le_one (le_of_lt hz) hz1 (by omega)
  have he : (q : ℝ) * (1 - z) / z ≤ a * (1 - z) := by
    simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hz1)
  have hbig : 8 ≤ z ^ i * Real.exp (a * (1 - z)) := by
    calc
      (8 : ℝ) ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) :=
        eight_le_clock_barrier hδ hδ1 q hq
      _ ≤ z ^ i * Real.exp (a * (1 - z)) := by
        exact mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_nonneg _)
          (pow_nonneg (le_of_lt hz) i)
  have heq : Real.exp (a * (1 - z)) = (Real.exp (a * (z - 1)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [heq] at hbig
  apply (le_div_iff₀ (by positivity : 0 < 8 * Real.exp (a * (z - 1)))).mpr
  have h := (le_div_iff₀ (Real.exp_pos (a * (z - 1)))).mp
    (show 8 ≤ z ^ i / Real.exp (a * (z - 1)) by simpa [div_eq_mul_inv] using hbig)
  simpa using h

private theorem k_clock_barrier {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (k q : ℕ) (hk : 1 ≤ k) (hq : 512 * (k : ℝ) / δ ^ 2 ≤ (q : ℝ)) :
    let z := (1 + δ / 2) / (1 + δ)
    8 * (k : ℝ) ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) := by
  let z := (1 + δ / 2) / (1 + δ)
  change 8 * (k : ℝ) ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z)
  have hd : 0 < 1 + δ := by linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ hd).mpr
    linarith
  have hgap : δ / 4 ≤ 1 - z := by
    have heq : 1 - z = (δ / 2) / (1 + δ) := by
      dsimp [z]
      field_simp [ne_of_gt hd]
      <;> ring
    rw [heq]
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (le_of_lt hδ) (sub_nonneg.mpr hδ1)]
  have hlog : δ ^ 2 / 32 ≤ Real.log z + 1 / z - 1 := by
    have h := log_gap_lower hz hz1
    nlinarith [sq_nonneg (1 - z - δ / 4)]
  have hqδ : 512 * (k : ℝ) ≤ (q : ℝ) * δ ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hδ)).mp hq
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hq1r : (1 : ℝ) ≤ q := by
    have hd2 : δ ^ 2 ≤ 1 := by nlinarith
    have hn : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hq1 : 1 ≤ q := by exact_mod_cast hq1r
  have hprod : 16 * (k : ℝ) ≤ (q : ℝ) * (Real.log z + 1 / z - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith
  have hlog0 : Real.log z ≤ 0 := Real.log_nonpos (le_of_lt hz) hz1
  have hexp : 16 * (k : ℝ) ≤
      ((q - 1 : ℕ) : ℝ) * Real.log z + (q : ℝ) * (1 - z) / z := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
    have heq : ((q : ℝ) - 1) * Real.log z + (q : ℝ) * (1 - z) / z =
        (q : ℝ) * (Real.log z + 1 / z - 1) - Real.log z := by
      field_simp
      <;> ring
    rw [heq]
    linarith
  calc
    8 * (k : ℝ) ≤ Real.exp (16 * (k : ℝ)) := by
      nlinarith [Real.add_one_le_exp (16 * (k : ℝ))]
    _ ≤ Real.exp (((q - 1 : ℕ) : ℝ) * Real.log z + (q : ℝ) * (1 - z) / z) :=
      Real.exp_le_exp.mpr hexp
    _ = z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hz]

end RSP.Barrier
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem prod_exp_resource {α : Type*} (xs : List α) (w : α → ℝ) (r z : ℝ) :
    (xs.map (fun x => Real.exp (r * w x * (z - 1)))).prod =
      Real.exp (r * (xs.map w).sum * (z - 1)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih, ← Real.exp_add]
    congr 1
    ring

private theorem lengthPGF_prod (A : InnerInput) (P : List ℕ) :
    ((P.zip P.tail).map (fun e => lengthPGF A e.1 e.2)).prod =
      Real.exp (lengthRate A * pathWeight A.I.length P * (zValue A - 1)) := by
  exact prod_exp_resource (P.zip P.tail) (fun e => (A.I.length e.1 e.2 : ℝ))
    (lengthRate A) (zValue A)

private theorem costPGF_prod (A : InnerInput) (P : List ℕ) :
    ((P.zip P.tail).map (fun e => costPGF A e.1 e.2)).prod =
      Real.exp (costRate A * pathWeight A.I.cost P * (zValue A - 1)) := by
  exact prod_exp_resource (P.zip P.tail) (fun e => (A.I.cost e.1 e.2 : ℝ))
    (costRate A) (zValue A)

private theorem zValue_pos (A : InnerInput) : 0 < zValue A := by
  unfold zValue
  have hδ := A.accuracy_pos
  positivity

private theorem normalized_resource_barrier (A : InnerInput) (B w : ℝ) (hB : 0 < B)
    (hw : (1 + A.δ) * B ≤ w) (i : ℕ) (hi : i < tickLimit A) :
    1 ≤ zValue A ^ i /
      (8 * Real.exp (((tickLimit A : ℝ) / ((1 + A.δ / 2) * B)) * w * (zValue A - 1))) := by
  have hδ := A.accuracy_pos
  have hhalf : 0 < 1 + A.δ / 2 := by linarith
  have hwhole : 0 < 1 + A.δ := by linarith
  have ha : (tickLimit A : ℝ) / zValue A ≤
      (tickLimit A : ℝ) / ((1 + A.δ / 2) * B) * w := by
    calc
      (tickLimit A : ℝ) / zValue A =
          (tickLimit A : ℝ) / ((1 + A.δ / 2) * B) * ((1 + A.δ) * B) := by
        unfold zValue
        field_simp
        <;> ring
      _ ≤ (tickLimit A : ℝ) / ((1 + A.δ / 2) * B) * w :=
        mul_le_mul_of_nonneg_left hw (by positivity)
  exact RSP.Barrier.one_le_resource_term A.accuracy_pos A.accuracy_lt_one.le
    (tickLimit A) (Nat.le_ceil _) i hi
    ((tickLimit A : ℝ) / ((1 + A.δ / 2) * B) * w) ha

private theorem potential_detects_violation_of_nonneg (A : InnerInput) (S : RetrievalState)
    (hD : 0 ≤ dpValue A (buildTable A) S.front S.i S.j) :
    (pathWeight A.I.length S.path > (1 + A.δ) * A.L → S.i < tickLimit A →
      1 ≤ potential A S) ∧
    (pathWeight A.I.cost S.path > (1 + A.δ) * A.I.budget → S.j < tickLimit A →
      1 ≤ potential A S) := by
  have hz := zValue_pos A
  unfold potential
  rw [lengthPGF_prod, costPGF_prod]
  constructor
  · intro hw hi
    have h := normalized_resource_barrier A A.L (pathWeight A.I.length S.path)
      A.length_pos hw.le S.i hi
    change 1 ≤ zValue A ^ S.i /
      (8 * Real.exp (lengthRate A * pathWeight A.I.length S.path * (zValue A - 1))) at h
    have hnonneg : 0 ≤ zValue A ^ S.j /
        (8 * Real.exp (costRate A * pathWeight A.I.cost S.path * (zValue A - 1))) := by
      positivity
    linarith
  · intro hw hj
    have h := normalized_resource_barrier A A.I.budget (pathWeight A.I.cost S.path)
      A.budget_pos hw.le S.j hj
    change 1 ≤ zValue A ^ S.j /
      (8 * Real.exp (costRate A * pathWeight A.I.cost S.path * (zValue A - 1))) at h
    have hnonneg : 0 ≤ zValue A ^ S.i /
        (8 * Real.exp (lengthRate A * pathWeight A.I.length S.path * (zValue A - 1))) := by
      positivity
    linarith

private theorem potential_detects_violation (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (S : RetrievalState) (houtput : retrieve A t = some S) :
    (pathWeight A.I.length S.path > (1 + A.δ) * A.L → S.i < tickLimit A →
      1 ≤ potential A S) ∧
    (pathWeight A.I.cost S.path > (1 + A.δ) * A.I.budget → S.j < tickLimit A →
      1 ≤ potential A S) := by
  exact potential_detects_violation_of_nonneg A S
    (dpValue_buildTable_nonneg A S.front S.i S.j)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace RSP

private theorem retrievalRank_decreases_same_layer
    (cap width spent rank rank' : ℕ) (h : rank' < rank) :
    retrievalRank cap width spent rank' < retrievalRank cap width spent rank := by
  unfold retrievalRank
  omega

private theorem retrievalRank_decreases_tick
    (cap width spent spent' rank rank' : ℕ)
    (hs : spent < spent') (hs' : spent' ≤ cap) (hr' : rank' < width) :
    retrievalRank cap width spent' rank' < retrievalRank cap width spent rank := by
  have hsub : cap - spent' + 1 ≤ cap - spent := by omega
  have hmul := Nat.mul_le_mul_right width hsub
  simp only [Nat.add_mul, Nat.one_mul] at hmul
  unfold retrievalRank
  omega

private theorem steps_le_initial_rank (r : ℕ → ℕ) (steps : ℕ)
    (h : ∀ i < steps, r (i + 1) < r i) : steps ≤ r 0 := by
  have hstrong : ∀ n ≤ steps, r n + n ≤ r 0 := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hn' : n < steps := by omega
        have hp := ih (by omega)
        have hd := h n hn'
        omega
  have := hstrong steps le_rfl
  omega

private theorem total_ticks_le (k q : ℕ) (c : Fin k → ℕ)
    (hc : ∀ a, c a < q) : ∑ a, c a ≤ k * (q - 1) := by
  calc
    ∑ a, c a ≤ ∑ _a : Fin k, (q - 1) :=
      Finset.sum_le_sum (fun a _ => by have := hc a; omega)
    _ = k * (q - 1) := by simp

end RSP
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem retrievalStart_consistent (A : InnerInput) (t : ℕ) :
    RetrievalConsistent A (retrievalStart t) := by
  simp [RetrievalConsistent, retrievalStart]

private theorem potential_eq_stored (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) :
    potential A S = dpValue A (buildTable A) S.front S.i S.j + S.Hlength + S.Hcost := by
  rw [potential, hS.2.1, hS.2.2]

private theorem lengthPGF_pos (A : InnerInput) (u v : ℕ) : 0 < lengthPGF A u v :=
  Real.exp_pos _

private theorem costPGF_pos (A : InnerInput) (u v : ℕ) : 0 < costPGF A u v :=
  Real.exp_pos _

private theorem pathProduct_cons (F : ℕ → ℕ → ℝ) (P : List ℕ) (u v : ℕ)
    (hP : P.head? = some v) :
    (((u :: P).zip (u :: P).tail).map (fun e => F e.1 e.2)).prod =
      F u v * ((P.zip P.tail).map (fun e => F e.1 e.2)).prod := by
  cases P with
  | nil => simp at hP
  | cons a P =>
      have ha : a = v := by simpa using hP
      subst a
      simp

private theorem consistent_aux_pos (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) : 0 < S.Hlength ∧ 0 < S.Hcost := by
  rw [hS.2.1, hS.2.2, lengthPGF_prod, costPGF_prod]
  have hz := zValue_pos A
  constructor <;> positivity

private theorem crossEdge_consistent (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) (u a b : ℕ) :
    RetrievalConsistent A (crossEdge A S u a b) := by
  unfold RetrievalConsistent crossEdge
  simp only [List.head?_cons, true_and]
  rw [pathProduct_cons _ _ _ _ hS.1, pathProduct_cons _ _ _ _ hS.1]
  rw [hS.2.1, hS.2.2]
  constructor <;> simp only [pow_add, div_eq_mul_inv, mul_inv_rev] <;> ring

private theorem lengthTick_consistent (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) :
    RetrievalConsistent A { S with i := S.i + 1, Hlength := zValue A * S.Hlength } := by
  refine ⟨hS.1, ?_, hS.2.2⟩
  change zValue A * S.Hlength = zValue A ^ (S.i + 1) / _
  rw [hS.2.1, pow_succ]
  ring

private theorem costTick_consistent (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) :
    RetrievalConsistent A { S with j := S.j + 1, Hcost := zValue A * S.Hcost } := by
  refine ⟨hS.1, hS.2.1, ?_⟩
  change zValue A * S.Hcost = zValue A ^ (S.j + 1) / _
  rw [hS.2.2, pow_succ]
  ring

private theorem retrievalScore_eq_cross_potential (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) (u a b : ℕ) :
    retrievalScore A S u (a,b) = potential A (crossEdge A S u a b) := by
  rw [potential_eq_stored _ _ (crossEdge_consistent A S hS u a b)]
  rfl

private theorem mem_incrementPairs (A : InnerInput) (S : RetrievalState) (a b : ℕ) :
    (a,b) ∈ incrementPairs A S ↔ a < tickLimit A - S.i ∧ b < tickLimit A - S.j := by
  simp [incrementPairs]

private theorem incrementPairs_ne_nil (A : InnerInput) (S : RetrievalState)
    (hi : S.i < tickLimit A) (hj : S.j < tickLimit A) :
    incrementPairs A S ≠ [] := by
  have hz : (0,0) ∈ incrementPairs A S := by
    rw [mem_incrementPairs]
    omega
  intro h
  simp [h] at hz

private theorem incrementPairs_unsaturated (A : InnerInput) (S : RetrievalState) (a b : ℕ)
    (h : (a,b) ∈ incrementPairs A S) :
    S.i + a < tickLimit A ∧ S.j + b < tickLimit A := by
  rw [mem_incrementPairs] at h
  omega

private theorem retrievalStep_preserves_consistency (A : InnerInput) (S U : RetrievalState)
    (hS : RetrievalConsistent A S) (hstep : retrievalStep A S = some U) :
    RetrievalConsistent A U := by
  unfold retrievalStep at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · cases hstep
      exact lengthTick_consistent A S hS
    · cases hstep
      exact costTick_consistent A S hS
    · split at hstep
      · contradiction
      · cases hstep
        exact crossEdge_consistent A S hS _ _ _

private theorem retrievalRun_preserves_consistency (A : InnerInput) (fuel : ℕ)
    (S U : RetrievalState) (hS : RetrievalConsistent A S)
    (hrun : retrievalRun A fuel S = some U) : RetrievalConsistent A U := by
  induction fuel generalizing S U with
  | zero =>
      unfold retrievalRun at hrun
      split at hrun
      · cases hrun; exact hS
      · contradiction
  | succ fuel ih =>
      unfold retrievalRun at hrun
      split at hrun
      · cases hrun; exact hS
      · obtain ⟨T, hstep, hrun⟩ := Option.bind_eq_some_iff.mp hrun
        exact ih T U (retrievalStep_preserves_consistency A S T hS hstep) hrun

private theorem retrievalRun_terminal (A : InnerInput) (fuel : ℕ) (S U : RetrievalState)
    (hrun : retrievalRun A fuel S = some U) :
    U.front = A.I.source ∧ U.i < tickLimit A ∧ U.j < tickLimit A := by
  induction fuel generalizing S U with
  | zero =>
      unfold retrievalRun at hrun
      split at hrun
      · cases hrun; assumption
      · contradiction
  | succ fuel ih =>
      unfold retrievalRun at hrun
      split at hrun
      · cases hrun; assumption
      · obtain ⟨T, _, hrun⟩ := Option.bind_eq_some_iff.mp hrun
        exact ih T U hrun

private theorem retrieve_consistent (A : InnerInput) (t : ℕ) (U : RetrievalState)
    (h : retrieve A t = some U) : RetrievalConsistent A U :=
  retrievalRun_preserves_consistency A _ _ U (retrievalStart_consistent A t) h

private theorem retrieve_terminal (A : InnerInput) (t : ℕ) (U : RetrievalState)
    (h : retrieve A t = some U) :
    U.front = A.I.source ∧ U.i < tickLimit A ∧ U.j < tickLimit A :=
  retrievalRun_terminal A _ _ U h

private theorem isPath_prepend (G : Digraph) (u v t : ℕ) (P : List ℕ)
    (hP : IsPath G v t P) (he : (u,v) ∈ G.edges) : IsPath G u t (u :: P) := by
  refine ⟨rfl, ?_, ?_⟩
  · have hn : P ≠ [] := by intro h; simp [IsPath, h] at hP
    simpa [List.getLast?_cons_of_ne_nil hn] using hP.2.1
  · apply hP.2.2.cons
    intro w hw
    rw [hP.1] at hw
    have hwv : w = v := by symm; simpa using hw
    simpa [hwv] using he

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal BigOperators
namespace NearLinearRSP.TwoResources

private theorem poissonCountMass_weighted_sum_le (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z)
    (n : ℕ) :
    (∑ a ∈ Finset.range n, ActuarialValuation.poissonCountMass r a * z ^ a) ≤
      Real.exp (r * (z - 1)) := by
  exact sum_le_hasSum (Finset.range n)
    (fun a _ => mul_nonneg (RSP.PoissonBridge.poissonCountMass_nonneg r hr a)
      (pow_nonneg hz a))
    (RSP.Tails.poisson_pgf_hasSum ⟨r, hr⟩ z)

private theorem rectangle_lengthMoment_le (A : InnerInput) (u v na nb : ℕ) :
    (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb,
      edgeMass A u v a b * zValue A ^ a) ≤ lengthPGF A u v := by
  have hl : 0 ≤ lengthRate A * A.I.length u v :=
    mul_nonneg (RSP.PoissonBridge.lengthRate_nonneg A) (A.I.length u v).coe_nonneg
  have hc : 0 ≤ costRate A * A.I.cost u v :=
    mul_nonneg (RSP.PoissonBridge.costRate_nonneg A) (A.I.cost u v).coe_nonneg
  have hlen := poissonCountMass_weighted_sum_le _ _ hl (zValue_pos A).le na
  have hcost := RSP.PoissonBridge.poissonCountMass_sum_le_one _ hc nb
  have hc0 : 0 ≤ ∑ b ∈ Finset.range nb,
      ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b :=
    Finset.sum_nonneg (fun b _ => RSP.PoissonBridge.poissonCountMass_nonneg _ hc b)
  have hprod := mul_le_mul hlen hcost hc0 (lengthPGF_pos A u v).le
  have heq : (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb,
      edgeMass A u v a b * zValue A ^ a) =
      (∑ a ∈ Finset.range na,
        ActuarialValuation.poissonCountMass (lengthRate A * A.I.length u v) a * zValue A ^ a) *
      (∑ b ∈ Finset.range nb,
        ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    unfold edgeMass
    ring
  rw [heq]
  simpa [lengthPGF] using hprod

private theorem rectangle_costMoment_le (A : InnerInput) (u v na nb : ℕ) :
    (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb,
      edgeMass A u v a b * zValue A ^ b) ≤ costPGF A u v := by
  have hl : 0 ≤ lengthRate A * A.I.length u v :=
    mul_nonneg (RSP.PoissonBridge.lengthRate_nonneg A) (A.I.length u v).coe_nonneg
  have hc : 0 ≤ costRate A * A.I.cost u v :=
    mul_nonneg (RSP.PoissonBridge.costRate_nonneg A) (A.I.cost u v).coe_nonneg
  have hlen := RSP.PoissonBridge.poissonCountMass_sum_le_one _ hl na
  have hcost := poissonCountMass_weighted_sum_le _ _ hc (zValue_pos A).le nb
  have hc0 : 0 ≤ ∑ b ∈ Finset.range nb,
      ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b * zValue A ^ b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg
      (RSP.PoissonBridge.poissonCountMass_nonneg _ hc b) (pow_nonneg (zValue_pos A).le b))
  have hprod := mul_le_mul hlen hcost hc0 zero_le_one
  have heq : (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb,
      edgeMass A u v a b * zValue A ^ b) =
      (∑ a ∈ Finset.range na,
        ActuarialValuation.poissonCountMass (lengthRate A * A.I.length u v) a) *
      (∑ b ∈ Finset.range nb,
        ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b * zValue A ^ b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    unfold edgeMass
    ring
  rw [heq]
  simpa [costPGF] using hprod

private theorem exists_below_of_weighted_lt {α : Type*} (s : Finset α) (p f : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a)
    (h : ∑ a ∈ s, p a * f a < ∑ a ∈ s, p a) :
    ∃ a ∈ s, f a < 1 := by
  by_contra hn
  push Not at hn
  have hge : (∑ a ∈ s, p a) ≤ ∑ a ∈ s, p a * f a := by
    apply Finset.sum_le_sum
    intro a ha
    simpa using mul_le_mul_of_nonneg_left (hn a ha) (hp a ha)
  linarith

private theorem potential_lt_one_unsaturated (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) (hΦ : potential A S < 1) :
    S.i < tickLimit A ∧ S.j < tickLimit A := by
  have hH := consistent_aux_pos A S hS
  rw [potential_eq_stored A S hS] at hΦ
  by_contra h
  push Not at h
  have hs : tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j := by omega
  have hd : dpValue A (buildTable A) S.front S.i S.j = 1 := by simp [dpValue, hs]
  rw [hd] at hΦ
  linarith

private theorem edge_has_score_below_one_of_bellman (A : InnerInput) (S : RetrievalState)
    (u : ℕ) (hS : RetrievalConsistent A S) (hΦ : potential A S < 1)
    (hBellman : dpValue A (buildTable A) S.front S.i S.j =
      edgeExpectation A (buildTable A) u S.front S.i S.j) :
    ∃ ab ∈ incrementPairs A S, retrievalScore A S u ab < 1 := by
  have hs := potential_lt_one_unsaturated A S hS hΦ
  have hH := consistent_aux_pos A S hS
  have hl := rectangle_lengthMoment_le A u S.front (tickLimit A - S.i) (tickLimit A - S.j)
  have hc := rectangle_costMoment_le A u S.front (tickLimit A - S.i) (tickLimit A - S.j)
  have hl' := mul_le_mul_of_nonneg_right hl (div_nonneg hH.1.le (lengthPGF_pos A u S.front).le)
  have hc' := mul_le_mul_of_nonneg_right hc (div_nonneg hH.2.le (costPGF_pos A u S.front).le)
  have hlbound : (∑ a ∈ Finset.range (tickLimit A - S.i),
      ∑ b ∈ Finset.range (tickLimit A - S.j),
        edgeMass A u S.front a b * (zValue A ^ a * S.Hlength / lengthPGF A u S.front)) ≤
        S.Hlength := by
    calc
      _ = (∑ a ∈ Finset.range (tickLimit A - S.i),
        ∑ b ∈ Finset.range (tickLimit A - S.j), edgeMass A u S.front a b * zValue A ^ a) *
          (S.Hlength / lengthPGF A u S.front) := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ ≤ lengthPGF A u S.front * (S.Hlength / lengthPGF A u S.front) := hl'
      _ = S.Hlength := by field_simp [ne_of_gt (lengthPGF_pos A u S.front)]
  have hcbound : (∑ a ∈ Finset.range (tickLimit A - S.i),
      ∑ b ∈ Finset.range (tickLimit A - S.j),
        edgeMass A u S.front a b * (zValue A ^ b * S.Hcost / costPGF A u S.front)) ≤
        S.Hcost := by
    calc
      _ = (∑ a ∈ Finset.range (tickLimit A - S.i),
        ∑ b ∈ Finset.range (tickLimit A - S.j), edgeMass A u S.front a b * zValue A ^ b) *
          (S.Hcost / costPGF A u S.front) := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ ≤ costPGF A u S.front * (S.Hcost / costPGF A u S.front) := hc'
      _ = S.Hcost := by field_simp [ne_of_gt (costPGF_pos A u S.front)]
  have hn : ¬ (tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j) := by omega
  rw [edgeExpectation, if_neg hn] at hBellman
  rw [potential_eq_stored A S hS] at hΦ
  have hscore : (∑ a ∈ Finset.range (tickLimit A - S.i),
      ∑ b ∈ Finset.range (tickLimit A - S.j),
        edgeMass A u S.front a b * retrievalScore A S u (a,b)) <
      ∑ a ∈ Finset.range (tickLimit A - S.i),
        ∑ b ∈ Finset.range (tickLimit A - S.j), edgeMass A u S.front a b := by
    simp only [retrievalScore, mul_add, Finset.sum_add_distrib]
    linarith
  obtain ⟨⟨a,b⟩, hab, hsmall⟩ := exists_below_of_weighted_lt
    ((Finset.range (tickLimit A - S.i)) ×ˢ (Finset.range (tickLimit A - S.j)))
    (fun ab => edgeMass A u S.front ab.1 ab.2) (retrievalScore A S u)
    (fun ab _ => RSP.PoissonBridge.edgeMass_nonneg A u S.front ab.1 ab.2)
    (by simpa [Finset.sum_product] using hscore)
  refine ⟨(a,b), ?_, hsmall⟩
  simpa [mem_incrementPairs] using hab

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem zValue_le_one (A : InnerInput) : zValue A ≤ 1 := by
  have hp : 0 < 1 + A.δ := by linarith [A.accuracy_pos]
  unfold zValue
  apply (div_le_iff₀ hp).mpr
  linarith [A.accuracy_pos]

private theorem retrievalStart_potential_lt_one (A : InnerInput) (t : ℕ)
    (h : accepted A t) : potential A (retrievalStart t) < 1 := by
  have hc := retrievalStart_consistent A t
  rw [potential_eq_stored _ _ hc]
  change dpValue A (buildTable A) t 0 0 + 1 / 8 + 1 / 8 < 1
  change dpValue A (buildTable A) t 0 0 ≤ 1 / 4 at h
  linarith

private theorem lengthTick_potential_le (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S)
    (hEq : dpValue A (buildTable A) S.front S.i S.j =
      dpValue A (buildTable A) S.front (S.i + 1) S.j) :
    potential A { S with i := S.i + 1, Hlength := zValue A * S.Hlength } ≤ potential A S := by
  rw [potential_eq_stored _ _ (lengthTick_consistent A S hS),
    potential_eq_stored _ _ hS]
  change dpValue A (buildTable A) S.front (S.i + 1) S.j +
    zValue A * S.Hlength + S.Hcost ≤
      dpValue A (buildTable A) S.front S.i S.j + S.Hlength + S.Hcost
  rw [hEq]
  have hmul := mul_le_mul_of_nonneg_right (zValue_le_one A) (consistent_aux_pos A S hS).1.le
  linarith

private theorem costTick_potential_le (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S)
    (hEq : dpValue A (buildTable A) S.front S.i S.j =
      dpValue A (buildTable A) S.front S.i (S.j + 1)) :
    potential A { S with j := S.j + 1, Hcost := zValue A * S.Hcost } ≤ potential A S := by
  rw [potential_eq_stored _ _ (costTick_consistent A S hS),
    potential_eq_stored _ _ hS]
  change dpValue A (buildTable A) S.front S.i (S.j + 1) +
    S.Hlength + zValue A * S.Hcost ≤
      dpValue A (buildTable A) S.front S.i S.j + S.Hlength + S.Hcost
  rw [hEq]
  have hmul := mul_le_mul_of_nonneg_right (zValue_le_one A) (consistent_aux_pos A S hS).2.le
  linarith

private theorem edge_retrievalStep_good (A : InnerInput) (S : RetrievalState) (u : ℕ)
    (hS : RetrievalConsistent A S) (hΦ : potential A S < 1)
    (hp : (buildTable A S.front S.i S.j).parent = .edge u)
    (hEq : dpValue A (buildTable A) S.front S.i S.j =
      edgeExpectation A (buildTable A) u S.front S.i S.j) :
    ∃ U, retrievalStep A S = some U ∧ RetrievalConsistent A U ∧ potential A U < 1 := by
  have hs := potential_lt_one_unsaturated A S hS hΦ
  have hn : ¬ (tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j) := by omega
  have hne := incrementPairs_ne_nil A S hs.1 hs.2
  obtain ⟨y, hy, hscore⟩ := edge_has_score_below_one_of_bellman A S u hS hΦ hEq
  cases hlist : incrementPairs A S with
  | nil => contradiction
  | cons p ps =>
      let ab := firstMin (retrievalScore A S u) (incrementPairs A S) p
      have hmin : retrievalScore A S u ab < 1 :=
        (firstMin_le_of_mem _ _ p y hy).trans_lt hscore
      refine ⟨crossEdge A S u ab.1 ab.2, ?_, crossEdge_consistent A S hS u ab.1 ab.2, ?_⟩
      · simp [retrievalStep, hn, hp, hlist, ab]
      · rw [← retrievalScore_eq_cross_potential A S hS]
        exact hmin

private theorem retrievalStep_good_of_parent_rules (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) (hΦ : potential A S < 1)
    (hnone : (buildTable A S.front S.i S.j).parent ≠ .none)
    (hl : (buildTable A S.front S.i S.j).parent = .lengthTick →
      dpValue A (buildTable A) S.front S.i S.j =
      dpValue A (buildTable A) S.front (S.i + 1) S.j)
    (hc : (buildTable A S.front S.i S.j).parent = .costTick →
      dpValue A (buildTable A) S.front S.i S.j =
      dpValue A (buildTable A) S.front S.i (S.j + 1))
    (he : ∀ u, (buildTable A S.front S.i S.j).parent = .edge u →
      dpValue A (buildTable A) S.front S.i S.j =
      edgeExpectation A (buildTable A) u S.front S.i S.j) :
    ∃ U, retrievalStep A S = some U ∧ RetrievalConsistent A U ∧ potential A U < 1 := by
  have hs := potential_lt_one_unsaturated A S hS hΦ
  have hn : ¬ (tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j) := by omega
  cases hp : (buildTable A S.front S.i S.j).parent with
  | none => exact False.elim (hnone hp)
  | lengthTick =>
      refine ⟨{ S with i := S.i + 1, Hlength := zValue A * S.Hlength }, ?_,
        lengthTick_consistent A S hS, ?_⟩
      · simp [retrievalStep, hn, hp]
      · exact (lengthTick_potential_le A S hS (hl hp)).trans_lt hΦ
  | costTick =>
      refine ⟨{ S with j := S.j + 1, Hcost := zValue A * S.Hcost }, ?_,
        costTick_consistent A S hS, ?_⟩
      · simp [retrievalStep, hn, hp]
      · exact (costTick_potential_le A S hS (hc hp)).trans_lt hΦ
  | edge u => exact edge_retrievalStep_good A S u hS hΦ hp (he u hp)

private theorem retrievalStep_path (A : InnerInput) (t : ℕ) (S U : RetrievalState)
    (hP : IsPath A.I.graph S.front t S.path)
    (he : ∀ u, (buildTable A S.front S.i S.j).parent = .edge u →
      (u,S.front) ∈ A.I.graph.edges)
    (hstep : retrievalStep A S = some U) : IsPath A.I.graph U.front t U.path := by
  unfold retrievalStep at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · cases hstep; exact hP
    · cases hstep; exact hP
    · rename_i u hp
      split at hstep
      · contradiction
      · cases hstep
        exact isPath_prepend A.I.graph u S.front t S.path hP (he u hp)

private theorem retrievalRun_path (A : InnerInput) (t fuel : ℕ) (S U : RetrievalState)
    (hP : IsPath A.I.graph S.front t S.path)
    (he : ∀ v i j u, (buildTable A v i j).parent = .edge u → (u,v) ∈ A.I.graph.edges)
    (hrun : retrievalRun A fuel S = some U) : IsPath A.I.graph U.front t U.path := by
  induction fuel generalizing S U with
  | zero =>
      unfold retrievalRun at hrun
      split at hrun
      · cases hrun; exact hP
      · contradiction
  | succ fuel ih =>
      unfold retrievalRun at hrun
      split at hrun
      · cases hrun; exact hP
      · obtain ⟨T, hstep, hrun⟩ := Option.bind_eq_some_iff.mp hrun
        exact ih T U (retrievalStep_path A t S T hP (he S.front S.i S.j) hstep) hrun

private theorem standalone_Mission_QueueParentSupport__foldl_preserves_on {α β : Type*} (f : β → α → β) (P : β → Prop)
    (xs : List α) (b : β) (hb : P b)
    (hf : ∀ a ∈ xs, ∀ b, P b → P (f b a)) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      apply ih (f b a) (hf a (by simp) b hb)
      intro c hc U hU
      exact hf c (by simp [hc]) U hU

private theorem putCell_parentsSupported (A : InnerInput) (T : Table) (v i j : ℕ) (c : Cell)
    (hT : TableParentsSupported A T) (hc : ParentSupported A v c.parent) :
    TableParentsSupported A (putCell T v i j c) := by
  intro w a b
  unfold putCell
  split
  · rename_i h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact hc
  · exact hT w a b

private theorem initLayer_parentsSupported (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableParentsSupported A T) : LayerParentsSupported A (initLayer A T i j) := by
  refine ⟨hT, ?_⟩
  intro v
  change ParentSupported A v (if v = A.I.source then Parent.none else
    if dpValue A T v (i+1) j ≤ dpValue A T v i (j+1) then .lengthTick else .costTick)
  split
  · assumption
  · split <;> trivial

private theorem relaxEdge_parentsSupported (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerParentsSupported A S) (he : e ∈ A.I.graph.edges) :
    LayerParentsSupported A (relaxEdge A i j u S e) := by
  unfold relaxEdge
  dsimp only
  split
  · rename_i hguard
    split
    · refine ⟨hS.1, ?_⟩
      intro v
      change ParentSupported A v (Function.update S.parents e.2 (.edge u) v)
      by_cases hv : v = e.2
      · subst v
        simp only [Function.update_self]
        change (u,e.2) ∈ A.I.graph.edges
        simpa [← hguard.1] using he
      · simpa [Function.update_of_ne hv] using hS.2 v
    · exact hS
  · exact hS

private theorem popLayer_parentsSupported (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hS : LayerParentsSupported A S) : LayerParentsSupported A (popLayer A i j S) := by
  unfold popLayer
  split
  · exact hS
  · apply standalone_Mission_QueueParentSupport__foldl_preserves_on
    · exact ⟨putCell_parentsSupported A S.table _ i j _ hS.1 (hS.2 _), hS.2⟩
    · intro e he U hU
      exact relaxEdge_parentsSupported A i j _ U e hU he

private theorem buildLayer_parentsSupported (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableParentsSupported A T) : TableParentsSupported A (buildLayer A T i j) := by
  exact (standalone_Mission_QueueParentSupport__foldl_preserves_on (fun S _ => popLayer A i j S) (LayerParentsSupported A)
    (List.range (activeVertices A.I).length) (initLayer A T i j)
    (initLayer_parentsSupported A T i j hT)
    (fun _ _ S hS => popLayer_parentsSupported A i j S hS)).1

private theorem buildTable_parentsSupported (A : InnerInput) :
    TableParentsSupported A (buildTable A) := by
  unfold buildTable
  apply standalone_Mission_QueueParentSupport__foldl_preserves_on
  · intro v i j
    trivial
  · intro i _ T hT
    apply standalone_Mission_QueueParentSupport__foldl_preserves_on
    · exact hT
    · intro j _ U hU
      exact buildLayer_parentsSupported A U i j hU

private theorem buildTable_parent_none_only_source (A : InnerInput) (v i j : ℕ)
    (hp : (buildTable A v i j).parent = .none) : v = A.I.source := by
  have h := buildTable_parentsSupported A v i j
  simpa [hp, ParentSupported] using h

private theorem buildTable_parent_ne_none (A : InnerInput) (v i j : ℕ) (hv : v ≠ A.I.source) :
    (buildTable A v i j).parent ≠ .none := by
  intro hp
  exact hv (buildTable_parent_none_only_source A v i j hp)

private theorem buildTable_parent_edge_mem (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) : (u,v) ∈ A.I.graph.edges := by
  have h := buildTable_parentsSupported A v i j
  simpa [hp, ParentSupported] using h

private theorem retrieve_isPath (A : InnerInput) (t : ℕ) (U : RetrievalState)
    (h : retrieve A t = some U) : IsPath A.I.graph A.I.source t U.path := by
  have hpath : IsPath A.I.graph (retrievalStart t).front t (retrievalStart t).path := by
    simp [IsPath, retrievalStart]
  have hP := retrievalRun_path A t (retrievalFuel A) (retrievalStart t) U hpath
    (buildTable_parent_edge_mem A) h
  have ht := retrieve_terminal A t U h
  simpa [ht.1] using hP

private theorem retrievalRun_success_of_rank (A : InnerInput)
    (Good : RetrievalState → Prop) (rank : RetrievalState → ℕ)
    (hstep : ∀ S, Good S → ¬ RetrievalTerminal A S →
      ∃ U, retrievalStep A S = some U ∧ Good U ∧ rank U < rank S)
    (fuel : ℕ) (S : RetrievalState) (hS : Good S) (hrank : rank S ≤ fuel) :
    ∃ U, retrievalRun A fuel S = some U ∧ Good U ∧ RetrievalTerminal A U := by
  induction fuel generalizing S with
  | zero =>
      have ht : RetrievalTerminal A S := by
        by_contra hn
        obtain ⟨U, _, _, hlt⟩ := hstep S hS hn
        omega
      change S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A at ht
      exact ⟨S, by simp only [retrievalRun, if_pos ht], hS, ht⟩
  | succ fuel ih =>
      by_cases ht : RetrievalTerminal A S
      · change S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A at ht
        exact ⟨S, by simp only [retrievalRun, if_pos ht], hS, ht⟩
      · obtain ⟨T, hst, hT, hdec⟩ := hstep S hS ht
        change ¬ (S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A) at ht
        obtain ⟨U, hrun, hU, hterm⟩ := ih T hT (by omega)
        refine ⟨U, ?_, hU, hterm⟩
        simpa [retrievalRun, RetrievalTerminal, ht, hst] using hrun

private theorem actualRetrievalRank_initial_le_fuel (A : InnerInput) (t : ℕ)
    (hr : (buildTable A t 0 0).rank ≤ (activeVertices A.I).length) :
    actualRetrievalRank A (retrievalStart t) ≤ retrievalFuel A := by
  unfold actualRetrievalRank RSP.retrievalRank retrievalStart retrievalFuel
  simp only [Nat.zero_add, Nat.sub_zero]
  have : (buildTable A t 0 0).rank ≤ (activeVertices A.I).length + 1 := by omega
  nlinarith

private theorem actualRetrievalRank_decreases (A : InnerInput) (S U : RetrievalState)
    (hi : U.i < tickLimit A) (hj : U.j < tickLimit A)
    (hbound : (buildTable A U.front U.i U.j).rank ≤ (activeVertices A.I).length)
    (hprogress : S.i + S.j < U.i + U.j ∨
      (S.i + S.j = U.i + U.j ∧
        (buildTable A U.front U.i U.j).rank < (buildTable A S.front S.i S.j).rank)) :
    actualRetrievalRank A U < actualRetrievalRank A S := by
  unfold actualRetrievalRank
  rcases hprogress with h | ⟨heq, h⟩
  · exact RSP.retrievalRank_decreases_tick _ _ _ _ _ _ h (by omega) (by omega)
  · rw [← heq]
    exact RSP.retrievalRank_decreases_same_layer _ _ _ _ _ h

private theorem retrievalStep_progress (A : InnerInput) (S U : RetrievalState)
    (hr : ∀ u, (buildTable A S.front S.i S.j).parent = .edge u →
      (buildTable A u S.i S.j).rank < (buildTable A S.front S.i S.j).rank)
    (hstep : retrievalStep A S = some U) :
    S.i + S.j < U.i + U.j ∨
      (S.i + S.j = U.i + U.j ∧
        (buildTable A U.front U.i U.j).rank < (buildTable A S.front S.i S.j).rank) := by
  unfold retrievalStep at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · cases hstep
      left
      change S.i + S.j < (S.i + 1) + S.j
      omega
    · cases hstep
      left
      change S.i + S.j < S.i + (S.j + 1)
      omega
    · rename_i u hp
      split at hstep
      · contradiction
      · rename_i p ps hlist
        cases hstep
        simp only [crossEdge]
        by_cases hzero :
            (firstMin (retrievalScore A S u) (incrementPairs A S) p).1 +
            (firstMin (retrievalScore A S u) (incrementPairs A S) p).2 = 0
        · have ha : (firstMin (retrievalScore A S u) (incrementPairs A S) p).1 = 0 := by omega
          have hb : (firstMin (retrievalScore A S u) (incrementPairs A S) p).2 = 0 := by omega
          right
          simpa [ha, hb] using hr u hp
        · left
          omega

private theorem deterministic_retrieval_of_table_facts (A : InnerInput) (t : ℕ)
    (haccept : accepted A t)
    (hnone : ∀ v i j, v ≠ A.I.source →
      (buildTable A v i j).parent ≠ .none)
    (hlength : ∀ v i j, (buildTable A v i j).parent = .lengthTick →
      dpValue A (buildTable A) v i j = dpValue A (buildTable A) v (i+1) j)
    (hcost : ∀ v i j, (buildTable A v i j).parent = .costTick →
      dpValue A (buildTable A) v i j = dpValue A (buildTable A) v i (j+1))
    (hedge : ∀ v i j u, (buildTable A v i j).parent = .edge u →
      dpValue A (buildTable A) v i j = edgeExpectation A (buildTable A) u v i j)
    (hgraph : ∀ v i j u, (buildTable A v i j).parent = .edge u →
      (u,v) ∈ A.I.graph.edges)
    (hrank : ∀ v i j, (buildTable A v i j).rank ≤ (activeVertices A.I).length)
    (hparentRank : ∀ v i j u, (buildTable A v i j).parent = .edge u →
      (buildTable A u i j).rank < (buildTable A v i j).rank) :
    ∃ U : RetrievalState, retrieve A t = some U ∧
      IsPath A.I.graph A.I.source t U.path ∧
      pathWeight A.I.length U.path ≤ (1 + A.δ) * A.L ∧
      pathWeight A.I.cost U.path ≤ (1 + A.δ) * A.I.budget := by
  let Good : RetrievalState → Prop := fun S =>
    RetrievalConsistent A S ∧ IsPath A.I.graph S.front t S.path ∧ potential A S < 1
  have hstep : ∀ S, Good S → ¬ RetrievalTerminal A S →
      ∃ U, retrievalStep A S = some U ∧ Good U ∧
        actualRetrievalRank A U < actualRetrievalRank A S := by
    intro S hS hnterm
    have hs := potential_lt_one_unsaturated A S hS.1 hS.2.2
    have hv : S.front ≠ A.I.source := by
      intro hv
      exact hnterm ⟨hv, hs⟩
    obtain ⟨U, hst, hU, hΦ⟩ := retrievalStep_good_of_parent_rules A S hS.1 hS.2.2
      (hnone S.front S.i S.j hv) (hlength S.front S.i S.j) (hcost S.front S.i S.j)
      (hedge S.front S.i S.j)
    have hu := potential_lt_one_unsaturated A U hU hΦ
    refine ⟨U, hst, ⟨hU,
      retrievalStep_path A t S U hS.2.1 (hgraph S.front S.i S.j) hst, hΦ⟩, ?_⟩
    exact actualRetrievalRank_decreases A S U hu.1 hu.2 (hrank U.front U.i U.j)
      (retrievalStep_progress A S U (hparentRank S.front S.i S.j) hst)
  have hstart : Good (retrievalStart t) := by
    refine ⟨retrievalStart_consistent A t, ?_, retrievalStart_potential_lt_one A t haccept⟩
    simp [retrievalStart, IsPath]
  obtain ⟨U, hrun, hU, hterm⟩ := retrievalRun_success_of_rank A Good
    (actualRetrievalRank A) hstep (retrievalFuel A) (retrievalStart t) hstart
    (actualRetrievalRank_initial_le_fuel A t (hrank t 0 0))
  refine ⟨U, hrun, ?_, ?_, ?_⟩
  · simpa [hterm.1] using hU.2.1
  · by_contra hbad
    have hdet := (potential_detects_violation_of_nonneg A U
      (dpValue_buildTable_nonneg A U.front U.i U.j)).1 (lt_of_not_ge hbad) hterm.2.1
    exact (not_le_of_gt hU.2.2) hdet
  · by_contra hbad
    have hdet := (potential_detects_violation_of_nonneg A U
      (dpValue_buildTable_nonneg A U.front U.i U.j)).2 (lt_of_not_ge hbad) hterm.2.2
    exact (not_le_of_gt hU.2.2) hdet

private theorem edgeExpectation_putCell_other (A : InnerInput) (T : Table)
    (w u v i j : ℕ) (c : Cell) (hu : u ≠ w) :
    edgeExpectation A (putCell T w i j c) u v i j = edgeExpectation A T u v i j := by
  simp [edgeExpectation, dpValue, putCell, hu]

private theorem dpValue_putCell_next_length (A : InnerInput) (T : Table)
    (u v i j : ℕ) (c : Cell) :
    dpValue A (putCell T u i j c) v (i + 1) j = dpValue A T v (i + 1) j := by
  simp [dpValue, putCell]

private theorem dpValue_putCell_next_cost (A : InnerInput) (T : Table)
    (u v i j : ℕ) (c : Cell) :
    dpValue A (putCell T u i j c) v i (j + 1) = dpValue A T v i (j + 1) := by
  simp [dpValue, putCell]

private theorem initLayer_tickConsistency (A : InnerInput) (T : Table) (i j : ℕ) :
    TickConsistency A i j (initLayer A T i j) := by
  intro v
  by_cases hv : v = A.I.source
  · simp [initLayer, hv]
  · by_cases hle : dpValue A T v (i + 1) j ≤ dpValue A T v i (j + 1)
    · simp [initLayer, hv, hle, min_eq_left hle]
    · simp [initLayer, hv, hle, min_eq_right (le_of_not_ge hle)]

private theorem initLayer_edgeConsistency (A : InnerInput) (T : Table) (i j : ℕ) :
    EdgeConsistency A i j (initLayer A T i j) := by
  intro v u hp
  simp only [initLayer] at hp
  split_ifs at hp <;> contradiction

private theorem relaxEdge_tickConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (h : TickConsistency A i j S) :
    TickConsistency A i j (relaxEdge A i j u S e) := by
  unfold relaxEdge
  dsimp only
  split
  · split
    · intro v
      by_cases hv : v = e.2
      · subst v
        simp
      · simpa [Function.update_of_ne hv] using h v
    · exact h
  · exact h

private theorem relaxAll_tickConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (h : TickConsistency A i j S) : TickConsistency A i j (relaxAll A i j u S) := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact h
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih _ (relaxEdge_tickConsistency A i j u S e h)

private theorem settleState_tickConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (h : TickConsistency A i j S) : TickConsistency A i j (settleState S i j u) := by
  intro v
  change (S.parents v = .lengthTick → S.keys v = dpValue A (putCell S.table u i j _) v (i + 1) j) ∧
    (S.parents v = .costTick → S.keys v = dpValue A (putCell S.table u i j _) v i (j + 1))
  rw [dpValue_putCell_next_length, dpValue_putCell_next_cost]
  exact h v

private theorem popLayer_tickConsistency (A : InnerInput) (i j : ℕ) (S : LayerState)
    (h : TickConsistency A i j S) : TickConsistency A i j (popLayer A i j S) := by
  unfold popLayer
  split
  · exact h
  · change TickConsistency A i j (relaxAll A i j _ (settleState S i j _))
    exact relaxAll_tickConsistency A i j _ _ (settleState_tickConsistency A i j _ S h)

private theorem queueRun_tickConsistency (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (h : TickConsistency A i j S) : TickConsistency A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [queueRun_succ]; exact popLayer_tickConsistency A i j _ ih

private theorem relaxEdge_edgeConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hu : u ∉ S.queue) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (relaxEdge A i j u S e) := by
  unfold relaxEdge
  dsimp only
  split
  · rename_i he
    split
    · intro v p hp
      by_cases hv : v = e.2
      · subst v
        simp only [Function.update_self, Parent.edge.injEq] at hp
        subst p
        exact ⟨hu, by simpa only [Function.update_self, he.1]⟩
      · simp only [Function.update_of_ne hv] at hp ⊢
        exact h v p hp
    · exact h
  · exact h

private theorem relaxAll_edgeConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hu : u ∉ S.queue) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (relaxAll A i j u S) := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact h
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih _ (by simpa using hu) (relaxEdge_edgeConsistency A i j u S e hu h)

private theorem settleState_edgeConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hu : u ∈ S.queue) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (settleState S i j u) := by
  intro v p hp
  have hold := h v p hp
  have hpu : p ≠ u := by intro hpu; subst p; exact hold.1 hu
  refine ⟨fun hm => hold.1 (List.mem_of_mem_erase hm), ?_⟩
  change S.keys v = edgeExpectation A (putCell S.table u i j _) p v i j
  rw [edgeExpectation_putCell_other A S.table u p v i j _ hpu]
  exact hold.2

private theorem popLayer_edgeConsistency (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (popLayer A i j S) := by
  unfold popLayer
  split
  · exact h
  · rename_i w ws hq
    let u := firstMin S.keys S.queue w
    have hu : u ∈ S.queue := firstMin_mem _ _ _ (by rw [hq]; simp)
    change EdgeConsistency A i j (relaxAll A i j u (settleState S i j u))
    exact relaxAll_edgeConsistency A i j u _ hdup.not_mem_erase
      (settleState_edgeConsistency A i j u S hu h)

private theorem queueRun_edgeConsistency (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [queueRun_succ]
      exact popLayer_edgeConsistency A i j _ (queueRun_queue_nodup A i j n S hdup) ih

private theorem popLayer_parentSync (A : InnerInput) (i j : ℕ) (S : LayerState)
    (h : PoppedParentSync A i j S) : PoppedParentSync A i j (popLayer A i j S) := by
  unfold popLayer
  split
  · exact h
  · rename_i w ws hq
    let u := firstMin S.keys S.queue w
    let U := settleState S i j u
    change PoppedParentSync A i j (relaxAll A i j u U)
    intro v hv hvq
    have hvU : v ∉ U.queue := by simpa only [relaxAll_queue] using hvq
    rw [relaxAll_table, relaxAll_parents_outside A i j u v U hvU]
    change (putCell S.table u i j _ v i j).parent = S.parents v
    by_cases hvu : v = u
    · subst v
      simp
    · rw [putCell_other_vertex _ _ _ _ _ _ hvu]
      apply h v hv
      intro hm
      exact hvU ((List.mem_erase_of_ne hvu).mpr hm)

private theorem queueRun_parentSync (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (h : PoppedParentSync A i j S) : PoppedParentSync A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [queueRun_succ]; exact popLayer_parentSync A i j _ ih

private theorem buildLayer_selected_edge (A : InnerInput) (T : Table) (i j v u : ℕ)
    (hv : v ∈ activeVertices A.I) (hp : (buildLayer A T i j v i j).parent = .edge u) :
    (buildLayer A T i j v i j).value = edgeExpectation A (buildLayer A T i j) u v i j := by
  let S := initLayer A T i j
  let n := (activeVertices A.I).length
  have hs : PoppedSync A i j S := by intro v hv hn; exact False.elim (hn hv)
  have hp' : PoppedParentSync A i j S := by intro v hv hn; exact False.elim (hn hv)
  have hsync := queueRun_sync A i j n S (activeVertices_nodup A.I) hs
  have hpsync := queueRun_parentSync A i j n S hp'
  have he := queueRun_edgeConsistency A i j n S (activeVertices_nodup A.I)
    (initLayer_edgeConsistency A T i j)
  have hnot : v ∉ (queueRun A i j n S).queue := by
    rw [buildLayer_queue_exhausted A T i j]; simp
  have hparent : (queueRun A i j n S).parents v = .edge u :=
    (hpsync v hv hnot).symm.trans hp
  exact (hsync v hv hnot).trans (he v u hparent).2

private theorem buildLayer_selected_ticks (A : InnerInput) (T : Table) (i j v : ℕ)
    (hv : v ∈ activeVertices A.I) :
    ((buildLayer A T i j v i j).parent = .lengthTick →
      (buildLayer A T i j v i j).value = dpValue A (buildLayer A T i j) v (i + 1) j) ∧
    ((buildLayer A T i j v i j).parent = .costTick →
      (buildLayer A T i j v i j).value = dpValue A (buildLayer A T i j) v i (j + 1)) := by
  let S := initLayer A T i j
  let n := (activeVertices A.I).length
  have hs : PoppedSync A i j S := by intro v hv hn; exact False.elim (hn hv)
  have hp' : PoppedParentSync A i j S := by intro v hv hn; exact False.elim (hn hv)
  have hsync := queueRun_sync A i j n S (activeVertices_nodup A.I) hs
  have hpsync := queueRun_parentSync A i j n S hp'
  have ht := queueRun_tickConsistency A i j n S (initLayer_tickConsistency A T i j)
  have hnot : v ∉ (queueRun A i j n S).queue := by
    rw [buildLayer_queue_exhausted A T i j]; simp
  constructor
  · intro hp
    exact (hsync v hv hnot).trans ((ht v).1 ((hpsync v hv hnot).symm.trans hp))
  · intro hp
    exact (hsync v hv hnot).trans ((ht v).2 ((hpsync v hv hnot).symm.trans hp))

private theorem layerSchedule_mem (A : InnerInput) (i j : ℕ) :
    (i,j) ∈ layerSchedule A ↔ i < tickLimit A ∧ j < tickLimit A := by
  simp [layerSchedule, List.mem_flatMap, List.mem_map]

private theorem layerSchedule_ordered (A : InnerInput) :
    (layerSchedule A).Pairwise layerBefore := by
  have hr : ((List.range (tickLimit A)).reverse).Pairwise
      (fun i j : ℕ => j < i) := by
    simpa only [List.pairwise_reverse] using
      (List.pairwise_lt_range : (List.range (tickLimit A)).Pairwise (· < ·))
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    apply List.pairwise_map.mpr
    exact hr.imp (fun {_ _} hjk => Or.inr ⟨rfl, hjk⟩)
  · apply hr.imp
    intro i j hij x hx y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    exact Or.inl hij

private theorem buildTable_eq_runLayers (A : InnerInput) :
    buildTable A = runLayers A (layerSchedule A) (fun _ _ _ => ⟨1,.lengthTick,0⟩) := by
  simp only [buildTable, runLayers, layerSchedule, List.foldl_flatMap, List.foldl_map]

private theorem runLayers_range (A : InnerInput) (layers : List (ℕ × ℕ)) (T : Table)
    (hT : TableRange T) : TableRange (runLayers A layers T) := by
  induction layers generalizing T with
  | nil => exact hT
  | cons p ps ih => exact ih (buildLayer A T p.1 p.2) (buildLayer_range A T hT _ _)

private theorem runLayers_frame (A : InnerInput) (layers : List (ℕ × ℕ)) (T : Table)
    (v a b : ℕ) (h : ∀ p ∈ layers, a ≠ p.1 ∨ b ≠ p.2) :
    runLayers A layers T v a b = T v a b := by
  induction layers generalizing T with
  | nil => rfl
  | cons p ps ih =>
      change runLayers A ps (buildLayer A T p.1 p.2) v a b = T v a b
      rw [ih _ (fun p hp => h p (by simp [hp]))]
      exact buildLayer_other_layer A T p.1 p.2 v a b (h p (by simp))

private theorem buildTable_layer_witness (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A) :
    ∃ T : Table, TableRange T ∧
      ∀ v a b, (i < a ∨ i = a ∧ j ≤ b) →
        buildTable A v a b = buildLayer A T i j v a b := by
  have hm := (layerSchedule_mem A i j).mpr ⟨hi,hj⟩
  obtain ⟨pre, post, hs⟩ := List.mem_iff_append.mp hm
  let T : Table := runLayers A pre (fun _ _ _ => ⟨1,.lengthTick,0⟩)
  refine ⟨T, runLayers_range A pre _ (by intro v a b; exact ⟨zero_le_one,le_rfl⟩), ?_⟩
  intro v a b hab
  have hord := layerSchedule_ordered A
  rw [hs] at hord
  have hpost : ∀ p ∈ post, layerBefore (i,j) p :=
    (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1
  rw [buildTable_eq_runLayers, hs]
  change ((pre ++ (i,j) :: post).foldl
    (fun U p => buildLayer A U p.1 p.2) (fun _ _ _ => ⟨1,.lengthTick,0⟩)) v a b = _
  rw [List.foldl_append, List.foldl_cons]
  apply runLayers_frame A post (buildLayer A T i j) v a b
  intro p hp
  have hh := hpost p hp
  dsimp [layerBefore] at hh
  omega

private theorem initLayer_ranks (A : InnerInput) (T : Table) (i j : ℕ) :
    LayerRanks A i j (initLayer A T i j) := by
  constructor
  · intro v hv hn
    exact False.elim (hn hv)
  · intro v u hp
    simp only [initLayer] at hp
    split_ifs at hp
  · intro v hv hn
    exact False.elim (hn hv)

private theorem settleState_ranks (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hu : u ∈ S.queue) (h : LayerRanks A i j S) :
    LayerRanks A i j (settleState S i j u) := by
  constructor
  · intro v hv hn
    change (putCell S.table u i j _ v i j).rank < S.nextRank + 1
    by_cases hvu : v = u
    · subst v
      simp
    · rw [putCell_other_vertex _ _ _ _ _ _ hvu]
      have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne hvu).mpr hm)
      exact (h.settled v hv hn').trans (Nat.lt_succ_self _)
  · intro v p hp
    have hold := h.pending v p hp
    have hpu : p ≠ u := by intro heq; subst p; exact hold.1 hu
    refine ⟨fun hm => hold.1 (List.mem_of_mem_erase hm), ?_⟩
    change (putCell S.table u i j _ p i j).rank < S.nextRank + 1
    rw [putCell_other_vertex _ _ _ _ _ _ hpu]
    exact hold.2.trans (Nat.lt_succ_self _)
  · intro v hv hn p hp
    by_cases hvu : v = u
    · subst v
      have hparent : S.parents u = .edge p := by simpa [settleState] using hp
      have hold := h.pending u p hparent
      have hpu : p ≠ u := by intro heq; subst p; exact hold.1 hu
      refine ⟨fun hm => hold.1 (List.mem_of_mem_erase hm), ?_⟩
      change (putCell S.table u i j _ p i j).rank < (putCell S.table u i j _ u i j).rank
      rw [putCell_other_vertex _ _ _ _ _ _ hpu, putCell_same]
      exact hold.2
    · have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne hvu).mpr hm)
      have hp' : (S.table v i j).parent = .edge p := by
        simpa [settleState, putCell_other_vertex _ _ _ _ _ _ hvu] using hp
      have hold := h.edge v hv hn' p hp'
      have hpu : p ≠ u := by intro heq; subst p; exact hold.1 hu
      refine ⟨fun hm => hold.1 (List.mem_of_mem_erase hm), ?_⟩
      change (putCell S.table u i j _ p i j).rank < (putCell S.table u i j _ v i j).rank
      rw [putCell_other_vertex _ _ _ _ _ _ hpu, putCell_other_vertex _ _ _ _ _ _ hvu]
      exact hold.2

private theorem relaxEdge_ranks (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hu : u ∉ S.queue) (hur : (S.table u i j).rank < S.nextRank)
    (h : LayerRanks A i j S) : LayerRanks A i j (relaxEdge A i j u S e) := by
  unfold relaxEdge
  dsimp only
  split
  · split
    · constructor
      · exact h.settled
      · intro v p hp
        by_cases hv : v = e.2
        · subst v
          simp only [Function.update_self, Parent.edge.injEq] at hp
          subst p
          exact ⟨hu, hur⟩
        · simp only [Function.update_of_ne hv] at hp
          exact h.pending v p hp
      · exact h.edge
    · exact h
  · exact h

private theorem relaxAll_ranks (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hu : u ∉ S.queue) (hur : (S.table u i j).rank < S.nextRank)
    (h : LayerRanks A i j S) : LayerRanks A i j (relaxAll A i j u S) := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact h
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih _ (by simpa using hu) (by simpa using hur)
        (relaxEdge_ranks A i j u S e hu hur h)

private theorem popLayer_ranks (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (h : LayerRanks A i j S) :
    LayerRanks A i j (popLayer A i j S) := by
  by_cases hne : S.queue = []
  · simpa [popLayer, hne] using h
  · rw [popLayer_eq_relaxAll A i j S hne]
    apply relaxAll_ranks
    · exact hdup.not_mem_erase
    · simp [settleState]
    · exact settleState_ranks A i j _ S (pickedVertex_mem S hne) h

private theorem queueRun_ranks (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (h : LayerRanks A i j S) :
    LayerRanks A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [queueRun_succ]
      exact popLayer_ranks A i j _ (queueRun_queue_nodup A i j n S hdup) ih

private theorem buildLayer_parent_rank (A : InnerInput) (T : Table) (i j v u : ℕ)
    (hv : v ∈ activeVertices A.I)
    (hp : (buildLayer A T i j v i j).parent = .edge u) :
    (buildLayer A T i j u i j).rank < (buildLayer A T i j v i j).rank := by
  have h := queueRun_ranks A i j (activeVertices A.I).length (initLayer A T i j)
    (activeVertices_nodup A.I) (initLayer_ranks A T i j)
  have hn : v ∉ (queueRun A i j (activeVertices A.I).length (initLayer A T i j)).queue := by
    rw [buildLayer_queue_exhausted]
    simp
  exact (h.edge v hv hn u hp).2

private theorem initLayer_rankBound (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableRankBound T (activeVertices A.I).length) :
    LayerRankBound (initLayer A T i j) (activeVertices A.I).length := by
  exact ⟨hT, by simp [initLayer]⟩

private theorem relaxAll_rankBound (A : InnerInput) (i j u : ℕ) (S : LayerState) (n : ℕ)
    (h : LayerRankBound S n) : LayerRankBound (relaxAll A i j u S) n := by
  simpa only [LayerRankBound, relaxAll_table, relaxAll_nextRank, relaxAll_queue] using h

private theorem settleState_rankBound (i j u : ℕ) (S : LayerState) (n : ℕ)
    (hu : u ∈ S.queue) (h : LayerRankBound S n) :
    LayerRankBound (settleState S i j u) n := by
  constructor
  · intro v a b
    change (putCell S.table u i j _ v a b).rank ≤ n
    unfold putCell
    split
    · have hc := h.2
      dsimp only
      omega
    · exact h.1 v a b
  · change S.nextRank + 1 + (S.queue.erase u).length = n
    rw [List.length_erase_of_mem hu]
    have hc := h.2
    have hlen : 0 < S.queue.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hu)
    omega

private theorem popLayer_rankBound (A : InnerInput) (i j : ℕ) (S : LayerState) (n : ℕ)
    (h : LayerRankBound S n) : LayerRankBound (popLayer A i j S) n := by
  by_cases hne : S.queue = []
  · simpa [popLayer, hne] using h
  · rw [popLayer_eq_relaxAll A i j S hne]
    exact relaxAll_rankBound A i j _ _ n
      (settleState_rankBound i j _ S n (pickedVertex_mem S hne) h)

private theorem queueRun_rankBound (A : InnerInput) (i j k : ℕ) (S : LayerState) (n : ℕ)
    (h : LayerRankBound S n) : LayerRankBound (queueRun A i j k S) n := by
  induction k with
  | zero => exact h
  | succ k ih => rw [queueRun_succ]; exact popLayer_rankBound A i j _ n ih

private theorem buildLayer_rankBound (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableRankBound T (activeVertices A.I).length) :
    TableRankBound (buildLayer A T i j) (activeVertices A.I).length :=
  (queueRun_rankBound A i j _ _ _ (initLayer_rankBound A T i j hT)).1

private theorem runLayers_rankBound (A : InnerInput) (layers : List (ℕ × ℕ)) (T : Table)
    (hT : TableRankBound T (activeVertices A.I).length) :
    TableRankBound (runLayers A layers T) (activeVertices A.I).length := by
  induction layers generalizing T with
  | nil => exact hT
  | cons p ps ih => exact ih _ (buildLayer_rankBound A T p.1 p.2 hT)

private theorem buildTable_rank_le (A : InnerInput) (v i j : ℕ) :
    (buildTable A v i j).rank ≤ (activeVertices A.I).length := by
  rw [buildTable_eq_runLayers]
  exact runLayers_rankBound A _ _ (by intro v a b; exact Nat.zero_le _) v i j

private theorem buildTable_outside (A : InnerInput) (v i j : ℕ)
    (hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j) :
    buildTable A v i j = ⟨1, .lengthTick, 0⟩ := by
  rw [buildTable_eq_runLayers]
  apply runLayers_frame
  intro p hp
  have hp' := (layerSchedule_mem A p.1 p.2).mp hp
  omega

private theorem buildTable_outside_rank (A : InnerInput) (v i j : ℕ)
    (hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j) :
    (buildTable A v i j).rank = 0 := by
  rw [buildTable_outside A v i j hsat]

private theorem buildTable_outside_parent (A : InnerInput) (v i j : ℕ)
    (hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j) :
    (buildTable A v i j).parent = .lengthTick := by
  rw [buildTable_outside A v i j hsat]

private theorem buildTable_edge_parent_nonsaturated (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) :
    i < tickLimit A ∧ j < tickLimit A := by
  by_contra hn
  have hs : tickLimit A ≤ i ∨ tickLimit A ≤ j := by omega
  rw [buildTable_outside_parent A v i j hs] at hp
  cases hp

private theorem dpValue_buildTable_selected_edge (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) :
    dpValue A (buildTable A) v i j = edgeExpectation A (buildTable A) u v i j := by
  by_cases hs : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · exact dp_faithfulness_saturated A (buildTable A) u v i j hs
  have hi : i < tickLimit A := by omega
  have hj : j < tickLimit A := by omega
  have hv : v ∈ activeVertices A.I :=
    activeVertices_edge_right A.I u v (buildTable_parent_edge_mem A v i j u hp)
  obtain ⟨T, _, hfinal⟩ := buildTable_layer_witness A i j hi hj
  have hhere := hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)
  have hparent : (buildLayer A T i j v i j).parent = .edge u := by
    rw [← hhere]; exact hp
  have he := buildLayer_selected_edge A T i j v u hv hparent
  have hexp : edgeExpectation A (buildTable A) u v i j =
      edgeExpectation A (buildLayer A T i j) u v i j := by
    apply edgeExpectation_congr
    intro a _ b _
    apply dpValue_congr_at
    apply hfinal
    omega
  rw [hexp]
  simpa only [dpValue, if_neg hs, hhere] using he

private theorem dpValue_buildTable_selected_length (A : InnerInput) (v i j : ℕ)
    (hp : (buildTable A v i j).parent = .lengthTick) :
    dpValue A (buildTable A) v i j = dpValue A (buildTable A) v (i + 1) j := by
  by_cases hs : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · have hs' : tickLimit A ≤ i + 1 ∨ tickLimit A ≤ j := by omega
    simp only [dpValue, if_pos hs, if_pos hs']
  by_cases hv : v ∈ activeVertices A.I
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, _, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere := hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)
    have hparent : (buildLayer A T i j v i j).parent = .lengthTick := by
      rw [← hhere]; exact hp
    have he := (buildLayer_selected_ticks A T i j v hv).1 hparent
    have hn := dpValue_congr_at A (buildTable A) (buildLayer A T i j) v (i + 1) j
      (hfinal v (i + 1) j (Or.inl (by omega)))
    rw [hn]
    simpa only [dpValue, if_neg hs, hhere] using he
  · rw [dpValue_buildTable_inactive A v i j hv,
      dpValue_buildTable_inactive A v (i + 1) j hv]

private theorem dpValue_buildTable_selected_cost (A : InnerInput) (v i j : ℕ)
    (hp : (buildTable A v i j).parent = .costTick) :
    dpValue A (buildTable A) v i j = dpValue A (buildTable A) v i (j + 1) := by
  by_cases hs : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · have hs' : tickLimit A ≤ i ∨ tickLimit A ≤ j + 1 := by omega
    simp only [dpValue, if_pos hs, if_pos hs']
  by_cases hv : v ∈ activeVertices A.I
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, _, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere := hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)
    have hparent : (buildLayer A T i j v i j).parent = .costTick := by
      rw [← hhere]; exact hp
    have he := (buildLayer_selected_ticks A T i j v hv).2 hparent
    have hn := dpValue_congr_at A (buildTable A) (buildLayer A T i j) v i (j + 1)
      (hfinal v i (j + 1) (Or.inr ⟨rfl, by omega⟩))
    rw [hn]
    simpa only [dpValue, if_neg hs, hhere] using he
  · rw [dpValue_buildTable_inactive A v i j hv,
      dpValue_buildTable_inactive A v i (j + 1) hv]

private theorem buildTable_parent_rank (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) :
    (buildTable A u i j).rank < (buildTable A v i j).rank := by
  obtain ⟨hi, hj⟩ := buildTable_edge_parent_nonsaturated A v i j u hp
  have hv : v ∈ activeVertices A.I :=
    activeVertices_edge_right A.I u v (buildTable_parent_edge_mem A v i j u hp)
  obtain ⟨T, _, hfinal⟩ := buildTable_layer_witness A i j hi hj
  have hhere := hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)
  have hparent : (buildLayer A T i j v i j).parent = .edge u := by
    rw [← hhere]; exact hp
  rw [hhere, hfinal u i j (Or.inr ⟨rfl, le_rfl⟩)]
  exact buildLayer_parent_rank A T i j v u hv hparent

private theorem deterministic_retrieval (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (haccept : accepted A t) :
    ∃ S : RetrievalState, retrieve A t = some S ∧
      IsPath A.I.graph A.I.source t S.path ∧
      pathWeight A.I.length S.path ≤ (1 + A.δ) * A.L ∧
      pathWeight A.I.cost S.path ≤ (1 + A.δ) * A.I.budget := by
  clear ht
  exact deterministic_retrieval_of_table_facts A t haccept
    (buildTable_parent_ne_none A)
    (dpValue_buildTable_selected_length A)
    (dpValue_buildTable_selected_cost A)
    (dpValue_buildTable_selected_edge A)
    (buildTable_parent_edge_mem A)
    (buildTable_rank_le A)
    (buildTable_parent_rank A)

private theorem inner_soundness (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (haccept : accepted A t) :
    ∃ P : List ℕ, IsPath A.I.graph A.I.source t P ∧
      pathWeight A.I.length P ≤ (1 + A.δ) * A.L ∧
      pathWeight A.I.cost P ≤ (1 + A.δ) * A.I.budget := by
  obtain ⟨S, _, hP, hL, hC⟩ := deterministic_retrieval A t ht haccept
  exact ⟨S.path, hP, hL, hC⟩

private theorem retrievalStep_counts (A : InnerInput) (S U : RetrievalState)
    (hstep : retrievalStep A S = some U) :
    artificialTickCharge A S + graphEdgeCharge A S = 1 ∧
      S.i + S.j + artificialTickCharge A S ≤ U.i + U.j ∧
      U.path.length = S.path.length + graphEdgeCharge A S := by
  unfold retrievalStep at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · rename_i hp
      cases hstep
      simp [artificialTickCharge, graphEdgeCharge, hp]
    · rename_i hp
      cases hstep
      simp [artificialTickCharge, graphEdgeCharge, hp]
    · rename_i u hp
      split at hstep
      · contradiction
      · cases hstep
        simp [artificialTickCharge, graphEdgeCharge, hp, crossEdge]
        omega

private theorem RetrievalTrace.count_bounds (A : InnerInput) (S U : RetrievalState)
    (ticks edges : ℕ) (h : RetrievalTrace A S U ticks edges) :
    S.i + S.j + ticks ≤ U.i + U.j ∧ U.path.length = S.path.length + edges := by
  induction h with
  | refl S => simp
  | step S T U ticks edges hstep _ ih =>
      have hc := retrievalStep_counts A S T hstep
      constructor <;> omega

private theorem retrievalRun_trace (A : InnerInput) (fuel : ℕ) (S U : RetrievalState)
    (h : retrievalRun A fuel S = some U) :
    ∃ ticks edges, RetrievalTrace A S U ticks edges ∧ ticks + edges ≤ fuel := by
  induction fuel generalizing S with
  | zero =>
      unfold retrievalRun at h
      split at h
      · cases h
        exact ⟨0, 0, .refl _, by omega⟩
      · contradiction
  | succ fuel ih =>
      unfold retrievalRun at h
      split at h
      · cases h
        exact ⟨0, 0, .refl _, by omega⟩
      · cases hstep : retrievalStep A S with
        | none => simp [hstep] at h
        | some T =>
            have htail : retrievalRun A fuel T = some U := by simpa [hstep] using h
            obtain ⟨ticks, edges, ht, hcount⟩ := ih T htail
            refine ⟨artificialTickCharge A S + ticks, graphEdgeCharge A S + edges,
              .step S T U ticks edges hstep ht, ?_⟩
            have hc := (retrievalStep_counts A S T hstep).1
            omega

private theorem retrieve_trace_counts (A : InnerInput) (t : ℕ) (U : RetrievalState)
    (h : retrieve A t = some U) :
    ∃ ticks edges, RetrievalTrace A (retrievalStart t) U ticks edges ∧
      edges + 1 = U.path.length ∧ ticks ≤ U.i + U.j ∧
      ticks ≤ 2 * (tickLimit A - 1) ∧
      ticks + edges ≤ 2 * (tickLimit A - 1) + U.path.length - 1 := by
  obtain ⟨ticks, edges, ht, _⟩ := retrievalRun_trace A (retrievalFuel A) (retrievalStart t) U h
  have hb := ht.count_bounds A _ _ ticks edges
  have hterm := retrieve_terminal A t U h
  simp only [retrievalStart, List.length_singleton, Nat.zero_add] at hb
  refine ⟨ticks, edges, ht, ?_, hb.1, ?_, ?_⟩ <;> omega

private theorem ActiveRetrievalTrace.forget (A : InnerInput) (S U : RetrievalState)
    (ticks edges : ℕ) (h : ActiveRetrievalTrace A S U ticks edges) :
    RetrievalTrace A S U ticks edges := by
  induction h with
  | done S _ => exact .refl S
  | step S T U ticks edges _ _ _ hstep _ ih => exact .step S T U ticks edges hstep ih

private theorem ActiveRetrievalTrace.terminal (A : InnerInput) (S U : RetrievalState)
    (ticks edges : ℕ) (h : ActiveRetrievalTrace A S U ticks edges) :
    RetrievalTerminal A U := by
  induction h with
  | done _ hterm => exact hterm
  | step _ _ _ _ _ _ _ _ _ _ ih => exact ih

private theorem retrievalStep_unsaturated (A : InnerInput) (S U : RetrievalState)
    (h : retrievalStep A S = some U) : S.i < tickLimit A ∧ S.j < tickLimit A := by
  by_cases hs : tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j
  · simp [retrievalStep, hs] at h
  · omega

private theorem retrievalRun_active_trace (A : InnerInput) (fuel : ℕ) (S U : RetrievalState)
    (h : retrievalRun A fuel S = some U) :
    ∃ ticks edges, ActiveRetrievalTrace A S U ticks edges ∧ ticks + edges ≤ fuel := by
  induction fuel generalizing S with
  | zero =>
      unfold retrievalRun at h
      split at h
      · rename_i ht
        cases h
        exact ⟨0, 0, .done _ ht, by omega⟩
      · contradiction
  | succ fuel ih =>
      unfold retrievalRun at h
      split at h
      · rename_i ht
        cases h
        exact ⟨0, 0, .done _ ht, by omega⟩
      · rename_i hn
        cases hstep : retrievalStep A S with
        | none => simp [hstep] at h
        | some T =>
            have htail : retrievalRun A fuel T = some U := by simpa [hstep] using h
            obtain ⟨ticks, edges, ht, hc⟩ := ih T htail
            obtain ⟨hi,hj⟩ := retrievalStep_unsaturated A S T hstep
            have hfront : S.front ≠ A.I.source := fun he => hn ⟨he,hi,hj⟩
            refine ⟨artificialTickCharge A S + ticks, graphEdgeCharge A S + edges,
              .step S T U ticks edges hfront hi hj hstep ht, ?_⟩
            have hcharge := (retrievalStep_counts A S T hstep).1
            omega

private theorem retrieve_active_trace_counts (A : InnerInput) (t : ℕ) (U : RetrievalState)
    (h : retrieve A t = some U) :
    ∃ ticks edges, ActiveRetrievalTrace A (retrievalStart t) U ticks edges ∧
      edges + 1 = U.path.length ∧ ticks ≤ U.i + U.j ∧
      ticks ≤ 2 * (tickLimit A - 1) ∧
      ticks + edges ≤ 2 * (tickLimit A - 1) + U.path.length - 1 := by
  obtain ⟨ticks, edges, ht, _⟩ := retrievalRun_active_trace A (retrievalFuel A) (retrievalStart t) U h
  have hb := (ht.forget A _ _ ticks edges).count_bounds A _ _ ticks edges
  have hterm := ht.terminal A _ _ ticks edges
  simp only [retrievalStart, List.length_singleton, Nat.zero_add] at hb
  refine ⟨ticks, edges, ht, ?_, hb.1, ?_, ?_⟩ <;> change RetrievalTerminal A U at hterm <;>
    unfold RetrievalTerminal at hterm <;> omega

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem InnerEnv.address_next_length {A : InnerInput} (E : InnerEnv A) (v i j : ℕ) :
    E.address v (i + 1) j = E.address v i j + 4 * A.I.graph.n * tickLimit A := by
  unfold InnerEnv.address
  ring

private theorem InnerEnv.address_next_cost {A : InnerInput} (E : InnerEnv A) (v i j : ℕ) :
    E.address v i (j + 1) = E.address v i j + 4 * A.I.graph.n := by
  unfold InnerEnv.address
  ring

private theorem InnerEnv.address_change_vertex {A : InnerInput} (E : InnerEnv A) (v u i j : ℕ) :
    E.address v i j - 4 * v + 4 * u = E.address u i j := by
  have h v : E.address v i j = (E.base + 4 * (i * tickLimit A + j) * A.I.graph.n) + 4 * v := by
    unfold InnerEnv.address
    ring
  rw [h v, h u, Nat.add_sub_cancel]

private theorem length_tick_state {A : InnerInput} (E : InnerEnv A) (input : RAMInput)
    (S : RetrievalState) (s : Store) (h : InnerState E S s) :
    InnerState E { S with i := S.i + 1, Hlength := zValue A * S.Hlength }
      (evalAtoms input lengthTickAtoms s) := by
  rcases h with ⟨hc, hs, hm, hp, h50⟩
  rcases hc with ⟨h4, h5, h21, h24, h25, h30, h31, h32, h0, hrm⟩
  rcases hs with ⟨hv, hi, hj, ha, hL, hC⟩
  rcases hp with ⟨hlen, hpath, hbase⟩
  simp [InnerState, InnerConstants, InnerCore, InnerMemory, InnerPath,
    evalAtoms, lengthTickAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
    evalNat, evalReal, h4, h5, h21, h24, h25, h30, h31, h32, h0, hrm,
    hv, hi, hj, ha, hL, hC, hlen, hpath, hbase, h50, hm, E.address_next_length]
  exact hm

private theorem cost_tick_state {A : InnerInput} (E : InnerEnv A) (input : RAMInput)
    (S : RetrievalState) (s : Store) (h : InnerState E S s) :
    InnerState E { S with j := S.j + 1, Hcost := zValue A * S.Hcost }
      (evalAtoms input costTickAtoms s) := by
  rcases h with ⟨hc, hs, hm, hp, h50⟩
  rcases hc with ⟨h4, h5, h21, h24, h25, h30, h31, h32, h0, hrm⟩
  rcases hs with ⟨hv, hi, hj, ha, hL, hC⟩
  rcases hp with ⟨hlen, hpath, hbase⟩
  simp [InnerState, InnerConstants, InnerCore, InnerMemory, InnerPath,
    evalAtoms, costTickAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
    evalNat, evalReal, h4, h5, h21, h24, h25, h30, h31, h32, h0, hrm,
    hv, hi, hj, ha, hL, hC, hlen, hpath, hbase, h50, hm, E.address_next_cost]
  exact hm

private theorem length_tick_pointer (input : RAMInput) (s : Store) :
    (evalAtoms input lengthTickAtoms s).nr 3 = s.nr 3 := by
  simp [evalAtoms, lengthTickAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at]

private theorem cost_tick_pointer (input : RAMInput) (s : Store) :
    (evalAtoms input costTickAtoms s).nr 3 = s.nr 3 := by
  simp [evalAtoms, costTickAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at]

private theorem parentLoaded_state {A : InnerInput} (E : InnerEnv A) (input : RAMInput)
    (S : RetrievalState) (s : Store) (h : InnerState E S s) :
    InnerState E S (parentLoaded input s) := by
  simpa [InnerState, InnerConstants, InnerCore, InnerMemory, InnerPath,
    parentLoaded, Atom.eval, Store.ofRAM, ramStep, Store.at] using h

private theorem parentLoaded_pointer (input : RAMInput) (s : Store) :
    (parentLoaded input s).nr 3 = s.nr 3 := by
  simp [parentLoaded, Atom.eval, Store.ofRAM, ramStep, Store.at]

private theorem parentLoaded_tag {A : InnerInput} (E : InnerEnv A) (input : RAMInput)
    (S : RetrievalState) (s : Store) (hl : InnerLayout E) (h : InnerState E S s)
    (hv : S.front ∈ activeVertices A.I) (hi : S.i < tickLimit A) (hj : S.j < tickLimit A) :
    (parentLoaded input s).nr 14 = parentTag (buildTable A S.front S.i S.j).parent := by
  have haddr := h.2.1.2.2.2.1
  have hmem := h.2.2.1
  have ht := hl.2 S.front hv S.i hi S.j hj
  simp only [parentLoaded, Atom.eval, Store.ofRAM, ramStep, Store.at,
    Bool.false_eq_true, ↓reduceIte, List.getElem?_cons_zero, Option.getD_some,
    Function.update_self]
  rw [haddr, hmem _ (by omega)]
  exact ht.2.2.1

private theorem stopped_flag (input : RAMInput) (s : Store) :
    (stopped input s).nr 1 = 1 ∧ (stopped input s).nr 50 = 0 := by
  simp [stopped, evalAtoms, innerStopAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at]

private theorem stopped_path {A : InnerInput} (E : InnerEnv A) (input : RAMInput)
    (S : RetrievalState) (s : Store) (h : InnerPath E S s) :
    InnerPath E S (stopped input s) := by
  simpa [InnerPath, stopped, evalAtoms, innerStopAtoms, Atom.eval, Store.ofRAM,
    ramStep, Store.at] using h

private theorem stopped_memory {A : InnerInput} (E : InnerEnv A) (input : RAMInput)
    (s : Store) (h : InnerMemory E s) : InnerMemory E (stopped input s) := h

private theorem edgeParams_address {A : InnerInput} (E : InnerEnv A)
    (S : RetrievalState) (u a b : ℕ) :
    (edgeParams E S u).address a b = E.address u (S.i + a) (S.j + b) := by
  unfold edgeParams RectParams.address InnerEnv.address
  ring

private theorem edgeParams_score {A : InnerInput} (E : InnerEnv A) (hE : InnerLayout E)
    (S : RetrievalState) (u a b : ℕ) (hu : u ∈ activeVertices A.I)
    (ha : a < tickLimit A - S.i) (hb : b < tickLimit A - S.j) :
    (edgeParams E S u).score (a,b) = retrievalScore A S u (a,b) := by
  have hai : S.i + a < tickLimit A := by omega
  have hbj : S.j + b < tickLimit A := by omega
  have hm := (hE.2 u hu (S.i + a) hai (S.j + b) hbj).2.1
  have hpa := hE.1 a (by omega)
  have hpb := hE.1 b (by omega)
  unfold RectParams.score
  rw [edgeParams_address]
  simp only [edgeParams, hm, hpa, hpb, retrievalScore, dpValue,
    Nat.not_le.mpr hai, Nat.not_le.mpr hbj, or_self, if_false]
  ring

private theorem edgeSetup_contract {A : InnerInput} (E : InnerEnv A) (hE : InnerLayout E)
    (S : RetrievalState) (u : ℕ) (input : RAMInput) (s : Store)
    (hstate : InnerState E S s) (hfront : S.front ∈ activeVertices A.I)
    (hi : S.i < tickLimit A) (hj : S.j < tickLimit A)
    (hp : (buildTable A S.front S.i S.j).parent = .edge u) :
    RectConstants (edgeParams E S u) (edgeSetupResult input s) ∧
      (edgeSetupResult input s).nr 27 = (edgeParams E S u).base ∧
      (edgeSetupResult input s).nr 15 = u := by
  rcases hstate with ⟨hc,hcore,hmem,hpath,hflag⟩
  rcases hc with ⟨h4,h5,h21,h24,h25,h30,h31,h32,h0,hrm⟩
  rcases hcore with ⟨hf,hi',hj',haddr,hL,hC⟩
  obtain ⟨hbelow,hval,htag,hparent,hpgf⟩ := hE.2 S.front hfront S.i hi S.j hj
  have hload : s.nm (E.address S.front S.i S.j + 1) = u := by
    rw [hmem _ (by omega), hparent, hp]
    rfl
  have hPL : s.rm (E.address S.front S.i S.j + 1) = lengthPGF A u S.front := by
    rw [hrm]
    exact (hpgf u hp).1
  have hPC : s.rm (E.address S.front S.i S.j + 2) = costPGF A u S.front := by
    rw [hrm]
    exact (hpgf u hp).2
  have hEPL := (hpgf u hp).1
  have hEPC := (hpgf u hp).2
  have hchange := E.address_change_vertex S.front u S.i S.j
  simp [RectConstants, edgeParams, edgeSetupResult, evalAtoms, edgeSetupAtoms,
    Atom.eval, ramStep, Store.at, Store.ofRAM, evalNat, h4,h21,h24,h25,h31,
    hf,hi',hj',haddr,hL,hC,hload,hPL,hPC,hEPL,hEPC,hrm,Nat.add_assoc]
  omega

private theorem rectConstants_after_rectangle (P : RectParams) (input : RAMInput)
    (s t : Store) (n : ℕ) (h : RectConstants P s) (hr : Run input rectangleCmd s t n) :
    RectConstants P t := by
  rcases h with ⟨h21,h24,h25,h28,h29,h31,h1,h2,h3,h4,hm⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hr.nat_frame 21 (by decide)).trans h21
  · exact (hr.nat_frame 24 (by decide)).trans h24
  · exact (hr.nat_frame 25 (by decide)).trans h25
  · exact (hr.nat_frame 28 (by decide)).trans h28
  · exact (hr.nat_frame 29 (by decide)).trans h29
  · exact (hr.nat_frame 31 (by decide)).trans h31
  · exact (hr.real_frame 1 (by decide)).trans h1
  · exact (hr.real_frame 2 (by decide)).trans h2
  · exact (hr.real_frame 3 (by decide)).trans h3
  · exact (hr.real_frame 4 (by decide)).trans h4
  · exact (hr.realMemory_frame (by decide)).trans hm

private theorem edgeFinish_core {A : InnerInput} (E : InnerEnv A) (hE : InnerLayout E)
    (S : RetrievalState) (u : ℕ) (best : ℕ × ℕ) (input : RAMInput) (s : Store)
    (hconst : RectConstants (edgeParams E S u) s)
    (hbest : RectBest (edgeParams E S u) best s)
    (h15 : s.nr 15 = u) (h9 : s.nr 9 = S.i) (h10 : s.nr 10 = S.j)
    (ha : best.1 < tickLimit A - S.i) (hb : best.2 < tickLimit A - S.j) :
    InnerCore E (crossEdge A S u best.1 best.2) (edgeFinishResult input s) := by
  rcases hconst with ⟨h21,h24,h25,h28,h29,h31,hL,hC,hPL,hPC,hm⟩
  rcases hbest with ⟨h18,h19,h49,hscore⟩
  have hpa := hE.1 best.1 (by omega)
  have hpb := hE.1 best.2 (by omega)
  simp only [edgeParams] at h21 hL hC hPL hPC hm
  rw [edgeParams_address] at h49
  simp [InnerCore, crossEdge, edgeFinishResult, evalAtoms, edgeFinishAtoms,
    Atom.eval, ramStep, Store.at, Store.ofRAM, evalNat, evalReal,
    h9,h10,h15,h18,h19,h49,h21,hL,hC,hPL,hPC,hm,hpa,hpb]

private theorem innerConstants_after_edgeMove {A : InnerInput} (E : InnerEnv A)
    (input : RAMInput) (s t : Store) (n : ℕ)
    (hc : InnerConstants E s) (hr : Run input edgeMoveCmd s t n) :
    InnerConstants E t := by
  rcases hc with ⟨h4,h5,h21,h24,h25,h30,h31,h32,h0,hm⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hr.nat_frame 4 (by decide)).trans h4
  · exact (hr.nat_frame 5 (by decide)).trans h5
  · exact (hr.nat_frame 21 (by decide)).trans h21
  · exact (hr.nat_frame 24 (by decide)).trans h24
  · exact (hr.nat_frame 25 (by decide)).trans h25
  · exact (hr.nat_frame 30 (by decide)).trans h30
  · exact (hr.nat_frame 31 (by decide)).trans h31
  · exact (hr.nat_frame 32 (by decide)).trans h32
  · exact (hr.real_frame 0 (by decide)).trans h0
  · exact (hr.realMemory_frame (by decide)).trans hm

private theorem edge_run {A : InnerInput} (E : InnerEnv A) (hE : InnerLayout E)
    (S : RetrievalState) (u : ℕ) (input : RAMInput) (s : Store)
    (hstate : InnerState E S s) (hfront : S.front ∈ activeVertices A.I)
    (hi : S.i < tickLimit A) (hj : S.j < tickLimit A)
    (hp : (buildTable A S.front S.i S.j).parent = .edge u)
    (hspace : E.scratchBase < s.nr 3) :
    ∃ (t : Store) (steps : ℕ) (best : ℕ × ℕ),
      Run input edgeCmd s t steps ∧
      best = firstMin (retrievalScore A S u) (incrementPairs A S) (0,0) ∧
      InnerState E (crossEdge A S u best.1 best.2) t ∧
      t.nr 3 = s.nr 3 - 1 ∧ steps ≤ 100 * (tickLimit A + 1) ^ 2 := by
  let P := edgeParams E S u
  let p := edgeSetupResult input s
  obtain ⟨hpc,hbase,hpu⟩ := edgeSetup_contract E hE S u input s hstate hfront hi hj hp
  obtain ⟨v,n,best,hr,hbest,hvb,hba,hbb,hn⟩ := rectangle_run_firstMin P input p hpc hbase
    (by dsimp [P,edgeParams]; omega) (by dsimp [P,edgeParams]; omega)
  have ha : best.1 < tickLimit A - S.i := hba
  have hb : best.2 < tickLimit A - S.j := hbb
  have hu : u ∈ activeVertices A.I := activeVertices_edge_left A.I u S.front
    (buildTable_parent_edge_mem A S.front S.i S.j u hp)
  have hwinner : best = firstMin (retrievalScore A S u) (incrementPairs A S) (0,0) := by
    rw [hbest]
    apply firstMin_congr_on
    · apply rectanglePairs_ne_nil <;> dsimp [P,edgeParams] <;> omega
    · intro ab hab
      have hab' := (mem_rectanglePairs P.rows P.cols ab.1 ab.2).mp hab
      exact edgeParams_score E hE S u ab.1 ab.2 hu hab'.1 hab'.2
  have hvc : RectConstants P v := rectConstants_after_rectangle P input p v n hpc hr
  have h15 : v.nr 15 = u := (hr.nat_frame 15 (by decide)).trans hpu
  have h9 : v.nr 9 = S.i := by
    rw [hr.nat_frame 9 (by decide)]
    simpa [p,edgeSetupResult,evalAtoms,edgeSetupAtoms,Atom.eval,ramStep,Store.at,Store.ofRAM]
      using hstate.2.1.2.1
  have h10 : v.nr 10 = S.j := by
    rw [hr.nat_frame 10 (by decide)]
    simpa [p,edgeSetupResult,evalAtoms,edgeSetupAtoms,Atom.eval,ramStep,Store.at,Store.ofRAM]
      using hstate.2.1.2.2.1
  let w := edgeFinishResult input v
  have hwcore : InnerCore E (crossEdge A S u best.1 best.2) w :=
    edgeFinish_core E hE S u best input v hvc hvb h15 h9 h10 ha hb
  have hsetup : Run input (.atoms edgeSetupAtoms) s p 14 := run_atoms input edgeSetupAtoms s
  have hfinish : Run input (.atoms edgeFinishAtoms) v w 12 := run_atoms input edgeFinishAtoms v
  have hmove : Run input edgeMoveCmd s w (14 + (n + 12)) :=
    Run.seq hsetup (Run.seq hr hfinish)
  have hwconst := innerConstants_after_edgeMove E input s w _ hstate.1 hmove
  have hw31 : w.nr 31 = 1 := hwconst.2.2.2.2.2.2.1
  have hprepend := prepend_run input w hw31
  let t := prependResult w
  have hlen : w.nr 2 = S.path.length :=
    (hmove.nat_frame 2 (by decide)).trans hstate.2.2.2.1.1
  have hptr : w.nr 3 = s.nr 3 := hmove.nat_frame 3 (by decide)
  have hmem : w.nm = s.nm := hmove.natMemory_frame (by decide)
  have hpath : StoresList w.nm (w.nr 3) S.path := by
    rw [hptr,hmem]
    exact hstate.2.2.2.1.2.1
  have hout := prepend_stores w S.path hlen (by omega) hpath
  have hfront' : w.nr 0 = u := hwcore.1
  have hrun : Run input edgeCmd s t (14 + (n + (12 + 3))) :=
    Run.seq hsetup (Run.seq hr (Run.seq hfinish hprepend))
  refine ⟨t,_,best,hrun,hwinner,?_,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [t,InnerConstants,prependResult] using hwconst
    · simpa [t,InnerCore,prependResult] using hwcore
    · intro a ha'
      rw [prepend_memory_frame w a (by omega), hmem]
      exact hstate.2.2.1 a ha'
    · refine ⟨?_,?_,?_⟩
      · simpa only [hfront',crossEdge] using hout.1
      · simpa only [hfront',crossEdge] using hout.2
      · change E.scratchBase ≤ w.nr 3 - 1
        omega
    · have hf50 := (hmove.nat_frame 50 (by decide)).trans hstate.2.2.2.2
      simpa [t,prependResult] using hf50
  · simp [t,prependResult,hptr]
  · have hn' := rectangle_cost_le (tickLimit A) P.rows P.cols
      (by dsimp [P,edgeParams]; omega) (by dsimp [P,edgeParams]; omega)
    nlinarith

private theorem inner_step_run {A : InnerInput} (E : InnerEnv A) (input : RAMInput)
    (S T : RetrievalState) (s : Store) (hl : InnerLayout E) (hs : InnerState E S s)
    (hv : S.front ∈ activeVertices A.I) (hstep : retrievalStep A S = some T)
    (hspace : E.scratchBase < s.nr 3) :
    ∃ t n, Run input innerStepCmd s t n ∧ InnerState E T t ∧
      t.nr 3 + graphEdgeCharge A S = s.nr 3 ∧
      n ≤ 8 + 100 * (tickLimit A + 1) ^ 2 * graphEdgeCharge A S := by
  obtain ⟨hi, hj⟩ := retrievalStep_unsaturated A S T hstep
  have hsat : ¬ (tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j) := by omega
  let p := parentLoaded input s
  have hpstate : InnerState E S p := parentLoaded_state E input S s hs
  have htag := parentLoaded_tag E input S s hl hs hv hi hj
  have htagp : p.nr 14 = parentTag (buildTable A S.front S.i S.j).parent := htag
  have hone : p.nr 31 = 1 := hpstate.1.2.2.2.2.2.2.1
  have htwo : p.nr 32 = 2 := hpstate.1.2.2.2.2.2.2.2.1
  have hload : Run input (.atom ⟨.loadNat 14 13, trivial⟩) s p 1 := Run.atom _ s
  cases hp : (buildTable A S.front S.i S.j).parent with
  | none => simp [retrievalStep, hsat, hp] at hstep
  | lengthTick =>
      have heq : T = { S with i := S.i + 1, Hlength := zValue A * S.Hlength } := by
        simpa only [retrievalStep, hsat, ↓reduceIte, hp, Option.some.injEq] using hstep.symm
      subst T
      let t := evalAtoms input lengthTickAtoms p
      refine ⟨t, 6, Run.seq hload (Run.branchTrue ?_
        (run_atoms input lengthTickAtoms p)), length_tick_state E input S p hpstate, ?_, ?_⟩
      · simp [Guard.eval, natTest, htagp, hp, parentTag, hone]
      · simp [graphEdgeCharge, hp, t, length_tick_pointer, p, parentLoaded_pointer]
      · simp [graphEdgeCharge, hp]
  | costTick =>
      have heq : T = { S with j := S.j + 1, Hcost := zValue A * S.Hcost } := by
        simpa only [retrievalStep, hsat, ↓reduceIte, hp, Option.some.injEq] using hstep.symm
      subst T
      let t := evalAtoms input costTickAtoms p
      refine ⟨t, 7, Run.seq hload (Run.branchFalse ?_ (Run.branchTrue ?_
        (run_atoms input costTickAtoms p))), cost_tick_state E input S p hpstate, ?_, ?_⟩
      · simp [Guard.eval, natTest, htagp, hp, parentTag, hone]
      · simp [Guard.eval, natTest, htagp, hp, parentTag, htwo]
      · simp [graphEdgeCharge, hp, t, cost_tick_pointer, p, parentLoaded_pointer]
      · simp [graphEdgeCharge, hp]
  | edge u =>
      obtain ⟨t, n, best, hn, hbest, ht, hptr, hcost⟩ := edge_run E hl S u input p
        hpstate hv hi hj hp (by simpa [p, parentLoaded_pointer] using hspace)
      have heq : T = crossEdge A S u best.1 best.2 := by
        cases hxs : incrementPairs A S with
        | nil => simp [retrievalStep, hsat, hp, hxs] at hstep
        | cons x xs =>
            have hw : firstMin (retrievalScore A S u) (x :: xs) x = best := by
              rw [hbest, hxs]
              simp [firstMin]
            simpa only [retrievalStep, hsat, ↓reduceIte, hp, hxs, hw, Option.some.injEq]
              using hstep.symm
      subst T
      refine ⟨t, 1 + (1 + (1 + n)),
        Run.seq hload (Run.branchFalse ?_ (Run.branchFalse ?_ hn)), ht, ?_, ?_⟩
      · simp [Guard.eval, natTest, htagp, hp, parentTag, hone]
      · simp [Guard.eval, natTest, htagp, hp, parentTag, htwo]
      · simp only [graphEdgeCharge, hp]
        rw [hptr, parentLoaded_pointer]
        omega
      · simp only [graphEdgeCharge, hp, Nat.mul_one]
        omega

private theorem retrievalStep_front_active (A : InnerInput) (S T : RetrievalState)
    (hs : S.front ∈ activeVertices A.I) (hstep : retrievalStep A S = some T) :
    T.front ∈ activeVertices A.I := by
  unfold retrievalStep at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · cases hstep
      exact hs
    · cases hstep
      exact hs
    · rename_i u hp
      split at hstep
      · contradiction
      · cases hstep
        exact activeVertices_edge_left A.I u S.front
          (buildTable_parent_edge_mem A S.front S.i S.j u hp)

private theorem inner_loop_run {A : InnerInput} (E : InnerEnv A) (input : RAMInput)
    (hl : InnerLayout E) (S U : RetrievalState) (ticks edges : ℕ)
    (trace : ActiveRetrievalTrace A S U ticks edges) :
    ∀ s, InnerState E S s → S.front ∈ activeVertices A.I →
      E.scratchBase + ticks + edges ≤ s.nr 3 →
    ∃ t n, Run input innerLoopCmd s t n ∧ t.nr 1 = 1 ∧
      InnerPath E U t ∧ InnerMemory E t ∧
      n ≤ 11 * ticks + 111 * (tickLimit A + 1) ^ 2 * edges + 7 := by
  induction trace with
  | done S hterminal =>
      intro s hs hv hspace
      let t := stopped input s
      have hstop : Run input (.atoms innerStopAtoms) s t 2 := run_atoms input innerStopAtoms s
      have hzero : s.nr 30 = 0 := hs.1.2.2.2.2.2.1
      have hone : s.nr 50 = 1 := hs.2.2.2.2
      have hfront : s.nr 0 = s.nr 5 := by
        rw [hs.2.1.1, hs.1.2.1]
        exact hterminal.1
      have htest : (Guard.nat .eq 0 5).eval s = true := by
        simp [Guard.eval, natTest, hfront]
      have hguard : (Guard.nat .lt 30 50).eval s = true := by
        simp [Guard.eval, natTest, hzero, hone]
      have hzero' : t.nr 30 = 0 := (hstop.nat_frame 30 (by decide)).trans hzero
      have hguard' : (Guard.nat .lt 30 50).eval t = false := by
        simp [Guard.eval, natTest, hzero', (stopped_flag input s).2, t]
      refine ⟨t, 7, ?_, (stopped_flag input s).1,
        stopped_path E input S s hs.2.2.2.1, stopped_memory E input s hs.2.2.1, by simp⟩
      exact Run.loopTrue hguard (Run.branchTrue htest hstop) (Run.loopFalse hguard')
  | step S T U ticks edges hsource hi hj hstep htail ih =>
      intro s hs hv hspace
      have hcounts := retrievalStep_counts A S T hstep
      have hreserve : E.scratchBase < s.nr 3 := by omega
      obtain ⟨p, k, hk, hp, hptr, hcost⟩ := inner_step_run E input S T s hl hs hv hstep hreserve
      have hnextreserve : E.scratchBase + ticks + edges ≤ p.nr 3 := by omega
      obtain ⟨t, m, hm, hflag, hpath, hmem, hbound⟩ :=
        ih p hp (retrievalStep_front_active A S T hv hstep) hnextreserve
      have hzero : s.nr 30 = 0 := hs.1.2.2.2.2.2.1
      have hone : s.nr 50 = 1 := hs.2.2.2.2
      have hguard : (Guard.nat .lt 30 50).eval s = true := by
        simp [Guard.eval, natTest, hzero, hone]
      have hfront : s.nr 0 ≠ s.nr 5 := by
        rw [hs.2.1.1, hs.1.2.1]
        exact hsource
      have htest : (Guard.nat .eq 0 5).eval s = false := by
        simp [Guard.eval, natTest, hfront]
      refine ⟨t, 1 + (1 + k) + 1 + m,
        Run.loopTrue hguard (Run.branchFalse htest hk) hm,
        hflag, hpath, hmem, ?_⟩
      have hq : 1 ≤ (tickLimit A + 1) ^ 2 := by nlinarith
      have hunit := hcounts.1
      rcases Nat.eq_zero_or_pos (graphEdgeCharge A S) with he | he
      · simp only [he, Nat.zero_add, Nat.mul_zero] at hcost ⊢
        have htick : artificialTickCharge A S = 1 := by omega
        rw [htick]
        omega
      · have hedge : graphEdgeCharge A S = 1 := by omega
        have htick : artificialTickCharge A S = 0 := by omega
        simp only [hedge, htick, Nat.zero_add, Nat.mul_one] at hcost ⊢
        nlinarith

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem queryHeader_run (input : RAMInput) (s : Store) :
    Run input queryHeaderCmd s (queryHeaderResult input s) 24 := run_atoms input queryHeaderOps s

private theorem queryHeader_values (input : RAMInput) (s : Store) :
    let t := queryHeaderResult input s
    t.nr 0 = s.nr 0 ∧ t.nr 1 = 0 ∧
    t.nr 4 = s.nm 0 ∧ t.nr 5 = s.nm 1 ∧ t.nr 6 = s.nm 2 ∧
    t.nr 7 = s.nm 3 ∧ t.nr 24 = s.nm 4 ∧ t.nr 25 = s.nm 5 ∧
    t.nr 21 = s.nm 6 ∧ t.nr 22 = s.nm 7 ∧
    t.nr 30 = 0 ∧ t.nr 31 = 1 ∧ t.nr 32 = 2 ∧ t.nr 33 = 3 ∧
    t.nr 36 = targetAddress (s.nr 0) ∧ t.nr 35 = s.nm (targetAddress (s.nr 0)) ∧
    t.rr 0 = s.rm 0 := by
  simp [queryHeaderResult,evalAtoms,queryHeaderOps,Atom.eval,Store.ofRAM,ramStep,
    Store.at,evalNat,targetAddress,show s.nr 0+s.nr 0+(s.nr 0+s.nr 0)+16=16+4*s.nr 0 by omega]

private theorem queryHeader_memory (input : RAMInput) (s : Store) :
    (queryHeaderResult input s).nm = s.nm ∧ (queryHeaderResult input s).rm = s.rm := ⟨rfl,rfl⟩

private theorem QueryReady.of_memory (I : Instance) (ε : ℝ) (snapshot : RAMState)
    (s : Store) (h : QueryReady I ε snapshot) (hnm : s.nm = snapshot.nm)
    (hrm : s.rm = snapshot.rm) : QueryReady I ε (s.at 0) := by
  simpa only [QueryReady,EncodesOutput,Store.at,hnm,hrm] using h

private theorem queryHeader_ready (input : RAMInput) (I : Instance) (ε : ℝ)
    (snapshot : RAMState) (hready : QueryReady I ε snapshot) (target : ℕ)
    (ht : target < I.graph.n) :
    ReadyRegisters I ε target (queryHeaderResult input (queryStore snapshot target)) := by
  let s := queryStore snapshot target
  let u := queryHeaderResult input s
  obtain ⟨hfront,hflag,hq,hsource,hn,hactive,hcs,hls,hpowers,hscratch,
    hzero,hone,htwo,hthree,haddr,hbranch,hratio⟩ := queryHeader_values input s
  have hfront0 : s.nr 0 = target := by simp [s,queryStore]
  have hnm : u.nm = snapshot.nm := rfl
  have hrm : u.rm = snapshot.rm := rfl
  have hencode := hready.1
  refine ⟨QueryReady.of_memory I ε snapshot u hready hnm hrm,
    hfront.trans hfront0,hflag,?_,?_,?_,?_,?_,?_,?_,?_,
    hzero,hone,htwo,hthree,?_,?_,?_⟩
  · exact hq.trans hencode.1
  · exact hsource.trans hencode.2.1
  · exact hn.trans hencode.2.2.1
  · exact hactive.trans hready.2.1
  · exact hcs.trans hready.2.2.1
  · exact hls.trans hready.2.2.2.1
  · exact hpowers
  · exact hscratch
  · simpa only [hfront0] using haddr
  · have hb' : u.nr 35 = snapshot.nm (targetAddress target) := by
      simpa only [u, s, queryStore, Function.update_self] using hbranch
    exact hb'.trans (hencode.2.2.2.2.1 target ht).1
  · exact hratio.trans hencode.2.2.2.1

private theorem innerFuel_values (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) :
    (innerFuelResult input s).nr 40 = 0 ∧
    (innerFuelResult input s).nr 41 = s.nr 7 + 1 ∧
    (innerFuelResult input s).nr 42 = 2 * s.nr 4 + 1 ∧
    (innerFuelResult input s).nr 43 = 0 := by
  simp [innerFuelResult,evalAtoms,innerFuelAtoms,Atom.eval,Store.ofRAM,ramStep,Store.at,
    evalNat,hone,two_mul]

private theorem innerPrepare_run (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) :
    Run input innerPrepareCmd s (innerPreparedStore input s) (17 + 8 * s.nr 4) := by
  have hf := run_atoms input innerFuelAtoms s
  have ha := Address.addressCmd_run input (innerFuelResult input s)
  have hh := Run.seq hf ha
  have hv := (innerFuel_values input s hone).2.2.1
  have hn : 17 + 8 * s.nr 4 = innerFuelAtoms.length +
      (8 + 4 * (innerFuelResult input s).nr 42) := by
    rw [hv]
    change 17 + 8 * s.nr 4 = 5 + (8 + 4 * (2 * s.nr 4 + 1))
    omega
  rw [hn]
  exact hh

private theorem innerPrepared_fuel (A : InnerInput) (input : RAMInput) (s : Store)
    (hone : s.nr 31 = 1) (hq : s.nr 4 = tickLimit A)
    (hactive : s.nr 7 = (activeVertices A.I).length) :
    (innerPreparedStore input s).nr 44 = retrievalFuel A := by
  rw [innerPreparedStore, Address.addressResult_value]
  obtain ⟨h0,h1,h2,h3⟩ := innerFuel_values input s hone
  rw [h0,h1,h2,h3,hq,hactive]
  simp only [retrievalFuel,Nat.zero_add,Nat.mul_zero,Nat.add_zero]
  exact Nat.mul_comm _ _

private theorem innerInitAtom_values (input : RAMInput) (s : Store) (hone : s.nr 31 = 1)
    (hsep : s.nr 36 + 1 < s.nr 22) :
    let out := evalAtoms input innerInitAtoms s
    out.nr 11 = s.nr 44 ∧ out.nr 3 = s.nr 22 + s.nr 44 ∧ out.nr 2 = 1 ∧
    out.nr 9 = 0 ∧ out.nr 10 = 0 ∧ out.nr 50 = 1 ∧
    out.nr 13 = s.nm (s.nr 36 + 1) + 4 * s.nr 0 ∧
    out.rr 1 = 1 / 8 ∧ out.rr 2 = 1 / 8 ∧
    out.nm = Function.update s.nm (s.nr 22 + s.nr 44) (s.nr 0) := by
  have hne : s.nr 36 + 1 ≠ s.nr 22 + s.nr 44 := by omega
  simp [evalAtoms,innerInitAtoms,Atom.eval,Store.ofRAM,ramStep,Store.at,evalNat,
    hone,hne,show s.nr 0+s.nr 0+(s.nr 0+s.nr 0)=4*s.nr 0 by omega]

private theorem innerInit_run (A : InnerInput) (E : InnerEnv A) (input : RAMInput)
    (s : Store) (target : ℕ) (hc : InnerConstants E s) (hfront : s.nr 0 = target)
    (hactive : s.nr 7 = (activeVertices A.I).length) (hscratch : s.nr 22 = E.scratchBase)
    (hsep : s.nr 36 + 1 < E.scratchBase) (hbase : s.nm (s.nr 36 + 1) = E.base)
    (hmem : InnerMemory E s) :
    Run input innerInitCmd s (innerInitialStore input s) (31 + 8 * tickLimit A) ∧
    InnerState E (retrievalStart target) (innerInitialStore input s) ∧
    (innerInitialStore input s).nr 3 = E.scratchBase + retrievalFuel A := by
  rcases hc with ⟨hq,hsource,hpowers,hcostStride,hlengthStride,hzero,hone,htwo,hratio,hrm⟩
  let p := innerPreparedStore input s
  have hp := innerPrepare_run input s hone
  have hp0 : p.nr 0 = target := (hp.nat_frame 0 (by decide)).trans hfront
  have hp22 : p.nr 22 = E.scratchBase := (hp.nat_frame 22 (by decide)).trans hscratch
  have hp31 : p.nr 31 = 1 := (hp.nat_frame 31 (by decide)).trans hone
  have hp36 : p.nr 36 = s.nr 36 := hp.nat_frame 36 (by decide)
  have hpnm : p.nm = s.nm := hp.natMemory_frame (by decide)
  have hp44 : p.nr 44 = retrievalFuel A := innerPrepared_fuel A input s hone hq hactive
  have hpsep : p.nr 36 + 1 < p.nr 22 := by rw [hp36,hp22]; exact hsep
  obtain ⟨h11,h3,h2,h9,h10,h50,h13,h1,h2r,hnm⟩ := innerInitAtom_values input p hp31 hpsep
  have hrun : Run input innerInitCmd s (innerInitialStore input s) (31 + 8 * tickLimit A) := by
    have hf := run_atoms input innerFuelAtoms s
    have ha := Address.addressCmd_run input (innerFuelResult input s)
    have hi := run_atoms input innerInitAtoms p
    have hh := Run.seq hf (Run.seq ha hi)
    have hv := (innerFuel_values input s hone).2.2.1
    have hn : 31 + 8 * tickLimit A = innerFuelAtoms.length +
        (8 + 4 * (innerFuelResult input s).nr 42 + innerInitAtoms.length) := by
      rw [hv,hq]
      change 31 + 8 * tickLimit A = 5 + (8 + 4 * (2 * tickLimit A + 1) + 14)
      omega
    rw [hn]
    exact hh
  have hbaseout : (innerInitialStore input s).nr 3 = E.scratchBase + retrievalFuel A := by
    exact h3.trans (congrArg₂ (· + ·) hp22 hp44)
  refine ⟨hrun,?_,hbaseout⟩
  constructor
  · refine ⟨(hrun.nat_frame 4 (by decide)).trans hq,
      (hrun.nat_frame 5 (by decide)).trans hsource,
      (hrun.nat_frame 21 (by decide)).trans hpowers,
      (hrun.nat_frame 24 (by decide)).trans hcostStride,
      (hrun.nat_frame 25 (by decide)).trans hlengthStride,
      (hrun.nat_frame 30 (by decide)).trans hzero,
      (hrun.nat_frame 31 (by decide)).trans hone,
      (hrun.nat_frame 32 (by decide)).trans htwo,
      (hrun.real_frame 0 (by decide)).trans hratio,
      (hrun.realMemory_frame (by decide)).trans hrm⟩
  · refine ⟨?_,?_,?_,h50⟩
    · refine ⟨(hrun.nat_frame 0 (by decide)).trans hfront,h9,h10,?_,h1,h2r⟩
      change (evalAtoms input innerInitAtoms p).nr 13 = E.address target 0 0
      rw [h13,hpnm,hp36,hbase,hp0]
      simp [InnerEnv.address]
    · intro a ha
      change (evalAtoms input innerInitAtoms p).nm a = E.naturalMemory a
      rw [hnm,hpnm,hp22,hp44,hp0]
      have hne : a ≠ E.scratchBase + retrievalFuel A := by omega
      rw [Function.update_of_ne hne]
      exact hmem a ha
    · refine ⟨h2,?_,?_⟩
      · intro k hk
        have hk0 : k = 0 := by simpa [retrievalStart] using hk
        subst k
        change (evalAtoms input innerInitAtoms p).nm ((innerInitialStore input s).nr 3 + 0) = target
        rw [hbaseout,hnm,hpnm,hp22,hp44,hp0]
        simp
      · rw [hbaseout]
        omega

private theorem outerInput_tickLimit (I : Instance) (ε : ℝ) (A : InnerInput)
    (hA : A ∈ outerInputs I ε) : tickLimit A = outerQ ε := by
  have hδ := (outerInputs_mem_fields I ε A hA).2.1
  simp [tickLimit,outerQ,hδ]

private theorem outerInput_zValue (I : Instance) (ε : ℝ) (A : InnerInput)
    (hA : A ∈ outerInputs I ε) : zValue A = (1+ε/8)/(1+ε/4) := by
  have hδ := (outerInputs_mem_fields I ε A hA).2.1
  unfold zValue
  rw [hδ]
  congr 1
  ring

private theorem selectedInnerEnv_layout (I : Instance) (ε : ℝ) (target r : ℕ)
    (A : InnerInput) (s : Store) (hready : ReadyRegisters I ε target s)
    (hA : (outerInputs I ε)[r]? = some A) :
    InnerLayout (selectedInnerEnv I ε r A s) := by
  have hAm := List.mem_of_getElem? hA
  have hI := (outerInputs_mem_fields I ε A hAm).1
  have hq := outerInput_tickLimit I ε A hAm
  have hz := outerInput_zValue I ε A hAm
  have hquery := hready.memory
  constructor
  · intro a ha
    have hh := hquery.2.2.2.2.2 a (by simpa [hq] using ha)
    simpa [selectedInnerEnv,hready.powers,hz,Store.at] using hh
  · intro v hv i hi j hj
    have hvI : v ∈ activeVertices I := by simpa [hI] using hv
    have hcell := hquery.1.2.2.2.2.2.2 r A hA v hvI i hi j hj
    have haddress : (selectedInnerEnv I ε r A s).address v i j = tableAddress I ε r v i j := by
      simp [selectedInnerEnv,InnerEnv.address,tableAddress,hI,hq]
    dsimp only
    rw [haddress]
    refine ⟨?_,hcell.1,hcell.2.1,hcell.2.2.1,hcell.2.2.2.2⟩
    have hrl := (List.getElem?_eq_some_iff.mp hA).choose
    have hh := table_lt_outputEnd I ε r v i j 2 hrl (activeVertices_valid I v hvI)
      (by simpa [hq] using hi) (by simpa [hq] using hj) (by omega)
    change tableAddress I ε r v i j + 2 < s.nr 22
    rw [hready.scratch]
    exact hh.trans_le hquery.2.2.2.2.1

private theorem innerInit_ready (I : Instance) (ε : ℝ) (input : RAMInput) (target r : ℕ)
    (s : Store) (ht : target < I.graph.n) (hready : ReadyRegisters I ε target s)
    (hb : answerBranch I ε target = .inner r) :
    ∃ A : InnerInput, (outerInputs I ε)[r]? = some A ∧ accepted A target ∧
      InnerLayout (selectedInnerEnv I ε r A s) ∧
      Run input innerInitCmd s (innerInitialStore input s) (31 + 8 * tickLimit A) ∧
      InnerState (selectedInnerEnv I ε r A s) (retrievalStart target) (innerInitialStore input s) ∧
      (innerInitialStore input s).nr 3 = s.nr 22 + retrievalFuel A := by
  obtain ⟨A,hA,ha⟩ := answerBranch_inner_input I ε target r hb
  have hAm := List.mem_of_getElem? hA
  have hI := (outerInputs_mem_fields I ε A hAm).1
  have hq := outerInput_tickLimit I ε A hAm
  have hz := outerInput_zValue I ε A hAm
  let E := selectedInnerEnv I ε r A s
  have hc : InnerConstants E s := by
    refine ⟨?_,?_,rfl,?_,?_,hready.zero,hready.one,hready.two,?_,rfl⟩
    · simpa [hq] using hready.limit
    · simpa [hI] using hready.source
    · simpa [hI] using hready.costStride
    · simpa [hI,hq] using hready.lengthStride
    · simpa [hz] using hready.ratio
  have hsep : s.nr 36 + 1 < E.scratchBase := by
    change s.nr 36 + 1 < s.nr 22
    rw [hready.targetAddr,hready.scratch]
    exact (target_lt_outputEnd I ε target 1 ht (by omega)).trans_le
      hready.memory.2.2.2.2.1
  have hbase : s.nm (s.nr 36 + 1) = E.base := by
    rw [hready.targetAddr]
    exact (hready.memory.1.2.2.2.2.1 target ht).2.2 r hb
  have hinit := innerInit_run A E input s target hc hready.front
    (by simpa [hI] using hready.active) rfl hsep hbase (by intro a ha; rfl)
  exact ⟨A,hA,ha,selectedInnerEnv_layout I ε target r A s hready hA,hinit.1,hinit.2.1,hinit.2.2⟩

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem inner_query_ready (I : Instance) (ε : ℝ) (input : RAMInput) (target r : ℕ)
    (s : Store) (ht : target < I.graph.n) (hready : ReadyRegisters I ε target s)
    (hb : answerBranch I ε target = .inner r) :
    ∃ P out steps, Run input innerQueryCmd s out steps ∧
      answerPath I ε target = some P ∧ out.nr 1 = 1 ∧ out.nr 2 = P.length ∧
      StoresList out.nm (out.nr 3) P ∧
      (∀ a < s.nm 7, out.nm a = s.nm a) ∧
      steps ≤ 555 * (outerQ ε + 1) ^ 2 * (P.length + 1) := by
  obtain ⟨A, hA, haccept, hlayout, hinit, hstate, hptr⟩ :=
    innerInit_ready I ε input target r s ht hready hb
  have hAm := List.mem_of_getElem? hA
  have hI := (outerInputs_mem_fields I ε A hAm).1
  have hq := outerInput_tickLimit I ε A hAm
  obtain ⟨U, hretrieve, _, _, _⟩ := deterministic_retrieval A target
    (by simpa [hI] using ht) haccept
  obtain ⟨ticks, edges, htrace, htracefuel⟩ :=
    retrievalRun_active_trace A (retrievalFuel A) (retrievalStart target) U hretrieve
  let E := selectedInnerEnv I ε r A s
  have hreserve : E.scratchBase + ticks + edges ≤ (innerInitialStore input s).nr 3 := by
    rw [hptr]
    change s.nr 22 + ticks + edges ≤ s.nr 22 + retrievalFuel A
    omega
  obtain ⟨out, n, hn, hflag, hpath, hmem, hcost⟩ :=
    inner_loop_run E input hlayout (retrievalStart target) U ticks edges htrace
      (innerInitialStore input s) hstate (accepted_active A target haccept) hreserve
  have hcounts := (htrace.forget A _ _ ticks edges).count_bounds A _ _ ticks edges
  have hterminal := htrace.terminal A _ _ ticks edges
  simp only [retrievalStart, List.length_singleton, Nat.zero_add] at hcounts
  have hticks : ticks ≤ 2 * tickLimit A := by
    unfold RetrievalTerminal at hterminal
    omega
  have hedges : edges ≤ U.path.length := by omega
  have hnumeric := retrieval_instruction_bound (tickLimit A) U.path.length ticks edges 111 hticks hedges
  have htotal : 31 + 8 * tickLimit A + n ≤
      555 * (tickLimit A + 1) ^ 2 * (U.path.length + 1) := by
    have hsmall : 31 + 8 * tickLimit A + n ≤
        111 * (tickLimit A + 1) + 111 * ticks + 111 * (tickLimit A + 1)^2 * edges +
          111 * (U.path.length + 1) := by omega
    exact hsmall.trans (by simpa using hnumeric)
  refine ⟨U.path, out, 31 + 8 * tickLimit A + n,
    Run.seq hinit hn, ?_, hflag, hpath.1, hpath.2.1, ?_, ?_⟩
  · simp [answerPath, hb, hA, hretrieve]
  · intro a ha
    exact hmem a (by simpa [E, selectedInnerEnv, hready.scratch] using ha)
  · simpa [hq] using htotal

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem pathWeight_prepend (w : ℕ → ℕ → ℝ≥0) (u v : ℕ) (P : List ℕ)
    (hp : P.head? = some v) :
    pathWeight w (u :: P) = (w u v : ℝ) + pathWeight w P := by
  cases P with
  | nil => simp at hp
  | cons a P =>
      have ha : a = v := by simpa using hp
      subst a
      exact pathWeight_cons_cons w u v P

private theorem treePath_correct (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (T : ShortestTree)
    (hs : (T I.source).distance = some 0)
    (hparent : ∀ v d, v ≠ I.source → (T v).distance = some d →
      ∃ u a, (T v).parent = some u ∧ (T u).distance = some a ∧
        d = a + (w u v : ℝ) ∧ (u,v) ∈ I.graph.edges ∧ allow u v = true ∧
        (T u).rank < (T v).rank)
    (fuel v t : ℕ) (d : ℝ) (P : List ℕ)
    (hd : (T v).distance = some d) (hr : (T v).rank < fuel)
    (hP : IsPath I.graph v t P) (hal : P.IsChain (fun u v => allow u v = true)) :
    ∃ Q, treePath I T fuel v P = some Q ∧ IsPath I.graph I.source t Q ∧
      Q.IsChain (fun u v => allow u v = true) ∧
      pathWeight w Q = d + pathWeight w P := by
  induction fuel generalizing v d P with
  | zero => omega
  | succ fuel ih =>
      by_cases hv : v = I.source
      · subst v
        have hd0 : d = 0 := by rw [hs] at hd; exact (Option.some.inj hd).symm
        refine ⟨P,?_,hP,hal,?_⟩
        · simp [treePath]
        · simp [hd0]
      · obtain ⟨u,a,hp,ha,heq,he,huv,hur⟩ := hparent v d hv hd
        have hr' : (T u).rank < fuel := by omega
        have hP' := isPath_prepend I.graph u v t P hP he
        have hal' : (u :: P).IsChain (fun a b => allow a b = true) := by
          apply hal.cons
          intro a hma
          rw [hP.1] at hma
          have hav : a = v := by symm; simpa using hma
          simpa [hav] using huv
        obtain ⟨Q,hQ,hpath,hallow,hw⟩ := ih u a (u::P) ha hr' hP' hal'
        refine ⟨Q,?_,hpath,hallow,?_⟩
        · simpa only [treePath, if_neg hv, hp, Option.bind_some] using hQ
        · rw [pathWeight_prepend w u v P hP.1] at hw
          rw [hw, heq]
          ring

private theorem readTreePath_correct_of_source (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0)
    (hs : (shortestTree I allow (fun u v => (w u v : ℝ)) I.source).distance = some 0)
    (t : ℕ) (d : ℝ)
    (hd : (shortestTree I allow (fun u v => (w u v : ℝ)) t).distance = some d) :
    ∃ P, readTreePath I (shortestTree I allow (fun u v => (w u v : ℝ))) t = some P ∧
      IsPath I.graph I.source t P ∧ P.IsChain (fun u v => allow u v = true) ∧
      pathWeight w P = d := by
  obtain ⟨P,hP,hpath,hallow,hw⟩ := treePath_correct I allow w
    (shortestTree I allow (fun u v => (w u v : ℝ))) hs
    (shortestTree_finite_parent I allow (fun u v => (w u v : ℝ)))
    (activeVertices I).length t t d [t] hd
    (shortestTree_finite_rank I allow (fun u v => (w u v : ℝ)) t d hd)
    (by simp [IsPath]) (by simp)
  refine ⟨P,?_,hpath,hallow,?_⟩
  · simpa only [readTreePath, hd] using hP
  · simpa [pathWeight] using hw

private theorem pathWeight_eq_zero_of_chain (w : ℕ → ℕ → ℝ≥0) (P : List ℕ)
    (h : P.IsChain (fun u v => w u v = 0)) : pathWeight w P = 0 := by
  induction P with
  | nil => simp [pathWeight]
  | cons a P ih =>
      cases P with
      | nil => simp [pathWeight]
      | cons b P =>
          rw [pathWeight_cons_cons, h.rel, ih h.tail]
          simp

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

private theorem zeroLengthTree_source_zero (I : Instance) :
    (zeroLengthTree I I.source).distance = some 0 :=
  shortestTree_source_zero I _ _ (fun u v => (I.cost u v).coe_nonneg)

private theorem zeroBudgetTree_source_zero (I : Instance) :
    (zeroBudgetTree I I.source).distance = some 0 :=
  shortestTree_source_zero I _ _ (fun u v => (I.length u v).coe_nonneg)

private theorem zeroLengthTree_path (I : Instance) (t : ℕ) (d : ℝ)
    (hd : (zeroLengthTree I t).distance = some d) :
    ∃ P, readTreePath I (zeroLengthTree I) t = some P ∧
      IsPath I.graph I.source t P ∧ pathWeight I.length P = 0 ∧
      pathWeight I.cost P = d := by
  obtain ⟨P,hP,hpath,hallow,hw⟩ := readTreePath_correct_of_source I
    (fun u v => decide (I.length u v = 0)) I.cost (zeroLengthTree_source_zero I) t d hd
  refine ⟨P,hP,hpath,?_,hw⟩
  apply pathWeight_eq_zero_of_chain
  simpa only [decide_eq_true_eq] using hallow

private theorem zeroBudgetTree_path (I : Instance) (t : ℕ) (d : ℝ)
    (hd : (zeroBudgetTree I t).distance = some d) :
    ∃ P, readTreePath I (zeroBudgetTree I) t = some P ∧
      IsPath I.graph I.source t P ∧ pathWeight I.cost P = 0 ∧
      pathWeight I.length P = d := by
  obtain ⟨P,hP,hpath,hallow,hw⟩ := readTreePath_correct_of_source I
    (fun u v => decide (I.cost u v = 0)) I.length (zeroBudgetTree_source_zero I) t d hd
  refine ⟨P,hP,hpath,?_,hw⟩
  apply pathWeight_eq_zero_of_chain
  simpa only [decide_eq_true_eq] using hallow

private theorem zeroLengthTree_read_valid (I : Instance) (t : ℕ) (P : List ℕ)
    (hP : readTreePath I (zeroLengthTree I) t = some P) :
    IsPath I.graph I.source t P ∧ pathWeight I.length P = 0 ∧
      (zeroLengthTree I t).distance = some (pathWeight I.cost P) := by
  cases hd : (zeroLengthTree I t).distance with
  | none => simp [readTreePath, hd] at hP
  | some d =>
      obtain ⟨Q,hQ,hpath,hzero,hw⟩ := zeroLengthTree_path I t d hd
      have heq : Q = P := Option.some.inj (hQ.symm.trans hP)
      subst Q
      exact ⟨hpath,hzero,by rw [hw]⟩

private theorem zeroBudgetTree_read_valid (I : Instance) (t : ℕ) (P : List ℕ)
    (hP : readTreePath I (zeroBudgetTree I) t = some P) :
    IsPath I.graph I.source t P ∧ pathWeight I.cost P = 0 ∧
      (zeroBudgetTree I t).distance = some (pathWeight I.length P) := by
  cases hd : (zeroBudgetTree I t).distance with
  | none => simp [readTreePath, hd] at hP
  | some d =>
      obtain ⟨Q,hQ,hpath,hzero,hw⟩ := zeroBudgetTree_path I t d hd
      have heq : Q = P := Option.some.inj (hQ.symm.trans hP)
      subst Q
      exact ⟨hpath,hzero,by rw [hw]⟩

private theorem zeroLengthTree_source_path (I : Instance) :
    readTreePath I (zeroLengthTree I) I.source = some [I.source] := by
  rw [readTreePath, zeroLengthTree_source_zero]
  cases (activeVertices I).length <;> simp [treePath]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem tree_read_run (input : RAMInput) (s : Store) (u k slot : ℕ)
    (hone : s.nr 31 = 1) (hf : s.nr 7 = k + 1) (hslot : s.nr 35 + 1 = slot)
    (hparent : s.nm (targetAddress (s.nr 0) + slot) = u + 1) :
    Run input (.atoms treeReadAtoms) s (treeReadResult s u k slot) 9 := by
  have haddr : (s.nr 0 + s.nr 0 + (s.nr 0 + s.nr 0) + 16 + s.nr 35 + 1) =
      targetAddress (s.nr 0) + slot := by unfold targetAddress; omega
  have heval : evalAtoms input treeReadAtoms s = treeReadResult s u k slot := by
    apply Store.ext <;> funext r <;>
      simp [evalAtoms, treeReadAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
        evalNat, treeReadResult, hone, hf, haddr, hparent, Function.update_apply]
    all_goals split_ifs <;> simp_all
  have hrun := run_atoms input treeReadAtoms s
  rw [heval] at hrun
  exact hrun

private theorem tree_advance_run (input : RAMInput) (s : Store) (u k slot : ℕ)
    (hone : s.nr 31 = 1) (hf : s.nr 7 = k + 1) (hslot : s.nr 35 + 1 = slot)
    (hparent : s.nm (targetAddress (s.nr 0) + slot) = u + 1) :
    Run input treeAdvanceCmd s (treeAdvanceResult s u k slot) 12 := by
  exact Run.seq (tree_read_run input s u k slot hone hf hslot hparent)
    (prepend_run input _ (by simpa [treeReadResult] using hone))

private theorem tree_stop_run (input : RAMInput) (s : Store) :
    Run input treeStopCmd s (treeStopResult s) 1 := by
  exact Run.atom _ _

private theorem tree_init_run (input : RAMInput) (s : Store) :
    Run input (.atoms treeInitAtoms) s (treeInitResult s) 5 := by
  have heval : evalAtoms input treeInitAtoms s = treeInitResult s := by
    apply Store.ext <;>
      simp [evalAtoms, treeInitAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
        evalNat, treeInitResult]
  have hrun := run_atoms input treeInitAtoms s
  rw [heval] at hrun
  exact hrun

private theorem treeAdvance_state (I : Instance) (T : ShortestTree) (slot scratch k v u : ℕ)
    (P : List ℕ) (s : Store) (h : TreeLoopState I T slot scratch (k+1) v P s)
    (haddr : ∀ v ∈ activeVertices I, targetAddress v + slot < scratch) :
    TreeLoopState I T slot scratch k u (u::P) (treeAdvanceResult s u k slot) := by
  have hbase : 0 < s.nr 3 := by have hs := h.space; omega
  have hprep := prepend_stores (treeReadResult s u k slot) P
    (by simpa [treeReadResult] using h.length_eq) (by simpa [treeReadResult] using hbase)
    (by simpa [treeReadResult] using h.path)
  constructor
  · simp [treeAdvanceResult, prependResult, treeReadResult]
  · simpa [treeAdvanceResult, prependResult, treeReadResult] using h.source
  · simp [treeAdvanceResult, prependResult, treeReadResult]
  · simpa [treeAdvanceResult, prependResult, treeReadResult] using h.slot_eq
  · simpa [treeAdvanceResult, prependResult, treeReadResult] using h.zero
  · simpa [treeAdvanceResult, prependResult, treeReadResult] using h.one
  · have hs := h.space
    have hb : scratch + k ≤ s.nr 3 - 1 := by omega
    simpa [treeAdvanceResult, prependResult, treeReadResult] using hb
  · simpa [treeAdvanceResult, treeReadResult] using hprep.1
  · simpa [treeAdvanceResult, treeReadResult] using hprep.2
  · intro w hw
    have hlt : targetAddress w + slot < s.nr 3 - 1 := by
      have ha := haddr w hw
      have hs := h.space
      omega
    simpa [treeAdvanceResult, prependResult, treeReadResult, ne_of_lt hlt] using h.parents w hw

private theorem treeAdvance_frame (s : Store) (u k slot scratch : ℕ)
    (hspace : scratch + (k+1) ≤ s.nr 3) (a : ℕ) (ha : a < scratch) :
    (treeAdvanceResult s u k slot).nm a = s.nm a := by
  have hlt : a < s.nr 3 - 1 := by omega
  simp [treeAdvanceResult, prependResult, treeReadResult, ne_of_lt hlt]

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

private theorem treeRun_tree_outside (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (v : ℕ) (hv : v ∉ S.queue) :
    (treeRun I allow w n S).tree v = S.tree v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [treeRun_succ,treePop_outside I allow w _ v]
      · exact ih
      · intro hm
        exact hv ((treeRun_queue_sublist I allow w n S).subset hm)

private theorem shortestTree_inactive (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (hv : v ∉ activeVertices I) :
    shortestTree I allow w v = ⟨none,none,0⟩ := by
  rw [shortestTree_eq_treeRun,
    treeRun_tree_outside I allow w _ (treeInitial I) v hv]
  have hvs : v ≠ I.source := by
    intro he
    apply hv
    simpa only [he] using activeVertices_source_mem I
  simp [treeInitial,hvs]

private theorem shortestTree_inactive_parent (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (hv : v ∉ activeVertices I) :
    (shortestTree I allow w v).parent=none := by
  rw [shortestTree_inactive I allow w v hv]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem treePath_loop_run (input : RAMInput) (I : Instance) (T : ShortestTree)
    (slot scratch : ℕ)
    (hactive : ∀ v d, (T v).distance = some d → v ∈ activeVertices I)
    (hparent : ∀ v d, v ≠ I.source → (T v).distance = some d →
      ∃ u a, (T v).parent = some u ∧ (T u).distance = some a)
    (haddr : ∀ v ∈ activeVertices I, targetAddress v + slot < scratch)
    (fuel v : ℕ) (d : ℝ) (P Q : List ℕ) (s : Store)
    (hd : (T v).distance = some d)
    (hpath : treePath I T fuel v P = some Q)
    (hs : TreeLoopState I T slot scratch fuel v P s) :
    ∃ out n, Run input treeLoop s out n ∧ out.nr 2 = Q.length ∧
      StoresList out.nm (out.nr 3) Q ∧
      (∀ a < scratch, out.nm a = s.nm a) ∧
      n + 15*P.length ≤ 15*Q.length + 6 := by
  induction fuel generalizing v d P s with
  | zero =>
      have hPQ : P = Q := by
        simp only [treePath] at hpath
        split at hpath
        · exact Option.some.inj hpath
        · contradiction
      subst Q
      exact ⟨s,1,Run.loopFalse (by simp [Guard.eval,natTest,hs.zero,hs.fuel_eq]),
        hs.length_eq,hs.path,by intros; rfl,by omega⟩
  | succ fuel ih =>
      have hg : (Guard.nat .lt 30 7).eval s = true := by
        simp [Guard.eval,natTest,hs.zero,hs.fuel_eq]
      by_cases hv : v = I.source
      · have hPQ : P = Q := by simpa [treePath,hv] using hpath
        subst Q
        let stopped := treeStopResult s
        have hb : Run input treeBody s stopped 3 :=
          Run.branchTrue (by simp [Guard.eval,natTest,hs.front,hs.source,hv]) (tree_stop_run input s)
        have hx : Run input treeLoop stopped stopped 1 :=
          Run.loopFalse (by simp [Guard.eval,natTest,stopped,treeStopResult,hs.zero])
        refine ⟨stopped,6,?_,?_,?_,?_,by omega⟩
        · exact Run.loopTrue hg hb hx
        · simpa [stopped,treeStopResult] using hs.length_eq
        · simpa [stopped,treeStopResult] using hs.path
        · intros; rfl
      · obtain ⟨u,a,hpu,hdu⟩ := hparent v d hv hd
        have htail : treePath I T fuel u (u::P) = some Q := by
          simpa [treePath,hv,hpu] using hpath
        have hm : s.nm (targetAddress (s.nr 0)+slot) = u+1 := by
          rw [hs.front,hs.parents v (hactive v d hd),hpu]
          rfl
        have ha := tree_advance_run input s u fuel slot hs.one hs.fuel_eq hs.slot_eq hm
        have hstate := treeAdvance_state I T slot scratch fuel v u P s hs haddr
        obtain ⟨out,n,hrun,hlen,hlist,hframe,hn⟩ := ih u a (u::P)
          (treeAdvanceResult s u fuel slot) hdu htail hstate
        have hb : Run input treeBody s (treeAdvanceResult s u fuel slot) 13 :=
          Run.branchFalse (by simp [Guard.eval,natTest,hs.front,hs.source,hv]) ha
        refine ⟨out,15+n,?_,hlen,hlist,?_,?_⟩
        · exact Run.loopTrue hg hb hrun
        · intro b hb
          exact (hframe b hb).trans (treeAdvance_frame s u fuel slot scratch hs.space b hb)
        · simp only [List.length_cons] at hn
          omega

private theorem treeQuery_run (input : RAMInput) (I : Instance) (T : ShortestTree)
    (scratch slot v : ℕ) (P : List ℕ) (s : Store)
    (hactive : ∀ v d, (T v).distance = some d → v ∈ activeVertices I)
    (hparent : ∀ v d, v ≠ I.source → (T v).distance = some d →
      ∃ u a, (T v).parent = some u ∧ (T u).distance = some a)
    (hP : readTreePath I T v = some P)
    (hv : s.nr 0 = v) (hsource : s.nr 5 = I.source)
    (hf : s.nr 7 = (activeVertices I).length) (hslot : s.nr 35+1=slot)
    (hscratch : s.nr 22 = scratch)
    (haddr : ∀ v ∈ activeVertices I, targetAddress v+slot < scratch)
    (hmem : TreeParentMemory I T slot s.nm) :
    ∃ out n, Run input treeQueryCmd s out n ∧ out.nr 1 = 1 ∧
      out.nr 2 = P.length ∧ StoresList out.nm (out.nr 3) P ∧
      (∀ a < scratch, out.nm a = s.nm a) ∧ n ≤ 20*(P.length+1) := by
  cases hd : (T v).distance with
  | none => simp [readTreePath,hd] at hP
  | some d =>
      have hpath : treePath I T (activeVertices I).length v [v] = some P := by
        simpa only [readTreePath,hd] using hP
      let p := treeInitResult s
      have hp := tree_init_run input s
      have hstate : TreeLoopState I T slot scratch (activeVertices I).length v [v] p := by
        constructor
        · simpa [p,treeInitResult] using hv
        · simpa [p,treeInitResult] using hsource
        · simpa [p,treeInitResult] using hf
        · simpa [p,treeInitResult] using hslot
        · simp [p,treeInitResult]
        · simp [p,treeInitResult]
        · simp [p,treeInitResult,hscratch,hf]
        · simp [p,treeInitResult]
        · intro k hk
          have hk0 : k = 0 := by simpa using hk
          subst k
          simp [p,treeInitResult,hv]
        · intro w hw
          have hne : targetAddress w+slot ≠ s.nr 22+s.nr 7 := by
            have := haddr w hw
            rw [hscratch,hf]
            omega
          simpa [p,treeInitResult,hne] using hmem w hw
      obtain ⟨t,n,ht,hlen,hlist,hframe,hn⟩ := treePath_loop_run input I T slot scratch
        hactive hparent haddr (activeVertices I).length v d [v] P p hd hpath hstate
      let out := Atom.eval (⟨.natConst 1 1,trivial⟩ : Atom) input t
      have hdone : Run input (.atom ⟨.natConst 1 1,trivial⟩) t out 1 := Run.atom _ _
      refine ⟨out,5+(n+1),Run.seq hp (Run.seq ht hdone),?_,?_,?_,?_,?_⟩
      · simp [out,Atom.eval,Store.ofRAM,Store.at,ramStep]
      · simpa [out,Atom.eval,Store.ofRAM,Store.at,ramStep] using hlen
      · simpa [out,Atom.eval,Store.ofRAM,Store.at,ramStep] using hlist
      · intro a ha
        change t.nm a = s.nm a
        rw [hframe a ha]
        have hne : a ≠ s.nr 22+s.nr 7 := by rw [hscratch,hf]; omega
        simp [p,treeInitResult,hne]
      · simp only [List.length_cons,List.length_nil] at hn
        omega

private theorem shortestTree_query_run (input : RAMInput) (I : Instance)
    (allow : ℕ → ℕ → Bool) (w : ℕ → ℕ → ℝ)
    (scratch slot v : ℕ) (P : List ℕ) (s : Store)
    (hP : readTreePath I (shortestTree I allow w) v = some P)
    (hv : s.nr 0 = v) (hsource : s.nr 5 = I.source)
    (hf : s.nr 7 = (activeVertices I).length) (hslot : s.nr 35+1=slot)
    (hscratch : s.nr 22 = scratch)
    (haddr : ∀ v ∈ activeVertices I, targetAddress v+slot < scratch)
    (hmem : TreeParentMemory I (shortestTree I allow w) slot s.nm) :
    ∃ out n, Run input treeQueryCmd s out n ∧ out.nr 1 = 1 ∧
      out.nr 2 = P.length ∧ StoresList out.nm (out.nr 3) P ∧
      (∀ a < scratch, out.nm a = s.nm a) ∧ n ≤ 20*(P.length+1) := by
  apply treeQuery_run input I (shortestTree I allow w) scratch slot v P s
    (fun u d hd => ?_) (fun u d hu hd => ?_) hP hv hsource hf hslot hscratch haddr hmem
  · by_contra hu
    rw [shortestTree_inactive I allow w u hu] at hd
    contradiction
  · obtain ⟨p,a,hp,ha,_⟩ := shortestTree_finite_parent I allow w u d hu hd
    exact ⟨p,a,hp,ha⟩

private theorem zeroLengthTree_query_run (input : RAMInput) (I : Instance)
    (scratch v : ℕ) (P : List ℕ) (s : Store)
    (hP : readTreePath I (zeroLengthTree I) v = some P)
    (hv : s.nr 0 = v) (hsource : s.nr 5 = I.source)
    (hf : s.nr 7 = (activeVertices I).length) (hbranch : s.nr 35 = 1)
    (hscratch : s.nr 22 = scratch)
    (haddr : ∀ v ∈ activeVertices I, targetAddress v+2 < scratch)
    (hmem : TreeParentMemory I (zeroLengthTree I) 2 s.nm) :
    ∃ out n, Run input treeQueryCmd s out n ∧ out.nr 1 = 1 ∧
      out.nr 2 = P.length ∧ StoresList out.nm (out.nr 3) P ∧
      (∀ a < scratch, out.nm a = s.nm a) ∧ n ≤ 20*(P.length+1) := by
  unfold zeroLengthTree at hP hmem
  exact shortestTree_query_run input I _ _ scratch 2 v P s hP hv hsource hf
    (by omega) hscratch haddr hmem

private theorem zeroBudgetTree_query_run (input : RAMInput) (I : Instance)
    (scratch v : ℕ) (P : List ℕ) (s : Store)
    (hP : readTreePath I (zeroBudgetTree I) v = some P)
    (hv : s.nr 0 = v) (hsource : s.nr 5 = I.source)
    (hf : s.nr 7 = (activeVertices I).length) (hbranch : s.nr 35 = 2)
    (hscratch : s.nr 22 = scratch)
    (haddr : ∀ v ∈ activeVertices I, targetAddress v+3 < scratch)
    (hmem : TreeParentMemory I (zeroBudgetTree I) 3 s.nm) :
    ∃ out n, Run input treeQueryCmd s out n ∧ out.nr 1 = 1 ∧
      out.nr 2 = P.length ∧ StoresList out.nm (out.nr 3) P ∧
      (∀ a < scratch, out.nm a = s.nm a) ∧ n ≤ 20*(P.length+1) := by
  unfold zeroBudgetTree at hP hmem
  exact shortestTree_query_run input I _ _ scratch 3 v P s hP hv hsource hf
    (by omega) hscratch haddr hmem

private theorem treeQuery_output_path (s : Store) (P : List ℕ)
    (hflag : s.nr 1=1) (hlen : s.nr 2=P.length)
    (hlist : StoresList s.nm (s.nr 3) P) (pc : ℕ) : queryPath (s.at pc)=some P := by
  simp only [queryPath,Store.at,hflag,show ¬(1:ℕ)=0 by decide,if_false,hlen]
  exact congrArg some (storesList_map s.nm (s.nr 3) P hlist)

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem QueryReady.tree_scratch_bound (I : Instance) (ε : ℝ) (snapshot : RAMState)
    (h : QueryReady I ε snapshot) (v off : ℕ) (hv : v ∈ activeVertices I) (hoff : off < 4) :
    targetAddress v + off < snapshot.nm 7 :=
  (target_lt_outputEnd I ε v off (activeVertices_valid I v hv) hoff).trans_le h.2.2.2.2.1

private theorem QueryReady.zeroLength_parent_memory (I : Instance) (ε : ℝ) (snapshot : RAMState)
    (h : QueryReady I ε snapshot) : TreeParentMemory I (zeroLengthTree I) 2 snapshot.nm := by
  intro v hv
  exact (h.1.2.2.2.2.2.1 v hv).1

private theorem QueryReady.zeroBudget_parent_memory (I : Instance) (ε : ℝ) (snapshot : RAMState)
    (h : QueryReady I ε snapshot) : TreeParentMemory I (zeroBudgetTree I) 3 snapshot.nm := by
  intro v hv
  exact (h.1.2.2.2.2.2.1 v hv).2

private theorem zeroLength_query_ready (input : RAMInput) (I : Instance) (ε : ℝ)
    (snapshot : RAMState) (s : Store) (v : ℕ) (hready : QueryReady I ε snapshot)
    (hb : answerBranch I ε v = .zeroLength)
    (hfront : s.nr 0 = v) (hsource : s.nr 5 = I.source)
    (hf : s.nr 7 = (activeVertices I).length) (hbranch : s.nr 35 = 1)
    (hscratch : s.nr 22 = snapshot.nm 7) (hmem : s.nm = snapshot.nm) :
    ∃ P out steps, Run input treeQueryCmd s out steps ∧ answerPath I ε v = some P ∧
      out.nr 1 = 1 ∧ out.nr 2 = P.length ∧ StoresList out.nm (out.nr 3) P ∧
      (∀ a < snapshot.nm 7, out.nm a = snapshot.nm a) ∧
      steps ≤ 20 * (P.length + 1) := by
  have hpath : ∃ P, readTreePath I (zeroLengthTree I) v = some P := by
    rcases answerBranch_zeroLength_spec I ε v hb with hs | ⟨d,hd,_⟩
    · exact ⟨[I.source], by simpa [hs] using zeroLengthTree_source_path I⟩
    · obtain ⟨P,hP,_,_,_⟩ := zeroLengthTree_path I v d hd
      exact ⟨P,hP⟩
  obtain ⟨P,hP⟩ := hpath
  have hparents : TreeParentMemory I (zeroLengthTree I) 2 s.nm := by
    rw [hmem]
    exact hready.zeroLength_parent_memory I ε snapshot
  obtain ⟨out,steps,hrun,hflag,hlen,hlist,hframe,hcost⟩ :=
    zeroLengthTree_query_run input I (snapshot.nm 7) v P s hP hfront hsource hf hbranch
      hscratch (fun u hu => hready.tree_scratch_bound I ε snapshot u 2 hu (by omega)) hparents
  exact ⟨P,out,steps,hrun,by simpa [answerPath,hb] using hP,hflag,hlen,hlist,
    by intro a ha; rw [hframe a ha,hmem],hcost⟩

private theorem zeroBudget_query_ready (input : RAMInput) (I : Instance) (ε : ℝ)
    (snapshot : RAMState) (s : Store) (v : ℕ) (hready : QueryReady I ε snapshot)
    (hb : answerBranch I ε v = .zeroBudget)
    (hfront : s.nr 0 = v) (hsource : s.nr 5 = I.source)
    (hf : s.nr 7 = (activeVertices I).length) (hbranch : s.nr 35 = 2)
    (hscratch : s.nr 22 = snapshot.nm 7) (hmem : s.nm = snapshot.nm) :
    ∃ P out steps, Run input treeQueryCmd s out steps ∧ answerPath I ε v = some P ∧
      out.nr 1 = 1 ∧ out.nr 2 = P.length ∧ StoresList out.nm (out.nr 3) P ∧
      (∀ a < snapshot.nm 7, out.nm a = snapshot.nm a) ∧
      steps ≤ 20 * (P.length + 1) := by
  have hsome := (answerBranch_zeroBudget_spec I ε v hb).2
  obtain ⟨d,hd⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨P,hP,_,_,_⟩ := zeroBudgetTree_path I v d hd
  have hparents : TreeParentMemory I (zeroBudgetTree I) 3 s.nm := by
    rw [hmem]
    exact hready.zeroBudget_parent_memory I ε snapshot
  obtain ⟨out,steps,hrun,hflag,hlen,hlist,hframe,hcost⟩ :=
    zeroBudgetTree_query_run input I (snapshot.nm 7) v P s hP hfront hsource hf hbranch
      hscratch (fun u hu => hready.tree_scratch_bound I ε snapshot u 3 hu (by omega)) hparents
  exact ⟨P,out,steps,hrun,by simpa [answerPath,hb] using hP,hflag,hlen,hlist,
    by intro a ha; rw [hframe a ha,hmem],hcost⟩

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem dispatch_absent (input : RAMInput) (s : Store) (h : s.nr 35 = s.nr 30) :
    Run input queryDispatchCmd s s 2 := by
  exact Run.branchTrue (by simp [Guard.eval,natTest,h]) (Run.skip s)

private theorem dispatch_tree (input : RAMInput) (s out : Store) (n : ℕ)
    (h0 : s.nr 35 ≠ s.nr 30) (h3 : s.nr 35 < s.nr 33)
    (hrun : Run input treeQueryCmd s out n) :
    Run input queryDispatchCmd s out (n+3) := by
  have h := Run.branchFalse
    (a := Cmd.skip) (by simp [Guard.eval,natTest,h0] : (Guard.nat .eq 35 30).eval s = false)
    (Run.branchTrue (b := innerQueryCmd)
      (by simp [Guard.eval,natTest,h3] : (Guard.nat .lt 35 33).eval s = true) hrun)
  simpa only [queryDispatchCmd,show n+3=1+(1+n+1) by omega] using h

private theorem dispatch_inner (input : RAMInput) (s out : Store) (n : ℕ)
    (h0 : s.nr 35 ≠ s.nr 30) (h3 : ¬s.nr 35 < s.nr 33)
    (hrun : Run input innerQueryCmd s out n) :
    Run input queryDispatchCmd s out (n+2) := by
  have h := Run.branchFalse
    (a := Cmd.skip) (by simp [Guard.eval,natTest,h0] : (Guard.nat .eq 35 30).eval s = false)
    (Run.branchFalse (a := treeQueryCmd)
      (by simp [Guard.eval,natTest,h3] : (Guard.nat .lt 35 33).eval s = false) hrun)
  simpa only [queryDispatchCmd,show n+2=1+(1+n) by omega] using h

private theorem query_factor_one (q p : ℕ) : 1 ≤ (q+1)^2*(p+1) := by
  have hq : 1 ≤ (q+1)^2 := Nat.succ_le_of_lt (pow_pos (by omega : 0 < q+1) 2)
  simpa using Nat.mul_le_mul hq (show 1 ≤ p+1 by omega)

private theorem query_tree_cost (q p n : ℕ) (hn : n ≤ 20*(p+1)) :
    24+(n+3) ≤ 600*(q+1)^2*(p+1) := by
  have hq : 1 ≤ (q+1)^2 := Nat.succ_le_of_lt (pow_pos (by omega : 0 < q+1) 2)
  have hp : p+1 ≤ (q+1)^2*(p+1) := by
    simpa using Nat.mul_le_mul_right (p+1) hq
  have hm := Nat.mul_le_mul_left 20 hp
  have hf := query_factor_one q p
  have he : 600*(q+1)^2*(p+1) = 600*((q+1)^2*(p+1)) := by ring
  rw [he]
  omega

private theorem queryCmd_run (input : RAMInput) (I : Instance) (ε : ℝ)
    (snapshot : RAMState) (hready : QueryReady I ε snapshot) (target : ℕ)
    (ht : target < I.graph.n) :
    ∃ out steps, Run input queryCmd (queryStore snapshot target) out steps ∧
      queryPath (out.at 0) = answerPath I ε target ∧
      steps ≤ 600*(outerQ ε+1)^2*(((answerPath I ε target).getD []).length+1) := by
  let s := queryHeaderResult input (queryStore snapshot target)
  have hs := queryHeader_ready input I ε snapshot hready target ht
  change ReadyRegisters I ε target s at hs
  have hh : Run input queryHeaderCmd (queryStore snapshot target) s 24 :=
    queryHeader_run input _
  have hz := hs.zero
  have hthree := hs.three
  cases hb : answerBranch I ε target with
  | absent =>
      have htag : s.nr 35 = 0 := by simpa [hb,branchTag] using hs.branch
      refine ⟨s,26,Run.seq hh (dispatch_absent input s (by omega)),?_,?_⟩
      · simp [queryPath,Store.at,hs.absentFlag,answerPath,hb]
      · simp only [answerPath,hb,Option.getD_none,List.length_nil,Nat.zero_add]
        have hf := query_factor_one (outerQ ε) 0
        nlinarith
  | zeroLength =>
      have htag : s.nr 35 = 1 := by simpa [hb,branchTag] using hs.branch
      obtain ⟨P,out,n,hrun,hpath,hflag,hlen,hlist,_,hcost⟩ :=
        zeroLength_query_ready input I ε (s.at 0) s target hs.memory hb
          hs.front hs.source hs.active htag hs.scratch rfl
      refine ⟨out,24+(n+3),Run.seq hh (dispatch_tree input s out n
        (by omega) (by omega) hrun),?_,?_⟩
      · rw [hpath]
        exact treeQuery_output_path out P hflag hlen hlist 0
      · simpa only [hpath,Option.getD_some] using query_tree_cost (outerQ ε) P.length n hcost
  | zeroBudget =>
      have htag : s.nr 35 = 2 := by simpa [hb,branchTag] using hs.branch
      obtain ⟨P,out,n,hrun,hpath,hflag,hlen,hlist,_,hcost⟩ :=
        zeroBudget_query_ready input I ε (s.at 0) s target hs.memory hb
          hs.front hs.source hs.active htag hs.scratch rfl
      refine ⟨out,24+(n+3),Run.seq hh (dispatch_tree input s out n
        (by omega) (by omega) hrun),?_,?_⟩
      · rw [hpath]
        exact treeQuery_output_path out P hflag hlen hlist 0
      · simpa only [hpath,Option.getD_some] using query_tree_cost (outerQ ε) P.length n hcost
  | inner r =>
      have htag : s.nr 35 = 3 := by simpa [hb,branchTag] using hs.branch
      obtain ⟨P,out,n,hrun,hpath,hflag,hlen,hlist,_,hcost⟩ :=
        inner_query_ready I ε input target r s ht hs hb
      refine ⟨out,24+(n+2),Run.seq hh (dispatch_inner input s out n
        (by omega) (by omega) hrun),?_,?_⟩
      · rw [hpath]
        exact treeQuery_output_path out P hflag hlen hlist 0
      · rw [hpath]
        simp only [Option.getD_some]
        have hf := query_factor_one (outerQ ε) P.length
        have he : 600*(outerQ ε+1)^2*(P.length+1) =
            600*((outerQ ε+1)^2*(P.length+1)) := by ring
        have he' : 555*(outerQ ε+1)^2*(P.length+1) =
            555*((outerQ ε+1)^2*(P.length+1)) := by ring
        rw [he' ] at hcost
        rw [he]
        omega

private theorem queryProgram_correct (I : Instance) (ε : ℝ) (snapshot : RAMState)
    (hready : QueryReady I ε snapshot) (target : ℕ) (ht : target < I.graph.n) :
    ∃ steps final,
      Execution queryProgram (encodeInput I ε) (queryStart snapshot target) final steps ∧
      queryPath final = answerPath I ε target ∧
      (steps : ℝ) ≤ 601 * retrievalScale ε (answerPath I ε target) := by
  obtain ⟨out,n,hrun,hpath,hcost⟩ := queryCmd_run (encodeInput I ε) I ε snapshot hready target ht
  obtain ⟨steps,final,hexec,hsteps,hstore⟩ := compiled_query snapshot target hrun
  have hnr : final.nr = out.nr := congrArg Store.nr hstore
  have hnm : final.nm = out.nm := congrArg Store.nm hstore
  refine ⟨steps,final,hexec,?_,?_⟩
  · calc
      queryPath final = queryPath (out.at 0) := by
        unfold queryPath
        rw [hnr,hnm]
        rfl
      _ = answerPath I ε target := hpath
  · have hf := query_factor_one (outerQ ε) ((answerPath I ε target).getD []).length
    have hb : steps ≤ 601*(outerQ ε+1)^2*(((answerPath I ε target).getD []).length+1) := by
      have he : 600*(outerQ ε+1)^2*(((answerPath I ε target).getD []).length+1) =
          600*((outerQ ε+1)^2*(((answerPath I ε target).getD []).length+1)) := by ring
      have he' : 601*(outerQ ε+1)^2*(((answerPath I ε target).getD []).length+1) =
          601*((outerQ ε+1)^2*(((answerPath I ε target).getD []).length+1)) := by ring
      rw [he] at hcost
      rw [he']
      omega
    unfold retrievalScale
    rw [Nat.mul_assoc] at hb
    exact_mod_cast hb

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal BigOperators
namespace NearLinearRSP.TwoResources.Completeness

private theorem quadratic_nonneg (q M i r : ℝ) (hr : 0 ≤ r) :
    0 ≤ quadratic q M i r := by
  unfold quadratic
  positivity

private theorem quadratic_saturated (q M i r : ℝ) (hM : M < q)
    (hi : q ≤ i) (hr : 0 ≤ r) : 1 ≤ quadratic q M i r := by
  unfold quadratic
  apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hM))).mpr
  have hx : 0 ≤ i + r - q := by linarith
  nlinarith [sq_nonneg (i + r - q), mul_nonneg (sub_nonneg.mpr hM.le) hx]

private theorem quadratic_initial (q M : ℝ) : quadratic q M 0 M = M / (q - M) ^ 2 := by
  simp [quadratic]

private theorem quadratic_hasSum (q M i r : ℝ) (e : ℝ≥0) :
    HasSum (fun a : ℕ => RSP.Tails.mass e a * quadratic q M (i + a) r)
      (quadratic q M i (r + e)) := by
  have h := ((RSP.Tails.secondMoment_hasSum e).add
    ((RSP.Tails.firstMoment_hasSum e).mul_right (2 * (i + r - M)))).add
      ((RSP.Tails.mass_hasSum e).mul_right (r + (i + r - M) ^ 2))
  convert! h.div_const ((q - M) ^ 2) using 1
  · ext a
    unfold quadratic
    ring
  · unfold quadratic
    ring

private theorem standalone_Mission_Completeness__product_hasSum {f g : ℕ → ℝ} {x y : ℝ}
    (hf : HasSum f x) (hg : HasSum g y)
    (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i) :
    HasSum (fun ab : ℕ × ℕ => f ab.1 * g ab.2) (x * y) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

private theorem product_mass_hasSum (e f : ℝ≥0) :
    HasSum (fun ab : ℕ × ℕ => RSP.Tails.mass e ab.1 * RSP.Tails.mass f ab.2) 1 := by
  simpa using standalone_Mission_Completeness__product_hasSum (RSP.Tails.mass_hasSum e) (RSP.Tails.mass_hasSum f)
    (RSP.Tails.mass_nonneg e) (RSP.Tails.mass_nonneg f)

private theorem quadratic_pair_hasSum (q M N i j r s : ℝ) (e f : ℝ≥0)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    HasSum (fun ab : ℕ × ℕ =>
      (RSP.Tails.mass e ab.1 * RSP.Tails.mass f ab.2) *
        (quadratic q M (i + ab.1) r + quadratic q N (j + ab.2) s))
      (quadratic q M i (r + e) + quadratic q N j (s + f)) := by
  have hL := standalone_Mission_Completeness__product_hasSum (quadratic_hasSum q M i r e)
    (RSP.Tails.mass_hasSum f)
    (fun a => mul_nonneg (RSP.Tails.mass_nonneg e a)
      (quadratic_nonneg q M (i + a) r hr)) (RSP.Tails.mass_nonneg f)
  have hC := standalone_Mission_Completeness__product_hasSum (RSP.Tails.mass_hasSum e)
    (quadratic_hasSum q N j s f) (RSP.Tails.mass_nonneg e)
    (fun b => mul_nonneg (RSP.Tails.mass_nonneg f b)
      (quadratic_nonneg q N (j + b) s hs))
  convert! hL.add hC using 1
  · ext ab
    ring
  · ring

private theorem rectangle_comparison {α : Type*} (R : Finset α) (p D G : α → ℝ) (bound : ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp : HasSum p 1)
    (hG : HasSum (fun a => p a * G a) bound)
    (hin : ∀ a ∈ R, D a ≤ G a) (hout : ∀ a ∉ R, 1 ≤ G a) :
    1 - ∑ a ∈ R, p a + ∑ a ∈ R, p a * D a ≤ bound := by
  classical
  let correction := fun a => if a ∈ R then p a * (1 - D a) else 0
  have hc : HasSum correction (∑ a ∈ R, p a * (1 - D a)) := by
    have hc0 : HasSum correction (∑ a ∈ R, correction a) :=
      hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional α)
        (s := R) (f := correction) (fun a ha => by simp [correction, ha])
    simpa [correction] using hc0
  have hsum := hG.add hc
  have hle : 1 ≤ bound + ∑ a ∈ R, p a * (1 - D a) := by
    apply hasSum_le _ hp hsum
    intro a
    by_cases ha : a ∈ R
    · dsimp [correction]
      rw [if_pos ha]
      nlinarith [mul_le_mul_of_nonneg_left (hin a ha) (hp0 a)]
    · dsimp [correction]
      rw [if_neg ha]
      nlinarith [mul_le_mul_of_nonneg_left (hout a ha) (hp0 a)]
  have hid : (∑ a ∈ R, p a * (1 - D a)) =
      (∑ a ∈ R, p a) - ∑ a ∈ R, p a * D a := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hid] at hle
  linarith

private theorem edgeExpectation_le_quadratic (A : InnerInput) (T : Table)
    (u v i j : ℕ) (M N r s : ℝ)
    (hM : M < (tickLimit A : ℝ)) (hN : N < (tickLimit A : ℝ))
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hD : ∀ a b : ℕ, dpValue A T u (i + a) (j + b) ≤
      quadratic (tickLimit A) M (i + a) r + quadratic (tickLimit A) N (j + b) s) :
    edgeExpectation A T u v i j ≤
      quadratic (tickLimit A) M i (r + lengthRate A * A.I.length u v) +
      quadratic (tickLimit A) N j (s + costRate A * A.I.cost u v) := by
  let e : ℝ≥0 := ⟨lengthRate A * A.I.length u v,
    mul_nonneg (RSP.PoissonBridge.lengthRate_nonneg A) (A.I.length u v).coe_nonneg⟩
  let f : ℝ≥0 := ⟨costRate A * A.I.cost u v,
    mul_nonneg (RSP.PoissonBridge.costRate_nonneg A) (A.I.cost u v).coe_nonneg⟩
  have he : (e : ℝ) = lengthRate A * A.I.length u v := rfl
  have hf : (f : ℝ) = costRate A * A.I.cost u v := rfl
  have hr' : 0 ≤ r + (e : ℝ) := add_nonneg hr e.coe_nonneg
  have hs' : 0 ≤ s + (f : ℝ) := add_nonneg hs f.coe_nonneg
  unfold edgeExpectation
  split
  · rename_i hsat
    rcases hsat with hi | hj
    · have hL := quadratic_saturated (tickLimit A) M i (r + e) hM
        (by exact_mod_cast hi) hr'
      have hC := quadratic_nonneg (tickLimit A) N j (s + f) hs'
      change 1 ≤ quadratic (tickLimit A) M i (r + e) + quadratic (tickLimit A) N j (s + f)
      linarith
    · have hL := quadratic_nonneg (tickLimit A) M i (r + e) hr'
      have hC := quadratic_saturated (tickLimit A) N j (s + f) hN
        (by exact_mod_cast hj) hs'
      change 1 ≤ quadratic (tickLimit A) M i (r + e) + quadratic (tickLimit A) N j (s + f)
      linarith
  · let R := Finset.range (tickLimit A - i) ×ˢ Finset.range (tickLimit A - j)
    have h := rectangle_comparison R
      (fun ab : ℕ × ℕ => RSP.Tails.mass e ab.1 * RSP.Tails.mass f ab.2)
      (fun ab => dpValue A T u (i + ab.1) (j + ab.2))
      (fun ab => quadratic (tickLimit A) M ((i : ℝ) + ab.1) r +
        quadratic (tickLimit A) N ((j : ℝ) + ab.2) s)
      (quadratic (tickLimit A) M i (r + e) + quadratic (tickLimit A) N j (s + f))
      (fun ab => mul_nonneg (RSP.Tails.mass_nonneg e ab.1) (RSP.Tails.mass_nonneg f ab.2))
      (product_mass_hasSum e f) (quadratic_pair_hasSum _ _ _ _ _ _ _ e f hr hs)
      (fun ab _ => by simpa only [Nat.cast_add] using hD ab.1 ab.2) ?_
    · simpa only [R, Finset.sum_product, RSP.Tails.mass, he, hf,
        edgeMass, ActuarialValuation.poissonCountMass] using h
    · intro ab hab
      have hab' : tickLimit A ≤ i + ab.1 ∨ tickLimit A ≤ j + ab.2 := by
        simp only [R, Finset.mem_product, Finset.mem_range] at hab
        omega
      rcases hab' with hi | hj
      · have hL := quadratic_saturated (tickLimit A) M ((i : ℝ) + ab.1) r hM
          (by exact_mod_cast hi) hr
        have hC := quadratic_nonneg (tickLimit A) N ((j : ℝ) + ab.2) s hs
        linarith
      · have hL := quadratic_nonneg (tickLimit A) M ((i : ℝ) + ab.1) r hr
        have hC := quadratic_saturated (tickLimit A) N ((j : ℝ) + ab.2) s hN
          (by exact_mod_cast hj) hs
        linarith

private theorem quadratic_feasible_mean (A : InnerInput) (M : ℝ)
    (hM : M ≤ (tickLimit A : ℝ) / (1 + A.δ / 2)) :
    quadratic (tickLimit A) M 0 M ≤ 1 / 16 := by
  have hδ := A.accuracy_pos
  have hq : (0 : ℝ) < tickLimit A := by
    have : 0 < tickLimit A := by
      unfold tickLimit
      apply Nat.ceil_pos.mpr
      positivity
    exact_mod_cast this
  have hbase : (tickLimit A : ℝ) / (1 + A.δ / 2) < tickLimit A :=
    div_lt_self hq (by linarith)
  have hgap := sub_pos.mpr hbase
  rw [quadratic_initial]
  apply le_trans (div_le_div₀ (by positivity) hM (sq_pos_of_pos hgap) ?_)
  · have hsize : 128 * (2 : ℝ) ≤ (tickLimit A : ℝ) * A.δ ^ 2 := by
      have hh : 512 ≤ (tickLimit A : ℝ) * A.δ ^ 2 :=
        (div_le_iff₀ (sq_pos_of_pos hδ)).mp (Nat.le_ceil _)
      linarith
    have hh := RSP.Tails.completeness_ratio_le (tickLimit A) A.δ 2 (by norm_num)
      hq hδ A.accuracy_lt_one.le hsize
    norm_num at hh
    exact hh
  · nlinarith [sq_nonneg ((tickLimit A : ℝ) / (1 + A.δ / 2) - M),
      mul_nonneg hgap.le (sub_nonneg.mpr hM)]

private theorem pathWeight_nonneg (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) :
    0 ≤ pathWeight w P := by
  unfold pathWeight
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
  exact (w e.1 e.2).coe_nonneg

private theorem pathWeight_cons_cons (w : ℕ → ℕ → ℝ≥0) (a b : ℕ) (P : List ℕ) :
    pathWeight w (a :: b :: P) = w a b + pathWeight w (b :: P) := by
  simp [pathWeight]

private theorem pathWeight_snoc (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) (u v : ℕ)
    (hP : P.getLast? = some u) :
    pathWeight w (P ++ [v]) = pathWeight w P + w u v := by
  induction P with
  | nil => simp at hP
  | cons a P ih =>
      cases P with
      | nil =>
          have : a = u := by simpa using hP
          subst u
          simp [pathWeight]
      | cons b P =>
          have hp : (b :: P).getLast? = some u := by simpa using hP
          simp only [List.cons_append, pathWeight_cons_cons]
          have hh := ih hp
          simp only [List.cons_append] at hh
          rw [hh]
          ring

private theorem path_quadratic_bound (A : InnerInput) (T : Table)
    (hsource : ∀ i j, i < tickLimit A → j < tickLimit A →
      dpValue A T A.I.source i j = 0)
    (hbellman : ∀ u v, (u, v) ∈ A.I.graph.edges → ∀ i j,
      dpValue A T v i j ≤ edgeExpectation A T u v i j)
    (M N : ℝ) (hM : M < (tickLimit A : ℝ)) (hN : N < (tickLimit A : ℝ)) :
    ∀ (P : List ℕ) (t : ℕ), IsPath A.I.graph A.I.source t P → ∀ i j,
      dpValue A T t i j ≤
        quadratic (tickLimit A) M i (lengthRate A * pathWeight A.I.length P) +
        quadratic (tickLimit A) N j (costRate A * pathWeight A.I.cost P) := by
  intro P
  induction P using List.reverseRecOn with
  | nil =>
      intro t hP
      simp [IsPath] at hP
  | append_singleton P v ih =>
      intro t hP i j
      have ht : v = t := by simpa using hP.2.1
      subst t
      by_cases hnil : P = []
      · subst P
        have hv : v = A.I.source := by simpa using hP.1
        subst v
        simp only [List.nil_append, pathWeight, List.tail_cons, List.zip_nil_right,
          List.map_nil, List.sum_nil, mul_zero]
        by_cases hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j
        · have hd : dpValue A T A.I.source i j = 1 := by simp [dpValue, hsat]
          rw [hd]
          rcases hsat with hi | hj
          · have hL := quadratic_saturated (tickLimit A) M i 0 hM
              (by exact_mod_cast hi) (by norm_num)
            have hC := quadratic_nonneg (tickLimit A) N j 0 (by norm_num)
            linarith
          · have hL := quadratic_nonneg (tickLimit A) M i 0 (by norm_num)
            have hC := quadratic_saturated (tickLimit A) N j 0 hN
              (by exact_mod_cast hj) (by norm_num)
            linarith
        · rw [hsource i j (by omega) (by omega)]
          exact add_nonneg (quadratic_nonneg _ _ _ _ (by norm_num))
            (quadratic_nonneg _ _ _ _ (by norm_num))
      · obtain ⟨u, hu⟩ : ∃ u, P.getLast? = some u := by
          apply Option.isSome_iff_exists.mp
          simpa using hnil
        have hprefix : IsPath A.I.graph A.I.source u P := by
          refine ⟨?_, hu, hP.2.2.left_of_append⟩
          simpa [List.head?_append_of_ne_nil P hnil] using hP.1
        have hedge : (u, v) ∈ A.I.graph.edges :=
          (List.isChain_append.mp hP.2.2).2.2 u (by simp [hu]) v (by simp)
        have hr : 0 ≤ lengthRate A * pathWeight A.I.length P :=
          mul_nonneg (RSP.PoissonBridge.lengthRate_nonneg A) (pathWeight_nonneg _ _)
        have hs : 0 ≤ costRate A * pathWeight A.I.cost P :=
          mul_nonneg (RSP.PoissonBridge.costRate_nonneg A) (pathWeight_nonneg _ _)
        apply (hbellman u v hedge i j).trans
        have h := edgeExpectation_le_quadratic A T u v i j M N
          (lengthRate A * pathWeight A.I.length P) (costRate A * pathWeight A.I.cost P)
          hM hN hr hs (fun a b => by
            simpa only [Nat.cast_add] using ih u hprefix (i + a) (j + b))
        simpa only [pathWeight_snoc _ P u v hu, mul_add] using h

private theorem inner_completeness_of_bellman (A : InnerInput)
    (hsource : ∀ i j, i < tickLimit A → j < tickLimit A →
      dpValue A (buildTable A) A.I.source i j = 0)
    (hbellman : ∀ u v, (u, v) ∈ A.I.graph.edges → ∀ i j,
      dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j)
    (t : ℕ) (P : List ℕ) (hP : IsPath A.I.graph A.I.source t P)
    (hL : pathWeight A.I.length P ≤ A.L)
    (hC : pathWeight A.I.cost P ≤ A.I.budget) : accepted A t := by
  let M := lengthRate A * pathWeight A.I.length P
  let N := costRate A * pathWeight A.I.cost P
  have hδ := A.accuracy_pos
  have hhalf : 0 < 1 + A.δ / 2 := by linarith
  have hLpos := A.length_pos
  have hCpos := A.budget_pos
  have hM : M ≤ (tickLimit A : ℝ) / (1 + A.δ / 2) := by
    calc
      M ≤ lengthRate A * A.L :=
        mul_le_mul_of_nonneg_left hL (RSP.PoissonBridge.lengthRate_nonneg A)
      _ = _ := by unfold lengthRate; field_simp
  have hN : N ≤ (tickLimit A : ℝ) / (1 + A.δ / 2) := by
    calc
      N ≤ costRate A * A.I.budget :=
        mul_le_mul_of_nonneg_left hC (RSP.PoissonBridge.costRate_nonneg A)
      _ = _ := by unfold costRate; field_simp
  have hq : (0 : ℝ) < tickLimit A := by
    have : 0 < tickLimit A := by
      unfold tickLimit
      apply Nat.ceil_pos.mpr
      positivity
    exact_mod_cast this
  have hbase : (tickLimit A : ℝ) / (1 + A.δ / 2) < tickLimit A :=
    div_lt_self hq (by linarith)
  have hbound := path_quadratic_bound A (buildTable A) hsource hbellman M N
    (hM.trans_lt hbase) (hN.trans_lt hbase) P t hP 0 0
  have hML := quadratic_feasible_mean A M hM
  have hNC := quadratic_feasible_mean A N hN
  unfold accepted
  have hbound' : dpValue A (buildTable A) t 0 0 ≤ quadratic (tickLimit A) M 0 M +
      quadratic (tickLimit A) N 0 N := by
    simpa only [Nat.cast_zero] using hbound
  linarith

private theorem inner_completeness_of_edge_bounds (A : InnerInput)
    (hbellman : ∀ u v, (u, v) ∈ A.I.graph.edges → ∀ i j,
      dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j)
    (t : ℕ) (P : List ℕ) (hP : IsPath A.I.graph A.I.source t P)
    (hL : pathWeight A.I.length P ≤ A.L)
    (hC : pathWeight A.I.cost P ≤ A.I.budget) : accepted A t :=
  inner_completeness_of_bellman A (dpValue_buildTable_source A) hbellman t P hP hL hC

end NearLinearRSP.TwoResources.Completeness
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem queueRun_keys_le (A : InnerInput) (i j n v : ℕ) (S : LayerState) :
    (queueRun A i j n S).keys v ≤ S.keys v := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [queueRun_succ]
      exact (popLayer_keys_le A i j v _).trans ih

private theorem buildLayer_value_le_initial (A : InnerInput) (T : Table) (i j v : ℕ)
    (hv : v ∈ activeVertices A.I) :
    (buildLayer A T i j v i j).value ≤ (initLayer A T i j).keys v := by
  have hsync : PoppedSync A i j (initLayer A T i j) := by
    intro w hw hwq
    exact False.elim (hwq hw)
  have h := queueRun_sync A i j (activeVertices A.I).length (initLayer A T i j)
    (activeVertices_nodup A.I) hsync
  have hempty := buildLayer_queue_exhausted A T i j
  have heq := h v hv (by rw [hempty]; simp)
  exact heq.le.trans (queueRun_keys_le A i j (activeVertices A.I).length v _)

private theorem buildLayer_value_le_next_length (A : InnerInput) (T : Table) (i j v : ℕ)
    (hT : TableRange T) (hv : v ∈ activeVertices A.I) :
    (buildLayer A T i j v i j).value ≤ dpValue A T v (i + 1) j := by
  apply (buildLayer_value_le_initial A T i j v hv).trans
  change (if v = A.I.source then 0 else
    min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))) ≤ _
  split
  · exact (dpValue_range A T hT v (i + 1) j).1
  · exact min_le_left _ _

private theorem buildLayer_value_le_next_cost (A : InnerInput) (T : Table) (i j v : ℕ)
    (hT : TableRange T) (hv : v ∈ activeVertices A.I) :
    (buildLayer A T i j v i j).value ≤ dpValue A T v i (j + 1) := by
  apply (buildLayer_value_le_initial A T i j v hv).trans
  change (if v = A.I.source then 0 else
    min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))) ≤ _
  split
  · exact (dpValue_range A T hT v i (j + 1)).1
  · exact min_le_right _ _

private theorem dpValue_buildTable_le_next_length (A : InnerInput) (v i j : ℕ)
    (hv : v ∈ activeVertices A.I) :
    dpValue A (buildTable A) v i j ≤ dpValue A (buildTable A) v (i + 1) j := by
  by_cases hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · have hsat' : tickLimit A ≤ i + 1 ∨ tickLimit A ≤ j := by omega
    simp [dpValue, hsat, hsat']
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, hT, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere : dpValue A (buildTable A) v i j = (buildLayer A T i j v i j).value := by
      simp [dpValue, hsat, hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)]
    have hnext : dpValue A T v (i + 1) j = dpValue A (buildTable A) v (i + 1) j := by
      unfold dpValue
      split
      · rfl
      · rw [hfinal v (i + 1) j (Or.inl (by omega)),
          buildLayer_other_layer A T i j v (i + 1) j (Or.inl (by omega))]
    rw [hhere, ← hnext]
    exact buildLayer_value_le_next_length A T i j v hT hv

private theorem dpValue_buildTable_le_next_cost (A : InnerInput) (v i j : ℕ)
    (hv : v ∈ activeVertices A.I) :
    dpValue A (buildTable A) v i j ≤ dpValue A (buildTable A) v i (j + 1) := by
  by_cases hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · have hsat' : tickLimit A ≤ i ∨ tickLimit A ≤ j + 1 := by omega
    simp [dpValue, hsat, hsat']
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, hT, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere : dpValue A (buildTable A) v i j = (buildLayer A T i j v i j).value := by
      simp [dpValue, hsat, hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)]
    have hnext : dpValue A T v i (j + 1) = dpValue A (buildTable A) v i (j + 1) := by
      unfold dpValue
      split
      · rfl
      · rw [hfinal v i (j + 1) (Or.inr ⟨rfl, by omega⟩),
          buildLayer_other_layer A T i j v i (j + 1) (Or.inr (by omega))]
    rw [hhere, ← hnext]
    exact buildLayer_value_le_next_cost A T i j v hT hv

private theorem dpValue_buildTable_monotone_length (A : InnerInput) (v j : ℕ)
    (hv : v ∈ activeVertices A.I) :
    Monotone (fun i => dpValue A (buildTable A) v i j) :=
  monotone_nat_of_le_succ (fun i => dpValue_buildTable_le_next_length A v i j hv)

private theorem dpValue_buildTable_monotone_cost (A : InnerInput) (v i : ℕ)
    (hv : v ∈ activeVertices A.I) :
    Monotone (fun j => dpValue A (buildTable A) v i j) :=
  monotone_nat_of_le_succ (fun j => dpValue_buildTable_le_next_cost A v i j hv)

private theorem dpValue_buildTable_mono (A : InnerInput) (v i j a b : ℕ)
    (hv : v ∈ activeVertices A.I) (hi : i ≤ a) (hj : j ≤ b) :
    dpValue A (buildTable A) v i j ≤ dpValue A (buildTable A) v a b :=
  (dpValue_buildTable_monotone_length A v j hv hi).trans
    (dpValue_buildTable_monotone_cost A v a hv hj)

private theorem dpValue_buildTable_le_increment (A : InnerInput) (v i j a b : ℕ)
    (hv : v ∈ activeVertices A.I) :
    dpValue A (buildTable A) v i j ≤ dpValue A (buildTable A) v (i + a) (j + b) :=
  dpValue_buildTable_mono A v i j (i + a) (j + b) hv (by omega) (by omega)

private theorem popLayer_keys_outside (A : InnerInput) (i j v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue) : (popLayer A i j S).keys v = S.keys v := by
  by_cases hne : S.queue = []
  · simp [popLayer, hne]
  · rw [popLayer_eq_relaxAll A i j S hne]
    apply relaxAll_keys_outside
    intro hm
    exact hv (List.mem_of_mem_erase hm)

private theorem popLayer_key_picked (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []) (hdup : S.queue.Nodup) :
    (popLayer A i j S).keys (pickedVertex S) = S.keys (pickedVertex S) := by
  rw [popLayer_eq_relaxAll A i j S hne]
  exact relaxAll_keys_outside A i j _ _ _ hdup.not_mem_erase

private theorem popLayer_expectation_other_vertex (A : InnerInput) (i j u v : ℕ)
    (S : LayerState) (hne : S.queue ≠ []) (hu : u ≠ pickedVertex S) :
    edgeExpectation A (popLayer A i j S).table u v i j =
      edgeExpectation A S.table u v i j := by
  rw [popLayer_eq_relaxAll A i j S hne, relaxAll_table]
  apply edgeExpectation_congr
  intro a _ b _
  apply dpValue_congr_at
  simp [settleState, putCell, hu]

private theorem relaxEdge_edge_bound (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (huv : u ≠ v) (hv : v ∈ S.queue) :
    (relaxEdge A i j u S (u, v)).keys v ≤ edgeExpectation A S.table u v i j := by
  unfold relaxEdge
  rw [if_pos ⟨rfl, huv, hv⟩]
  dsimp only
  split
  · simp
  · rename_i h
    exact le_of_not_gt h

private theorem standalone_Mission_QueueBellman__relaxFold_keys_le (A : InnerInput) (i j u v : ℕ)
    (es : List (ℕ × ℕ)) (S : LayerState) :
    (es.foldl (relaxEdge A i j u) S).keys v ≤ S.keys v := by
  induction es generalizing S with
  | nil => exact le_rfl
  | cons e es ih =>
      rw [List.foldl_cons]
      exact (ih _).trans (relaxEdge_keys_le A i j u v S e)

private theorem relaxAll_edge_bound (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (huv : u ≠ v) (hv : v ∈ S.queue) (hedge : (u, v) ∈ A.I.graph.edges) :
    (relaxAll A i j u S).keys v ≤ edgeExpectation A S.table u v i j := by
  unfold relaxAll
  generalize he : A.I.graph.edges = es at hedge ⊢
  clear he
  induction es generalizing S with
  | nil => simp at hedge
  | cons e es ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hedge with he | hm
      · subst e
        exact (standalone_Mission_QueueBellman__relaxFold_keys_le A i j u v es _).trans
          (relaxEdge_edge_bound A i j u v S huv hv)
      · have hrec := ih (relaxEdge A i j u S e) (by simpa using hv) hm
        simpa only [relaxEdge_table] using hrec

private theorem popLayer_separation (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hdup : S.queue.Nodup)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S)
    (hsep : SettledSeparation A S) : SettledSeparation A (popLayer A i j S) := by
  by_cases hne : S.queue = []
  · simpa [popLayer, hne] using hsep
  · intro u hu huq v hvq
    have hp := pickedVertex_mem S hne
    have hvbound := popLayer_keys_ge_picked A i j S hi hj hne hS hfuture v hvq
    by_cases hup : u = pickedVertex S
    · subst u
      rw [popLayer_key_picked A i j S hne hdup]
      exact hvbound
    · have huold : u ∉ S.queue := by
        intro hm
        apply huq
        rw [popLayer_eq_relaxAll A i j S hne, relaxAll_queue]
        exact (List.mem_erase_of_ne hup).mpr hm
      rw [popLayer_keys_outside A i j u S huold]
      exact (hsep u hu huold _ hp).trans hvbound

private theorem popLayer_bellman (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hdup : S.queue.Nodup)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S)
    (hsep : SettledSeparation A S) (hbell : SettledBellman A i j S) :
    SettledBellman A i j (popLayer A i j S) := by
  by_cases hne : S.queue = []
  · simpa [popLayer, hne] using hbell
  · intro u hu huq v huv
    have hp := pickedVertex_mem S hne
    have hpop := popLayer_eq_relaxAll A i j S hne
    have htable : (popLayer A i j S).table =
        (settleState S i j (pickedVertex S)).table := by rw [hpop, relaxAll_table]
    by_cases hup : u = pickedVertex S
    · subst u
      rw [htable]
      have hext := settleState_expectation_ge A i j (pickedVertex S) S hi hj hp hS hfuture v
      by_cases hvnew : v ∈ (popLayer A i j S).queue
      · have hvU : v ∈ (settleState S i j (pickedVertex S)).queue := by
          simpa only [hpop, relaxAll_queue] using hvnew
        have hpv : pickedVertex S ≠ v := by
          intro heq
          subst v
          exact hdup.not_mem_erase hvU
        rw [hpop]
        exact relaxAll_edge_bound A i j _ v _ hpv hvU huv
      · by_cases hvp : v = pickedVertex S
        · subst v
          rw [popLayer_key_picked A i j S hne hdup]
          exact hext
        · have hvold : v ∉ S.queue := by
            intro hm
            apply hvnew
            rw [hpop, relaxAll_queue]
            exact (List.mem_erase_of_ne hvp).mpr hm
          rw [popLayer_keys_outside A i j v S hvold]
          exact (hsep v (activeVertices_edge_right A.I _ v huv) hvold _ hp).trans hext
    · have huold : u ∉ S.queue := by
        intro hm
        apply huq
        rw [hpop, relaxAll_queue]
        exact (List.mem_erase_of_ne hup).mpr hm
      rw [popLayer_expectation_other_vertex A i j u v S hne hup]
      exact (popLayer_keys_le A i j v S).trans (hbell u hu huold v huv)

private theorem queueRun_bellman_separation (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hdup : S.queue.Nodup)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S)
    (hsep : SettledSeparation A S) (hbell : SettledBellman A i j S) :
    SettledSeparation A (queueRun A i j n S) ∧
      SettledBellman A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact ⟨hsep, hbell⟩
  | succ n ih =>
      rw [queueRun_succ]
      have hdup' := queueRun_queue_nodup A i j n S hdup
      have hrange' := queueRun_range A i j n S hS
      have hfut' := queueRun_futureBound A i j n S hfuture
      exact ⟨popLayer_separation A i j _ hi hj hdup' hrange' hfut' ih.1,
        popLayer_bellman A i j _ hi hj hdup' hrange' hfut' ih.1 ih.2⟩

private theorem buildLayer_edge_le (A : InnerInput) (T : Table) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hT : TableRange T)
    (hfuture : LayerFutureBound A i j (initLayer A T i j))
    (u v : ℕ) (huv : (u, v) ∈ A.I.graph.edges) :
    dpValue A (buildLayer A T i j) v i j ≤
      edgeExpectation A (buildLayer A T i j) u v i j := by
  let S := initLayer A T i j
  let final := queueRun A i j (activeVertices A.I).length S
  have hsep : SettledSeparation A S := by
    intro a ha hnot
    exact False.elim (hnot ha)
  have hbell : SettledBellman A i j S := by
    intro a ha hnot
    exact False.elim (hnot ha)
  have hterminal : final.queue = [] := buildLayer_queue_exhausted A T i j
  have hmain := (queueRun_bellman_separation A i j (activeVertices A.I).length S hi hj
    (activeVertices_nodup A.I) (initLayer_range A T hT i j) hfuture hsep hbell).2
  have hbound := hmain u (activeVertices_edge_left A.I u v huv)
    (by rw [hterminal]; simp) v huv
  have hsync : PoppedSync A i j final := queueRun_sync A i j _ S
    (activeVertices_nodup A.I) (by intro a ha hnot; exact False.elim (hnot ha))
  have hvalue := hsync v (activeVertices_edge_right A.I u v huv)
    (by rw [hterminal]; simp)
  change dpValue A final.table v i j ≤ edgeExpectation A final.table u v i j
  simpa only [dpValue, Nat.not_le.mpr hi, Nat.not_le.mpr hj, or_self, if_false, hvalue] using hbound

private theorem layer_witness_future_eq (A : InnerInput) (T : Table) (i j : ℕ)
    (hfinal : ∀ v a b, (i < a ∨ i = a ∧ j ≤ b) →
      buildTable A v a b = buildLayer A T i j v a b)
    (v a b : ℕ) (hab : a ≠ 0 ∨ b ≠ 0) :
    dpValue A T v (i + a) (j + b) = dpValue A (buildTable A) v (i + a) (j + b) := by
  unfold dpValue
  split
  · rfl
  · rw [hfinal v (i + a) (j + b) (by omega),
      buildLayer_other_layer A T i j v (i + a) (j + b) (by omega)]

private theorem layer_witness_futureBound (A : InnerInput) (T : Table) (i j : ℕ)
    (hfinal : ∀ v a b, (i < a ∨ i = a ∧ j ≤ b) →
      buildTable A v a b = buildLayer A T i j v a b) :
    LayerFutureBound A i j (initLayer A T i j) := by
  intro v hv a b hab
  have hv' : v ∈ activeVertices A.I := hv
  change (if v = A.I.source then 0 else
    min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))) ≤
      dpValue A T v (i + a) (j + b)
  rw [layer_witness_future_eq A T i j hfinal v a b hab]
  split
  · exact dpValue_buildTable_nonneg A v (i + a) (j + b)
  · by_cases ha : a = 0
    · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
      apply (min_le_right _ _).trans
      have heq := layer_witness_future_eq A T i j hfinal v 0 1 (Or.inr (by omega))
      simp only [Nat.add_zero] at heq
      rw [heq]
      exact dpValue_buildTable_mono A v i (j + 1) (i + a) (j + b) hv' (by omega) (by omega)
    · apply (min_le_left _ _).trans
      have heq := layer_witness_future_eq A T i j hfinal v 1 0 (Or.inl (by omega))
      simp only [Nat.add_zero] at heq
      rw [heq]
      exact dpValue_buildTable_mono A v (i + 1) j (i + a) (j + b) hv' (by omega) (by omega)

private theorem dpValue_buildTable_le_edgeExpectation (A : InnerInput) (u v : ℕ)
    (huv : (u, v) ∈ A.I.graph.edges) (i j : ℕ) :
    dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j := by
  by_cases hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · simp [dpValue, edgeExpectation, hsat]
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, hT, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere : dpValue A (buildTable A) v i j = dpValue A (buildLayer A T i j) v i j :=
      dpValue_congr_at A _ _ v i j (hfinal v i j (Or.inr ⟨rfl, le_rfl⟩))
    have hedge : edgeExpectation A (buildTable A) u v i j =
        edgeExpectation A (buildLayer A T i j) u v i j := by
      apply edgeExpectation_congr
      intro a _ b _
      apply dpValue_congr_at
      apply hfinal
      omega
    rw [hhere, hedge]
    exact buildLayer_edge_le A T i j hi hj hT (layer_witness_futureBound A T i j hfinal) u v huv

end NearLinearRSP.TwoResources
end



namespace NearLinearRSP.TwoResources

private theorem dp_faithfulness (A : InnerInput) :
    ∀ u v : ℕ, (u, v) ∈ A.I.graph.edges → ∀ i j : ℕ,
      dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j ∧
      (i < tickLimit A → j < tickLimit A →
        (buildTable A v i j).parent = .edge u →
        dpValue A (buildTable A) v i j = edgeExpectation A (buildTable A) u v i j) := by
  intro u v huv i j
  exact ⟨dpValue_buildTable_le_edgeExpectation A u v huv i j,
    fun _ _ hp => dpValue_buildTable_selected_edge A v i j u hp⟩

end NearLinearRSP.TwoResources



set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem inner_completeness (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (P : List ℕ) (hP : IsPath A.I.graph A.I.source t P)
    (hL : pathWeight A.I.length P ≤ A.L) (hC : pathWeight A.I.cost P ≤ A.I.budget) :
    accepted A t :=
  Completeness.inner_completeness_of_edge_bounds A
    (fun u v huv i j => (dp_faithfulness A u v huv i j).1) t P hP hL hC

private theorem answerBranch_inner_minimal (I : Instance) (ε : ℝ) (hε : 0 ≤ ε)
    (t r : ℕ) (hb : answerBranch I ε t = .inner r)
    (B : InnerInput) (hB : B ∈ outerInputs I ε) (haB : accepted B t) :
    ∃ A, (outerInputs I ε)[r]? = some A ∧ accepted A t ∧ A.L ≤ B.L := by
  obtain ⟨A, hA, haA⟩ := answerBranch_inner_input I ε t r hb
  obtain ⟨s, hs⟩ := List.mem_iff_getElem?.mp hB
  have hrs := acceptedIndex_le I ε t r s B
    ((answerBranch_inner_iff I ε t r).mp hb).2.2.2 hs haB
  exact ⟨A, hA, haA, outerInputs_get_length_le I ε hε r s A B hA hs hrs⟩

private theorem answerBranch_inner_sound (I : Instance) (ε : ℝ) (hε : 0 ≤ ε)
    (t r : ℕ) (ht : t < I.graph.n) (hb : answerBranch I ε t = .inner r) :
    ∃ d P, answerDistance I ε t = some d ∧ answerPath I ε t = some P ∧
      IsPath I.graph I.source t P ∧ pathWeight I.length P ≤ d ∧
      pathWeight I.cost P ≤ (1 + ε) * I.budget := by
  obtain ⟨A, hA, ha⟩ := answerBranch_inner_input I ε t r hb
  have hm : A ∈ outerInputs I ε := List.mem_of_getElem? hA
  obtain ⟨hI, hδ, _⟩ := outerInputs_mem_fields I ε A hm
  obtain ⟨S, hS, hP, hL, hC⟩ := deterministic_retrieval A t (by simpa [hI] using ht) ha
  refine ⟨(1 + A.δ) * A.L, S.path, ?_, ?_, ?_, ?_, ?_⟩
  · simp [answerDistance, hb, hA]
  · simp [answerPath, hb, hA, hS]
  · simpa [hI] using hP
  · simpa [hI] using hL
  · have hslack : (1 + A.δ) * (I.budget : ℝ) ≤ (1 + ε) * I.budget := by
      rw [hδ]
      exact mul_le_mul_of_nonneg_right (by linarith) I.budget.coe_nonneg
    have hc' : pathWeight I.cost S.path ≤ (1 + A.δ) * I.budget := by
      simpa [hI] using hC
    exact hc'.trans hslack

private theorem answerBranch_inner_comparison_of_covered (I : Instance) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 < (I.budget : ℝ))
    (t r : ℕ) (ht : t < I.graph.n) (hb : answerBranch I ε t = .inner r)
    (P Q : List ℕ) (hQ : Feasible I t Q) (L : ℝ)
    (hL : L ∈ geometricGuesses I ε) (hLpos : 0 < L)
    (hQL : pathWeight I.length Q ≤ L)
    (hLP : L ≤ (1 + ε / 4) * pathWeight I.length P) :
    ∃ d, answerDistance I ε t = some d ∧ d ≤ (1 + ε) * pathWeight I.length P := by
  obtain ⟨B, hB, hBI, hBδ, hBL⟩ :=
    outerInputs_contains_positive_guess I ε L hε hε1 hC hL hLpos
  have haB : accepted B t := by
    apply inner_completeness B t (by simpa [hBI] using ht) Q
    · simpa [hBI] using hQ.1
    · simpa [hBI, hBL] using hQL
    · simpa [hBI] using hQ.2
  obtain ⟨A, hA, _, hAB⟩ := answerBranch_inner_minimal I ε hε.le t r hb B hB haB
  have hm : A ∈ outerInputs I ε := List.mem_of_getElem? hA
  have hAδ := (outerInputs_mem_fields I ε A hm).2.1
  refine ⟨(1 + A.δ) * A.L, by simp [answerDistance, hb, hA], ?_⟩
  have hLA : A.L ≤ L := by simpa [hBL] using hAB
  have hfirst : (1 + A.δ) * A.L ≤ (1 + ε / 4) * L := by
    rw [hAδ]
    exact mul_le_mul_of_nonneg_left hLA (by linarith)
  have hsecond := mul_le_mul_of_nonneg_left hLP (by linarith : 0 ≤ 1 + ε / 4)
  have hfactor : (1 + ε / 4) * (1 + ε / 4) ≤ 1 + ε := by nlinarith
  have hthird := mul_le_mul_of_nonneg_right hfactor (pathWeight_nonneg I.length P)
  nlinarith

private theorem geometricGuesses_member_pos (I : Instance) (ε L : ℝ)
    (hε : 0 ≤ ε) (hL : L ∈ geometricGuesses I ε) : 0 < L := by
  unfold geometricGuesses at hL
  split at hL
  · simp at hL
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hL
    exact mul_pos (firstPositiveLength_pos I) (pow_pos (by linarith) k)

private theorem answerBranch_zeroLength_of_distance (I : Instance) (ε d : ℝ) (t : ℕ)
    (hd : (zeroLengthTree I t).distance = some d) (hC : d ≤ I.budget) :
    answerBranch I ε t = .zeroLength := by
  by_cases hs : t = I.source <;> simp [answerBranch, hs, hd, hC]

private theorem answerBranch_ne_absent_of_acceptedIndex (I : Instance) (ε : ℝ) (t r : ℕ)
    (hC : I.budget ≠ 0) (hr : acceptedIndex I ε t = some r) :
    answerBranch I ε t ≠ .absent := by
  by_cases hs : t = I.source
  · simp [answerBranch, hs]
  · have hr' := hr
    unfold acceptedIndex at hr'
    cases hd : (zeroLengthTree I t).distance with
    | none => simp [answerBranch, hs, hd, hC, hr']
    | some d =>
        by_cases hc : d ≤ I.budget <;> simp [answerBranch, hs, hd, hC, hc, hr']

private theorem answerBranch_ne_absent_of_zeroBudgetDistance (I : Instance) (ε d : ℝ) (t : ℕ)
    (hC : I.budget = 0) (hd : (zeroBudgetTree I t).distance = some d) :
    answerBranch I ε t ≠ .absent := by
  by_cases hs : t = I.source
  · simp [answerBranch, hs]
  · cases hz : (zeroLengthTree I t).distance with
    | none => simp [answerBranch, hs, hz, hC, hd]
    | some c =>
        by_cases hc : c ≤ (0 : ℝ) <;> simp [answerBranch, hs, hz, hC, hd, hc]

private theorem answerBranch_inner_comparison (I : Instance) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (t r : ℕ) (ht : t < I.graph.n)
    (hb : answerBranch I ε t = .inner r) (P : List ℕ) (hP : Feasible I t P) :
    ∃ d, answerDistance I ε t = some d ∧ d ≤ (1 + ε) * pathWeight I.length P := by
  have hspec := (answerBranch_inner_iff I ε t r).mp hb
  have hcne : (I.budget : ℝ) ≠ 0 := by exact_mod_cast hspec.2.2.1
  have hcpos : 0 < (I.budget : ℝ) :=
    lt_of_le_of_ne I.budget.coe_nonneg (Ne.symm hcne)
  obtain ⟨Q, hQ, _, hcover⟩ := feasible_zero_or_covered I ε hε t P hP
  rcases hcover with hz | ⟨L, hL, hQL, hLP⟩
  · obtain ⟨d, hd, hdc⟩ := zeroLengthTree_path_bound I Q t hQ.1 hz
    have hlt := hspec.2.1 d hd
    exact False.elim ((not_lt_of_ge (hdc.trans hQ.2)) hlt)
  · exact answerBranch_inner_comparison_of_covered I ε hε hε1 hcpos t r ht hb
      P Q hQ L hL (geometricGuesses_member_pos I ε L hε.le hL) hQL hLP

private theorem answerDistance_sound (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (t : ℕ) (ht : t < I.graph.n) (d : ℝ) (hd : answerDistance I ε t = some d) :
    ∃ P : List ℕ, answerPath I ε t = some P ∧ IsPath I.graph I.source t P ∧
      pathWeight I.length P ≤ d ∧ pathWeight I.cost P ≤ (1 + ε) * I.budget ∧
      ∀ R : List ℕ, Feasible I t R → d ≤ (1 + ε) * pathWeight I.length R := by
  cases hb : answerBranch I ε t with
  | absent => simp [answerDistance, hb] at hd
  | zeroLength =>
      have hd0 : d = 0 := by simpa [answerDistance, hb] using hd.symm
      subst d
      have htree : ∃ c, (zeroLengthTree I t).distance = some c ∧ c ≤ I.budget := by
        rcases answerBranch_zeroLength_spec I ε t hb with hs | hc
        · subst t
          exact ⟨0, zeroLengthTree_source_zero I, I.budget.coe_nonneg⟩
        · exact hc
      obtain ⟨c, hc, hcC⟩ := htree
      obtain ⟨P, hp, hpath, hL, hC⟩ := zeroLengthTree_path I t c hc
      refine ⟨P, by simpa [answerPath, hb] using hp, hpath, hL.le, ?_, ?_⟩
      · rw [hC]
        have hbudget := mul_nonneg hε.le I.budget.coe_nonneg
        nlinarith
      · intro R _
        exact mul_nonneg (by linarith) (pathWeight_nonneg I.length R)
  | zeroBudget =>
      have hbudget := (answerBranch_zeroBudget_spec I ε t hb).1
      have htree : (zeroBudgetTree I t).distance = some d := by
        simpa [answerDistance, hb] using hd
      obtain ⟨P, hp, hpath, hC, hL⟩ := zeroBudgetTree_path I t d htree
      refine ⟨P, by simpa [answerPath, hb] using hp, hpath, hL.le, ?_, ?_⟩
      · simp [hC, hbudget]
      · intro R hR
        have hz : pathWeight I.cost R = 0 := le_antisymm
          (by simpa [hbudget] using hR.2) (pathWeight_nonneg I.cost R)
        obtain ⟨c, hc, hcR⟩ := zeroBudgetTree_path_bound I R t hR.1 hz
        have hcd : c = d := Option.some.inj (hc.symm.trans htree)
        subst c
        have hw := mul_nonneg hε.le (pathWeight_nonneg I.length R)
        nlinarith
  | inner r =>
      obtain ⟨c, P, hc, hp, hpath, hL, hC⟩ := answerBranch_inner_sound I ε hε.le t r ht hb
      have hcd : c = d := Option.some.inj (hc.symm.trans hd)
      subst c
      refine ⟨P, hp, hpath, hL, hC, ?_⟩
      intro R hR
      obtain ⟨c, hc, hcR⟩ := answerBranch_inner_comparison I ε hε hε1 t r ht hb R hR
      have hcd : c = d := Option.some.inj (hc.symm.trans hd)
      simpa [hcd] using hcR

private theorem answerDistance_complete (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (t : ℕ) (ht : t < I.graph.n) (hfeasible : ∃ R : List ℕ, Feasible I t R) :
    (answerDistance I ε t).isSome = true := by
  have hn : answerBranch I ε t ≠ .absent := by
    obtain ⟨R, hR⟩ := hfeasible
    by_cases hC : I.budget = 0
    · have hz : pathWeight I.cost R = 0 := le_antisymm
        (by simpa [hC] using hR.2) (pathWeight_nonneg I.cost R)
      obtain ⟨d, hd, _⟩ := zeroBudgetTree_path_bound I R t hR.1 hz
      exact answerBranch_ne_absent_of_zeroBudgetDistance I ε d t hC hd
    · have hcne : (I.budget : ℝ) ≠ 0 := by exact_mod_cast hC
      have hcpos : 0 < (I.budget : ℝ) :=
        lt_of_le_of_ne I.budget.coe_nonneg (Ne.symm hcne)
      obtain ⟨Q, hQ, _, hcover⟩ := feasible_zero_or_covered I ε hε t R hR
      rcases hcover with hz | ⟨L, hL, hQL, _⟩
      · obtain ⟨d, hd, hdc⟩ := zeroLengthTree_path_bound I Q t hQ.1 hz
        have hb := answerBranch_zeroLength_of_distance I ε d t hd (hdc.trans hQ.2)
        simp [hb]
      · obtain ⟨A, hA, hAI, _, hAL⟩ := outerInputs_contains_positive_guess I ε L hε hε1 hcpos
          hL (geometricGuesses_member_pos I ε L hε.le hL)
        have ha : accepted A t := by
          apply inner_completeness A t (by simpa [hAI] using ht) Q
          · simpa [hAI] using hQ.1
          · simpa [hAI, hAL] using hQL
          · simpa [hAI] using hQ.2
        obtain ⟨r, hr⟩ := acceptedIndex_exists I ε t A hA ha
        exact answerBranch_ne_absent_of_acceptedIndex I ε t r hC hr
  cases hd : answerDistance I ε t with
  | none => exact False.elim (hn ((answerDistance_eq_none_iff I ε t).mp hd))
  | some d => rfl

private theorem answerPath_sound (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (t : ℕ) (ht : t < I.graph.n) (P : List ℕ) (hp : answerPath I ε t = some P) :
    IsPath I.graph I.source t P ∧ pathWeight I.cost P ≤ (1 + ε) * I.budget := by
  cases hd : answerDistance I ε t with
  | none =>
      have hb := (answerDistance_eq_none_iff I ε t).mp hd
      simp [answerPath, hb] at hp
  | some d =>
      obtain ⟨Q, hQ, hpath, _, hcost, _⟩ := answerDistance_sound I ε hε hε1 t ht d hd
      have heq : Q = P := Option.some.inj (hQ.symm.trans hp)
      simpa [heq] using And.intro hpath hcost

private theorem answer_correct (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (t : ℕ) (ht : t < I.graph.n) :
    (∀ d : ℝ, answerDistance I ε t = some d →
      ∃ P : List ℕ, answerPath I ε t = some P ∧ IsPath I.graph I.source t P ∧
        pathWeight I.length P ≤ d ∧ pathWeight I.cost P ≤ (1 + ε) * I.budget ∧
        ∀ R : List ℕ, Feasible I t R → d ≤ (1 + ε) * pathWeight I.length R) ∧
    ((∃ R : List ℕ, Feasible I t R) → (answerDistance I ε t).isSome = true) ∧
    (∀ P : List ℕ, answerPath I ε t = some P →
      IsPath I.graph I.source t P ∧ pathWeight I.cost P ≤ (1 + ε) * I.budget) :=
  ⟨answerDistance_sound I ε hε hε1 t ht,
    answerDistance_complete I ε hε hε1 t ht, answerPath_sound I ε hε hε1 t ht⟩

private theorem mission_of_executions (preprocessing retrieval : Program) (K : ℝ) (hK : 0 < K)
    (himplementation : ∀ (I : Instance) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ (steps : ℕ) (snapshot : RAMState),
        Execution preprocessing (encodeInput I ε) initialState snapshot steps ∧
        (steps : ℝ) ≤ K * preprocessingScale I ε ∧ EncodesOutput I ε snapshot ∧
        ∀ t : ℕ, t < I.graph.n →
          ∃ (querySteps : ℕ) (out : RAMState),
            Execution retrieval (encodeInput I ε) (queryStart snapshot t) out querySteps ∧
            queryPath out = answerPath I ε t ∧
            (querySteps : ℝ) ≤ K * retrievalScale ε (answerPath I ε t)) : StandaloneMissionGoal := by
  refine ⟨preprocessing,retrieval,K,hK,?_⟩
  intro I ε hε hε1
  obtain ⟨steps,snapshot,hexec,hcost,hencode,hquery⟩ := himplementation I ε hε hε1
  refine ⟨steps,snapshot,hexec,hcost,hencode,?_⟩
  intro t ht
  have hread := EncodesOutput.readDistance_eq I ε snapshot hencode t ht
  obtain ⟨hsound,hcomplete,hpath⟩ := answer_correct I ε hε hε1 t ht
  refine ⟨hread,hquery t ht,?_,?_,hpath⟩
  · simpa only [hread] using hsound
  · simpa only [hread] using hcomplete

private theorem mission_of_preprocessing (preprocessing : Program) (K : ℝ) (hK : 0 < K)
    (hpre : ∀ (I : Instance) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ (steps : ℕ) (snapshot : RAMState),
        Execution preprocessing (encodeInput I ε) initialState snapshot steps ∧
        (steps : ℝ) ≤ K * preprocessingScale I ε ∧
        Mission.Query.QueryReady I ε snapshot) : StandaloneMissionGoal := by
  apply mission_of_executions preprocessing Mission.Query.queryProgram (K+601) (by linarith)
  intro I ε hε hε1
  obtain ⟨steps,snapshot,hexec,hcost,hready⟩ := hpre I ε hε hε1
  have hscale : 0 ≤ preprocessingScale I ε := by
    have hn := log_size_nonneg I
    have hw := log_aspect_size_nonneg I
    unfold preprocessingScale
    positivity
  refine ⟨steps,snapshot,hexec,hcost.trans ?_,hready.1,?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) hscale
  · intro t ht
    obtain ⟨n,out,hrun,hpath,hbound⟩ := Mission.Query.queryProgram_correct I ε snapshot hready t ht
    refine ⟨n,out,hrun,hpath,hbound.trans ?_⟩
    apply mul_le_mul_of_nonneg_right (by linarith)
    unfold retrievalScale
    positivity

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

private theorem deterministic_bicriteria_rsp : StandaloneMissionGoal := by
  apply mission_of_preprocessing Mission.Preprocess.preprocessingProgram
    Mission.Preprocess.preprocessingConstant Mission.Preprocess.preprocessingConstant_pos
  intro I ε hε hε1
  obtain ⟨steps,snapshot,hrun,hbound,hready⟩ :=
    Mission.Preprocess.preprocessingProgram_run I ε hε hε1
  refine ⟨steps,snapshot,hrun,?_,hready⟩
  exact (Nat.cast_le.mpr hbound).trans
    (Mission.Preprocess.preprocessingInstructionBound_scale I ε hε hε1.le)

end NearLinearRSP.TwoResources
end

open NearLinearRSP.TwoResources

theorem solution :
    ∃ preprocessing retrieval : Program, ∃ K : ℝ, 0 < K ∧
      ∀ (I : Instance) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ (steps : ℕ) (snapshot : RAMState),
          Execution preprocessing (encodeInput I ε) initialState snapshot steps ∧
          (steps : ℝ) ≤ K * preprocessingScale I ε ∧ EncodesOutput I ε snapshot ∧
          ∀ t : ℕ, t < I.graph.n →
            readDistance snapshot t = answerDistance I ε t ∧
            (∃ (querySteps : ℕ) (out : RAMState),
              Execution retrieval (encodeInput I ε) (queryStart snapshot t) out querySteps ∧
              queryPath out = answerPath I ε t ∧
              (querySteps : ℝ) ≤ K * retrievalScale ε (answerPath I ε t)) ∧
            (∀ d : ℝ, readDistance snapshot t = some d →
              ∃ P : List ℕ, answerPath I ε t = some P ∧
                IsPath I.graph I.source t P ∧ pathWeight I.length P ≤ d ∧
                pathWeight I.cost P ≤ (1 + ε) * I.budget ∧
                ∀ R : List ℕ, Feasible I t R → d ≤ (1 + ε) * pathWeight I.length R) ∧
            ((∃ R : List ℕ, Feasible I t R) → (readDistance snapshot t).isSome = true) ∧
            (∀ P : List ℕ, answerPath I ε t = some P →
              IsPath I.graph I.source t P ∧ pathWeight I.cost P ≤ (1 + ε) * I.budget)  := by
  exact NearLinearRSP.TwoResources.deterministic_bicriteria_rsp
