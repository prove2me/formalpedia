-- Prove2me | solution 1 for NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-15T18:26:57.350548+00:00
-- url     : https://prove2.me/submissions/35fe93f1-a4ac-44d6-9f20-28ca72939f4b

import Definitions.Def_NearLinearRSP_TwoResources_Implementation_Foundations

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

universe u_1

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem ramStep_of_halted (p : Program) (input : RAMInput) (S : RAMState)
    (h : S.halted = true) : ramStep p input S = S := by
  simp [ramStep, h]

private theorem execute_add (p : Program) (input : RAMInput) (a b : ℕ) (S : RAMState) :
    execute p input (a + b) S = execute p input b (execute p input a S) := by
  induction b with
  | zero => simp [execute]
  | succ b ih =>
      change ramStep p input (execute p input (a + b) S) =
        ramStep p input (execute p input b (execute p input a S))
      exact congrArg (ramStep p input) ih

private theorem execute_of_halted (p : Program) (input : RAMInput) (k : ℕ) (S : RAMState)
    (h : S.halted = true) : execute p input k S = S := by
  induction k with
  | zero => rfl
  | succ k ih => rw [execute, ih, ramStep_of_halted p input S h]

private theorem Execution.steps_pos {p : Program} {input : RAMInput}
    {initial final : RAMState} {k : ℕ} (h : Execution p input initial final k)
    (hi : initial.halted = false) : 0 < k := by
  by_contra hn
  have hk : k = 0 := by omega
  subst k
  have heq : initial = final := h.1
  have : initial.halted = true := by
    rw [heq]
    exact h.2.1
  simp [hi] at this

private theorem Execution.steps_unique {p : Program} {input : RAMInput}
    {initial final₁ final₂ : RAMState} {k₁ k₂ : ℕ}
    (h₁ : Execution p input initial final₁ k₁)
    (h₂ : Execution p input initial final₂ k₂) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · have hf := h₂.2.2 k₁ hlt
    rw [h₁.1, h₁.2.1] at hf
    contradiction
  · exact heq
  · have hf := h₁.2.2 k₂ hgt
    rw [h₂.1, h₂.2.1] at hf
    contradiction

private theorem Execution.deterministic {p : Program} {input : RAMInput}
    {initial final₁ final₂ : RAMState} {k₁ k₂ : ℕ}
    (h₁ : Execution p input initial final₁ k₁)
    (h₂ : Execution p input initial final₂ k₂) :
    k₁ = k₂ ∧ final₁ = final₂ := by
  have hk := h₁.steps_unique h₂
  refine ⟨hk, ?_⟩
  rw [← h₁.1, ← h₂.1, hk]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
namespace Mission

private theorem countdown_prefix (input : RAMInput) :
    execute countdownProgram input 10 initialState =
      countdownLoopState (512 / (input.reals 0 / 4) ^ 2) 0 := by
  simp [execute, countdownProgram, ramStep, initialState, evalReal,
    countdownLoopState, Function.update, pow_two]
  funext a
  by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;> by_cases h2 : a = 2 <;>
    simp_all

private theorem countdown_iteration (input : RAMInput) (x : ℝ) (k : ℕ)
    (hk : (k : ℝ) < x) :
    execute countdownProgram input 4 (countdownLoopState x k) =
      countdownLoopState x (k + 1) := by
  simp [execute, countdownProgram, ramStep, countdownLoopState, realTest,
    evalReal, evalNat, hk, Function.update, Nat.cast_add, Nat.cast_one]

private theorem countdown_iterations (input : RAMInput) (x : ℝ) (k : ℕ)
    (hk : k ≤ Nat.ceil x) :
    execute countdownProgram input (4 * k) (countdownLoopState x 0) =
      countdownLoopState x k := by
  induction k with
  | zero => simp [execute]
  | succ k ih =>
      have hk' : k < Nat.ceil x := by omega
      have hx : (k : ℝ) < x := Nat.lt_ceil.mp hk'
      rw [Nat.mul_succ, execute_add, ih (by omega)]
      exact countdown_iteration input x k hx

private theorem countdown_exit (input : RAMInput) (x : ℝ) :
    execute countdownProgram input 4 (countdownLoopState x (Nat.ceil x)) =
      countdownFinalState x := by
  have hx : ¬(Nat.ceil x : ℝ) < x := not_lt.mpr (Nat.le_ceil x)
  simp [execute, countdownProgram, ramStep, countdownLoopState, countdownFinalState,
    realTest, hx, Function.update]

private theorem countdown_evaluation (input : RAMInput) :
    execute countdownProgram input
      (14 + 4 * Nat.ceil (512 / (input.reals 0 / 4) ^ 2)) initialState =
      countdownFinalState (512 / (input.reals 0 / 4) ^ 2) := by
  let x := 512 / (input.reals 0 / 4) ^ 2
  change execute countdownProgram input (14 + 4 * Nat.ceil x) initialState =
    countdownFinalState x
  rw [show 14 + 4 * Nat.ceil x = 10 + 4 * Nat.ceil x + 4 by omega,
    execute_add, execute_add, countdown_prefix]
  rw [countdown_iterations input x (Nat.ceil x) le_rfl, countdown_exit]

private theorem execution_of_bounded_halt (p : Program) (input : RAMInput)
    (initial : RAMState) (n : ℕ)
    (hh : (execute p input n initial).halted = true) :
    ∃ steps ≤ n, Execution p input initial (execute p input n initial) steps := by
  let h : ∃ k : ℕ, (execute p input k initial).halted = true := ⟨n, hh⟩
  let k := Nat.find h
  have hk : k ≤ n := Nat.find_min' h hh
  have heq : execute p input k initial = execute p input n initial := by
    rw [show n = k + (n - k) by omega, execute_add,
      execute_of_halted p input (n - k) _ (Nat.find_spec h)]
  refine ⟨k, hk, heq, hh, ?_⟩
  intro j hj
  have hn := Nat.find_min h hj
  cases he : (execute p input j initial).halted with
  | false => rfl
  | true => exact False.elim (hn he)

private theorem countdownProgram_correct (I : Instance) (ε : ℝ) :
    ∃ (steps : ℕ) (out : RAMState),
      Execution countdownProgram (encodeInput I ε) initialState out steps ∧
      steps ≤ 14 + 4 * outerQ ε ∧ out.nm 0 = outerQ ε := by
  let x := 512 / (ε / 4) ^ 2
  have he := countdown_evaluation (encodeInput I ε)
  change execute countdownProgram (encodeInput I ε)
    (14 + 4 * outerQ ε) initialState = countdownFinalState x at he
  have hh : (execute countdownProgram (encodeInput I ε)
      (14 + 4 * outerQ ε) initialState).halted = true := by
    rw [he]
    rfl
  obtain ⟨steps, hs, hx⟩ := execution_of_bounded_halt countdownProgram
    (encodeInput I ε) initialState (14 + 4 * outerQ ε) hh
  refine ⟨steps, countdownFinalState x, ?_, hs, ?_⟩
  · rwa [he] at hx
  · simp [countdownFinalState, outerQ, x]

private theorem countdownProgram_cost (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (steps : ℕ) (out : RAMState),
      Execution countdownProgram (encodeInput I ε) initialState out steps ∧
      (steps : ℝ) ≤ 32786 / ε ^ 2 ∧ out.nm 0 = outerQ ε := by
  obtain ⟨steps, out, he, hs, ho⟩ := countdownProgram_correct I ε
  refine ⟨steps, out, he, ?_, ho⟩
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hsq1 : ε ^ 2 ≤ 1 := by nlinarith
  have hq := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 512 / (ε / 4) ^ 2 by positivity)
  have hid : (512 : ℝ) / (ε / 4) ^ 2 = 8192 / ε ^ 2 := by ring
  rw [hid] at hq
  have hout : (outerQ ε : ℝ) < 8192 / ε ^ 2 + 1 := by
    simpa only [outerQ, hid] using hq
  have hs' : (steps : ℝ) ≤ 14 + 4 * (outerQ ε : ℝ) := by exact_mod_cast hs
  apply (le_div_iff₀ hsq).mpr
  have hm := mul_le_mul_of_nonneg_right hs' hsq.le
  have hqmul := mul_le_mul_of_nonneg_right hout.le hsq.le
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hsq), one_mul] at hqmul
  nlinarith

end Mission
end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Structured

private theorem initialStore_at : initialStore.at 0 = initialState := rfl

private theorem queryStore_at (snapshot : RAMState) (target : ℕ) :
    (queryStore snapshot target).at 0 = queryStart snapshot target := rfl

private theorem Cmd.compile_length (c : Cmd) (base : ℕ) : (c.compile base).length = c.size := by
  induction c generalizing base <;> simp_all [compile, size] <;> omega

private theorem run_countdown_loop (input : RAMInput) (g : Guard) (body : Cmd)
    (state : ℕ → Store) (bodyCost : ℕ → ℕ)
    (hexit : g.eval (state 0) = false)
    (hguard : ∀ k, g.eval (state (k + 1)) = true)
    (hbody : ∀ k, Run input body (state (k + 1)) (state k) (bodyCost (k + 1)))
    (k : ℕ) : Run input (.loop g body) (state k) (state 0) (loopCost bodyCost k) := by
  induction k with
  | zero => exact Run.loopFalse hexit
  | succ k ih => exact Run.loopTrue (hguard k) (hbody k) ih

private theorem loopCost_le (bodyCost : ℕ → ℕ) (bound k : ℕ)
    (h : ∀ j, 1 ≤ j → j ≤ k → bodyCost j ≤ bound) :
    loopCost bodyCost k ≤ (bound + 2) * k + 1 := by
  induction k with
  | zero => simp [loopCost]
  | succ k ih =>
      have hlast := h (k + 1) (by omega) le_rfl
      have hprev := ih (fun j hj hjk => h j hj (by omega))
      simp only [loopCost, Nat.mul_succ]
      omega

private theorem CodeAt.left {p a b : Program} {base : ℕ} (h : CodeAt p base (a ++ b)) :
    CodeAt p base a := by
  intro i hi
  rw [h i (by simpa using lt_of_lt_of_le hi (Nat.le_add_right a.length b.length)),
    List.getElem?_append_left hi]

private theorem CodeAt.right {p a b : Program} {base : ℕ} (h : CodeAt p base (a ++ b)) :
    CodeAt p (base + a.length) b := by
  intro i hi
  rw [Nat.add_assoc, h (a.length + i) (by simp only [List.length_append]; omega),
    List.getElem?_append_right (by omega)]
  simp

private theorem CodeAt.head {p : Program} {base : ℕ} {i : RAMInstr} {code : Program}
    (h : CodeAt p base (i :: code)) : p[base]?.getD .halt = i := by
  have hh := h 0 (by simp)
  simpa using congrArg (fun o => o.getD .halt) hh

private theorem codeAt_prefix (pre code post : Program) :
    CodeAt (pre ++ code ++ post) pre.length code := by
  intro i hi
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
    List.getElem?_append_right (by omega)]
  simp

private theorem atom_step (a : Atom) (input : RAMInput) (s : Store) (pc : ℕ) (p : Program)
    (h : p[pc]?.getD .halt = a.val) :
    ramStep p input (s.at pc) = (a.eval input s).at (pc + 1) := by
  rcases a with ⟨a, ha⟩
  cases a <;> simp_all [ramStep, Atom.eval, Store.at, Store.ofRAM, IsAtom]
  all_goals
    change False at ha
    contradiction

private theorem guard_step (g : Guard) (input : RAMInput) (s : Store)
    (pc yes no : ℕ) (p : Program) (h : p[pc]?.getD .halt = g.instr yes no) :
    ramStep p input (s.at pc) = s.at (if g.eval s then yes else no) := by
  cases g <;> simp_all [ramStep, Store.at, Guard.instr, Guard.eval]
  all_goals rfl

private theorem jump_step (input : RAMInput) (s : Store) (pc target : ℕ) (p : Program)
    (h : p[pc]?.getD .halt = .jump target) :
    ramStep p input (s.at pc) = s.at target := by
  simp [ramStep, Store.at, h]

private theorem compile_correct {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (hrun : Run input c s t n) :
    ∀ (p : Program) (base : ℕ), CodeAt p base (c.compile base) →
      execute p input n (s.at base) = t.at (base + c.size) := by
  induction hrun with
  | skip s =>
      intro p base hc
      simp [execute, Cmd.size]
  | atom a s =>
      intro p base hc
      exact atom_step a input s base p (CodeAt.head hc)
  | @seq a b s u t n m ha hb iha ihb =>
      intro p base hc
      have hca : CodeAt p base (a.compile base) := CodeAt.left hc
      have hcb : CodeAt p (base + a.size) (b.compile (base + a.size)) := by
        simpa only [Cmd.compile_length] using CodeAt.right hc
      rw [execute_add, iha p base hca, ihb p (base + a.size) hcb]
      simp [Cmd.size, Nat.add_assoc]
  | @branchTrue g a b s t n hg ha iha =>
      intro p base hc
      have hc' : CodeAt p base ([g.instr (base + 1) (base + 1 + a.size + 1)] ++
          (a.compile (base + 1) ++
            ([.jump (base + (1 + a.size + 1 + b.size))] ++
              b.compile (base + 1 + a.size + 1)))) := by
        simpa only [Cmd.compile, List.append_assoc] using hc
      have hrest : CodeAt p (base + 1) (a.compile (base + 1) ++
          ([.jump (base + (1 + a.size + 1 + b.size))] ++
            b.compile (base + 1 + a.size + 1))) := by
        simpa only [List.length_singleton] using hc'.right
      have hafter : CodeAt p (base + 1 + a.size)
          ([.jump (base + (1 + a.size + 1 + b.size))] ++
            b.compile (base + 1 + a.size + 1)) := by
        simpa only [Cmd.compile_length] using hrest.right
      have hguard : execute p input 1 (s.at base) = s.at (base + 1) := by
        change ramStep p input (s.at base) = _
        rw [guard_step g input s base _ _ p hc'.head, hg]
        rfl
      rw [execute_add, execute_add, hguard, iha p (base + 1) hrest.left]
      exact jump_step input t (base + 1 + a.size) _ p hafter.head
  | @branchFalse g a b s t n hg hb ihb =>
      intro p base hc
      have hc' : CodeAt p base ([g.instr (base + 1) (base + 1 + a.size + 1)] ++
          (a.compile (base + 1) ++
            ([.jump (base + (1 + a.size + 1 + b.size))] ++
              b.compile (base + 1 + a.size + 1)))) := by
        simpa only [Cmd.compile, List.append_assoc] using hc
      have hrest : CodeAt p (base + 1) (a.compile (base + 1) ++
          ([.jump (base + (1 + a.size + 1 + b.size))] ++
            b.compile (base + 1 + a.size + 1))) := by
        simpa only [List.length_singleton] using hc'.right
      have hafter : CodeAt p (base + 1 + a.size)
          ([.jump (base + (1 + a.size + 1 + b.size))] ++
            b.compile (base + 1 + a.size + 1)) := by
        simpa only [Cmd.compile_length] using hrest.right
      have hcb : CodeAt p (base + 1 + a.size + 1)
          (b.compile (base + 1 + a.size + 1)) := by
        simpa only [List.length_singleton] using hafter.right
      have hguard : execute p input 1 (s.at base) =
          s.at (base + 1 + a.size + 1) := by
        change ramStep p input (s.at base) = _
        rw [guard_step g input s base _ _ p hc'.head, hg]
        rfl
      rw [execute_add, hguard, ihb p _ hcb]
      simp [Cmd.size, Nat.add_assoc]
  | @loopFalse g body s hg =>
      intro p base hc
      have hhead : p[base]?.getD .halt =
          g.instr (base + 1) (base + (1 + body.size + 1)) :=
        CodeAt.head hc
      change ramStep p input (s.at base) = _
      rw [guard_step g input s base _ _ p hhead, hg]
      rfl
  | @loopTrue g body s u t n m hg hb hl ihb ihl =>
      intro p base hc
      have hc' : CodeAt p base
          ([g.instr (base + 1) (base + (1 + body.size + 1))] ++
            (body.compile (base + 1) ++ [.jump base])) := by
        simpa only [Cmd.compile, List.append_assoc] using hc
      have hrest : CodeAt p (base + 1)
          (body.compile (base + 1) ++ [.jump base]) := by
        simpa only [List.length_singleton] using hc'.right
      have hafter : CodeAt p (base + 1 + body.size) [.jump base] := by
        simpa only [Cmd.compile_length] using hrest.right
      have hguard : execute p input 1 (s.at base) = s.at (base + 1) := by
        change ramStep p input (s.at base) = _
        rw [guard_step g input s base _ _ p hc'.head, hg]
        rfl
      have hcycle : execute p input (1 + n + 1) (s.at base) = u.at base := by
        rw [execute_add, execute_add, hguard, ihb p (base + 1) hrest.left]
        exact jump_step input u (base + 1 + body.size) base p hafter.head
      rw [execute_add, hcycle]
      exact ihl p base hc

private theorem compiled_execution {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) :
    ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input (s.at 0) out steps ∧ steps ≤ n + 1 ∧
      Store.ofRAM out = t := by
  have hc : CodeAt c.program 0 (c.compile 0) := by
    simpa [Cmd.program] using codeAt_prefix [] (c.compile 0) [.halt]
  have hrun : execute c.program input n (s.at 0) = t.at c.size := by
    simpa using compile_correct h c.program 0 hc
  have hfetch : c.program[c.size]?.getD .halt = .halt := by
    simp [Cmd.program, List.getElem?_append_right, Cmd.compile_length]
  have hfinal : execute c.program input (n + 1) (s.at 0) =
      { t.at c.size with halted := true } := by
    rw [execute, hrun]
    simp [ramStep, Store.at, hfetch]
  have hh : (execute c.program input (n + 1) (s.at 0)).halted = true := by
    rw [hfinal]
  obtain ⟨steps, hs, hx⟩ := execution_of_bounded_halt c.program input
    (s.at 0) (n + 1) hh
  refine ⟨steps, { t.at c.size with halted := true }, ?_, hs, ?_⟩
  · rwa [hfinal] at hx
  · rfl

private theorem compiled_preprocessing {input : RAMInput} {c : Cmd} {t : Store} {n : ℕ}
    (h : Run input c initialStore t n) :
    ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input initialState out steps ∧ steps ≤ n + 1 ∧
      Store.ofRAM out = t := by
  simpa only [initialStore_at] using compiled_execution h

private theorem compiled_query {input : RAMInput} {c : Cmd} {t : Store} {n : ℕ}
    (snapshot : RAMState) (target : ℕ)
    (h : Run input c (queryStore snapshot target) t n) :
    ∃ (steps : ℕ) (out : RAMState),
      Execution c.program input (queryStart snapshot target) out steps ∧
      steps ≤ n + 1 ∧ Store.ofRAM out = t := by
  simpa only [queryStore_at] using compiled_execution h

end Structured
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem standalone_RSP_FirstMin__fold_choice_le_seed {α : Type} (f : α → ℝ) (xs : List α) (x : α) :
    f (xs.foldl (fun a b => if f b < f a then b else a) x) ≤ f x := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      apply (ih _).trans
      split_ifs with h
      · exact h.le
      · exact le_rfl

private theorem standalone_RSP_FirstMin__fold_choice_le_member {α : Type} (f : α → ℝ) (xs : List α)
    (x y : α) (hy : y ∈ xs) :
    f (xs.foldl (fun a b => if f b < f a then b else a) x) ≤ f y := by
  induction xs generalizing x with
  | nil => simp at hy
  | cons z zs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hy with rfl | hy
      · apply (standalone_RSP_FirstMin__fold_choice_le_seed f zs _).trans
        split_ifs with h
        · exact le_rfl
        · exact le_of_not_gt h
      · exact ih _ hy

private theorem firstMin_le_of_mem {α : Type} (f : α → ℝ) (xs : List α)
    (fallback y : α) (hy : y ∈ xs) :
    f (firstMin f xs fallback) ≤ f y :=
  standalone_RSP_FirstMin__fold_choice_le_member f xs (xs.headD fallback) y hy

private theorem standalone_RSP_FirstMin__fold_choice_pred {α : Type} (f : α → ℝ) (xs : List α)
    (P : α → Prop) (x : α) (hx : P x) (hall : ∀ y ∈ xs, P y) :
    P (xs.foldl (fun a b => if f b < f a then b else a) x) := by
  induction xs generalizing x with
  | nil => exact hx
  | cons y ys ih =>
      simp only [List.foldl_cons]
      apply ih
      · split_ifs
        · exact hall y (by simp)
        · exact hx
      · intro z hz
        exact hall z (by simp [hz])

private theorem firstMin_mem {α : Type} (f : α → ℝ) (xs : List α) (fallback : α)
    (h : xs ≠ []) : firstMin f xs fallback ∈ xs := by
  unfold firstMin
  apply standalone_RSP_FirstMin__fold_choice_pred f xs (· ∈ xs)
  · cases xs with
    | nil => contradiction
    | cons x xs => simp
  · intro y hy
    exact hy

private theorem dp_faithfulness_saturated (A : InnerInput) (T : Table) (u v i j : ℕ)
    (h : tickLimit A ≤ i ∨ tickLimit A ≤ j) :
    dpValue A T v i j = edgeExpectation A T u v i j := by
  simp [dpValue, edgeExpectation, h]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue

@[simp] private theorem choose_none_left {α : Type} (key : α → ℝ) (x : Option α) :
    choose key none x = x := rfl

@[simp] private theorem choose_none_right {α : Type} (key : α → ℝ) (x : Option α) :
    choose key x none = x := by cases x <;> rfl

private theorem choose_assoc {α : Type} (key : α → ℝ) (a b c : Option α) :
    choose key (choose key a b) c = choose key a (choose key b c) := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      cases c with
      | none => simp
      | some c =>
        by_cases hab : key b < key a
        · by_cases hbc : key c < key b
          · simp [choose, hab, hbc, hbc.trans hab]
          · simp [choose, hab, hbc]
        · by_cases hbc : key c < key b
          · simp [choose, hab, hbc]
          · have hac : ¬ key c < key a := by linarith
            simp [choose, hab, hbc, hac]

private theorem fold_choose {α : Type} (key : α → ℝ) (xs : List α) (a : Option α) :
    xs.foldl (fun a b => choose key a (some b)) a = choose key a (winner key xs) := by
  induction xs generalizing a with
  | nil => simp [winner]
  | cons x xs ih =>
      change xs.foldl (fun a b => choose key a (some b)) (choose key a (some x)) =
        choose key a (xs.foldl (fun a b => choose key a (some b)) (some x))
      rw [ih (choose key a (some x)), ih (some x)]
      exact choose_assoc key a (some x) _

private theorem winner_append {α : Type} (key : α → ℝ) (xs ys : List α) :
    winner key (xs ++ ys) = choose key (winner key xs) (winner key ys) := by
  exact (List.foldl_append ..).trans (fold_choose key ys _)

@[simp] private theorem winner_nil {α : Type} (key : α → ℝ) : winner key [] = none := rfl

@[simp] private theorem winner_singleton {α : Type} (key : α → ℝ) (x : α) :
    winner key [x] = some x := rfl

private theorem fold_some {α : Type} (key : α → ℝ) (xs : List α) (x : α) :
    xs.foldl (fun a b => choose key a (some b)) (some x) =
      some (xs.foldl (fun a b => if key b < key a then b else a) x) := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
      simp only [List.foldl_cons, choose]
      split_ifs <;> exact ih _

private theorem winner_eq_firstMin {α : Type} (key : α → ℝ) (xs : List α)
    (fallback : α) (hne : xs ≠ []) :
    winner key xs = some (firstMin key xs fallback) := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simp only [winner, firstMin, List.headD_cons, List.foldl_cons, choose,
        lt_self_iff_false, if_false]
      exact fold_some key xs x

private theorem Tree.champion_eq_winner {α : Type} (key : α → ℝ) {h : ℕ} (t : Tree α h) :
    t.champion key = winner key t.leaves := by
  induction t with
  | leaf x => cases x <;> rfl
  | node l r ihl ihr => simp only [champion, leaves, ihl, ihr, winner_append]

private theorem Tree.champion_eq_firstMin {α : Type} (key : α → ℝ) {h : ℕ}
    (t : Tree α h) (fallback : α) (hne : t.leaves ≠ []) :
    t.champion key = some (firstMin key t.leaves fallback) := by
  rw [t.champion_eq_winner key]
  exact winner_eq_firstMin key t.leaves fallback hne

private theorem Path.index_lt {h : ℕ} (p : Path h) : p.index < 2 ^ h := by
  induction p with
  | done => decide
  | @left h p ih => simp only [index, pow_succ]; omega
  | @right h p ih => simp only [index, pow_succ]; omega

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

@[ext] private theorem store_ext (s t : Store)
    (hnr : ∀ a, s.nr a = t.nr a) (hrr : ∀ a, s.rr a = t.rr a)
    (hnm : ∀ a, s.nm a = t.nm a) (hrm : ∀ a, s.rm a = t.rm a) : s = t := by
  cases s
  cases t
  simp only [Store.mk.injEq]
  exact ⟨funext hnr, funext hrr, funext hnm, funext hrm⟩

private theorem run_atoms (input : RAMInput) (as : List Atom) (s : Store) :
    Run input (atoms as) s (evalAtoms input as s) as.length := by
  induction as generalizing s with
  | nil => exact Run.skip s
  | cons a as ih =>
      simpa only [atoms, evalAtoms, List.foldl_cons, List.length_cons, Nat.add_comm] using
        Run.seq (Run.atom a s) (ih (a.eval input s))

private theorem merge_decode (a b : Record) :
    (merge a b).decode = choose Record.key a.decode b.decode := by
  unfold merge Record.decode
  split_ifs <;> simp_all [choose]

private theorem loadChildren_eval (input : RAMInput) (s : Store) :
    evalAtoms input loadChildren s = loaded s := by
  ext a <;> simp [evalAtoms, loadChildren, Atom.eval, ramStep, Store.at, Store.ofRAM,
    loaded, evalNat, Function.update]
  by_cases h : a = 7 <;> simp [h]

private theorem storeLeft_eval (input : RAMInput) (s : Store) :
    evalAtoms input storeLeft s = writeRecord s (s.nr 7) ⟨s.nr 8, s.rr 0⟩ := by
  rfl

private theorem storeRight_eval (input : RAMInput) (s : Store) :
    evalAtoms input storeRight s = writeRecord s (s.nr 7) ⟨s.nr 9, s.rr 1⟩ := by
  rfl

private theorem selectChild_run (input : RAMInput) (s : Store) (hz : s.nr 3 = 0) :
    ∃ k ≤ 6, Run input selectChild s
      (writeRecord s (s.nr 7) (merge ⟨s.nr 8, s.rr 0⟩ ⟨s.nr 9, s.rr 1⟩)) k := by
  have hl := run_atoms input storeLeft s
  have hr := run_atoms input storeRight s
  rw [storeLeft_eval] at hl
  rw [storeRight_eval] at hr
  by_cases hright : s.nr 9 = 0
  · refine ⟨4, by omega, ?_⟩
    simpa [selectChild, merge, hright, storeLeft, storeRight] using
      (Run.branchTrue (a := atoms storeLeft)
        (b := .branch (.nat .eq 8 3) (atoms storeRight)
          (.branch (.real .lt 1 0) (atoms storeRight) (atoms storeLeft)))
        (g := Guard.nat .eq 9 3) (by simp [Guard.eval, natTest, hz, hright]) hl)
  · by_cases hleft : s.nr 8 = 0
    · refine ⟨5, by omega, ?_⟩
      have hinner := Run.branchTrue (g := Guard.nat .eq 8 3)
        (b := .branch (.real .lt 1 0) (atoms storeRight) (atoms storeLeft))
        (by simp [Guard.eval, natTest, hz, hleft]) hr
      simpa [selectChild, merge, hright, hleft, storeLeft, storeRight] using
        Run.branchFalse (a := atoms storeLeft) (g := Guard.nat .eq 9 3)
          (by simp [Guard.eval, natTest, hz, hright]) hinner
    · by_cases hkey : s.rr 1 < s.rr 0
      · refine ⟨6, by omega, ?_⟩
        have hinner := Run.branchTrue (g := Guard.real .lt 1 0) (b := atoms storeLeft)
          (by simp [Guard.eval, realTest, hkey]) hr
        have hmiddle := Run.branchFalse (a := atoms storeRight) (g := Guard.nat .eq 8 3)
          (by simp [Guard.eval, natTest, hz, hleft]) hinner
        simpa [selectChild, merge, hright, hleft, hkey, storeLeft, storeRight] using
          Run.branchFalse (a := atoms storeLeft) (g := Guard.nat .eq 9 3)
            (by simp [Guard.eval, natTest, hz, hright]) hmiddle
      · refine ⟨5, by omega, ?_⟩
        have hinner := Run.branchFalse (g := Guard.real .lt 1 0) (a := atoms storeRight)
          (by simp [Guard.eval, realTest, hkey]) hl
        have hmiddle := Run.branchFalse (a := atoms storeRight) (g := Guard.nat .eq 8 3)
          (by simp [Guard.eval, natTest, hz, hleft]) hinner
        simpa [selectChild, merge, hright, hleft, hkey, storeLeft, storeRight] using
          Run.branchFalse (a := atoms storeLeft) (g := Guard.nat .eq 9 3)
            (by simp [Guard.eval, natTest, hz, hright]) hmiddle

private theorem refreshNode_run (input : RAMInput) (s : Store) (hz : s.nr 3 = 0) :
    ∃ k ≤ 15, Run input refreshNode s (refreshed s) k := by
  have hload := run_atoms input loadChildren s
  rw [loadChildren_eval] at hload
  obtain ⟨k, hk, hselect⟩ := selectChild_run input (loaded s) (by simp [loaded, hz])
  refine ⟨9 + k, by omega, ?_⟩
  have hrun := Run.seq hload hselect
  simpa [refreshNode, loadChildren, refreshed, loaded, readRecord] using hrun

private theorem refreshed_record (s : Store) :
    readRecord (refreshed s) (s.nr 1 + s.nr 0) =
      merge (readRecord s (s.nr 1 + (s.nr 0 + s.nr 0)))
        (readRecord s (s.nr 1 + (s.nr 0 + s.nr 0 + s.nr 4))) := by
  simp [readRecord, refreshed, writeRecord]

private theorem refreshed_other (s : Store) (a : ℕ) (ha : a ≠ s.nr 1 + s.nr 0) :
    (refreshed s).nm a = s.nm a ∧ (refreshed s).rm a = s.rm a := by
  simp [refreshed, writeRecord, loaded, Function.update_of_ne ha]

private theorem refreshed_header (s : Store) (a : ℕ) (ha : a < 5) :
    (refreshed s).nr a = s.nr a := by
  simp [refreshed, writeRecord, loaded, Function.update_of_ne (show a ≠ 5 by omega),
    Function.update_of_ne (show a ≠ 6 by omega), Function.update_of_ne (show a ≠ 7 by omega),
    Function.update_of_ne (show a ≠ 8 by omega), Function.update_of_ne (show a ≠ 9 by omega)]

private theorem parentHop_eval (input : RAMInput) (s : Store) :
    evalAtoms input parentHop s = advanced s := by
  ext a <;> simp [evalAtoms, parentHop, Atom.eval, ramStep, Store.at, Store.ofRAM,
    advanced, evalNat, Function.update]

private theorem repairBody_run (input : RAMInput) (s : Store) (hz : s.nr 3 = 0) :
    ∃ k ≤ 17, Run input repairBody s (repairStep s) k := by
  obtain ⟨k, hk, hrefresh⟩ := refreshNode_run input s hz
  have hhop := run_atoms input parentHop (refreshed s)
  rw [parentHop_eval] at hhop
  refine ⟨k + 2, by omega, ?_⟩
  exact Run.seq hrefresh hhop

@[simp] private theorem hops_zero : hops 0 = 0 := by rw [hops]; simp

private theorem hops_pos (n : ℕ) (hn : 0 < n) : hops n = hops (n / 2) + 1 := by
  rw [hops, dif_neg (Nat.ne_of_gt hn)]

private theorem hops_le_of_lt_pow (n h : ℕ) (hn : n < 2 ^ h) : hops n ≤ h := by
  induction h generalizing n with
  | zero =>
      have : n = 0 := by simpa using hn
      subst n
      simp
  | succ h ih =>
      by_cases hzero : n = 0
      · subst n; simp
      · rw [hops_pos n (Nat.pos_of_ne_zero hzero)]
        have hdiv : n / 2 < 2 ^ h := by
          apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
          simpa [pow_succ] using hn
        exact Nat.add_le_add_right (ih _ hdiv) 1

private theorem hops_le_clog (n capacity : ℕ) (hn : n < capacity) :
    hops n ≤ Nat.clog 2 capacity :=
  hops_le_of_lt_pow n _ (hn.trans_le (Nat.le_pow_clog (by decide) capacity))

private theorem repairStep_header (s : Store) (a : ℕ) (ha : 0 < a) (ha' : a < 5) :
    (repairStep s).nr a = s.nr a := by
  simp only [repairStep, advanced]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  exact refreshed_header s a ha'

private theorem repairStep_parent (capacity : ℕ) (s : Store) (h : ParentLayout capacity s) :
    (repairStep s).nr 0 = s.nr 0 / 2 := by
  have hspace := h.2.1
  have hnode := h.1
  have haddr : s.nr 2 + s.nr 0 ≠ s.nr 1 + s.nr 0 := by omega
  have hmem := (refreshed_other s _ haddr).1
  simp only [repairStep, advanced, Function.update_self]
  rw [refreshed_header s 2 (by omega), refreshed_header s 0 (by omega), hmem]
  exact h.2.2.2 _ h.1

private theorem repairStep_layout (capacity : ℕ) (s : Store) (h : ParentLayout capacity s) :
    ParentLayout capacity (repairStep s) := by
  have hspace := h.2.1
  have hnode := h.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [repairStep_parent capacity s h]
    exact (Nat.div_le_self _ _).trans_lt h.1
  · simpa only [repairStep_header s 1 (by omega) (by omega),
      repairStep_header s 2 (by omega) (by omega)] using h.2.1
  · simpa only [repairStep_header s 3 (by omega) (by omega)] using h.2.2.1
  · intro u hu
    rw [repairStep_header s 2 (by omega) (by omega)]
    change (refreshed s).nm (s.nr 2 + u) = _
    rw [(refreshed_other s _ (by omega)).1]
    exact h.2.2.2 u hu

private theorem repairAncestors_run (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s) :
    ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * hops (s.nr 0) + 1 ∧ out.nr 0 = 0 ∧ ParentLayout capacity out := by
  generalize hn : s.nr 0 = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hzero : n = 0
      · refine ⟨s, 1, ?_, ?_, by omega, h⟩
        · exact Run.loopFalse (by simp [Guard.eval, natTest, h.2.2.1, hn, hzero])
        · simp [hn, hzero]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hstep := repairStep_parent capacity s h
        rw [hn] at hstep
        obtain ⟨midCost, hcost, hbody⟩ := repairBody_run input s h.2.2.1
        obtain ⟨out, tailCost, htail, htailCost, hout, hlayout⟩ :=
          ih (n / 2) (Nat.div_lt_self hnpos (by decide)) (repairStep s)
            (repairStep_layout capacity s h) hstep
        refine ⟨out, 1 + midCost + 1 + tailCost, ?_, ?_, hout, hlayout⟩
        · exact Run.loopTrue (by simp [Guard.eval, natTest, h.2.2.1, hn, hnpos]) hbody htail
        · rw [hops_pos n hnpos]
          omega

private theorem repairAncestors_logarithmic (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s) :
    ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * Nat.clog 2 capacity + 1 ∧ out.nr 0 = 0 ∧ ParentLayout capacity out := by
  obtain ⟨out, k, hrun, hk, hz, hp⟩ := repairAncestors_run input capacity s h
  refine ⟨out, k, hrun, hk.trans ?_, hz, hp⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 19 (hops_le_clog _ _ h.1)) 1

@[simp] private theorem ancestors_zero : ancestors 0 = [] := by rw [ancestors]; simp

private theorem ancestors_pos (n : ℕ) (hn : 0 < n) :
    ancestors n = n :: ancestors (n / 2) := by
  rw [ancestors, dif_neg (Nat.ne_of_gt hn)]

private theorem le_of_mem_ancestors (n v : ℕ) (hv : v ∈ ancestors n) : v ≤ n := by
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
      by_cases hn : n = 0
      · subst n; simp at hv
      · rw [ancestors_pos n (Nat.pos_of_ne_zero hn), List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact le_rfl
        · exact (ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)) v hv).trans
            (Nat.div_le_self _ _)

private theorem repairStep_record_other (s : Store) (v : ℕ) (hv : v ≠ s.nr 0) :
    readRecord (repairStep s) (s.nr 1 + v) = readRecord s (s.nr 1 + v) := by
  have h := refreshed_other s (s.nr 1 + v) (by omega)
  change (⟨(refreshed s).nm _, (refreshed s).rm _⟩ : Record) = _
  rw [h.1, h.2]
  rfl

private theorem repairStep_ready (capacity : ℕ) (truth : ℕ → Record) (s : Store)
    (h : ParentLayout capacity s) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hinternal : s.nr 0 + s.nr 0 + 1 < capacity)
    (hc : Coherent capacity truth) (hr : Ready capacity truth s) :
    Ready capacity truth (repairStep s) := by
  have hleft : readRecord s (s.nr 1 + (s.nr 0 + s.nr 0)) = truth (s.nr 0 + s.nr 0) := by
    apply hr _ (by omega)
    intro hm
    have := le_of_mem_ancestors _ _ hm
    omega
  have hright : readRecord s (s.nr 1 + (s.nr 0 + s.nr 0 + 1)) =
      truth (s.nr 0 + s.nr 0 + 1) := by
    apply hr _ hinternal
    intro hm
    have := le_of_mem_ancestors _ _ hm
    omega
  intro v hv hnot
  rw [repairStep_header s 1 (by omega) (by omega)]
  by_cases heq : v = s.nr 0
  · subst v
    change readRecord (refreshed s) (s.nr 1 + s.nr 0) = _
    rw [refreshed_record, hone, hleft, hright]
    exact (hc _ hpositive hinternal).symm
  · rw [repairStep_record_other s v heq]
    apply hr v hv
    rw [ancestors_pos _ hpositive, List.mem_cons]
    rw [repairStep_parent capacity s h] at hnot
    exact not_or.mpr ⟨heq, hnot⟩

private theorem repairAncestors_correct (input : RAMInput) (capacity : ℕ)
    (truth : ℕ → Record) (s : Store) (h : ParentLayout capacity s)
    (hone : s.nr 4 = 1) (hinternal : s.nr 0 + s.nr 0 + 1 < capacity)
    (hc : Coherent capacity truth) (hr : Ready capacity truth s) :
    ∃ out k, Run input repairAncestors s out k ∧
      k ≤ 19 * hops (s.nr 0) + 1 ∧ out.nr 0 = 0 ∧
      (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout capacity out ∧
      ∀ v < capacity, readRecord out (s.nr 1 + v) = truth v := by
  generalize hn : s.nr 0 = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hzero : n = 0
      · refine ⟨s, 1, ?_, ?_, by omega, ?_, h, ?_⟩
        · exact Run.loopFalse (by simp [Guard.eval, natTest, h.2.2.1, hn, hzero])
        · simp [hn, hzero]
        · intro a _ _; rfl
        · intro v hv
          apply hr v hv
          simp [hn, hzero]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hstep := repairStep_parent capacity s h
        have hnode : (repairStep s).nr 0 = n / 2 := by simpa only [hn] using hstep
        have hinternal' : (repairStep s).nr 0 + (repairStep s).nr 0 + 1 < capacity := by
          rw [hstep]
          have := Nat.div_le_self (s.nr 0) 2
          omega
        have hready := repairStep_ready capacity truth s h hone (by omega) hinternal hc hr
        obtain ⟨midCost, hcost, hbody⟩ := repairBody_run input s h.2.2.1
        obtain ⟨out, tailCost, htail, htailCost, hout, hheader, hlayout, hrecords⟩ :=
          ih (n / 2) (Nat.div_lt_self hnpos (by decide)) (repairStep s)
            (repairStep_layout capacity s h)
            (by simpa [repairStep_header s 4 (by omega) (by omega)] using hone)
            hinternal' hready hnode
        refine ⟨out, 1 + midCost + 1 + tailCost, ?_, ?_, hout, ?_, hlayout, ?_⟩
        · exact Run.loopTrue (by simp [Guard.eval, natTest, h.2.2.1, hn, hnpos]) hbody htail
        · rw [hops_pos n hnpos]
          omega
        · intro a ha ha'
          exact (hheader a ha ha').trans (repairStep_header s a ha ha')
        · simpa only [repairStep_header s 1 (by omega) (by omega)] using hrecords

private theorem writeLeaf_eval (input : RAMInput) (s : Store) :
    evalAtoms input writeLeaf s = leafWritten s := by
  ext a <;> simp [evalAtoms, writeLeaf, Atom.eval, ramStep, Store.at, Store.ofRAM,
    leafWritten, writeRecord, evalNat, Function.update]

private theorem leafWritten_header (s : Store) (a : ℕ) (ha : a ≠ 7) :
    (leafWritten s).nr a = s.nr a := by
  simp [leafWritten, writeRecord, ha]

private theorem updateStart_header (s : Store) (a : ℕ) (ha : 0 < a) (ha' : a < 5) :
    (updateStart s).nr a = s.nr a := by
  simp [updateStart, advanced, Function.update_of_ne (show a ≠ 0 by omega),
    Function.update_of_ne (show a ≠ 7 by omega), leafWritten_header]
  exact leafWritten_header s a (by omega)

private theorem leafWritten_other (s : Store) (a : ℕ) (ha : a ≠ s.nr 1 + s.nr 0) :
    (leafWritten s).nm a = s.nm a ∧ (leafWritten s).rm a = s.rm a := by
  simp [leafWritten, writeRecord, Function.update_of_ne ha]

private theorem updateStart_parent (capacity : ℕ) (s : Store) (h : ParentLayout capacity s) :
    (updateStart s).nr 0 = s.nr 0 / 2 := by
  have hspace := h.2.1
  have hnode := h.1
  have haddr : s.nr 2 + s.nr 0 ≠ s.nr 1 + s.nr 0 := by omega
  simp only [updateStart, advanced, Function.update_self]
  rw [leafWritten_header s 2 (by omega), leafWritten_header s 0 (by omega),
    (leafWritten_other s _ haddr).1]
  exact h.2.2.2 _ h.1

private theorem updateStart_layout (capacity : ℕ) (s : Store) (h : ParentLayout capacity s) :
    ParentLayout capacity (updateStart s) := by
  have hspace := h.2.1
  have hnode := h.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [updateStart_parent capacity s h]
    exact (Nat.div_le_self _ _).trans_lt h.1
  · simpa only [updateStart_header s 1 (by omega) (by omega),
      updateStart_header s 2 (by omega) (by omega)] using h.2.1
  · simpa only [updateStart_header s 3 (by omega) (by omega)] using h.2.2.1
  · intro u hu
    rw [updateStart_header s 2 (by omega) (by omega)]
    change (leafWritten s).nm (s.nr 2 + u) = _
    rw [(leafWritten_other s _ (by omega)).1]
    exact h.2.2.2 u hu

private theorem updateStart_ready (capacity : ℕ) (truth : ℕ → Record) (s : Store)
    (h : ParentLayout capacity s) (hpositive : 0 < s.nr 0)
    (hr : Ready capacity truth s) (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 2⟩) :
    Ready capacity truth (updateStart s) := by
  intro v hv hnot
  rw [updateStart_header s 1 (by omega) (by omega)]
  by_cases heq : v = s.nr 0
  · subst v
    simp [updateStart, advanced, readRecord, leafWritten, writeRecord, hnew]
  · have haddr : s.nr 1 + v ≠ s.nr 1 + s.nr 0 := by omega
    have heqrecord : readRecord (updateStart s) (s.nr 1 + v) =
        readRecord s (s.nr 1 + v) := by
      change (⟨(leafWritten s).nm _, (leafWritten s).rm _⟩ : Record) = _
      rw [(leafWritten_other s _ haddr).1, (leafWritten_other s _ haddr).2]
      rfl
    rw [heqrecord]
    apply hr v hv
    rw [ancestors_pos _ hpositive, List.mem_cons]
    rw [updateStart_parent capacity s h] at hnot
    exact not_or.mpr ⟨heq, hnot⟩

private theorem updateLeaf_correct (input : RAMInput) (leaves : ℕ)
    (truth : ℕ → Record) (s : Store) (h : ParentLayout (2 * leaves) s)
    (hone : s.nr 4 = 1) (hpositive : 0 < s.nr 0)
    (hc : Coherent (2 * leaves) truth) (hr : Ready (2 * leaves) truth s)
    (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 2⟩) :
    ∃ out k, Run input updateLeaf s out k ∧
      k ≤ 19 * Nat.clog 2 (2 * leaves) + 6 ∧ out.nr 0 = 0 ∧
      (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout (2 * leaves) out ∧
      ∀ v < 2 * leaves, readRecord out (s.nr 1 + v) = truth v := by
  have hstart := updateStart_layout (2 * leaves) s h
  have hinternal : (updateStart s).nr 0 + (updateStart s).nr 0 + 1 < 2 * leaves := by
    rw [updateStart_parent (2 * leaves) s h]
    have hlt : s.nr 0 / 2 < leaves := by
      apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
      simpa [Nat.mul_comm] using h.1
    omega
  obtain ⟨out, tailCost, hrun, hcost, hz, hheader, hparents, hrecords⟩ :=
    repairAncestors_correct input (2 * leaves) truth (updateStart s) hstart
      (by simpa [updateStart_header s 4 (by omega) (by omega)] using hone)
      hinternal hc (updateStart_ready (2 * leaves) truth s h hpositive hr hnew)
  have hwrite := run_atoms input writeLeaf s
  rw [writeLeaf_eval] at hwrite
  have hhop := run_atoms input parentHop (leafWritten s)
  rw [parentHop_eval] at hhop
  refine ⟨out, 3 + (2 + tailCost), ?_, ?_, hz, ?_, hparents, ?_⟩
  · exact Run.seq hwrite (Run.seq hhop hrun)
  · have hlog := hops_le_clog ((updateStart s).nr 0) (2 * leaves) hstart.1
    omega
  · intro a ha ha'
    exact (hheader a ha ha').trans (updateStart_header s a ha ha')
  · simpa only [updateStart_header s 1 (by omega) (by omega)] using hrecords

private theorem run_final_unique {input : RAMInput} {c : Cmd} {s t u : Store} {n m : ℕ}
    (h : Run input c s t n) (h' : Run input c s u m) : t = u := by
  obtain ⟨k, out, hexec, _, hstore⟩ := compiled_execution h
  obtain ⟨k', out', hexec', _, hstore'⟩ := compiled_execution h'
  have heq := (hexec.deterministic hexec').2
  exact hstore.symm.trans ((congrArg Store.ofRAM heq).trans hstore')

private theorem WinnerFrame.refl (W capacity : ℕ) (s : Store) : WinnerFrame W capacity s s :=
  fun _ _ => ⟨rfl, rfl⟩

private theorem WinnerFrame.trans (W capacity : ℕ) (s u t : Store)
    (h : WinnerFrame W capacity s u) (h' : WinnerFrame W capacity u t) :
    WinnerFrame W capacity s t :=
  fun a ha => ⟨(h' a ha).1.trans (h a ha).1, (h' a ha).2.trans (h a ha).2⟩

private theorem repairStep_frame (capacity : ℕ) (s : Store) (hn : s.nr 0 < capacity) :
    WinnerFrame (s.nr 1) capacity s (repairStep s) := by
  intro a ha
  exact refreshed_other s a (by omega)

private theorem repairAncestors_run_frame (input : RAMInput) (capacity : ℕ) (s : Store)
    (h : ParentLayout capacity s) :
    ∃ out k, Run input repairAncestors s out k ∧ WinnerFrame (s.nr 1) capacity s out := by
  generalize hn : s.nr 0 = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hzero : n = 0
      · refine ⟨s, 1, ?_, WinnerFrame.refl _ _ _⟩
        exact Run.loopFalse (by simp [Guard.eval, natTest, h.2.2.1, hn, hzero])
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hzero
        have hstep : (repairStep s).nr 0 = n / 2 := by
          simpa only [hn] using repairStep_parent capacity s h
        obtain ⟨bodyCost, _, hbody⟩ := repairBody_run input s h.2.2.1
        obtain ⟨out, tailCost, htail, hframe⟩ := ih (n / 2)
          (Nat.div_lt_self hnpos (by decide)) (repairStep s) (repairStep_layout capacity s h) hstep
        refine ⟨out, 1 + bodyCost + 1 + tailCost, ?_, ?_⟩
        · exact Run.loopTrue (by simp [Guard.eval, natTest, h.2.2.1, hn, hnpos]) hbody htail
        · rw [repairStep_header s 1 (by omega) (by omega)] at hframe
          exact WinnerFrame.trans _ _ s (repairStep s) out (repairStep_frame capacity s h.1) hframe

private theorem repairAncestors_frame (input : RAMInput) (capacity : ℕ) (s out : Store) (k : ℕ)
    (h : ParentLayout capacity s) (hrun : Run input repairAncestors s out k) :
    WinnerFrame (s.nr 1) capacity s out := by
  obtain ⟨out', k', hrun', hframe⟩ := repairAncestors_run_frame input capacity s h
  rw [run_final_unique hrun hrun']
  exact hframe

private theorem updateStart_frame (capacity : ℕ) (s : Store) (hn : s.nr 0 < capacity) :
    WinnerFrame (s.nr 1) capacity s (updateStart s) := by
  intro a ha
  exact leafWritten_other s a (by omega)

private theorem updateLeaf_frame (input : RAMInput) (capacity : ℕ) (s out : Store) (k : ℕ)
    (h : ParentLayout capacity s) (hrun : Run input updateLeaf s out k) :
    WinnerFrame (s.nr 1) capacity s out := by
  obtain ⟨out', tailCost, htail, hframe⟩ :=
    repairAncestors_run_frame input capacity (updateStart s) (updateStart_layout capacity s h)
  have hwrite := run_atoms input writeLeaf s
  rw [writeLeaf_eval] at hwrite
  have hhop := run_atoms input parentHop (leafWritten s)
  rw [parentHop_eval] at hhop
  have hrun' : Run input updateLeaf s out' (3 + (2 + tailCost)) :=
    Run.seq hwrite (Run.seq hhop htail)
  rw [run_final_unique hrun hrun']
  rw [updateStart_header s 1 (by omega) (by omega)] at hframe
  exact WinnerFrame.trans _ _ s (updateStart s) out' (updateStart_frame capacity s h.1) hframe

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

private theorem run_atoms (input : RAMInput) (as : List Atom) (s : Store) :
    Run input (Cmd.atoms as) s (evalAtoms input as s) as.length := by
  induction as generalizing s with
  | nil => exact Run.skip s
  | cons a as ih =>
      simpa only [Cmd.atoms, evalAtoms, List.length_cons, Nat.add_comm] using
        Run.seq (Run.atom a s) (ih (a.eval input s))

@[simp] private theorem Cmd.atoms_size (as : List Atom) : (Cmd.atoms as).size = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [atoms, size, ih, Nat.add_comm]

@[ext] private theorem Store.ext {s t : Store} (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm) : s = t := by
  cases s
  cases t
  simp_all

private theorem run_atoms_append (input : RAMInput) (as bs : List Atom) (s : Store) :
    evalAtoms input (as ++ bs) s = evalAtoms input bs (evalAtoms input as s) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => exact ih (a.eval input s)

private theorem run_bounded_loop (input : RAMInput) (g : Guard) (body : Cmd)
    (limit bound : ℕ) (P : ℕ → Store → Prop)
    (hguard : ∀ k s, k ≤ limit → P k s → g.eval s = decide (k < limit))
    (hstep : ∀ k s, k < limit → P k s →
      ∃ t n, Run input body s t n ∧ P (k + 1) t ∧ n ≤ bound)
    (k : ℕ) (s : Store) (hk : k ≤ limit) (hs : P k s) :
    ∃ t n, Run input (.loop g body) s t n ∧ P limit t ∧
      n ≤ (bound + 2) * (limit - k) + 1 := by
  suffices h : ∀ remaining k s, k + remaining = limit → P k s →
      ∃ t n, Run input (.loop g body) s t n ∧ P limit t ∧
        n ≤ (bound + 2) * remaining + 1 by
    exact h (limit - k) k s (by omega) hs
  intro remaining
  induction remaining with
  | zero =>
      intro k s heq hp
      have heq' : k = limit := by omega
      subst k
      refine ⟨s, 1, Run.loopFalse ?_, hp, by simp⟩
      simpa using hguard limit s le_rfl hp
  | succ remaining ih =>
      intro k s heq hp
      have hk' : k < limit := by omega
      obtain ⟨u, n, hn, hu, hnb⟩ := hstep k s hk' hp
      obtain ⟨t, m, hm, ht, hmb⟩ := ih (k + 1) u (by omega) hu
      refine ⟨t, 1 + n + 1 + m, Run.loopTrue ?_ hn hm, ht, ?_⟩
      · simpa [hk'] using hguard k s (by omega) hp
      · rw [Nat.mul_succ]
        omega

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem treeLeafAtoms_eval (input : RAMInput) (s : Store) :
    evalAtoms input treeLeafAtoms s = treeLeafPrepared s := by
  ext a <;> simp [evalAtoms, treeLeafAtoms, treeLeafPrepared, Atom.eval, Store.at,
    Store.ofRAM, ramStep, evalNat, Function.update, targetAddress, show ∀ n : ℕ,
      n + n + (n + n) = 4 * n by omega]

private theorem treeLeafPrepare_run (input : RAMInput) (s : Store) :
    ∃ steps ≤ 13, Run input treeLeafPrepare s (treeLeafReady s) steps := by
  have hp := run_atoms input treeLeafAtoms s
  rw [treeLeafAtoms_eval] at hp
  by_cases hv : s.nm (s.nr 171 + s.nr 172) = s.nr 123
  · have hk := Run.branchTrue (g := Guard.nat .eq 175 123)
      (b := Cmd.atom ⟨.realCopy 2 170, trivial⟩)
      (by simp [Guard.eval, natTest, treeLeafPrepared, hv])
      (Run.atom (input := input) (⟨.realConst 2 0, trivial⟩ : Atom) (treeLeafPrepared s))
    refine ⟨13, le_rfl, ?_⟩
    simpa [treeLeafPrepare, treeLeafKey, treeLeafReady, treeLeafPrepared, hv, treeLeafAtoms,
      Atom.eval, Store.at, Store.ofRAM, ramStep] using Run.seq hp hk
  · have hk := Run.branchFalse (g := Guard.nat .eq 175 123)
      (a := Cmd.atom ⟨.realConst 2 0, trivial⟩)
      (by simp [Guard.eval, natTest, treeLeafPrepared, hv])
      (Run.atom (input := input) (⟨.realCopy 2 170, trivial⟩ : Atom) (treeLeafPrepared s))
    refine ⟨12, by omega, ?_⟩
    simpa [treeLeafPrepare, treeLeafKey, treeLeafReady, treeLeafPrepared, hv, treeLeafAtoms,
      Atom.eval, Store.at, Store.ofRAM, ramStep] using Run.seq hp hk

private theorem treeLeafReady_values (s : Store) (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) :
    (treeLeafReady s).nr 0 = s.nr 170 + s.nr 172 ∧
    (treeLeafReady s).nr 10 = s.nr 172 + 1 ∧
    (treeLeafReady s).nr 175 = s.nm (s.nr 171 + s.nr 172) ∧
    (treeLeafReady s).nm (targetAddress (s.nm (s.nr 171 + s.nr 172)) + s.nr 173) = 0 ∧
    (treeLeafReady s).rr 2 =
      (if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170) := by
  simp [treeLeafReady, treeLeafPrepared, hz, hone]

private theorem treeLeafReady_queue_header (s : Store) (r : ℕ) (hr : 0 < r) (hr' : r < 5) :
    (treeLeafReady s).nr r = s.nr r := by
  have h0 : r ≠ 0 := by omega
  have h10 : r ≠ 10 := by omega
  have h174 : r ≠ 174 := by omega
  have h175 : r ≠ 175 := by omega
  have h176 : r ≠ 176 := by omega
  have h177 : r ≠ 177 := by omega
  simp [treeLeafReady, treeLeafPrepared, h0, h10, h174, h175, h176, h177]

private theorem treeInitializeLeaf_run (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeLeafReady s))
    (hone : s.nr 4 = 1) (hpositive : 0 < s.nr 170 + s.nr 172)
    (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeLeafReady s))
    (hnew : truth (s.nr 170 + s.nr 172) =
      ⟨s.nr 172 + 1, if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170⟩) :
    ∃ out steps, Run input treeInitializeLeaf s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 19 ∧
      Queue.ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v := by
  obtain ⟨prepSteps, hprepCost, hprep⟩ := treeLeafPrepare_run input s
  obtain ⟨out, queueSteps, hqueue, hqueueCost, _, _, hpout, htruth⟩ :=
    Queue.updateLeaf_correct input B truth (treeLeafReady s) hp
      (by simpa only [treeLeafReady_queue_header s 4 (by decide) (by decide)] using hone)
      (by simpa [treeLeafReady, treeLeafPrepared] using hpositive) hc hr
      (by simpa [treeLeafReady, treeLeafPrepared, hone] using hnew)
  refine ⟨out, prepSteps + queueSteps, Run.seq hprep hqueue, by omega, hpout, ?_⟩
  simpa only [treeLeafReady_queue_header s 1 (by decide) (by decide)] using htruth

private theorem treeSeedBody_run (input : RAMInput) (s : Store) :
    ∃ steps ≤ 16, Run input treeSeedBody s (treeSeedStep input s) steps := by
  obtain ⟨steps, hs, hprep⟩ := treeLeafPrepare_run input s
  have hw := run_atoms input treeSeedWrite (treeLeafReady s)
  exact ⟨steps + 3, by omega, Run.seq hprep hw⟩

private theorem treeSeedStep_counter (input : RAMInput) (s : Store) :
    (treeSeedStep input s).nr 172 = s.nr 172 + s.nr 4 := by
  simp [treeSeedStep, treeSeedWrite, evalAtoms, treeLeafReady, treeLeafPrepared,
    Atom.eval, Store.at, Store.ofRAM, ramStep, evalNat]

private theorem treeSeedStep_fixed (input : RAMInput) (s : Store) :
    (treeSeedStep input s).nr 4 = s.nr 4 ∧
    (treeSeedStep input s).nr 12 = s.nr 12 := by
  simp [treeSeedStep, treeSeedWrite, evalAtoms, treeLeafReady, treeLeafPrepared,
    Atom.eval, Store.at, Store.ofRAM, ramStep, evalNat]

private theorem treeSeedStep_memory (input : RAMInput) (s : Store) :
    (treeSeedStep input s).nm =
      Function.update s.nm (targetAddress (s.nm (s.nr 171 + s.nr 172)) + s.nr 173) (s.nr 3) ∧
    (treeSeedStep input s).rm = Function.update s.rm (s.nr 13 + s.nr 172)
      (if s.nm (s.nr 171 + s.nr 172) = s.nr 123 then 0 else s.rr 170) := by
  constructor <;> rfl

private theorem treeSeedLoop_run (input : RAMInput) (remaining : ℕ) (s : Store)
    (hone : s.nr 4 = 1) (hend : s.nr 172 + remaining = s.nr 12) :
    ∃ steps ≤ 18 * remaining + 1,
      Run input (.loop (.nat .lt 172 12) treeSeedBody) s
        (treeSeedSteps input remaining s) steps := by
  induction remaining generalizing s with
  | zero =>
      refine ⟨1, le_rfl, Run.loopFalse ?_⟩
      simp [Guard.eval, natTest, show s.nr 172 = s.nr 12 by omega]
  | succ remaining ih =>
      obtain ⟨bodySteps, hb, hbody⟩ := treeSeedBody_run input s
      have hone' : (treeSeedStep input s).nr 4 = 1 := (treeSeedStep_fixed input s).1.trans hone
      have hend' : (treeSeedStep input s).nr 172 + remaining = (treeSeedStep input s).nr 12 := by
        rw [treeSeedStep_counter, (treeSeedStep_fixed input s).2, hone]
        omega
      obtain ⟨tailSteps, ht, htail⟩ := ih (treeSeedStep input s) hone' hend'
      exact ⟨1 + bodySteps + 1 + tailSteps, by omega,
        Run.loopTrue (by simp [Guard.eval, natTest, show s.nr 172 < s.nr 12 by omega]) hbody htail⟩

private theorem treeSeed_run (input : RAMInput) (s : Store) (hone : s.nr 4 = 1) :
    ∃ steps ≤ 18 * s.nr 12 + 2,
      Run input treeSeed s (treeSeedSteps input (s.nr 12) (treeSeedStart s)) steps := by
  have hstart : Run input (.atom ⟨.natConst 172 0, trivial⟩) s (treeSeedStart s) 1 := Run.atom _ s
  obtain ⟨steps, hs, hloop⟩ := treeSeedLoop_run input (s.nr 12) (treeSeedStart s)
    (by simpa [treeSeedStart] using hone) (by simp [treeSeedStart])
  exact ⟨1 + steps, by omega, Run.seq hstart hloop⟩

private theorem treeSeedStep_nr_fixed (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∈ [3,4,12,13,123,171,173]) : (treeSeedStep input s).nr r = s.nr r := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem treeSeedStep_top_fixed (input : RAMInput) (s : Store) :
    (treeSeedStep input s).rr 170 = s.rr 170 := rfl

private theorem TreeSeedInv.step {xs : List ℕ} {A R source off k : ℕ} {top : ℝ} {s : Store}
    (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (hk : k < xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A) :
    TreeSeedInv xs A R source off top (k + 1) (treeSeedStep input s) := by
  let v := xs[k]
  have hv : xs[k]? = some v := List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩
  have hval : s.nm (s.nr 171 + s.nr 172) = v := by
    rw [h.array_reg, h.counter]
    exact h.array k v hv
  have hbound := hspace v (List.mem_of_getElem? hv)
  have hm := treeSeedStep_memory input s
  rw [hval, h.offset_reg, h.zero_reg, h.key_reg, h.counter, h.source_reg, h.top_reg] at hm
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [treeSeedStep_counter, h.counter, h.one_reg]
  · exact (treeSeedStep_nr_fixed input s 12 (by simp)).trans h.length_reg
  · exact (treeSeedStep_nr_fixed input s 171 (by simp)).trans h.array_reg
  · exact (treeSeedStep_nr_fixed input s 13 (by simp)).trans h.key_reg
  · exact (treeSeedStep_nr_fixed input s 123 (by simp)).trans h.source_reg
  · exact (treeSeedStep_nr_fixed input s 173 (by simp)).trans h.offset_reg
  · exact (treeSeedStep_nr_fixed input s 3 (by simp)).trans h.zero_reg
  · exact (treeSeedStep_nr_fixed input s 4 (by simp)).trans h.one_reg
  · exact (treeSeedStep_top_fixed input s).trans h.top_reg
  · intro j w hw
    rw [hm.1, Function.update_of_ne (show A + j ≠ targetAddress v + off by omega)]
    exact h.array j w hw
  · intro j w hw hj
    by_cases hjk : j = k
    · subst j
      have hwv : w = v := Option.some.inj (hw.symm.trans hv)
      subst w
      rw [hm.2, Function.update_self]
    · rw [hm.2, Function.update_of_ne (show R + j ≠ R + k by omega)]
      exact h.key j w hw (by omega)
  · intro j w hw hj
    rw [hm.1]
    by_cases he : targetAddress w + off = targetAddress v + off
    · rw [he, Function.update_self]
    · rw [Function.update_of_ne he]
      apply h.parent j w hw
      by_contra hjk
      have hjk' : j = k := by omega
      subst j
      have hwv : w = v := Option.some.inj (hw.symm.trans hv)
      exact he (by rw [hwv])

private theorem TreeSeedInv.steps {xs : List ℕ} {A R source off k : ℕ} {top : ℝ} {s : Store}
    (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (remaining : ℕ) (hend : k + remaining = xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A) :
    TreeSeedInv xs A R source off top xs.length (treeSeedSteps input remaining s) := by
  induction remaining generalizing k s with
  | zero =>
      have hk : k = xs.length := by omega
      subst k
      exact h
  | succ remaining ih =>
      exact ih (h.step input (by omega) hspace) (by omega)

private theorem treeSeed_correct (input : RAMInput) (xs : List ℕ) (A R source off : ℕ) (top : ℝ)
    (s : Store) (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A)
    (hR : s.nr 13 = R) (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A) :
    ∃ out steps, Run input treeSeed s out steps ∧ steps ≤ 18 * xs.length + 2 ∧
      TreeSeedInv xs A R source off top xs.length out := by
  have hstart : TreeSeedInv xs A R source off top 0 (treeSeedStart s) := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htop, harray, ?_, ?_⟩
    · simp [treeSeedStart]
    · simpa [treeSeedStart] using hlen
    · simpa [treeSeedStart] using hA
    · simpa [treeSeedStart] using hR
    · simpa [treeSeedStart] using hsource
    · simpa [treeSeedStart] using hoff
    · simpa [treeSeedStart] using hz
    · simpa [treeSeedStart] using hone
    · intro j v hv hj; omega
    · intro j v hv hj; omega
  obtain ⟨steps, hs, hrun⟩ := treeSeed_run input s hone
  rw [hlen] at hs hrun
  exact ⟨_, steps, hrun, hs, hstart.steps input xs.length (by omega) hspace⟩

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

private theorem Atom.nat_frame (a : Atom) (input : RAMInput) (s : Store) (r : ℕ)
    (h : r ∉ a.natWrites) : (a.eval input s).nr r = s.nr r := by
  rcases a with ⟨a, ha⟩
  cases a <;> simp_all [IsAtom, Atom.natWrites, Atom.eval, Store.ofRAM, ramStep, Store.at]

private theorem Atom.real_frame (a : Atom) (input : RAMInput) (s : Store) (r : ℕ)
    (h : r ∉ a.realWrites) : (a.eval input s).rr r = s.rr r := by
  rcases a with ⟨a, ha⟩
  cases a <;> simp_all [IsAtom, Atom.realWrites, Atom.eval, Store.ofRAM, ramStep, Store.at]

private theorem Atom.natMemory_frame (a : Atom) (input : RAMInput) (s : Store)
    (h : a.writesNatMemory = false) : (a.eval input s).nm = s.nm := by
  rcases a with ⟨a, ha⟩
  cases a <;> simp_all [IsAtom, Atom.writesNatMemory, Atom.eval, Store.ofRAM, ramStep, Store.at]

private theorem Atom.realMemory_frame (a : Atom) (input : RAMInput) (s : Store)
    (h : a.writesRealMemory = false) : (a.eval input s).rm = s.rm := by
  rcases a with ⟨a, ha⟩
  cases a <;> simp_all [IsAtom, Atom.writesRealMemory, Atom.eval, Store.ofRAM, ramStep, Store.at]

private theorem Run.nat_frame {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.natWrites) : t.nr r = s.nr r := by
  revert hr
  induction h with
  | skip => intros; rfl
  | atom a s => exact a.nat_frame _ s r
  | seq ha hb iha ihb =>
      intro hr
      simp only [Cmd.natWrites, Finset.mem_union, not_or] at hr
      exact (ihb hr.2).trans (iha hr.1)
  | branchTrue hg ha ih =>
      intro hr
      simp only [Cmd.natWrites, Finset.mem_union, not_or] at hr
      exact ih hr.1
  | branchFalse hg hb ih =>
      intro hr
      simp only [Cmd.natWrites, Finset.mem_union, not_or] at hr
      exact ih hr.2
  | loopFalse => intros; rfl
  | loopTrue hg hb hl ihb ihl =>
      intro hr
      exact (ihl hr).trans (ihb hr)

private theorem Run.real_frame {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.realWrites) : t.rr r = s.rr r := by
  revert hr
  induction h with
  | skip => intros; rfl
  | atom a s => exact a.real_frame _ s r
  | seq ha hb iha ihb =>
      intro hr
      simp only [Cmd.realWrites, Finset.mem_union, not_or] at hr
      exact (ihb hr.2).trans (iha hr.1)
  | branchTrue hg ha ih =>
      intro hr
      simp only [Cmd.realWrites, Finset.mem_union, not_or] at hr
      exact ih hr.1
  | branchFalse hg hb ih =>
      intro hr
      simp only [Cmd.realWrites, Finset.mem_union, not_or] at hr
      exact ih hr.2
  | loopFalse => intros; rfl
  | loopTrue hg hb hl ihb ihl =>
      intro hr
      exact (ihl hr).trans (ihb hr)

private theorem Run.natMemory_frame {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesNatMemory = false) : t.nm = s.nm := by
  revert hw
  induction h with
  | skip => intros; rfl
  | atom a s => exact a.natMemory_frame _ s
  | seq ha hb iha ihb =>
      intro hw
      simp only [Cmd.writesNatMemory, Bool.or_eq_false_iff] at hw
      exact (ihb hw.2).trans (iha hw.1)
  | branchTrue hg ha ih =>
      intro hw
      simp only [Cmd.writesNatMemory, Bool.or_eq_false_iff] at hw
      exact ih hw.1
  | branchFalse hg hb ih =>
      intro hw
      simp only [Cmd.writesNatMemory, Bool.or_eq_false_iff] at hw
      exact ih hw.2
  | loopFalse => intros; rfl
  | loopTrue hg hb hl ihb ihl =>
      intro hw
      exact (ihl hw).trans (ihb hw)

private theorem Run.realMemory_frame {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesRealMemory = false) : t.rm = s.rm := by
  revert hw
  induction h with
  | skip => intros; rfl
  | atom a s => exact a.realMemory_frame _ s
  | seq ha hb iha ihb =>
      intro hw
      simp only [Cmd.writesRealMemory, Bool.or_eq_false_iff] at hw
      exact (ihb hw.2).trans (iha hw.1)
  | branchTrue hg ha ih =>
      intro hw
      simp only [Cmd.writesRealMemory, Bool.or_eq_false_iff] at hw
      exact ih hw.1
  | branchFalse hg hb ih =>
      intro hw
      simp only [Cmd.writesRealMemory, Bool.or_eq_false_iff] at hw
      exact ih hw.2
  | loopFalse => intros; rfl
  | loopTrue hg hb hl ihb ihl =>
      intro hw
      exact (ihl hw).trans (ihb hw)

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem TreeSeedInv.step_memory_frame {xs : List ℕ} {A R source off k : ℕ} {top : ℝ}
    {s : Store} (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (hk : k < xs.length) (a : ℕ)
    (hn : ∀ v ∈ xs, a ≠ targetAddress v + off)
    (hr : a < R ∨ R + xs.length ≤ a) :
    (treeSeedStep input s).nm a = s.nm a ∧ (treeSeedStep input s).rm a = s.rm a := by
  have hv : xs[k]? = some xs[k] := List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩
  have hval : s.nm (s.nr 171 + s.nr 172) = xs[k] := by
    rw [h.array_reg, h.counter]
    exact h.array k xs[k] hv
  have hm := treeSeedStep_memory input s
  rw [hval, h.offset_reg, h.key_reg, h.counter] at hm
  constructor
  · rw [hm.1, Function.update_of_ne (hn _ (List.getElem_mem hk))]
  · rw [hm.2, Function.update_of_ne (show a ≠ R + k by omega)]

private theorem TreeSeedInv.steps_memory_frame {xs : List ℕ} {A R source off k : ℕ} {top : ℝ}
    {s : Store} (h : TreeSeedInv xs A R source off top k s) (input : RAMInput)
    (remaining : ℕ) (hend : k + remaining = xs.length)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A) (a : ℕ)
    (hn : ∀ v ∈ xs, a ≠ targetAddress v + off)
    (hr : a < R ∨ R + xs.length ≤ a) :
    (treeSeedSteps input remaining s).nm a = s.nm a ∧
      (treeSeedSteps input remaining s).rm a = s.rm a := by
  induction remaining generalizing k s with
  | zero => exact ⟨rfl,rfl⟩
  | succ remaining ih =>
      have hk : k < xs.length := by omega
      have hi := ih (h.step input hk hspace) (by omega)
      have hs := h.step_memory_frame input hk a hn hr
      exact ⟨hi.1.trans hs.1, hi.2.trans hs.2⟩

private theorem treeSeed_register_frame {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input treeSeed s out steps)
    (hr : r ∉ ({0,10,172,174,175,176,177,178} : Finset ℕ)) : out.nr r = s.nr r := by
  apply h.nat_frame
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  simp_all [treeSeed, treeSeedBody, treeSeedWrite, treeLeafPrepare, treeLeafAtoms,
    treeLeafKey, Cmd.atoms, Cmd.natWrites, Atom.natWrites]

private theorem treeSeed_real_register_frame {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input treeSeed s out steps) (hr : r ≠ 2) : out.rr r = s.rr r := by
  apply h.real_frame
  simp [treeSeed, treeSeedBody, treeSeedWrite, treeLeafPrepare, treeLeafAtoms,
    treeLeafKey, Cmd.atoms, Cmd.realWrites, Atom.realWrites, hr]

private theorem treeSeedStart_inv (xs : List ℕ) (A R source off : ℕ) (top : ℝ) (s : Store)
    (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A) (hR : s.nr 13 = R)
    (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v) :
    TreeSeedInv xs A R source off top 0 (treeSeedStart s) := by
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htop, harray, ?_, ?_⟩
  · simp [treeSeedStart]
  · simpa [treeSeedStart] using hlen
  · simpa [treeSeedStart] using hA
  · simpa [treeSeedStart] using hR
  · simpa [treeSeedStart] using hsource
  · simpa [treeSeedStart] using hoff
  · simpa [treeSeedStart] using hz
  · simpa [treeSeedStart] using hone
  · intro j v hv hj; omega
  · intro j v hv hj; omega

private theorem treeSeed_framed (input : RAMInput) (xs : List ℕ) (A R source off : ℕ) (top : ℝ)
    (s : Store) (hlen : s.nr 12 = xs.length) (hA : s.nr 171 = A)
    (hR : s.nr 13 = R) (hsource : s.nr 123 = source) (hoff : s.nr 173 = off)
    (hz : s.nr 3 = 0) (hone : s.nr 4 = 1) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A + j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A) :
    ∃ out steps, Run input treeSeed s out steps ∧ steps ≤ 18 * xs.length + 2 ∧
      TreeSeedInv xs A R source off top xs.length out ∧
      (∀ a, (∀ v ∈ xs, a ≠ targetAddress v + off) →
        (a < R ∨ R + xs.length ≤ a) → out.nm a = s.nm a ∧ out.rm a = s.rm a) := by
  have hstart := treeSeedStart_inv xs A R source off top s hlen hA hR hsource hoff
    hz hone htop harray
  obtain ⟨steps, hs, hrun⟩ := treeSeed_run input s hone
  rw [hlen] at hs hrun
  refine ⟨_, steps, hrun, hs, hstart.steps input xs.length (by omega) hspace, ?_⟩
  intro a hn hr
  exact hstart.steps_memory_frame input xs.length (by omega) hspace a hn hr

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

private theorem heapTruth_internal (B : ℕ) (leaf : ℕ → Record) (v : ℕ)
    (hv : 0 < v) (hB : v < B) :
    heapTruth B leaf v = merge (heapTruth B leaf (v + v)) (heapTruth B leaf (v + v + 1)) := by
  rw [heapTruth, dif_pos ⟨hv,hB⟩]

private theorem heapTruth_leaf (B : ℕ) (leaf : ℕ → Record) (v : ℕ)
    (hv : B ≤ v) : heapTruth B leaf v = leaf v := by
  rw [heapTruth, dif_neg (by omega)]

private theorem heapTruth_coherent (B : ℕ) (leaf : ℕ → Record) :
    Coherent (2 * B) (heapTruth B leaf) := by
  intro u hu hcap
  exact heapTruth_internal B leaf u hu (by omega)

@[simp] private theorem merge_self (r : Record) : merge r r = r := by
  simp [merge]

private theorem heapTruth_const (B : ℕ) (r : Record) (v : ℕ) :
    heapTruth B (fun _ => r) v = r := by
  have main : ∀ d v, B-v=d → heapTruth B (fun _ => r) v = r := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro v hd
        by_cases hn : 0 < v ∧ v < B
        · rw [heapTruth_internal B (fun _ => r) v hn.1 hn.2,
            ih (B-(v+v)) (by omega) (v+v) rfl,
            ih (B-(v+v+1)) (by omega) (v+v+1) rfl, merge_self]
        · rw [heapTruth, dif_neg hn]
  exact main (B-v) v rfl

private theorem mem_ancestors_self (n : ℕ) (hn : 0 < n) : n ∈ ancestors n := by
  rw [ancestors_pos n hn]
  simp

private theorem parent_mem_ancestors (n v : ℕ) (hv : v ∈ ancestors n) (hp : 0 < v / 2) :
    v / 2 ∈ ancestors n := by
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
      by_cases hn : n = 0
      · subst n; simp at hv
      · rw [ancestors_pos n (Nat.pos_of_ne_zero hn), List.mem_cons] at hv ⊢
        rcases hv with rfl | hv
        · exact Or.inr (mem_ancestors_self _ hp)
        · exact Or.inr (ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)) v hv hp)

private theorem child_not_mem_ancestors (k v : ℕ) (hv : 0 < v) (hk : v ∉ ancestors k) :
    v + v ∉ ancestors k ∧ v + v + 1 ∉ ancestors k := by
  constructor
  · intro h
    have he : (v + v) / 2 = v := by omega
    exact hk (he ▸ parent_mem_ancestors k (v+v) h (by omega))
  · intro h
    have he : (v + v + 1) / 2 = v := by omega
    exact hk (he ▸ parent_mem_ancestors k (v+v+1) h (by omega))

private theorem heapTruth_frame (B : ℕ) (leaf leaf' : ℕ → Record) (k : ℕ)
    (hk : 0 < k) (hchange : ∀ v, v ≠ k → leaf' v = leaf v) :
    ∀ v, v ∉ ancestors k → heapTruth B leaf' v = heapTruth B leaf v := by
  have main : ∀ d v, B - v = d → v ∉ ancestors k →
      heapTruth B leaf' v = heapTruth B leaf v := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro v hd hv
        by_cases hnode : 0 < v ∧ v < B
        · rw [heapTruth_internal B leaf' v hnode.1 hnode.2,
            heapTruth_internal B leaf v hnode.1 hnode.2]
          have hc := child_not_mem_ancestors k v hnode.1 hv
          rw [ih (B-(v+v)) (by omega) (v+v) rfl hc.1,
            ih (B-(v+v+1)) (by omega) (v+v+1) rfl hc.2]
        · rw [heapTruth, dif_neg hnode, heapTruth, dif_neg hnode]
          apply hchange
          intro he; subst v
          exact hv (mem_ancestors_self k hk)
  intro v hv
  exact main (B-v) v rfl hv

private theorem leafRecords_add (leaf : ℕ → Record) (start a b : ℕ) :
    leafRecords leaf start (a+b) =
      leafRecords leaf start a ++ leafRecords leaf (start+a) b := by
  simp only [leafRecords, List.range_add, List.map_append, List.map_map,
    List.filterMap_append]
  congr 1
  congr 1
  simp [Function.comp_def,Nat.add_assoc]

private theorem heapTruth_decode_subtree (B : ℕ) (leaf : ℕ → Record) (h v : ℕ)
    (hv : 0 < v) (hlo : B ≤ v * 2^h) (hhi : (v+1)*2^h ≤ 2*B) :
    (heapTruth B leaf v).decode =
      winner Record.key (leafRecords leaf (v * 2^h) (2^h)) := by
  induction h generalizing v with
  | zero =>
      simp only [pow_zero, Nat.mul_one] at hlo hhi ⊢
      rw [heapTruth_leaf B leaf v hlo]
      simp only [leafRecords, List.range_one, List.map_cons, List.map_nil, Nat.add_zero,
        List.filterMap_cons, List.filterMap_nil]
      cases hdec : (leaf v).decode <;> simp [hdec]
  | succ h ih =>
      have hp : 0 < 2^h := by positivity
      rw [pow_succ, ← Nat.mul_assoc] at hlo hhi
      have hm := Nat.mul_le_mul_left (v+1) (show 1 ≤ 2^h by omega)
      have hnode : v < B := by omega
      have hexpand : (v+1)*2^h*2 = (v*2^h)*2 + 2*2^h := by ring
      rw [hexpand] at hhi
      have hleft : (v+v)*2^h = (v*2^h)*2 := by ring
      have hright : (v+v+1)*2^h = (v*2^h)*2 + 2^h := by ring
      have hend : (v+v+1+1)*2^h = (v*2^h)*2 + 2*2^h := by ring
      rw [heapTruth_internal B leaf v hv hnode, merge_decode]
      have hl := ih (v+v) (by omega) (by rw [hleft]; exact hlo)
        (by rw [hright]; omega)
      have hr := ih (v+v+1) (by omega) (by rw [hright]; omega)
        (by rw [hend]; exact hhi)
      rw [hl, hr, ← winner_append]
      have hstart : v * 2^(h+1) = (v+v)*2^h := by rw [pow_succ]; ring
      have hcount : 2^(h+1) = 2^h + 2^h := by rw [pow_succ]; ring
      have hrstart : (v+v)*2^h + 2^h = (v+v+1)*2^h := by ring
      rw [hstart, hcount, leafRecords_add, hrstart]

private theorem heapTruth_root (h : ℕ) (leaf : ℕ → Record) :
    (heapTruth (2^h) leaf 1).decode = winner Record.key (leafRecords leaf (2^h) (2^h)) := by
  simpa using heapTruth_decode_subtree (2^h) leaf h 1 (by decide) (by simp) (by simp)

private theorem choose_map {α β : Type} (key : β → ℝ) (f : α → β) (a b : Option α) :
    choose key (a.map f) (b.map f) = (choose (key ∘ f) a b).map f := by
  cases a <;> cases b <;> simp [choose, Function.comp_def]
  all_goals split_ifs <;> rfl

private theorem winner_map {α β : Type} (key : β → ℝ) (f : α → β) (xs : List α) :
    winner key (xs.map f) = (winner (key ∘ f) xs).map f := by
  have aux : ∀ (xs : List α) (a : Option α), (xs.map f).foldl (fun a b => choose key a (some b)) (a.map f) =
      (xs.foldl (fun a b => choose (key ∘ f) a (some b)) a).map f := by
    intro xs
    induction xs with
    | nil => intro a; rfl
    | cons x xs ih =>
        intro a
        simp only [List.map_cons, List.foldl_cons]
        change (xs.map f).foldl (fun a b => choose key a (some b))
          (choose key (a.map f) ((some x).map f)) = _
        rw [choose_map]
        exact ih _
  exact aux xs none

private theorem heapTruth_firstMin (h : ℕ) (leaf : ℕ → Record) (xs : List ℕ)
    (encode : ℕ → Record) (hslots : leafRecords leaf (2^h) (2^h) = xs.map encode)
    (fallback : ℕ) (hne : xs ≠ []) :
    (heapTruth (2^h) leaf 1).decode =
      some (encode (firstMin (fun v => (encode v).key) xs fallback)) := by
  rw [heapTruth_root, hslots, winner_map, winner_eq_firstMin _ xs fallback hne]
  rfl

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory
namespace RSP.Tails

private theorem mass_nonneg (r : ℝ≥0) (n : ℕ) : 0 ≤ mass r n := by
  unfold mass
  positivity

private theorem mass_succ_mul (r : ℝ≥0) (n : ℕ) :
    mass r (n + 1) * (n + 1 : ℝ) = (r : ℝ) * mass r n := by
  unfold mass
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem mass_hasSum (r : ℝ≥0) : HasSum (mass r) 1 :=
  hasSum_one_poissonMeasure r

private theorem poisson_pgf_hasSum (r : ℝ≥0) (z : ℝ) :
    HasSum (fun n : ℕ => mass r n * z ^ n) (Real.exp ((r : ℝ) * (z - 1))) := by
  convert! (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * z)).mul_left
    (Real.exp (-(r : ℝ))) using 1
  · ext n
    simp only [mass, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

private theorem poisson_pgf (r : ℝ≥0) (z : ℝ) :
    (∫ n : ℕ, z ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (z - 1)) := by
  rw [integral_poissonMeasure]
  exact (poisson_pgf_hasSum r z).tsum_eq

private theorem firstMoment_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => mass r n * (n : ℝ)) (r : ℝ) := by
  have h : HasSum (fun n : ℕ => mass r (n + 1) * ((n + 1 : ℕ) : ℝ)) (r : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one, mass_succ_mul, mul_one] using
      (mass_hasSum r).mul_left (r : ℝ)
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, add_zero] using
    (hasSum_nat_add_iff (f := fun n : ℕ => mass r n * (n : ℝ)) 1).mp h

private theorem factorialMoment_two_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => mass r n * ((n : ℝ) * ((n : ℝ) - 1))) ((r : ℝ) ^ 2) := by
  have h : HasSum
      (fun n : ℕ => mass r (n + 1) * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)))
      ((r : ℝ) ^ 2) := by
    convert! (firstMoment_hasSum r).mul_left (r : ℝ) using 1
    · ext n
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, ← mul_assoc,
        mass_succ_mul]
    · ring
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, mul_zero, add_zero] using
    (hasSum_nat_add_iff
      (f := fun n : ℕ => mass r n * ((n : ℝ) * ((n : ℝ) - 1))) 1).mp h

private theorem secondMoment_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => mass r n * (n : ℝ) ^ 2) ((r : ℝ) ^ 2 + (r : ℝ)) := by
  convert! (factorialMoment_two_hasSum r).add (firstMoment_hasSum r) using 1
  ext n
  ring

private theorem poisson_integrable_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ) ^ 2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simpa only [mass, Real.norm_eq_abs, abs_pow, Nat.abs_cast] using
    (secondMoment_hasSum r).summable

private theorem poisson_memLp_two (r : ℝ≥0) :
    MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mpr (poisson_integrable_sq r)

private theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = (r : ℝ) := by
  rw [integral_poissonMeasure]
  exact (firstMoment_hasSum r).tsum_eq

private theorem poisson_secondMoment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) = (r : ℝ) ^ 2 + (r : ℝ) := by
  rw [integral_poissonMeasure]
  exact (secondMoment_hasSum r).tsum_eq

private theorem poisson_variance (r : ℝ≥0) :
    variance (fun n : ℕ => (n : ℝ)) (poissonMeasure r) = (r : ℝ) := by
  rw [variance_eq_sub (poisson_memLp_two r), poisson_mean]
  change (∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r) - (r : ℝ) ^ 2 = (r : ℝ)
  rw [poisson_secondMoment]
  ring

private theorem poisson_upper_tail (r : ℝ≥0) (a : ℝ) (ha : (r : ℝ) < a) :
    poissonMeasure r {n : ℕ | a ≤ (n : ℝ)} ≤
      ENNReal.ofReal ((r : ℝ) / (a - (r : ℝ)) ^ 2) := by
  have h := meas_ge_le_variance_div_sq (poisson_memLp_two r) (sub_pos.mpr ha)
  rw [poisson_mean, poisson_variance] at h
  apply le_trans (measure_mono ?_) h
  intro n hn
  change a - (r : ℝ) ≤ |(n : ℝ) - (r : ℝ)|
  exact le_trans (sub_le_sub_right hn _) (le_abs_self _)

private theorem poisson_lower_tail (r : ℝ≥0) (a : ℝ) (ha : a < (r : ℝ)) :
    poissonMeasure r {n : ℕ | (n : ℝ) ≤ a} ≤
      ENNReal.ofReal ((r : ℝ) / ((r : ℝ) - a) ^ 2) := by
  have h := meas_ge_le_variance_div_sq (poisson_memLp_two r) (sub_pos.mpr ha)
  rw [poisson_mean, poisson_variance] at h
  apply le_trans (measure_mono ?_) h
  intro n hn
  change (n : ℝ) ≤ a at hn
  change (r : ℝ) - a ≤ |(n : ℝ) - (r : ℝ)|
  have hn' : (r : ℝ) - a ≤ -((n : ℝ) - (r : ℝ)) := by linarith
  exact le_trans hn' (neg_le_abs _)

private theorem completeness_ratio (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    (q / (1 + ε / 2)) / (q - q / (1 + ε / 2)) ^ 2 =
      (4 + 2 * ε) / (q * ε ^ 2) := by
  have hd : 0 < 1 + ε / 2 := by positivity
  have hg : 0 < q - q / (1 + ε / 2) := by
    exact sub_pos.mpr (div_lt_self hq (by linarith))
  field_simp [ne_of_gt hε]
  ring

private theorem soundness_ratio (q ε : ℝ) (hq : 0 < q) (hε : 0 < ε) :
    (q * (1 + ε) / (1 + ε / 2)) /
        (q * (1 + ε) / (1 + ε / 2) - q) ^ 2 =
      (4 + 6 * ε + 2 * ε ^ 2) / (q * ε ^ 2) := by
  have hd : 0 < 1 + ε / 2 := by positivity
  have hg : 0 < q * (1 + ε) / (1 + ε / 2) - q := by
    apply sub_pos.mpr
    rw [lt_div_iff₀ hd]
    nlinarith [mul_pos hq hε]
  field_simp [ne_of_gt hε]
  ring_nf
  field_simp [ne_of_gt hε]

private theorem completeness_ratio_le (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2) :
    (q / (1 + ε / 2)) / (q - q / (1 + ε / 2)) ^ 2 ≤
      1 / (8 * (k : ℝ)) := by
  rw [completeness_ratio q ε hq hε]
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < q * ε ^ 2 := by positivity
  apply (div_le_div_iff₀ hden (by positivity : 0 < 8 * (k : ℝ))).mpr
  nlinarith [mul_nonneg (le_of_lt hk') (sub_nonneg.mpr hε₁)]

private theorem soundness_ratio_le (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2) :
    (q * (1 + ε) / (1 + ε / 2)) /
        (q * (1 + ε) / (1 + ε / 2) - q) ^ 2 ≤
      1 / (8 * (k : ℝ)) := by
  rw [soundness_ratio q ε hq hε]
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < q * ε ^ 2 := by positivity
  have hnum : 4 + 6 * ε + 2 * ε ^ 2 ≤ 12 := by
    nlinarith [mul_nonneg (le_of_lt hε) (sub_nonneg.mpr hε₁)]
  apply (div_le_div_iff₀ hden (by positivity : 0 < 8 * (k : ℝ))).mpr
  nlinarith [mul_nonneg (le_of_lt hk') (sub_nonneg.mpr hnum)]

private theorem poisson_completeness_tail (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2) (hr : (r : ℝ) = q / (1 + ε / 2)) :
    (poissonMeasure r).real {n : ℕ | q ≤ (n : ℝ)} ≤ 1 / (8 * (k : ℝ)) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  apply le_trans (poisson_upper_tail r q ?_)
  · apply ENNReal.ofReal_le_ofReal
    rw [hr]
    exact completeness_ratio_le q ε k hk hq hε hε₁ hsize
  · rw [hr]
    exact div_lt_self hq (by linarith)

private theorem poisson_completeness_tail_of_le (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2) (hr : (r : ℝ) ≤ q / (1 + ε / 2)) :
    (poissonMeasure r).real {n : ℕ | q ≤ (n : ℝ)} ≤ 1 / (8 * (k : ℝ)) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbase : q / (1 + ε / 2) < q := div_lt_self hq (by linarith)
  have hgap : 0 < q - q / (1 + ε / 2) := sub_pos.mpr hbase
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  apply le_trans (poisson_upper_tail r q (hr.trans_lt hbase))
  apply ENNReal.ofReal_le_ofReal
  apply le_trans (div_le_div₀ (by positivity : 0 ≤ q / (1 + ε / 2)) hr
    (sq_pos_of_pos hgap) ?_)
  · exact completeness_ratio_le q ε k hk hq hε hε₁ hsize
  · nlinarith [sq_nonneg (q / (1 + ε / 2) - (r : ℝ)),
      mul_nonneg (le_of_lt hgap) (sub_nonneg.mpr hr)]

private theorem poisson_soundness_tail (r : ℝ≥0) (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (hr : (r : ℝ) = q * (1 + ε) / (1 + ε / 2)) :
    (poissonMeasure r).real {n : ℕ | (n : ℝ) < q} ≤ 1 / (8 * (k : ℝ)) := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  have hsub : {n : ℕ | (n : ℝ) < q} ⊆ {n : ℕ | (n : ℝ) ≤ q} := by
    intro n hn
    change (n : ℝ) < q at hn
    change (n : ℝ) ≤ q
    exact hn.le
  apply le_trans (measure_mono hsub)
  apply le_trans (poisson_lower_tail r q ?_)
  · apply ENNReal.ofReal_le_ofReal
    rw [hr]
    exact soundness_ratio_le q ε k hk hq hε hε₁ hsize
  · rw [hr, lt_div_iff₀ (by positivity : 0 < 1 + ε / 2)]
    nlinarith [mul_pos hq hε]

private theorem resource_union_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (events : Fin k → Set Ω)
    (h : ∀ i, μ.real (events i) ≤ 1 / (8 * (k : ℝ))) :
    μ.real (⋃ i, events i) ≤ 1 / 8 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  calc
    μ.real (⋃ i, events i) ≤ ∑ i, μ.real (events i) := measureReal_iUnion_fintype_le events
    _ ≤ ∑ _i : Fin k, 1 / (8 * (k : ℝ)) := Finset.sum_le_sum (fun i _ => h i)
    _ = 1 / 8 := by simp; field_simp

private theorem poisson_completeness_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : ℝ≥0) (hr : (r : ℝ) = q / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure r) μ) :
    μ.real (⋃ i, {ω | q ≤ (X i ω : ℝ)}) ≤ 1 / 8 := by
  apply resource_union_bound μ k hk
  intro i
  rw [(hX i).measureReal_eq (p := fun n : ℕ => q ≤ (n : ℝ)) (by measurability)]
  exact poisson_completeness_tail r q ε k hk hq hε hε₁ hsize hr

private theorem poisson_completeness_union_of_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : Fin k → ℝ≥0) (hr : ∀ i, (r i : ℝ) ≤ q / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure (r i)) μ) :
    μ.real (⋃ i, {ω | q ≤ (X i ω : ℝ)}) ≤ 1 / 8 := by
  apply resource_union_bound μ k hk
  intro i
  rw [(hX i).measureReal_eq (p := fun n : ℕ => q ≤ (n : ℝ)) (by measurability)]
  exact poisson_completeness_tail_of_le (r i) q ε k hk hq hε hε₁ hsize (hr i)

private theorem countdown_pos (k : ℕ) (ε : ℝ) (hk : 0 < k) (hε : 0 < ε) :
    0 < countdown k ε := by
  unfold countdown
  apply Nat.ceil_pos.mpr
  positivity

private theorem countdown_sufficient (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    128 * (k : ℝ) ≤ (countdown k ε : ℝ) * ε ^ 2 := by
  apply (div_le_iff₀ (sq_pos_of_pos hε)).mp
  exact Nat.le_ceil _

private theorem poisson_soundness_union {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (k : ℕ) (hk : 0 < k) (q ε : ℝ)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2)
    (r : ℝ≥0) (hr : (r : ℝ) = q * (1 + ε) / (1 + ε / 2))
    (X : Fin k → Ω → ℕ) (hX : ∀ i, HasLaw (X i) (poissonMeasure r) μ) :
    μ.real (⋃ i, {ω | (X i ω : ℝ) < q}) ≤ 1 / 8 := by
  apply resource_union_bound μ k hk
  intro i
  rw [(hX i).measureReal_eq (p := fun n : ℕ => (n : ℝ) < q) (by measurability)]
  exact poisson_soundness_tail r q ε k hk hq hε hε₁ hsize hr

end RSP.Tails
end

set_option autoImplicit false
section
set_option autoImplicit false
open NearLinearRSP.TwoResources
namespace RSP.PoissonBridge

private theorem lengthRate_nonneg (A : InnerInput) : 0 ≤ lengthRate A := by
  have hδ := A.accuracy_pos
  have hL := A.length_pos
  unfold lengthRate
  positivity

private theorem costRate_nonneg (A : InnerInput) : 0 ≤ costRate A := by
  have hδ := A.accuracy_pos
  have hC := A.budget_pos
  unfold costRate
  positivity

private theorem poissonCountMass_nonneg (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ ActuarialValuation.poissonCountMass r n := by
  unfold ActuarialValuation.poissonCountMass
  positivity

private theorem poissonCountMass_hasSum (r : ℝ) (hr : 0 ≤ r) :
    HasSum (ActuarialValuation.poissonCountMass r) 1 :=
  Tails.mass_hasSum ⟨r, hr⟩

private theorem poissonCountMass_sum_le_one (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (∑ a ∈ Finset.range n, ActuarialValuation.poissonCountMass r a) ≤ 1 := by
  exact sum_le_hasSum (Finset.range n)
    (fun a _ => poissonCountMass_nonneg r hr a) (poissonCountMass_hasSum r hr)

private theorem edgeMass_nonneg (A : InnerInput) (u v a b : ℕ) :
    0 ≤ edgeMass A u v a b := by
  unfold edgeMass
  apply mul_nonneg
  · exact poissonCountMass_nonneg _
      (mul_nonneg (lengthRate_nonneg A) (A.I.length u v).coe_nonneg) a
  · exact poissonCountMass_nonneg _
      (mul_nonneg (costRate_nonneg A) (A.I.cost u v).coe_nonneg) b

private theorem edgeMass_rectangle_eq (A : InnerInput) (u v na nb : ℕ) :
    (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b) =
      (∑ a ∈ Finset.range na,
        ActuarialValuation.poissonCountMass (lengthRate A * A.I.length u v) a) *
      (∑ b ∈ Finset.range nb,
        ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b) := by
  simp only [edgeMass, Finset.sum_mul_sum]

private theorem edgeMass_rectangle_nonneg (A : InnerInput) (u v na nb : ℕ) :
    0 ≤ ∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b := by
  apply Finset.sum_nonneg
  intro a _
  exact Finset.sum_nonneg (fun b _ => edgeMass_nonneg A u v a b)

private theorem edgeMass_rectangle_le_one (A : InnerInput) (u v na nb : ℕ) :
    (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb, edgeMass A u v a b) ≤ 1 := by
  rw [edgeMass_rectangle_eq]
  have hl : 0 ≤ lengthRate A * A.I.length u v :=
    mul_nonneg (lengthRate_nonneg A) (A.I.length u v).coe_nonneg
  have hc : 0 ≤ costRate A * A.I.cost u v :=
    mul_nonneg (costRate_nonneg A) (A.I.cost u v).coe_nonneg
  have hl_sum := poissonCountMass_sum_le_one _ hl na
  have hc_sum := poissonCountMass_sum_le_one _ hc nb
  have hc_sum_nonneg :
      0 ≤ ∑ b ∈ Finset.range nb,
        ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b :=
    Finset.sum_nonneg (fun b _ => poissonCountMass_nonneg _ hc b)
  simpa using mul_le_mul hl_sum hc_sum hc_sum_nonneg (by norm_num : (0 : ℝ) ≤ 1)

private theorem edgeMass_sum_le_one (A : InnerInput) (u v i j : ℕ) :
    (∑ a ∈ Finset.range (tickLimit A - i),
      ∑ b ∈ Finset.range (tickLimit A - j), edgeMass A u v a b) ≤ 1 :=
  edgeMass_rectangle_le_one A u v _ _

end RSP.PoissonBridge
end

set_option autoImplicit false
section
namespace NearLinearRSP.TwoResources
open scoped BigOperators

private theorem standalone_RSP_TableBounds__foldl_invariant {α β : Type*} (f : β → α → β) (P : β → Prop)
    (xs : List α) (b : β) (hb : P b)
    (hf : ∀ b a, P b → P (f b a)) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih => exact ih (f b a) (hf b a hb)

private theorem putCell_range (T : Table) (v i j : ℕ) (c : Cell)
    (hT : TableRange T) (hc : 0 ≤ c.value ∧ c.value ≤ 1) :
    TableRange (putCell T v i j c) := by
  intro w a b
  unfold putCell
  split
  · exact hc
  · exact hT w a b

private theorem dpValue_range (A : InnerInput) (T : Table) (hT : TableRange T)
    (v i j : ℕ) : 0 ≤ dpValue A T v i j ∧ dpValue A T v i j ≤ 1 := by
  unfold dpValue
  split
  · exact ⟨zero_le_one, le_rfl⟩
  · exact hT v i j

private theorem edgeExpectation_range (A : InnerInput) (T : Table) (hT : TableRange T)
    (u v i j : ℕ) :
    0 ≤ edgeExpectation A T u v i j ∧ edgeExpectation A T u v i j ≤ 1 := by
  unfold edgeExpectation
  split
  · exact ⟨zero_le_one, le_rfl⟩
  · have hm := RSP.PoissonBridge.edgeMass_sum_le_one A u v i j
    have hnonneg : 0 ≤ ∑ a ∈ Finset.range (tickLimit A - i),
        ∑ b ∈ Finset.range (tickLimit A - j),
          edgeMass A u v a b * dpValue A T u (i + a) (j + b) := by
      apply Finset.sum_nonneg
      intro a _
      apply Finset.sum_nonneg
      intro b _
      exact mul_nonneg (RSP.PoissonBridge.edgeMass_nonneg A u v a b)
        (dpValue_range A T hT u (i + a) (j + b)).1
    have hle : (∑ a ∈ Finset.range (tickLimit A - i),
        ∑ b ∈ Finset.range (tickLimit A - j),
          edgeMass A u v a b * dpValue A T u (i + a) (j + b)) ≤
        ∑ a ∈ Finset.range (tickLimit A - i),
          ∑ b ∈ Finset.range (tickLimit A - j), edgeMass A u v a b := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      simpa using mul_le_mul_of_nonneg_left
        (dpValue_range A T hT u (i + a) (j + b)).2
        (RSP.PoissonBridge.edgeMass_nonneg A u v a b)
    constructor <;> linarith

private theorem initLayer_range (A : InnerInput) (T : Table) (hT : TableRange T)
    (i j : ℕ) : LayerRange (initLayer A T i j) := by
  refine ⟨hT, ?_⟩
  intro v
  change 0 ≤ (if v = A.I.source then 0 else
      min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))) ∧
    (if v = A.I.source then 0 else
      min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))) ≤ 1
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨le_min (dpValue_range A T hT v (i + 1) j).1
        (dpValue_range A T hT v i (j + 1)).1,
      (min_le_left _ _).trans (dpValue_range A T hT v (i + 1) j).2⟩

private theorem relaxEdge_range (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerRange S) :
    LayerRange (relaxEdge A i j u S e) := by
  unfold relaxEdge
  split
  · dsimp only
    split
    · refine ⟨hS.1, ?_⟩
      intro v
      change 0 ≤ Function.update S.keys e.2
          (edgeExpectation A S.table e.1 e.2 i j) v ∧
        Function.update S.keys e.2 (edgeExpectation A S.table e.1 e.2 i j) v ≤ 1
      by_cases hv : v = e.2
      · subst v
        simpa using edgeExpectation_range A S.table hS.1 e.1 e.2 i j
      · simpa [Function.update_of_ne hv] using hS.2 v
    · exact hS
  · exact hS

private theorem popLayer_range (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hS : LayerRange S) : LayerRange (popLayer A i j S) := by
  unfold popLayer
  split
  · exact hS
  · apply standalone_RSP_TableBounds__foldl_invariant
    · exact ⟨putCell_range S.table _ i j _ hS.1 (hS.2 _), hS.2⟩
    · intro U e hU
      exact relaxEdge_range A i j _ U e hU

private theorem buildLayer_range (A : InnerInput) (T : Table) (hT : TableRange T)
    (i j : ℕ) : TableRange (buildLayer A T i j) := by
  exact (standalone_RSP_TableBounds__foldl_invariant (fun S _ => popLayer A i j S) LayerRange
    (List.range (activeVertices A.I).length) (initLayer A T i j)
    (initLayer_range A T hT i j) (fun S _ hS => popLayer_range A i j S hS)).1

private theorem buildTable_range (A : InnerInput) : TableRange (buildTable A) := by
  unfold buildTable
  apply standalone_RSP_TableBounds__foldl_invariant
  · intro v i j
    exact ⟨zero_le_one, le_rfl⟩
  · intro T i hT
    apply standalone_RSP_TableBounds__foldl_invariant
    · exact hT
    · intro U j hU
      exact buildLayer_range A U hU i j

private theorem dpValue_buildTable_nonneg (A : InnerInput) (v i j : ℕ) :
    0 ≤ dpValue A (buildTable A) v i j :=
  (dpValue_range A (buildTable A) (buildTable_range A) v i j).1

private theorem dpValue_buildTable_le_one (A : InnerInput) (v i j : ℕ) :
    dpValue A (buildTable A) v i j ≤ 1 :=
  (dpValue_range A (buildTable A) (buildTable_range A) v i j).2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem activeVertices_edge_left (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges) : u ∈ activeVertices I := by
  simp only [activeVertices, List.mem_eraseDups, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨(u,v), h, by simp⟩

private theorem activeVertices_edge_right (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges) : v ∈ activeVertices I := by
  simp only [activeVertices, List.mem_eraseDups, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨(u,v), h, by simp⟩

@[simp] private theorem putCell_same (T : Table) (v i j : ℕ) (c : Cell) :
    putCell T v i j c v i j = c := by simp [putCell]

private theorem putCell_other_vertex (T : Table) (v w i j : ℕ) (c : Cell) (h : w ≠ v) :
    putCell T v i j c w i j = T w i j := by simp [putCell, h]

private theorem putCell_other_layer (T : Table) (v w i j a b : ℕ) (c : Cell)
    (h : a ≠ i ∨ b ≠ j) : putCell T v i j c w a b = T w a b := by
  rcases h with h | h <;> simp [putCell, h]

@[simp] private theorem relaxEdge_table (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) : (relaxEdge A i j u S e).table = S.table := by
  unfold relaxEdge
  dsimp only
  split <;> try rfl
  split <;> rfl

@[simp] private theorem relaxEdge_queue (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) : (relaxEdge A i j u S e).queue = S.queue := by
  unfold relaxEdge
  dsimp only
  split <;> try rfl
  split <;> rfl

@[simp] private theorem relaxEdge_nextRank (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) : (relaxEdge A i j u S e).nextRank = S.nextRank := by
  unfold relaxEdge
  dsimp only
  split <;> try rfl
  split <;> rfl

private theorem relaxEdge_keys_outside (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hv : v ∉ S.queue) :
    (relaxEdge A i j u S e).keys v = S.keys v := by
  unfold relaxEdge
  dsimp only
  split
  · rename_i he
    split
    · have hne : v ≠ e.2 := by intro h; subst v; exact hv he.2.2
      simp [Function.update_of_ne hne]
    · rfl
  · rfl

private theorem relaxEdge_parents_outside (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hv : v ∉ S.queue) :
    (relaxEdge A i j u S e).parents v = S.parents v := by
  unfold relaxEdge
  dsimp only
  split
  · rename_i he
    split
    · have hne : v ≠ e.2 := by intro h; subst v; exact hv he.2.2
      simp [Function.update_of_ne hne]
    · rfl
  · rfl

private theorem relaxEdge_keys_le (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) : (relaxEdge A i j u S e).keys v ≤ S.keys v := by
  unfold relaxEdge
  dsimp only
  split
  · split
    · rename_i h
      by_cases hv : v = e.2
      · subst v; simpa using h.le
      · simp [Function.update_of_ne hv]
    · exact le_rfl
  · exact le_rfl

private theorem standalone_Mission_QueueStructure__fold_preserves {α β γ : Type*} (f : β → α → β) (p : β → γ)
    (hf : ∀ s a, p (f s a) = p s) (xs : List α) (s : β) :
    p (xs.foldl f s) = p s := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => simpa only [List.foldl_cons, ih, hf]

@[simp] private theorem relaxAll_table (A : InnerInput) (i j u : ℕ) (S : LayerState) :
    (relaxAll A i j u S).table = S.table := by
  exact standalone_Mission_QueueStructure__fold_preserves _ LayerState.table (fun _ _ => relaxEdge_table ..) _ _

@[simp] private theorem relaxAll_queue (A : InnerInput) (i j u : ℕ) (S : LayerState) :
    (relaxAll A i j u S).queue = S.queue := by
  exact standalone_Mission_QueueStructure__fold_preserves _ LayerState.queue (fun _ _ => relaxEdge_queue ..) _ _

@[simp] private theorem relaxAll_nextRank (A : InnerInput) (i j u : ℕ) (S : LayerState) :
    (relaxAll A i j u S).nextRank = S.nextRank := by
  exact standalone_Mission_QueueStructure__fold_preserves _ LayerState.nextRank (fun _ _ => relaxEdge_nextRank ..) _ _

private theorem relaxAll_keys_outside (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue) : (relaxAll A i j u S).keys v = S.keys v := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldl_cons, ih _ (by simpa using hv)]
      exact relaxEdge_keys_outside A i j u v S e hv

private theorem relaxAll_parents_outside (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue) : (relaxAll A i j u S).parents v = S.parents v := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldl_cons, ih _ (by simpa using hv)]
      exact relaxEdge_parents_outside A i j u v S e hv

private theorem popLayer_queue_length (A : InnerInput) (i j : ℕ) (S : LayerState) :
    (popLayer A i j S).queue.length = S.queue.length - 1 := by
  unfold popLayer
  split
  · rename_i h
    simp [h]
  · rename_i v vs hq
    change (relaxAll A i j _ _).queue.length = _
    rw [relaxAll_queue]
    dsimp only
    apply List.length_erase_of_mem
    exact firstMin_mem _ _ _ (by rw [hq]; simp)

private theorem popLayer_queue_subset (A : InnerInput) (i j : ℕ) (S : LayerState) :
    (popLayer A i j S).queue ⊆ S.queue := by
  unfold popLayer
  split
  · exact List.Subset.refl _
  · change (relaxAll A i j _ _).queue ⊆ S.queue
    rw [relaxAll_queue]
    exact List.erase_subset

private theorem popLayer_other_layer (A : InnerInput) (i j : ℕ) (S : LayerState)
    (v a b : ℕ) (h : a ≠ i ∨ b ≠ j) :
    (popLayer A i j S).table v a b = S.table v a b := by
  unfold popLayer
  split
  · rfl
  · change (relaxAll A i j _ _).table v a b = _
    rw [relaxAll_table]
    exact putCell_other_layer _ _ _ _ _ _ _ _ h

@[simp] private theorem queueRun_zero (A : InnerInput) (i j : ℕ) (S : LayerState) :
    queueRun A i j 0 S = S := rfl

@[simp] private theorem queueRun_succ (A : InnerInput) (i j n : ℕ) (S : LayerState) :
    queueRun A i j (n + 1) S = popLayer A i j (queueRun A i j n S) := by
  simp [queueRun, List.range_succ, List.foldl_append]

private theorem queueRun_queue_length (A : InnerInput) (i j n : ℕ) (S : LayerState) :
    (queueRun A i j n S).queue.length = S.queue.length - n := by
  induction n with
  | zero => simp
  | succ n ih => rw [queueRun_succ, popLayer_queue_length, ih]; omega

private theorem queueRun_queue_subset (A : InnerInput) (i j n : ℕ) (S : LayerState) :
    (queueRun A i j n S).queue ⊆ S.queue := by
  induction n with
  | zero => exact List.Subset.refl _
  | succ n ih =>
      rw [queueRun_succ]
      intro v hv
      exact ih (popLayer_queue_subset A i j _ hv)

private theorem queueRun_other_layer (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (v a b : ℕ) (h : a ≠ i ∨ b ≠ j) :
    (queueRun A i j n S).table v a b = S.table v a b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [queueRun_succ, popLayer_other_layer A i j _ v a b h, ih]

private theorem buildLayer_other_layer (A : InnerInput) (T : Table) (i j v a b : ℕ)
    (h : a ≠ i ∨ b ≠ j) : buildLayer A T i j v a b = T v a b :=
  queueRun_other_layer A i j _ (initLayer A T i j) v a b h

private theorem buildLayer_queue_exhausted (A : InnerInput) (T : Table) (i j : ℕ) :
    (queueRun A i j (activeVertices A.I).length (initLayer A T i j)).queue = [] := by
  apply List.length_eq_zero_iff.mp
  rw [queueRun_queue_length]
  simp [initLayer]

private theorem popLayer_queue_nodup (A : InnerInput) (i j : ℕ) (S : LayerState)
    (h : S.queue.Nodup) : (popLayer A i j S).queue.Nodup := by
  unfold popLayer
  split
  · exact h
  · change (relaxAll A i j _ _).queue.Nodup
    rw [relaxAll_queue]
    exact h.erase _

private theorem queueRun_queue_nodup (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (h : S.queue.Nodup) : (queueRun A i j n S).queue.Nodup := by
  induction n with
  | zero => exact h
  | succ n ih => rw [queueRun_succ]; exact popLayer_queue_nodup A i j _ ih

private theorem popLayer_sync (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (hS : PoppedSync A i j S) :
    PoppedSync A i j (popLayer A i j S) := by
  unfold popLayer
  split
  · exact hS
  · rename_i w ws hq
    let u := firstMin S.keys S.queue w
    let U : LayerState := { S with
      table := putCell S.table u i j ⟨S.keys u, S.parents u, S.nextRank⟩
      queue := S.queue.erase u
      nextRank := S.nextRank + 1 }
    change PoppedSync A i j (relaxAll A i j u U)
    intro v hv hvq
    have hvU : v ∉ U.queue := by simpa only [relaxAll_queue] using hvq
    rw [relaxAll_table, relaxAll_keys_outside A i j u v U hvU]
    change (putCell S.table u i j _ v i j).value = S.keys v
    by_cases hvu : v = u
    · subst v
      simp
    · rw [putCell_other_vertex _ _ _ _ _ _ hvu]
      apply hS v hv
      intro hm
      exact hvU ((List.mem_erase_of_ne hvu).mpr hm)

private theorem queueRun_sync (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (hS : PoppedSync A i j S) :
    PoppedSync A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact hS
  | succ n ih =>
      rw [queueRun_succ]
      exact popLayer_sync A i j _ (queueRun_queue_nodup A i j n S hdup) ih

private theorem relaxEdge_zero_key (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerRange S) (hz : S.keys v = 0) :
    (relaxEdge A i j u S e).keys v = 0 := by
  unfold relaxEdge
  dsimp only
  split
  · split
    · rename_i hk
      by_cases hv : v = e.2
      · subst v
        have hn := (edgeExpectation_range A S.table hS.1 e.1 e.2 i j).1
        rw [hz] at hk
        exact False.elim (not_lt_of_ge hn hk)
      · simpa [Function.update_of_ne hv] using hz
    · exact hz
  · exact hz

private theorem relaxAll_zero_key (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0) :
    (relaxAll A i j u S).keys v = 0 := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact hz
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih _ (relaxEdge_range A i j u S e hS) (relaxEdge_zero_key A i j u v S e hS hz)

private theorem popLayer_zero_key (A : InnerInput) (i j v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0) : (popLayer A i j S).keys v = 0 := by
  unfold popLayer
  split
  · exact hz
  · change (relaxAll A i j _ _).keys v = 0
    apply relaxAll_zero_key
    · exact ⟨putCell_range S.table _ i j _ hS.1 (hS.2 _), hS.2⟩
    · exact hz

private theorem queueRun_range (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hS : LayerRange S) : LayerRange (queueRun A i j n S) := by
  induction n with
  | zero => exact hS
  | succ n ih => rw [queueRun_succ]; exact popLayer_range A i j _ ih

private theorem queueRun_zero_key (A : InnerInput) (i j n v : ℕ) (S : LayerState)
    (hS : LayerRange S) (hz : S.keys v = 0) : (queueRun A i j n S).keys v = 0 := by
  induction n with
  | zero => exact hz
  | succ n ih =>
      rw [queueRun_succ]
      exact popLayer_zero_key A i j v _ (queueRun_range A i j n S hS) ih

private theorem buildLayer_source_zero (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableRange T) : (buildLayer A T i j A.I.source i j).value = 0 := by
  have hsync : PoppedSync A i j (initLayer A T i j) := by
    intro v hv hvq
    exact False.elim (hvq hv)
  have h := queueRun_sync A i j (activeVertices A.I).length (initLayer A T i j)
    (activeVertices_nodup A.I) hsync
  have hzero := queueRun_zero_key A i j (activeVertices A.I).length A.I.source
    (initLayer A T i j) (initLayer_range A T hT i j) (by simp [initLayer])
  have hempty := buildLayer_queue_exhausted A T i j
  exact (h A.I.source (activeVertices_source_mem A.I) (by rw [hempty]; simp)).trans hzero

private theorem edgeExpectation_congr (A : InnerInput) (T U : Table) (u v i j : ℕ)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        dpValue A T u (i + a) (j + b) = dpValue A U u (i + a) (j + b)) :
    edgeExpectation A T u v i j = edgeExpectation A U u v i j := by
  unfold edgeExpectation
  split
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [h a ha b hb]

private theorem edgeExpectation_mono (A : InnerInput) (T U : Table) (u v i j : ℕ)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        dpValue A T u (i + a) (j + b) ≤ dpValue A U u (i + a) (j + b)) :
    edgeExpectation A T u v i j ≤ edgeExpectation A U u v i j := by
  unfold edgeExpectation
  split
  · exact le_rfl
  · apply add_le_add_right
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    exact mul_le_mul_of_nonneg_left (h a ha b hb)
      (RSP.PoissonBridge.edgeMass_nonneg A u v a b)

private theorem edgeExpectation_extensive (A : InnerInput) (T : Table) (u v i j : ℕ)
    (baseline : ℝ) (hb : baseline ≤ 1)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        baseline ≤ dpValue A T u (i + a) (j + b)) :
    baseline ≤ edgeExpectation A T u v i j := by
  unfold edgeExpectation
  split
  · exact hb
  · let mass : ℝ := ∑ a ∈ Finset.range (tickLimit A - i),
        ∑ b ∈ Finset.range (tickLimit A - j), edgeMass A u v a b
    have hm : mass ≤ 1 := RSP.PoissonBridge.edgeMass_sum_le_one A u v i j
    have hsum : mass * baseline ≤ ∑ a ∈ Finset.range (tickLimit A - i),
        ∑ b ∈ Finset.range (tickLimit A - j),
          edgeMass A u v a b * dpValue A T u (i + a) (j + b) := by
      simp only [mass, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb'
      exact mul_le_mul_of_nonneg_left (h a ha b hb')
        (RSP.PoissonBridge.edgeMass_nonneg A u v a b)
    have hprod := mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hm)
    change baseline ≤ 1 - mass + _
    nlinarith

private theorem dpValue_congr_at (A : InnerInput) (T U : Table) (v i j : ℕ)
    (h : T v i j = U v i j) : dpValue A T v i j = dpValue A U v i j := by
  unfold dpValue
  split
  · rfl
  · rw [h]

private theorem relaxEdge_futureBound (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerFutureBound A i j S) :
    LayerFutureBound A i j (relaxEdge A i j u S e) := by
  intro v hv a b hab
  rw [relaxEdge_table]
  apply (relaxEdge_keys_le A i j u v S e).trans
  exact hS v (by simpa using hv) a b hab

private theorem relaxAll_keys_le (A : InnerInput) (i j u v : ℕ) (S : LayerState) :
    (relaxAll A i j u S).keys v ≤ S.keys v := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact le_rfl
  | cons e es ih =>
      rw [List.foldl_cons]
      exact (ih _).trans (relaxEdge_keys_le A i j u v S e)

private theorem relaxAll_futureBound (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S) :
    LayerFutureBound A i j (relaxAll A i j u S) := by
  intro v hv a b hab
  rw [relaxAll_table]
  apply (relaxAll_keys_le A i j u v S).trans
  exact hS v (by simpa using hv) a b hab

private theorem popLayer_keys_le (A : InnerInput) (i j v : ℕ) (S : LayerState) :
    (popLayer A i j S).keys v ≤ S.keys v := by
  unfold popLayer
  split
  · exact le_rfl
  · exact relaxAll_keys_le A i j _ v _

private theorem popLayer_future_dpValue (A : InnerInput) (i j : ℕ) (S : LayerState)
    (v a b : ℕ) (hab : a ≠ 0 ∨ b ≠ 0) :
    dpValue A (popLayer A i j S).table v (i + a) (j + b) =
      dpValue A S.table v (i + a) (j + b) := by
  apply dpValue_congr_at
  exact popLayer_other_layer A i j S v (i + a) (j + b) (by omega)

private theorem popLayer_futureBound (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S) :
    LayerFutureBound A i j (popLayer A i j S) := by
  intro v hv a b hab
  rw [popLayer_future_dpValue A i j S v a b hab]
  exact (popLayer_keys_le A i j v S).trans
    (hS v (popLayer_queue_subset A i j S hv) a b hab)

private theorem queueRun_futureBound (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S) :
    LayerFutureBound A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact hS
  | succ n ih => rw [queueRun_succ]; exact popLayer_futureBound A i j _ ih

private theorem settleState_expectation_ge (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hu : u ∈ S.queue)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S) (v : ℕ) :
    S.keys u ≤ edgeExpectation A (settleState S i j u).table u v i j := by
  apply edgeExpectation_extensive A _ u v i j (S.keys u) (hS.2 u).2
  intro a _ b _
  by_cases hab : a = 0 ∧ b = 0
  · rcases hab with ⟨rfl, rfl⟩
    simp [settleState, dpValue, Nat.not_le.mpr hi, Nat.not_le.mpr hj]
  · have heq : dpValue A (settleState S i j u).table u (i + a) (j + b) =
        dpValue A S.table u (i + a) (j + b) := by
      apply dpValue_congr_at
      exact putCell_other_layer _ _ _ _ _ _ _ _ (by omega)
    rw [heq]
    exact hfuture u hu a b (by omega)

private theorem relaxEdge_keys_ge (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (baseline : ℝ)
    (hkeys : ∀ v ∈ S.queue, baseline ≤ S.keys v)
    (hexpect : ∀ v, baseline ≤ edgeExpectation A S.table u v i j) :
    ∀ v ∈ (relaxEdge A i j u S e).queue,
      baseline ≤ (relaxEdge A i j u S e).keys v := by
  intro v hv
  have hvS : v ∈ S.queue := by simpa using hv
  unfold relaxEdge
  dsimp only
  split
  · rename_i he
    split
    · by_cases hve : v = e.2
      · subst v
        simp only [Function.update_self]
        simpa only [he.1] using hexpect e.2
      · simpa [Function.update_of_ne hve] using hkeys v hvS
    · exact hkeys v hvS
  · exact hkeys v hvS

private theorem relaxAll_keys_ge (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (baseline : ℝ) (hkeys : ∀ v ∈ S.queue, baseline ≤ S.keys v)
    (hexpect : ∀ v, baseline ≤ edgeExpectation A S.table u v i j) :
    ∀ v ∈ (relaxAll A i j u S).queue, baseline ≤ (relaxAll A i j u S).keys v := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact hkeys
  | cons e es ih =>
      rw [List.foldl_cons]
      apply ih
      · exact relaxEdge_keys_ge A i j u S e baseline hkeys hexpect
      · simpa only [relaxEdge_table] using hexpect

private theorem pickedVertex_mem (S : LayerState) (hne : S.queue ≠ []) :
    pickedVertex S ∈ S.queue := firstMin_mem _ _ _ hne

private theorem pickedVertex_le (S : LayerState) (v : ℕ) (hv : v ∈ S.queue) :
    S.keys (pickedVertex S) ≤ S.keys v := firstMin_le_of_mem _ _ _ _ hv

private theorem popLayer_eq_relaxAll (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []) :
    popLayer A i j S =
      relaxAll A i j (pickedVertex S) (settleState S i j (pickedVertex S)) := by
  cases hq : S.queue with
  | nil => exact False.elim (hne hq)
  | cons w ws => simp [popLayer, pickedVertex, settleState, relaxAll, hq]

private theorem popLayer_keys_ge_picked (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ [])
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S) :
    ∀ v ∈ (popLayer A i j S).queue,
      S.keys (pickedVertex S) ≤ (popLayer A i j S).keys v := by
  cases hq : S.queue with
  | nil => exact False.elim (hne hq)
  | cons w ws =>
      let u := firstMin S.keys S.queue w
      have hu : u ∈ S.queue := firstMin_mem S.keys S.queue w hne
      have hpick : pickedVertex S = u := by simp [pickedVertex, u, hq]
      have hpop : popLayer A i j S = relaxAll A i j u (settleState S i j u) := by
        simp [popLayer, settleState, relaxAll, u, hq]
      rw [hpop, hpick]
      apply relaxAll_keys_ge
      · intro v hv
        exact firstMin_le_of_mem S.keys S.queue w v
          (List.mem_of_mem_erase (by exact hv))
      · exact settleState_expectation_ge A i j u S hi hj hu hS hfuture

private theorem popLayer_picked_key_mono (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ [])
    (hnext : (popLayer A i j S).queue ≠ [])
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S) :
    S.keys (pickedVertex S) ≤ (popLayer A i j S).keys (pickedVertex (popLayer A i j S)) :=
  popLayer_keys_ge_picked A i j S hi hj hne hS hfuture _ (pickedVertex_mem _ hnext)

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem pathWeight_cons_cons (w : ℕ → ℕ → ℝ≥0) (a b : ℕ) (P : List ℕ) :
    pathWeight w (a :: b :: P) = (w a b : ℝ) + pathWeight w (b :: P) := by
  simp [pathWeight]

private theorem pathWeight_nonneg (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) :
    0 ≤ pathWeight w P := by
  unfold pathWeight
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
  exact (w e.1 e.2).coe_nonneg

private theorem pathWeight_tail_le (w : ℕ → ℕ → ℝ≥0) (a : ℕ) (P : List ℕ) :
    pathWeight w P ≤ pathWeight w (a :: P) := by
  cases P with
  | nil => simp [pathWeight]
  | cons b P =>
      rw [pathWeight_cons_cons]
      exact le_add_of_nonneg_left (w a b).coe_nonneg

private theorem pathWeight_suffix_le (w : ℕ → ℕ → ℝ≥0) (pre post : List ℕ) :
    pathWeight w post ≤ pathWeight w (pre ++ post) := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
      exact ih.trans (pathWeight_tail_le w a (pre ++ post))

private theorem exists_pathReduction (P : List ℕ) : ∃ Q, PathReduction P Q := by
  classical
  have main : ∀ n : ℕ, ∀ P : List ℕ, P.length = n → ∃ Q, PathReduction P Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hlen
      cases P with
      | nil =>
          exact ⟨[], ⟨rfl, rfl, by simp, fun _ h => h, fun _ h => h, fun _ => le_rfl⟩⟩
      | cons a P =>
          by_cases ha : a ∈ P
          · obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp ha
            have hshort : (a :: after).length < n := by
              simp only [List.length_cons, List.length_append] at hlen ⊢
              omega
            obtain ⟨Q, hQ⟩ := ih (a :: after).length hshort (a :: after) rfl
            refine ⟨Q, ⟨?_, ?_, hQ.nodup, ?_, ?_, ?_⟩⟩
            · simpa using hQ.head
            · change Q.getLast? = ((a :: before) ++ a :: after).getLast?
              rw [List.getLast?_append_of_ne_nil _ (by simp)]
              exact hQ.last
            · intro x hx
              have := hQ.subset hx
              simp only [List.mem_cons, List.mem_append] at this ⊢
              tauto
            · intro R hR
              exact hQ.chain R (by
                have hR' : ((a :: before) ++ a :: after).IsChain R := hR
                exact hR'.right_of_append)
            · intro w
              exact (hQ.weight w).trans (pathWeight_suffix_le w (a :: before) (a :: after))
          · have hshort : P.length < n := by simp only [List.length_cons] at hlen; omega
            obtain ⟨Q, hQ⟩ := ih P.length hshort P rfl
            refine ⟨a :: Q, ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩⟩
            · cases P with
              | nil =>
                  have hnil : Q = [] := by simpa using hQ.head
                  subst Q
                  rfl
              | cons b P =>
                  cases Q with
                  | nil => have h := hQ.head; simp at h
                  | cons c Q => simpa using hQ.last
            · exact List.nodup_cons.mpr ⟨fun h => ha (hQ.subset h), hQ.nodup⟩
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem a (hQ.subset hx)
            · intro R hR
              apply List.IsChain.cons (hQ.chain R hR.tail)
              intro y hy
              exact hR.rel_head? (by simpa only [hQ.head] using hy)
            · intro w
              cases P with
              | nil =>
                  have hnil : Q = [] := by simpa using hQ.head
                  subst Q
                  exact le_rfl
              | cons b P =>
                  cases Q with
                  | nil => have h := hQ.head; simp at h
                  | cons c Q =>
                      have hcb : c = b := by simpa using hQ.head
                      subst c
                      simp only [pathWeight_cons_cons]
                      have hw := hQ.weight w
                      linarith
  exact main P.length P rfl

private theorem isChain_vertices_lt (G : Digraph) (P : List ℕ)
    (hchain : P.IsChain (fun u v => (u, v) ∈ G.edges))
    (hhead : ∀ v ∈ P.head?, v < G.n) : ∀ v ∈ P, v < G.n := by
  induction P with
  | nil => simp
  | cons a P ih =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hhead _ rfl
      · apply ih hchain.tail ?_ v hv
        intro b hb
        exact (G.endpoints (a, b) (hchain.rel_head? hb)).2

private theorem IsPath.vertices_lt (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) : ∀ v ∈ P, v < G.n := by
  apply isChain_vertices_lt G P hP.2.2
  intro v hv
  rw [hP.1] at hv
  have hv' : s = v := by simpa using hv
  exact hv' ▸ hs

private theorem IsPath.length_le_of_nodup (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) (hnd : P.Nodup) : P.length ≤ G.n := by
  have hsub : P ⊆ List.range G.n := by
    intro v hv
    exact List.mem_range.mpr (IsPath.vertices_lt G s t P hP hs v hv)
  simpa using hnd.length_le_of_subset hsub

private theorem IsPath.exists_simple (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) :
    ∃ Q : List ℕ, IsPath G s t Q ∧ Q.Nodup ∧ Q.length ≤ G.n ∧
      Q ⊆ P ∧ ∀ w : ℕ → ℕ → ℝ≥0, pathWeight w Q ≤ pathWeight w P := by
  obtain ⟨Q, hQ⟩ := exists_pathReduction P
  have hpath : IsPath G s t Q :=
    ⟨hQ.head.trans hP.1, hQ.last.trans hP.2.1, hQ.chain _ hP.2.2⟩
  exact ⟨Q, hpath, hQ.nodup, IsPath.length_le_of_nodup G s t Q hpath hs hQ.nodup,
    hQ.subset, hQ.weight⟩

private theorem Feasible.exists_simple (I : Instance) (t : ℕ) (P : List ℕ)
    (hP : Feasible I t P) :
    ∃ Q : List ℕ, Feasible I t Q ∧ Q.Nodup ∧ Q.length ≤ I.graph.n ∧
      pathWeight I.length Q ≤ pathWeight I.length P := by
  obtain ⟨Q, hQ, hnd, hlen, _, hw⟩ :=
    IsPath.exists_simple I.graph I.source t P hP.1 I.source_valid
  exact ⟨Q, ⟨hQ, (hw I.cost).trans hP.2⟩, hnd, hlen, hw I.length⟩

private theorem pathWeight_le_length_mul (G : Digraph) (w : ℕ → ℕ → ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ u v, (u, v) ∈ G.edges → (w u v : ℝ) ≤ M)
    (P : List ℕ) (hP : P.IsChain (fun u v => (u, v) ∈ G.edges)) :
    pathWeight w P ≤ (P.length : ℝ) * M := by
  induction P with
  | nil => simp [pathWeight]
  | cons a P ih =>
      cases P with
      | nil => simpa [pathWeight] using hM
      | cons b P =>
          have htail := ih hP.tail
          have hedge := hw a b hP.rel
          rw [pathWeight_cons_cons]
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at htail ⊢
          nlinarith

private theorem IsPath.weight_le_n_mul (G : Digraph) (s t : ℕ) (P : List ℕ)
    (hP : IsPath G s t P) (hs : s < G.n) (hnd : P.Nodup)
    (w : ℕ → ℕ → ℝ≥0) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ u v, (u, v) ∈ G.edges → (w u v : ℝ) ≤ M) :
    pathWeight w P ≤ (G.n : ℝ) * M := by
  apply (pathWeight_le_length_mul G w M hM hw P hP.2.2).trans
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast IsPath.length_le_of_nodup G s t P hP hs hnd) hM

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem distanceLess_iff (x y : Option ℝ) :
    distanceLess x y = true ↔ optionDist x < optionDist y := by
  cases x <;> cases y <;> simp [distanceLess, optionDist]

private theorem standalone_Mission_ShortestTreeStructure__treeFold_mem (T : ShortestTree) (xs : List ℕ) (P : ℕ → Prop)
    (x : ℕ) (hx : P x) (hall : ∀ y ∈ xs, P y) :
    P (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x) := by
  induction xs generalizing x with
  | nil => exact hx
  | cons y ys ih =>
      simp only [List.foldl_cons]
      apply ih
      · split <;> first | exact hall y (by simp) | exact hx
      · intro z hz; exact hall z (by simp [hz])

private theorem treePick_mem (S : TreeQueue) (hne : S.queue ≠ []) :
    treePick S ∈ S.queue := by
  apply standalone_Mission_ShortestTreeStructure__treeFold_mem
  · cases h : S.queue with
    | nil => exact False.elim (hne h)
    | cons x xs => simp
  · intro y hy; exact hy

private theorem standalone_Mission_ShortestTreeStructure__treeFold_le_seed (T : ShortestTree) (xs : List ℕ) (x : ℕ) :
    treeDist T (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x) ≤ treeDist T x := by
  induction xs generalizing x with
  | nil => exact le_rfl
  | cons y ys ih =>
      simp only [List.foldl_cons]
      apply (ih _).trans
      split
      · rename_i h; exact (distanceLess_iff _ _ |>.mp h).le
      · exact le_rfl

private theorem standalone_Mission_ShortestTreeStructure__treeFold_le_mem (T : ShortestTree) (xs : List ℕ) (x y : ℕ)
    (hy : y ∈ xs) :
    treeDist T (xs.foldl (fun x y =>
      if distanceLess (T y).distance (T x).distance then y else x) x) ≤ treeDist T y := by
  induction xs generalizing x with
  | nil => simp at hy
  | cons z zs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hy with rfl | hy
      · apply (standalone_Mission_ShortestTreeStructure__treeFold_le_seed T zs _).trans
        split
        · exact le_rfl
        · rename_i h
          exact le_of_not_gt (fun hlt => h ((distanceLess_iff _ _).mpr hlt))
      · exact ih _ hy

private theorem treePick_le (S : TreeQueue) (v : ℕ) (hv : v ∈ S.queue) :
    treeDist S.tree (treePick S) ≤ treeDist S.tree v :=
  standalone_Mission_ShortestTreeStructure__treeFold_le_mem _ _ _ _ hv

@[simp] private theorem treeRelax_queue (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ) :
    (treeRelax I allow w u S e).queue = S.queue := by
  unfold treeRelax
  split <;> try rfl
  split <;> try rfl
  dsimp only
  split <;> rfl

@[simp] private theorem treeRelax_rank (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ) :
    (treeRelax I allow w u S e).rank = S.rank := by
  unfold treeRelax
  split <;> try rfl
  split <;> try rfl
  dsimp only
  split <;> rfl

private theorem treeRelax_outside (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (hv : v ∉ S.queue) : (treeRelax I allow w u S e).tree v = S.tree v := by
  unfold treeRelax
  split
  · rename_i he
    split <;> try rfl
    dsimp only
    split
    · have hne : v ≠ e.2 := by intro h; subst v; exact hv he.2.2.1
      simp [hne]
    · rfl
  · rfl

private theorem treeRelax_dist_le (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (e : ℕ × ℕ) :
    treeDist (treeRelax I allow w u S e).tree v ≤ treeDist S.tree v := by
  unfold treeRelax
  split <;> try exact le_rfl
  split <;> try exact le_rfl
  dsimp only
  split
  · rename_i h
    by_cases hv : v = e.2
    · subst v; simpa [treeDist] using (distanceLess_iff _ _ |>.mp h).le
    · simp [treeDist, hv]
  · exact le_rfl

private theorem standalone_Mission_ShortestTreeStructure__treeFold_preserves {α β γ : Type*} (f : β → α → β) (p : β → γ)
    (hf : ∀ s a, p (f s a) = p s) (xs : List α) (s : β) :
    p (xs.foldl f s) = p s := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => simpa only [List.foldl_cons, ih, hf]

@[simp] private theorem treeRelaxAll_queue (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) :
    (treeRelaxAll I allow w u S).queue = S.queue :=
  standalone_Mission_ShortestTreeStructure__treeFold_preserves _ TreeQueue.queue (fun _ _ => treeRelax_queue ..) _ _

@[simp] private theorem treeRelaxAll_rank (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) :
    (treeRelaxAll I allow w u S).rank = S.rank :=
  standalone_Mission_ShortestTreeStructure__treeFold_preserves _ TreeQueue.rank (fun _ _ => treeRelax_rank ..) _ _

private theorem treeRelaxFold_outside (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ))
    (hv : v ∉ S.queue) :
    (es.foldl (treeRelax I allow w u) S).tree v = S.tree v := by
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
      rw [List.foldl_cons, ih _ (by simpa using hv)]
      exact treeRelax_outside I allow w u v S e hv

private theorem treeRelaxAll_outside (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (hv : v ∉ S.queue) :
    (treeRelaxAll I allow w u S).tree v = S.tree v :=
  treeRelaxFold_outside I allow w u v S _ hv

private theorem treeRelaxFold_dist_le (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ)) :
    treeDist (es.foldl (treeRelax I allow w u) S).tree v ≤ treeDist S.tree v := by
  induction es generalizing S with
  | nil => exact le_rfl
  | cons e es ih =>
      rw [List.foldl_cons]
      exact (ih _).trans (treeRelax_dist_le I allow w u v S e)

private theorem treeRelaxAll_dist_le (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue) :
    treeDist (treeRelaxAll I allow w u S).tree v ≤ treeDist S.tree v :=
  treeRelaxFold_dist_le I allow w u v S _

@[simp] private theorem treeSettle_dist (S : TreeQueue) (u v : ℕ) :
    treeDist (treeSettle S u).tree v = treeDist S.tree v := by
  by_cases h : v = u <;> simp [treeDist, treeSettle, h]

private theorem treePop_eq_relaxAll (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []) :
    treePop I allow w S = treeRelaxAll I allow w (treePick S) (treeSettle S (treePick S)) := by
  unfold treePop treeRelaxAll treePick treeSettle
  split
  · contradiction
  · rename_i h
    simp only [h, List.headD_cons]

private theorem treePop_queue_length (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) :
    (treePop I allow w S).queue.length = S.queue.length - 1 := by
  by_cases h : S.queue = []
  · simp [treePop, h]
  · rw [treePop_eq_relaxAll I allow w S h, treeRelaxAll_queue]
    exact List.length_erase_of_mem (treePick_mem S h)

private theorem treePop_queue_subset (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) :
    (treePop I allow w S).queue ⊆ S.queue := by
  by_cases h : S.queue = []
  · simp [treePop, h]
  · rw [treePop_eq_relaxAll I allow w S h, treeRelaxAll_queue]
    exact List.erase_subset

private theorem treePop_queue_nodup (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hS : S.queue.Nodup) :
    (treePop I allow w S).queue.Nodup := by
  by_cases h : S.queue = []
  · simpa [treePop, h] using hS
  · rw [treePop_eq_relaxAll I allow w S h, treeRelaxAll_queue]
    exact hS.erase _

@[simp] private theorem treeRun_zero (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) : treeRun I allow w 0 S = S := rfl

private theorem treeRun_succ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) :
    treeRun I allow w (n + 1) S = treePop I allow w (treeRun I allow w n S) := by
  simp [treeRun, List.range_succ, List.foldl_append]

private theorem treeRun_queue_length (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) :
    (treeRun I allow w n S).queue.length = S.queue.length - n := by
  induction n with
  | zero => simp
  | succ n ih => rw [treeRun_succ, treePop_queue_length, ih]; omega

private theorem treeRun_queue_nodup (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (hS : S.queue.Nodup) :
    (treeRun I allow w n S).queue.Nodup := by
  induction n with
  | zero => exact hS
  | succ n ih => rw [treeRun_succ]; exact treePop_queue_nodup I allow w _ ih

private theorem shortestTree_eq_treeRun (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) :
    shortestTree I allow w = (treeRun I allow w (activeVertices I).length (treeInitial I)).tree := rfl

private theorem shortestTree_queue_exhausted (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) :
    (treeRun I allow w (activeVertices I).length (treeInitial I)).queue = [] := by
  apply List.length_eq_zero_iff.mp
  rw [treeRun_queue_length]
  exact Nat.sub_self _

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem treeInitial_policy (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) : TreePolicy I allow w (treeInitial I) := by
  constructor
  · intro v d hd
    by_cases hv : v = I.source
    · subst v; exact activeVertices_source_mem I
    · simp [treeInitial, hv] at hd
  · intro v hv hn
    exact False.elim (hn hv)
  · intro v d hd
    by_cases hv : v = I.source
    · exact Or.inl hv
    · simp [treeInitial, hv] at hd
  · simp [treeInitial]

private theorem treeSettle_policy (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (u : ℕ) (hu : u ∈ S.queue)
    (h : TreePolicy I allow w S) : TreePolicy I allow w (treeSettle S u) := by
  have hd : ∀ v, ((treeSettle S u).tree v).distance = (S.tree v).distance := by
    intro v; by_cases hv : v = u <;> simp [treeSettle, hv]
  constructor
  · intro v d hv
    rw [hd] at hv
    exact h.active v d hv
  · intro v hv hn
    change (Function.update S.tree u { S.tree u with rank := S.rank } v).rank < S.rank + 1
    by_cases hvu : v = u
    · subst v; simp
    · rw [Function.update_of_ne hvu]
      have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne hvu).mpr hm)
      exact (h.settled v hv hn').trans (Nat.lt_succ_self _)
  · intro v d hv
    rw [hd] at hv
    rcases h.finite v d hv with hvs | ⟨p,a,hp,ha,heq,he,hal,hpq,hpr,hvr⟩
    · exact Or.inl hvs
    · have hpu : p ≠ u := by intro hh; subst p; exact hpq hu
      refine Or.inr ⟨p,a,?_,?_,heq,he,hal,?_,?_,?_⟩
      · by_cases hvu : v = u
        · subst v; simpa [treeSettle] using hp
        · simpa [treeSettle, hvu] using hp
      · rw [hd]; exact ha
      · exact fun hm => hpq (List.mem_of_mem_erase hm)
      · change (Function.update S.tree u _ p).rank < S.rank + 1
        rw [Function.update_of_ne hpu]
        omega
      · intro hvq
        change (Function.update S.tree u _ p).rank < (Function.update S.tree u _ v).rank
        rw [Function.update_of_ne hpu]
        by_cases hvu : v = u
        · subst v; simpa using hpr
        · rw [Function.update_of_ne hvu]
          exact hvr (fun hm => hvq ((List.mem_erase_of_ne hvu).mpr hm))
  · change S.rank + 1 + (S.queue.erase u).length = _
    rw [List.length_erase_of_mem hu]
    have hlen : 0 < S.queue.length := List.length_pos_of_mem hu
    have hb := h.balance
    omega

private theorem treeRelax_policy (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : e ∈ I.graph.edges) (hu : u ∉ S.queue)
    (hur : (S.tree u).rank < S.rank) (h : TreePolicy I allow w S) :
    TreePolicy I allow w (treeRelax I allow w u S e) := by
  unfold treeRelax
  split
  · rename_i he'
    split
    · exact h
    · rename_i d hd
      dsimp only
      split
      · have hev : e.2 ∈ activeVertices I := activeVertices_edge_right I e.1 e.2 he
        have he1 : e.1 = u := he'.1
        constructor
        · intro v a hv
          by_cases hvv : v = e.2
          · simpa only [hvv] using hev
          · simp only [Function.update_of_ne hvv] at hv
            exact h.active v a hv
        · intro v hv hvq
          have hvv : v ≠ e.2 := by intro hh; subst v; exact hvq he'.2.2.1
          simp only [Function.update_of_ne hvv]
          exact h.settled v hv hvq
        · intro v a hv
          by_cases hvv : v = e.2
          · subst v
            simp only [Function.update_self, Option.some.injEq] at hv
            have huv : u ≠ e.2 := by simpa only [he1] using he'.2.1
            refine Or.inr ⟨u,d,?_,?_,?_,?_,?_,hu,?_,?_⟩
            · simp
            · simpa only [Function.update_of_ne huv] using hd
            · simpa only [he1] using hv.symm
            · have hepair : (e.1, e.2) ∈ I.graph.edges := by simpa using he
              simpa only [he1] using hepair
            · have hepair : (e.1, e.2) ∈ I.graph.edges := by simpa using he
              simpa only [he1] using he'.2.2.2
            · simpa only [Function.update_of_ne huv] using hur
            · intro hn; exact False.elim (hn he'.2.2.1)
          · simp only [Function.update_of_ne hvv] at hv
            rcases h.finite v a hv with hvs | ⟨p,b,hp,hb,heq,hpe,hpa,hpq,hpr,hvr⟩
            · exact Or.inl hvs
            · have hpv : p ≠ e.2 := by intro hh; subst p; exact hpq he'.2.2.1
              refine Or.inr ⟨p,b,?_,?_,heq,hpe,hpa,hpq,?_,?_⟩
              · simpa only [Function.update_of_ne hvv] using hp
              · simpa only [Function.update_of_ne hpv] using hb
              · simpa only [Function.update_of_ne hpv] using hpr
              · simpa only [Function.update_of_ne hpv, Function.update_of_ne hvv] using hvr
        · exact h.balance
      · exact h
  · exact h

private theorem treeRelaxFold_policy (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ))
    (hes : ∀ e ∈ es, e ∈ I.graph.edges) (hu : u ∉ S.queue)
    (hur : (S.tree u).rank < S.rank) (h : TreePolicy I allow w S) :
    TreePolicy I allow w (es.foldl (treeRelax I allow w u) S) := by
  induction es generalizing S with
  | nil => exact h
  | cons e es ih =>
      rw [List.foldl_cons]
      apply ih _ (fun e he => hes e (by simp [he]))
      · simpa only [treeRelax_queue] using hu
      · rw [treeRelax_outside I allow w u u S e hu, treeRelax_rank]
        exact hur
      · exact treeRelax_policy I allow w u S e (hes e (by simp)) hu hur h

private theorem treePop_policy (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hdup : S.queue.Nodup)
    (h : TreePolicy I allow w S) : TreePolicy I allow w (treePop I allow w S) := by
  by_cases hq : S.queue = []
  · simpa [treePop, hq] using h
  · rw [treePop_eq_relaxAll I allow w S hq]
    apply treeRelaxFold_policy
    · intro e he; exact he
    · exact hdup.not_mem_erase
    · simp [treeSettle]
    · exact treeSettle_policy I allow w S _ (treePick_mem S hq) h

private theorem treeRun_policy (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (hdup : S.queue.Nodup)
    (h : TreePolicy I allow w S) : TreePolicy I allow w (treeRun I allow w n S) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [treeRun_succ]
      exact treePop_policy I allow w _ (treeRun_queue_nodup I allow w n S hdup) ih

private theorem shortestTree_finite_rank (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d) :
    (shortestTree I allow w v).rank < (activeVertices I).length := by
  have h := treeRun_policy I allow w (activeVertices I).length (treeInitial I)
    (activeVertices_nodup I) (treeInitial_policy I allow w)
  have hn : v ∉ (treeRun I allow w (activeVertices I).length (treeInitial I)).queue := by
    rw [shortestTree_queue_exhausted]; simp
  have hb := h.balance
  rw [shortestTree_queue_exhausted] at hb
  have hrank : (treeRun I allow w (activeVertices I).length (treeInitial I)).rank =
      (activeVertices I).length := by simpa only [List.length_nil, Nat.add_zero] using hb
  rw [shortestTree_eq_treeRun]
  exact (h.settled v (h.active v d hd) hn).trans_le hrank.le

private theorem shortestTree_finite_parent (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ) (hv : v ≠ I.source)
    (hd : (shortestTree I allow w v).distance = some d) :
    ∃ u a, (shortestTree I allow w v).parent = some u ∧
      (shortestTree I allow w u).distance = some a ∧ d = a + w u v ∧
      (u,v) ∈ I.graph.edges ∧ allow u v = true ∧
      (shortestTree I allow w u).rank < (shortestTree I allow w v).rank := by
  have h := treeRun_policy I allow w (activeVertices I).length (treeInitial I)
    (activeVertices_nodup I) (treeInitial_policy I allow w)
  rcases h.finite v d hd with hs | ⟨u,a,hp,ha,heq,he,hal,_,_,hr⟩
  · exact False.elim (hv hs)
  · exact ⟨u,a,hp,ha,heq,he,hal,hr (by rw [shortestTree_queue_exhausted]; simp)⟩

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem treePop_dist_le (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (v : ℕ) :
    treeDist (treePop I allow w S).tree v ≤ treeDist S.tree v := by
  by_cases h : S.queue = []
  · simp [treePop, h]
  · rw [treePop_eq_relaxAll I allow w S h]
    exact (treeRelaxAll_dist_le I allow w _ v _).trans_eq (treeSettle_dist S _ v)

private theorem treePop_outside (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (v : ℕ) (hv : v ∉ S.queue) :
    (treePop I allow w S).tree v = S.tree v := by
  by_cases h : S.queue = []
  · simp [treePop, h]
  · rw [treePop_eq_relaxAll I allow w S h, treeRelaxAll_outside]
    · have hne : v ≠ treePick S := by intro heq; subst v; exact hv (treePick_mem S h)
      simp [treeSettle, hne]
    · intro hm; exact hv (List.mem_of_mem_erase hm)

private theorem treePop_dist_picked (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ [])
    (hdup : S.queue.Nodup) :
    treeDist (treePop I allow w S).tree (treePick S) = treeDist S.tree (treePick S) := by
  rw [treePop_eq_relaxAll I allow w S hne]
  unfold treeDist
  rw [treeRelaxAll_outside I allow w _ _ _ hdup.not_mem_erase]
  simp [treeSettle]

private theorem treeRelax_dist_ge (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (baseline : WithTop ℝ) (hkeys : ∀ v ∈ S.queue, baseline ≤ treeDist S.tree v)
    (hu : baseline ≤ treeDist S.tree u) (hw : 0 ≤ w e.1 e.2) :
    ∀ v ∈ (treeRelax I allow w u S e).queue,
      baseline ≤ treeDist (treeRelax I allow w u S e).tree v := by
  intro v hv
  have hv' : v ∈ S.queue := by simpa using hv
  unfold treeRelax
  split <;> try exact hkeys v hv'
  rename_i he
  split <;> try exact hkeys v hv'
  rename_i d hd
  dsimp only
  split <;> try exact hkeys v hv'
  by_cases hv : v = e.2
  · subst v
    have hdu : treeDist S.tree u = (d : WithTop ℝ) := by simp [treeDist, optionDist, optionDist, hd]
    have hstep : (d : WithTop ℝ) ≤ ((d + w e.1 e.2 : ℝ) : WithTop ℝ) := by
      exact WithTop.coe_le_coe.mpr (by linarith)
    simpa [treeDist, optionDist, optionDist] using hu.trans (by rw [hdu]; exact hstep)
  · simpa [treeDist, optionDist, hv] using hkeys v hv'

private theorem treeRelaxFold_dist_ge (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (es : List (ℕ × ℕ)) (baseline : WithTop ℝ)
    (hkeys : ∀ v ∈ S.queue, baseline ≤ treeDist S.tree v)
    (hu : baseline ≤ treeDist S.tree u) (huq : u ∉ S.queue) :
    ∀ v ∈ (es.foldl (treeRelax I allow w u) S).queue,
      baseline ≤ treeDist (es.foldl (treeRelax I allow w u) S).tree v := by
  induction es generalizing S with
  | nil => exact hkeys
  | cons e es ih =>
      rw [List.foldl_cons]
      apply ih
      · exact treeRelax_dist_ge I allow w u S e baseline hkeys hu (hw _ _)
      · unfold treeDist
        rw [treeRelax_outside I allow w u u S e huq]
        exact hu
      · simpa using huq

private theorem treePop_dist_ge_picked (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hne : S.queue ≠ []) (hdup : S.queue.Nodup) :
    ∀ v ∈ (treePop I allow w S).queue,
      treeDist S.tree (treePick S) ≤ treeDist (treePop I allow w S).tree v := by
  rw [treePop_eq_relaxAll I allow w S hne]
  apply treeRelaxFold_dist_ge I allow w hw
  · intro v hv
    rw [treeSettle_dist]
    exact treePick_le S v (List.mem_of_mem_erase hv)
  · rw [treeSettle_dist]
  · exact hdup.not_mem_erase

private theorem treeRelax_edge_bound (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue)
    (huv : u ≠ v) (hv : v ∈ S.queue) (ha : allow u v = true) :
    treeDist (treeRelax I allow w u S (u,v)).tree v ≤
      treeDist S.tree u + (w u v : WithTop ℝ) := by
  unfold treeRelax
  rw [if_pos ⟨rfl, huv, hv, ha⟩]
  split
  · rename_i h
    simp [treeDist, optionDist, h]
  · rename_i d hd
    dsimp only
    split
    · simp [treeDist, optionDist, hd, WithTop.coe_add]
    · rename_i h
      have hle := le_of_not_gt (fun hlt => h ((distanceLess_iff _ _).mpr hlt))
      simpa [treeDist, optionDist, hd, WithTop.coe_add] using hle

private theorem treeRelaxAll_edge_bound (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u v : ℕ) (S : TreeQueue)
    (huv : u ≠ v) (hv : v ∈ S.queue) (hu : u ∉ S.queue)
    (ha : allow u v = true) (hedge : (u,v) ∈ I.graph.edges) :
    treeDist (treeRelaxAll I allow w u S).tree v ≤
      treeDist S.tree u + (w u v : WithTop ℝ) := by
  unfold treeRelaxAll
  generalize he : I.graph.edges = es at hedge ⊢
  clear he
  induction es generalizing S with
  | nil => simp at hedge
  | cons e es ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hedge with he | hm
      · subst e
        exact (treeRelaxFold_dist_le I allow w u v _ es).trans
          (treeRelax_edge_bound I allow w u v S huv hv ha)
      · have hrec := ih (treeRelax I allow w u S e) (by simpa using hv)
          (by simpa using hu) hm
        simpa only [treeDist, treeRelax_outside I allow w u u S e hu] using hrec

private theorem treePop_separation (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S) :
    TreeSeparation I (treePop I allow w S) := by
  by_cases hne : S.queue = []
  · simpa [treePop, hne] using hsep
  · intro u hu huq v hvq
    have hp := treePick_mem S hne
    have hvbound := treePop_dist_ge_picked I allow w hw S hne hdup v hvq
    by_cases hup : u = treePick S
    · subst u
      rw [treePop_dist_picked I allow w S hne hdup]
      exact hvbound
    · have huold : u ∉ S.queue := by
        intro hm
        apply huq
        rw [treePop_eq_relaxAll I allow w S hne, treeRelaxAll_queue]
        exact (List.mem_erase_of_ne hup).mpr hm
      unfold treeDist
      rw [treePop_outside I allow w S u huold]
      exact (hsep u hu huold _ hp).trans hvbound

private theorem treePop_bellman (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S)
    (hbell : TreeBellman I allow w S) : TreeBellman I allow w (treePop I allow w S) := by
  by_cases hne : S.queue = []
  · simpa [treePop, hne] using hbell
  · intro u hu huq v huv ha
    have hp := treePick_mem S hne
    have hpop := treePop_eq_relaxAll I allow w S hne
    by_cases hup : u = treePick S
    · subst u
      rw [treePop_dist_picked I allow w S hne hdup]
      have hext : treeDist S.tree (treePick S) ≤
          treeDist S.tree (treePick S) + (w (treePick S) v : WithTop ℝ) :=
        le_add_of_nonneg_right (WithTop.coe_nonneg.mpr (hw _ _))
      by_cases hvnew : v ∈ (treePop I allow w S).queue
      · have hvU : v ∈ (treeSettle S (treePick S)).queue := by
          simpa only [hpop, treeRelaxAll_queue] using hvnew
        have hpv : treePick S ≠ v := by
          intro heq; subst v; exact hdup.not_mem_erase hvU
        rw [hpop]
        exact (treeRelaxAll_edge_bound I allow w _ v _ hpv hvU
          hdup.not_mem_erase ha huv).trans_eq (by rw [treeSettle_dist])
      · by_cases hvp : v = treePick S
        · subst v
          rw [treePop_dist_picked I allow w S hne hdup]
          exact hext
        · have hvold : v ∉ S.queue := by
            intro hm
            apply hvnew
            rw [hpop, treeRelaxAll_queue]
            exact (List.mem_erase_of_ne hvp).mpr hm
          unfold treeDist
          rw [treePop_outside I allow w S v hvold]
          exact (hsep v (activeVertices_edge_right I _ v huv) hvold _ hp).trans hext
    · have huold : u ∉ S.queue := by
        intro hm
        apply huq
        rw [hpop, treeRelaxAll_queue]
        exact (List.mem_erase_of_ne hup).mpr hm
      have heq : treeDist (treePop I allow w S).tree u = treeDist S.tree u := by
        unfold treeDist; rw [treePop_outside I allow w S u huold]
      rw [heq]
      exact (treePop_dist_le I allow w S v).trans (hbell u hu huold v huv ha)

private theorem treeRun_bellman_separation (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (n : ℕ) (S : TreeQueue)
    (hdup : S.queue.Nodup) (hsep : TreeSeparation I S) (hbell : TreeBellman I allow w S) :
    TreeSeparation I (treeRun I allow w n S) ∧ TreeBellman I allow w (treeRun I allow w n S) := by
  induction n with
  | zero => exact ⟨hsep, hbell⟩
  | succ n ih =>
      rw [treeRun_succ]
      have hd := treeRun_queue_nodup I allow w n S hdup
      exact ⟨treePop_separation I allow w hw _ hd ih.1,
        treePop_bellman I allow w hw _ hd ih.1 ih.2⟩

private theorem shortestTree_bellman (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u v : ℕ)
    (he : (u,v) ∈ I.graph.edges) (ha : allow u v = true) :
    treeDist (shortestTree I allow w) v ≤
      treeDist (shortestTree I allow w) u + (w u v : WithTop ℝ) := by
  have hs : TreeSeparation I (treeInitial I) := by
    intro a ha hq; exact False.elim (hq ha)
  have hb : TreeBellman I allow w (treeInitial I) := by
    intro a ha hq; exact False.elim (hq ha)
  have hmain := (treeRun_bellman_separation I allow w hw (activeVertices I).length
    (treeInitial I) (activeVertices_nodup I) hs hb).2
  rw [shortestTree_eq_treeRun]
  exact hmain u (activeVertices_edge_left I u v he)
    (by rw [shortestTree_queue_exhausted]; simp) v he ha

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem treeRelax_dist_nonneg (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v) (e : ℕ × ℕ) :
    ∀ v, 0 ≤ treeDist (treeRelax I allow w u S e).tree v := by
  intro v
  by_cases hv : v ∈ S.queue
  · exact treeRelax_dist_ge I allow w u S e 0 (fun v _ => hS v) (hS u)
      (hw _ _) v (by simpa using hv)
  · unfold treeDist
    rw [treeRelax_outside I allow w u v S e hv]
    exact hS v

private theorem treeRelaxAll_dist_nonneg (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v) :
    ∀ v, 0 ≤ treeDist (treeRelaxAll I allow w u S).tree v := by
  unfold treeRelaxAll
  generalize I.graph.edges = es
  induction es generalizing S with
  | nil => exact hS
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih _ (treeRelax_dist_nonneg I allow w hw u S hS e)

private theorem treePop_dist_nonneg (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v) :
    ∀ v, 0 ≤ treeDist (treePop I allow w S).tree v := by
  by_cases hne : S.queue = []
  · simpa [treePop, hne] using hS
  · rw [treePop_eq_relaxAll I allow w S hne]
    apply treeRelaxAll_dist_nonneg I allow w hw
    intro v; rw [treeSettle_dist]; exact hS v

private theorem treeRun_dist_nonneg (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (n : ℕ)
    (S : TreeQueue) (hS : ∀ v, 0 ≤ treeDist S.tree v) :
    ∀ v, 0 ≤ treeDist (treeRun I allow w n S).tree v := by
  induction n with
  | zero => exact hS
  | succ n ih => rw [treeRun_succ]; exact treePop_dist_nonneg I allow w hw _ ih

private theorem treeRun_dist_le (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue) (v : ℕ) :
    treeDist (treeRun I allow w n S).tree v ≤ treeDist S.tree v := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [treeRun_succ]; exact (treePop_dist_le I allow w _ v).trans ih

private theorem shortestTree_dist_nonneg (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (v : ℕ) :
    0 ≤ treeDist (shortestTree I allow w) v := by
  rw [shortestTree_eq_treeRun]
  apply treeRun_dist_nonneg I allow w hw
  intro v
  by_cases hv : v = I.source <;> simp [treeDist, treeInitial, optionDist, hv]

private theorem shortestTree_source_zero (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) :
    (shortestTree I allow w I.source).distance = some 0 := by
  have hge := shortestTree_dist_nonneg I allow w hw I.source
  have hle : treeDist (shortestTree I allow w) I.source ≤ 0 := by
    rw [shortestTree_eq_treeRun]
    exact (treeRun_dist_le I allow w _ _ _).trans_eq (by simp [treeDist, treeInitial, optionDist])
  have heq := le_antisymm hle hge
  unfold treeDist at heq
  cases hd : (shortestTree I allow w I.source).distance with
  | none => simp [hd, optionDist] at heq
  | some d => simpa [hd, optionDist] using heq

private theorem shortestTree_distance_nonneg (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d) : 0 ≤ d := by
  simpa [treeDist, optionDist, hd] using shortestTree_dist_nonneg I allow w hw v

private theorem treeDist_chain_bound (I : Instance) (T : ShortestTree)
    (allow : ℕ → ℕ → Bool) (w : ℕ → ℕ → ℝ≥0)
    (hbell : ∀ u v, (u,v) ∈ I.graph.edges → allow u v = true →
      treeDist T v ≤ treeDist T u + ((w u v : ℝ) : WithTop ℝ))
    (P : List ℕ) (s t : ℕ) (hp : IsPath I.graph s t P)
    (ha : P.IsChain (fun u v => allow u v = true)) :
    treeDist T t ≤ treeDist T s + ((pathWeight w P : ℝ) : WithTop ℝ) := by
  induction P generalizing s with
  | nil => simp [IsPath] at hp
  | cons a P ih =>
      have has : a = s := by simpa [IsPath] using hp.1
      subst s
      cases P with
      | nil =>
          have hat : a = t := by simpa using hp.2.1
          subst t
          simp [pathWeight]
      | cons b P =>
          have htail : IsPath I.graph b t (b :: P) :=
            ⟨by simp, by simpa using hp.2.1, hp.2.2.tail⟩
          have hed := hbell a b hp.2.2.rel ha.rel
          have hrec := ih b htail ha.tail
          apply hrec.trans
          rw [pathWeight_cons_cons, WithTop.coe_add]
          simpa only [add_assoc, add_comm, add_left_comm] using add_le_add_right hed ((pathWeight w (b :: P) : ℝ) : WithTop ℝ)

private theorem shortestTree_path_bound (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P)
    (ha : P.IsChain (fun u v => allow u v = true)) :
    ∃ d : ℝ, (shortestTree I allow (fun u v => w u v) t).distance = some d ∧
      d ≤ pathWeight w P := by
  have hw : ∀ u v, 0 ≤ (w u v : ℝ) := fun u v => (w u v).coe_nonneg
  have hb := treeDist_chain_bound I (shortestTree I allow (fun u v => w u v)) allow w
    (shortestTree_bellman I allow (fun u v => w u v) hw) P I.source t hp ha
  simp only [treeDist, shortestTree_source_zero I allow _ hw, optionDist, WithTop.coe_zero,
    zero_add] at hb
  cases hd : (shortestTree I allow (fun u v => w u v) t).distance with
  | none => simp [hd, optionDist] at hb
  | some d => exact ⟨d, rfl, by simpa [hd, optionDist] using hb⟩

private theorem pathWeight_zero_chain (w : ℕ → ℕ → ℝ≥0) (P : List ℕ)
    (h : pathWeight w P = 0) : P.IsChain (fun u v => w u v = 0) := by
  induction P with
  | nil => simp
  | cons a P ih =>
      cases P with
      | nil => simp
      | cons b P =>
          rw [pathWeight_cons_cons] at h
          have htail : pathWeight w (b :: P) = 0 := by
            have := pathWeight_nonneg w (b :: P)
            have := (w a b).coe_nonneg
            linarith
          have hab : w a b = 0 := by
            apply Subtype.ext
            change (w a b : ℝ) = 0
            linarith
          exact (ih htail).cons (by simpa using hab)

private theorem zeroLengthTree_path_bound (I : Instance) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P) (hz : pathWeight I.length P = 0) :
    ∃ d : ℝ, (zeroLengthTree I t).distance = some d ∧ d ≤ pathWeight I.cost P := by
  apply shortestTree_path_bound I _ I.cost P t hp
  simpa using pathWeight_zero_chain I.length P hz

private theorem zeroBudgetTree_path_bound (I : Instance) (P : List ℕ) (t : ℕ)
    (hp : IsPath I.graph I.source t P) (hz : pathWeight I.cost P = 0) :
    ∃ d : ℝ, (zeroBudgetTree I t).distance = some d ∧ d ≤ pathWeight I.length P := by
  apply shortestTree_path_bound I _ I.length P t hp
  simpa using pathWeight_zero_chain I.cost P hz

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem activeVertices_length_le_edges (I : Instance) :
    (activeVertices I).length ≤ 2 * I.graph.edges.length + 1 := by
  have hsub : activeVertices I ⊆ I.source :: I.graph.edges.flatMap (fun e => [e.1,e.2]) := by
    intro v hv
    simpa only [activeVertices, List.mem_eraseDups] using hv
  have hlen := (activeVertices_nodup I).length_le_of_subset hsub
  have hflat : (I.graph.edges.flatMap (fun e => [e.1,e.2])).length =
      2 * I.graph.edges.length := by
    generalize I.graph.edges = es
    induction es with
    | nil => rfl
    | cons e es ih => simp only [List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil, ih]; omega
  simpa only [List.length_cons, hflat] using hlen

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem edgeWeightSum_nonneg (I : Instance) (w : ℕ → ℕ → ℝ≥0) :
    0 ≤ edgeWeightSum I w := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx
  exact (w e.1 e.2).coe_nonneg

private theorem weight_le_edgeWeightSum (I : Instance) (w : ℕ → ℕ → ℝ≥0) (u v : ℕ)
    (he : (u,v) ∈ I.graph.edges) : (w u v : ℝ) ≤ edgeWeightSum I w := by
  apply List.single_le_sum
  · intro x hx
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx
    exact (w e.1 e.2).coe_nonneg
  · exact List.mem_map.mpr ⟨(u,v),he,rfl⟩

private theorem treePolicy_distance_bound (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (h : TreePolicy I allow w S)
    (hs : (S.tree I.source).distance = some 0) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ u v, (u,v) ∈ I.graph.edges → w u v ≤ W)
    (v : ℕ) (d : ℝ) (hd : (S.tree v).distance = some d) :
    d ≤ (S.rank : ℝ) * W := by
  have settled : ∀ n v d, (S.tree v).rank = n → v ∉ S.queue →
      (S.tree v).distance = some d → d ≤ (n : ℝ) * W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro v d hr hvq hd
        rcases h.finite v d hd with hv | ⟨u,a,_,ha,heq,he,_,hu,_,hur⟩
        · subst v
          have hd0 : d = 0 := by rw [hs] at hd; exact (Option.some.inj hd).symm
          rw [hd0]; positivity
        · have hun : (S.tree u).rank < n := by simpa only [hr] using hur hvq
          have hb := ih _ hun u a rfl hu ha
          have hn : ((S.tree u).rank : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hun)
          have hm := mul_le_mul_of_nonneg_right hn hW
          have hew := hw u v he
          rw [heq]
          nlinarith
  rcases h.finite v d hd with hv | ⟨u,a,_,ha,heq,he,_,hu,hur,_⟩
  · subst v
    have hd0 : d = 0 := by rw [hs] at hd; exact (Option.some.inj hd).symm
    rw [hd0]; positivity
  · have hb := settled _ u a rfl hu ha
    have hn : ((S.tree u).rank : ℝ) + 1 ≤ (S.rank : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hur)
    have hm := mul_le_mul_of_nonneg_right hn hW
    have hew := hw u v he
    rw [heq]
    nlinarith

private theorem treeRun_source_zero (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (k : ℕ) :
    ((treeRun I allow w k (treeInitial I)).tree I.source).distance = some 0 := by
  have hge := treeRun_dist_nonneg I allow w hw k (treeInitial I)
    (by intro v; by_cases hv : v = I.source <;> simp [treeDist,treeInitial,optionDist,hv]) I.source
  have hle : treeDist (treeRun I allow w k (treeInitial I)).tree I.source ≤ 0 := by
    exact (treeRun_dist_le I allow w k (treeInitial I) I.source).trans_eq
      (by simp [treeDist,treeInitial,optionDist])
  have hh := le_antisymm hle hge
  unfold treeDist at hh
  cases hd : ((treeRun I allow w k (treeInitial I)).tree I.source).distance with
  | none => simp [hd,optionDist] at hh
  | some d => simpa [hd,optionDist] using hh

private theorem treeRun_sentinel_bound (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (k v : ℕ) (d : ℝ)
    (hd : ((treeRun I allow (fun u v => (w u v : ℝ)) k (treeInitial I)).tree v).distance = some d) :
    d < ((I.graph.n : ℝ) + 1) * (1 + edgeWeightSum I w) := by
  let S := treeRun I allow (fun u v => (w u v : ℝ)) k (treeInitial I)
  have h := treeRun_policy I allow (fun u v => (w u v : ℝ)) k (treeInitial I)
    (activeVertices_nodup I) (treeInitial_policy I allow _)
  have hb := treePolicy_distance_bound I allow _ S h
    (treeRun_source_zero I allow _ (fun u v => (w u v).coe_nonneg) k)
    (edgeWeightSum I w) (edgeWeightSum_nonneg I w) (weight_le_edgeWeightSum I w) v d hd
  have hn : S.rank ≤ I.graph.n := by
    have hbal := h.balance
    change S.rank + S.queue.length = (activeVertices I).length at hbal
    have hactive := activeVertices_length_le_vertices I
    omega
  have hnr : (S.rank : ℝ) ≤ (I.graph.n : ℝ) := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_right hnr (edgeWeightSum_nonneg I w)
  have hn0 : (0 : ℝ) ≤ I.graph.n := Nat.cast_nonneg _
  have hw0 := edgeWeightSum_nonneg I w
  nlinarith

private theorem distanceLess_eq_sentinel (top : ℝ) (x y : Option ℝ)
    (hx : ∀ d, x = some d → d < top) (hy : ∀ d, y = some d → d < top) :
    distanceLess x y = decide (x.getD top < y.getD top) := by
  cases x with
  | none =>
      cases y with
      | none => simp [distanceLess]
      | some b => simp [distanceLess, not_lt.mpr (hy b rfl).le]
  | some a =>
      cases y with
      | none => simp [distanceLess, hx a rfl]
      | some b => rfl

private theorem treePick_eq_sentinel_firstMin (top : ℝ) (S : TreeQueue)
    (hfinite : ∀ v d, (S.tree v).distance = some d → d < top) :
    treePick S = firstMin (sentinelKey top S.tree) S.queue 0 := by
  have hf : (fun x y => if distanceLess (S.tree y).distance (S.tree x).distance
      then y else x) =
      (fun x y => if sentinelKey top S.tree y < sentinelKey top S.tree x then y else x) := by
    funext x y
    rw [distanceLess_eq_sentinel top _ _ (hfinite y) (hfinite x)]
    simp [sentinelKey]
    split_ifs with hh
    · exact (if_pos hh).symm
    · exact (if_neg hh).symm
  simp only [treePick, firstMin, hf]

private theorem treeRun_pick_sentinel (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ≥0) (k : ℕ) :
    let S := treeRun I allow (fun u v => (w u v : ℝ)) k (treeInitial I)
    treePick S = firstMin
      (sentinelKey (((I.graph.n : ℝ)+1)*(1+edgeWeightSum I w)) S.tree) S.queue 0 := by
  apply treePick_eq_sentinel_firstMin
  exact treeRun_sentinel_bound I allow w k

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

private theorem activeLeaf_at (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ)
    (hk : k<xs.length) : activeLeaf xs q key B (B+k) =
      ⟨if slotVertex xs k∈q then k+1 else 0,key (slotVertex xs k)⟩ := by
  simp [activeLeaf,slotVertex,hk]

private theorem activeLeaf_outside (xs q : List ℕ) (key : ℕ → ℝ) (B node : ℕ)
    (h : node<B ∨ B+xs.length≤node) : activeLeaf xs q key B node=⟨0,0⟩ := by
  have hn : ¬ (B≤node ∧ node<B+xs.length) := by omega
  simp [activeLeaf,hn]

private theorem slotVertex_injective (xs : List ℕ) (hxs : xs.Nodup) (i j : ℕ)
    (hi : i<xs.length) (hj : j<xs.length) : slotVertex xs i=slotVertex xs j ↔ i=j := by
  simp only [slotVertex,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some]
  exact hxs.getElem_inj_iff

private theorem slotVertex_idxOf (xs : List ℕ) (hxs : xs.Nodup) (k : ℕ) (hk : k<xs.length) :
    xs.idxOf (slotVertex xs k)=k := by
  simpa [slotVertex,List.getElem?_eq_getElem hk] using hxs.idxOf_getElem k hk

private theorem activeLeaf_single_change (xs q q' : List ℕ) (key key' : ℕ → ℝ)
    (B k : ℕ) (hxs : xs.Nodup) (hk : k<xs.length)
    (hkey : ∀ v, v≠slotVertex xs k → key' v=key v)
    (hq : ∀ v, v≠slotVertex xs k → (v∈q' ↔ v∈q)) :
    activeLeaf xs q' key' B = Function.update (activeLeaf xs q key B) (B+k)
      ⟨if slotVertex xs k∈q' then k+1 else 0,key' (slotVertex xs k)⟩ := by
  funext node
  by_cases hn : node=B+k
  · subst node
    rw [Function.update_self,activeLeaf_at xs q' key' B k hk]
  · rw [Function.update_of_ne hn]
    by_cases hinside : B≤node ∧ node<B+xs.length
    · have hneq : slotVertex xs (node-B)≠slotVertex xs k := by
        intro he
        have hi := (slotVertex_injective xs hxs (node-B) k (by omega) hk).mp he
        omega
      simp only [activeLeaf,if_pos hinside]
      change (⟨if slotVertex xs (node-B)∈q' then node-B+1 else 0,
        key' (slotVertex xs (node-B))⟩ : Record) =
        ⟨if slotVertex xs (node-B)∈q then node-B+1 else 0,key (slotVertex xs (node-B))⟩
      simp only [hkey _ hneq,hq _ hneq]
    · simp only [activeLeaf,if_neg hinside]

private theorem activeLeaf_delete (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ)
    (hxs : xs.Nodup) (hq : q.Nodup) (hk : k<xs.length) :
    activeLeaf xs (q.erase (slotVertex xs k)) key B =
      Function.update (activeLeaf xs q key B) (B+k) ⟨0,key (slotVertex xs k)⟩ := by
  have h := activeLeaf_single_change xs q (q.erase (slotVertex xs k)) key key B k hxs hk
    (fun _ _=>rfl) (fun v hv=>List.mem_erase_of_ne hv)
  simpa only [if_neg hq.not_mem_erase] using h

private theorem activeLeaf_update_key (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ) (value : ℝ)
    (hxs : xs.Nodup) (hk : k<xs.length) (hq : slotVertex xs k∈q) :
    activeLeaf xs q (Function.update key (slotVertex xs k) value) B =
      Function.update (activeLeaf xs q key B) (B+k) ⟨k+1,value⟩ := by
  have h := activeLeaf_single_change xs q q key (Function.update key (slotVertex xs k) value)
    B k hxs hk (fun v hv=>Function.update_of_ne hv _ _) (fun _ _=>Iff.rfl)
  simpa only [if_pos hq,Function.update_self] using h

private theorem slotVertex_idxOf_eq (xs : List ℕ) (u : ℕ) (hu : u∈xs) :
    slotVertex xs (xs.idxOf u)=u := by simp [slotVertex,List.getElem?_idxOf hu]

private theorem activeLeaf_delete_vertex (xs q : List ℕ) (key : ℕ→ℝ) (B u : ℕ)
    (hxs : xs.Nodup) (hq : q.Nodup) (hu : u∈xs) :
    activeLeaf xs (q.erase u) key B =
      Function.update (activeLeaf xs q key B) (B+xs.idxOf u) ⟨0,key u⟩ := by
  simpa only [slotVertex_idxOf_eq xs u hu] using
    activeLeaf_delete xs q key B (xs.idxOf u) hxs hq (List.idxOf_lt_length_of_mem hu)

private theorem activeLeaf_update_vertex (xs q : List ℕ) (key : ℕ→ℝ) (B u : ℕ) (value : ℝ)
    (hxs : xs.Nodup) (hu : u∈xs) (huq : u∈q) :
    activeLeaf xs q (Function.update key u value) B =
      Function.update (activeLeaf xs q key B) (B+xs.idxOf u) ⟨xs.idxOf u+1,value⟩ := by
  simpa only [slotVertex_idxOf_eq xs u hu] using
    activeLeaf_update_key xs q key B (xs.idxOf u) value hxs (List.idxOf_lt_length_of_mem hu)
      (by simpa only [slotVertex_idxOf_eq xs u hu] using huq)

private theorem standalone_Mission_QueueLeaves__getD_map_range (xs : List ℕ) :
    (List.range xs.length).map (slotVertex xs)=xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [slotVertex,List.getElem?_eq_getElem hj]

private theorem standalone_Mission_QueueLeaves__filterMap_live (xs q : List ℕ) (f : ℕ→Record) :
    xs.filterMap (fun v=>if v∈q then some (f v) else none) =
      (xs.filter (fun v=>decide (v∈q))).map f := by
  induction xs with
  | nil => rfl
  | cons v xs ih => by_cases hv : v∈q <;> simp [hv,ih]

private theorem filter_sublist_members (xs q : List ℕ) (hxs : xs.Nodup) (hq : q.Sublist xs) :
    xs.filter (fun v=>decide (v∈q))=q := by
  have hself : q.filter (fun v=>decide (v∈q))=q := by simp
  have hsub := hq.filter (fun v=>decide (v∈q))
  rw [hself] at hsub
  symm
  apply hsub.eq_of_length_le
  apply (hxs.filter _).length_le_of_subset
  intro v hv
  simpa only [List.mem_filter,decide_eq_true_eq] using (List.mem_filter.mp hv).2

private theorem activeLeaf_records (xs q : List ℕ) (key : ℕ→ℝ) (B : ℕ)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length≤B) :
    leafRecords (activeLeaf xs q key B) B B = q.map (vertexRecord xs key) := by
  have hpadding : leafRecords (activeLeaf xs q key B) (B+xs.length) (B-xs.length)=[] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    rw [activeLeaf_outside xs q key B _ (Or.inr (by omega))]
    simp [Record.decode]
  have hsplit := leafRecords_add (activeLeaf xs q key B) B xs.length (B-xs.length)
  rw [Nat.add_sub_of_le hB] at hsplit
  rw [hsplit,hpadding,List.append_nil]
  have hpref : leafRecords (activeLeaf xs q key B) B xs.length =
      (List.range xs.length).filterMap (fun k=>
        if slotVertex xs k∈q then some (vertexRecord xs key (slotVertex xs k)) else none) := by
    unfold leafRecords
    rw [List.filterMap_map]
    apply List.filterMap_congr
    intro k hk
    have hkl : k<xs.length := List.mem_range.mp hk
    simp only [Function.comp_apply]
    rw [activeLeaf_at xs q key B k hkl]
    unfold vertexRecord
    rw [slotVertex_idxOf xs hxs k hkl]
    by_cases hmem : slotVertex xs k∈q <;> simp [Record.decode,hmem]
  rw [hpref]
  have hmap := congrArg (fun ys : List ℕ => ys.filterMap
      (fun v=>if v∈q then some (vertexRecord xs key v) else none)) (standalone_Mission_QueueLeaves__getD_map_range xs)
  simp only [List.filterMap_map,Function.comp_def] at hmap
  rw [hmap,standalone_Mission_QueueLeaves__filterMap_live,filter_sublist_members xs q hxs hq]

private theorem activeLeaf_firstMin (xs q : List ℕ) (key : ℕ→ℝ) (height : ℕ)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length≤2^height)
    (fallback : ℕ) (hne : q≠[]) :
    (heapTruth (2^height) (activeLeaf xs q key (2^height)) 1).decode =
      some (vertexRecord xs key (firstMin key q fallback)) := by
  exact heapTruth_firstMin height _ q (vertexRecord xs key)
    (activeLeaf_records xs q key _ hxs hq hB) fallback hne

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

private theorem popLayer_queue_sublist (A : InnerInput) (i j : ℕ) (S : LayerState) :
    (popLayer A i j S).queue.Sublist S.queue := by
  by_cases hq : S.queue=[]
  · simp [popLayer,hq]
  · rw [popLayer_eq_relaxAll A i j S hq,relaxAll_queue]
    exact List.erase_sublist

private theorem queueRun_queue_sublist (A : InnerInput) (i j n : ℕ) (S : LayerState) :
    (queueRun A i j n S).queue.Sublist S.queue := by
  induction n with
  | zero => exact List.Sublist.refl _
  | succ n ih =>
      rw [queueRun_succ]
      exact (popLayer_queue_sublist A i j _).trans ih

private theorem treePop_queue_sublist (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ) (S : TreeQueue) : (treePop I allow w S).queue.Sublist S.queue := by
  by_cases hq : S.queue=[]
  · simp [treePop,hq]
  · rw [treePop_eq_relaxAll I allow w S hq,treeRelaxAll_queue]
    exact List.erase_sublist

private theorem treeRun_queue_sublist (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ) (n : ℕ) (S : TreeQueue) :
    (treeRun I allow w n S).queue.Sublist S.queue := by
  induction n with
  | zero => exact List.Sublist.refl _
  | succ n ih =>
      rw [treeRun_succ]
      exact (treePop_queue_sublist I allow w _).trans ih

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

private theorem initPrefix_eval (input : RAMInput) (s : Store) :
    evalAtoms input initPrefix s = prefixed s := by
  ext a <;> simp [evalAtoms, initPrefix, Atom.eval, ramStep, Store.at, Store.ofRAM,
    prefixed, evalNat, Function.update]

private theorem initPair_eval (input : RAMInput) (s : Store) :
    evalAtoms input initPair s = paired s := by
  ext a <;> simp [evalAtoms, initPair, Atom.eval, ramStep, Store.at, Store.ofRAM,
    paired, evalNat, Function.update]

private theorem empty_coherent (capacity : ℕ) : Coherent capacity (fun _ => (⟨0, 0⟩ : Record)) := by
  intro u hu hcap
  rfl

private theorem prefixed_inv (W P B : ℕ) (s : Store) (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1) :
    InitInv W P B (B - 1) (prefixed s) := by
  refine ⟨by simp [prefixed, h0], by simp [prefixed, h1], by simp [prefixed, h2],
    by simp [prefixed, h3], by simp [prefixed, h4], by simp [prefixed], ?_⟩
  intro v hv hvsmall
  have hv2 : v < 2 := by omega
  have hWneP : W ≠ P := by omega
  have hW1neP : W + 1 ≠ P := by omega
  have hWneP1 : W ≠ P + 1 := by omega
  have hW1neP1 : W + 1 ≠ P + 1 := by omega
  have hcases : v = 0 ∨ v = 1 := by omega
  rcases hcases with rfl | rfl <;>
    simp [prefixed, h1, h2, h3, h4, hWneP, hW1neP, hWneP1, hW1neP1,
      Ne.symm hWneP, Ne.symm hW1neP, Ne.symm hWneP1, Ne.symm hW1neP1]

private theorem paired_inv (W P B k : ℕ) (s : Store) (hspace : W + 2 * B ≤ P)
    (hk : 0 < k) (hkB : k < B) (h : InitInv W P B k s) :
    InitInv W P B (k - 1) (paired s) := by
  rcases h with ⟨h0, h1, h2, h3, h4, hr0, hmem⟩
  refine ⟨by simp [paired, h0, h4], by simp [paired, h1], by simp [paired, h2],
    by simp [paired, h3], by simp [paired, h4], hr0, ?_⟩
  intro v hv hvprocessed
  have hwpl : W + v ≠ P + (k + k) := by omega
  have hwpr : W + v ≠ P + (k + k + 1) := by omega
  have hpwl : P + v ≠ W + (k + k) := by omega
  have hpwr : P + v ≠ W + (k + k + 1) := by omega
  have hdivl : (k + k) / 2 = k := by omega
  have hdivr : (k + k + 1) / 2 = k := by omega
  by_cases hl : v = k + k
  · subst v
    simp [paired, h0, h1, h2, h3, h4, hr0, hwpl, hwpr, hpwl, hpwr, hdivl]
    rw [Function.update_of_ne hwpl, Function.update_of_ne (by omega), Function.update_self]
  · by_cases hr : v = k + k + 1
    · subst v
      simp [paired, h0, h1, h2, h3, h4, hr0, hwpl, hwpr, hpwl, hpwr, hdivr]
      rw [Function.update_of_ne hwpr, Function.update_of_ne hwpl, Function.update_self]
    · have hold : v < 2 ∨ 2 * (k + 1) ≤ v := by omega
      simpa [paired, h0, h1, h2, h3, h4, hr0, hwpl, hwpr, hpwl, hpwr, hl, hr,
        Function.update_of_ne hl, Function.update_of_ne hr] using hmem v hv hold

private theorem initLoop_run (input : RAMInput) (W P B k : ℕ) (s : Store)
    (hspace : W + 2 * B ≤ P) (hkB : k < B) (h : InitInv W P B k s) :
    ∃ out, Run input (.loop (.nat .lt 3 0) (atoms initPair)) s out (15 * k + 1) ∧
      InitInv W P B 0 out := by
  induction k generalizing s with
  | zero =>
      refine ⟨s, ?_, h⟩
      exact Run.loopFalse (by simp [Guard.eval, natTest, h.1, h.2.2.2.1])
  | succ k ih =>
      have hnext := paired_inv W P B (k + 1) s hspace (by omega) hkB h
      simp only [Nat.add_sub_cancel] at hnext
      obtain ⟨out, hout, hinv⟩ := ih (paired s) (by omega) hnext
      have hbody := run_atoms input initPair s
      rw [initPair_eval] at hbody
      refine ⟨out, ?_, hinv⟩
      have hrun := Run.loopTrue
        (g := Guard.nat .lt 3 0)
        (by simp [Guard.eval, natTest, h.1, h.2.2.2.1]) hbody hout
      simpa [initPair, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun

private theorem initializeEmpty_correct (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1) :
    ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      out.nr 0 = 0 ∧ out.nr 1 = W ∧ out.nr 2 = P ∧ out.nr 3 = 0 ∧ out.nr 4 = 1 ∧
      ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, readRecord out (W + v) = ⟨0, 0⟩ := by
  have hinv := prefixed_inv W P B s hB hspace h0 h1 h2 h3 h4
  obtain ⟨out, hrun, hout⟩ := initLoop_run input W P B (B - 1) (prefixed s)
    hspace (by omega) hinv
  have hprefix := run_atoms input initPrefix s
  rw [initPrefix_eval] at hprefix
  refine ⟨out, 11 + (15 * (B - 1) + 1), Run.seq hprefix hrun, by omega,
    hout.1, hout.2.1, hout.2.2.1, hout.2.2.2.1, hout.2.2.2.2.1, ?_, ?_⟩
  · refine ⟨by rw [hout.1]; omega, ?_, hout.2.2.2.1, ?_⟩
    · simpa only [hout.2.1, hout.2.2.1] using hspace
    · intro u hu
      rw [hout.2.2.1]
      exact (hout.2.2.2.2.2.2 u hu (by omega)).2.2
  · intro v hv
    have hm := hout.2.2.2.2.2.2 v hv (by omega)
    simp [readRecord, hm.1, hm.2.1]

private theorem InitFrame.refl (W P B : ℕ) (s : Store) : InitFrame W P B s s :=
  ⟨by intros; rfl, by intros; rfl⟩

private theorem InitFrame.trans (W P B : ℕ) (s u t : Store)
    (h : InitFrame W P B s u) (h' : InitFrame W P B u t) : InitFrame W P B s t :=
  ⟨fun a ha ha' => (h'.1 a ha ha').trans (h.1 a ha ha'),
    fun a ha => (h'.2 a ha).trans (h.2 a ha)⟩

private theorem prefixed_frame (W P B : ℕ) (s : Store) (hB : 0 < B)
    (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h4 : s.nr 4 = 1) :
    InitFrame W P B s (prefixed s) := by
  constructor
  · intro a hw hp
    have hW : a ≠ W := by omega
    have hW1 : a ≠ W + 1 := by omega
    have hP : a ≠ P := by omega
    have hP1 : a ≠ P + 1 := by omega
    simp [prefixed, h1, h2, h4, hW, hW1, hP, hP1]
  · intro a hw
    have hW : a ≠ W := by omega
    have hW1 : a ≠ W + 1 := by omega
    simp [prefixed, h1, h4, hW, hW1]

private theorem paired_frame (W P B k : ℕ) (s : Store) (hkB : k < B)
    (h0 : s.nr 0 = k) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h4 : s.nr 4 = 1) :
    InitFrame W P B s (paired s) := by
  constructor
  · intro a hw hp
    have hW : a ≠ W + (k + k) := by omega
    have hW1 : a ≠ W + (k + k + 1) := by omega
    have hP : a ≠ P + (k + k) := by omega
    have hP1 : a ≠ P + (k + k + 1) := by omega
    simp [paired, h0, h1, h2, h4, hW, hW1, hP, hP1]
  · intro a hw
    have hW : a ≠ W + (k + k) := by omega
    have hW1 : a ≠ W + (k + k + 1) := by omega
    simp [paired, h0, h1, h4, hW, hW1]

private theorem initLoop_run_framed (input : RAMInput) (W P B k : ℕ) (s : Store)
    (hspace : W + 2 * B ≤ P) (hkB : k < B) (h : InitInv W P B k s) :
    ∃ out, Run input (.loop (.nat .lt 3 0) (atoms initPair)) s out (15 * k + 1) ∧
      InitInv W P B 0 out ∧ InitFrame W P B s out := by
  induction k generalizing s with
  | zero =>
      refine ⟨s, ?_, h, InitFrame.refl W P B s⟩
      exact Run.loopFalse (by simp [Guard.eval, natTest, h.1, h.2.2.2.1])
  | succ k ih =>
      have hnext := paired_inv W P B (k + 1) s hspace (by omega) hkB h
      simp only [Nat.add_sub_cancel] at hnext
      obtain ⟨out, hout, hinv, hframe⟩ := ih (paired s) (by omega) hnext
      have hbody := run_atoms input initPair s
      rw [initPair_eval] at hbody
      refine ⟨out, ?_, hinv, ?_⟩
      · have hrun := Run.loopTrue (g := Guard.nat .lt 3 0)
          (by simp [Guard.eval, natTest, h.1, h.2.2.2.1]) hbody hout
        simpa [initPair, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun
      · exact InitFrame.trans W P B s (paired s) out
          (paired_frame W P B (k + 1) s hkB h.1 h.2.1 h.2.2.1 h.2.2.2.2.1) hframe

private theorem initializeEmpty_framed (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1) :
    ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      InitInv W P B 0 out ∧ InitFrame W P B s out := by
  have hinv := prefixed_inv W P B s hB hspace h0 h1 h2 h3 h4
  obtain ⟨out, hrun, hout, hframe⟩ := initLoop_run_framed input W P B (B - 1) (prefixed s)
    hspace (by omega) hinv
  have hprefix := run_atoms input initPrefix s
  rw [initPrefix_eval] at hprefix
  refine ⟨out, 11 + (15 * (B - 1) + 1), Run.seq hprefix hrun, by omega, hout, ?_⟩
  exact InitFrame.trans W P B s (prefixed s) out (prefixed_frame W P B s hB h1 h2 h4) hframe

private theorem updateLeaf_refines (input : RAMInput) (B : ℕ) (leaf : ℕ → Record) (s : Store)
    (hparent : ParentLayout (2 * B) s) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hleaf : B ≤ s.nr 0)
    (hrep : Represents B (s.nr 1) leaf s) :
    ∃ out k, Run input updateLeaf s out k ∧ k ≤ 19 * Nat.clog 2 (2 * B) + 6 ∧
      out.nr 0 = 0 ∧ (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout (2 * B) out ∧
      Represents B (s.nr 1) (Function.update leaf (s.nr 0) ⟨s.nr 10, s.rr 2⟩) out ∧
      WinnerFrame (s.nr 1) (2 * B) s out := by
  let leaf' := Function.update leaf (s.nr 0) (⟨s.nr 10, s.rr 2⟩ : Record)
  have hlocal := heapTruth_frame B leaf leaf' (s.nr 0) hpositive
    (fun v hv => Function.update_of_ne hv _ _)
  have hready : Ready (2 * B) (heapTruth B leaf') s := by
    intro v hv hn
    rw [hlocal v hn]
    exact hrep v hv
  have hnew : heapTruth B leaf' (s.nr 0) = ⟨s.nr 10, s.rr 2⟩ := by
    rw [heapTruth_leaf B leaf' (s.nr 0) hleaf]
    exact Function.update_self _ _ _
  obtain ⟨out, k, hrun, hk, hz, hheader, hparents, hrecords⟩ :=
    updateLeaf_correct input B (heapTruth B leaf') s hparent hone hpositive
      (heapTruth_coherent B leaf') hready hnew
  exact ⟨out, k, hrun, hk, hz, hheader, hparents, hrecords,
    updateLeaf_frame input (2 * B) s out k hparent hrun⟩

private theorem initializeEmpty_represents (input : RAMInput) (W P B : ℕ) (s : Store)
    (hB : 0 < B) (hspace : W + 2 * B ≤ P)
    (h0 : s.nr 0 = B - 1) (h1 : s.nr 1 = W) (h2 : s.nr 2 = P)
    (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1) :
    ∃ out k, Run input initializeEmpty s out k ∧ k ≤ 15 * B ∧
      InitInv W P B 0 out ∧ Represents B W (fun _ => ⟨0, 0⟩) out ∧ InitFrame W P B s out := by
  obtain ⟨out, k, hrun, hk, hinv, hframe⟩ :=
    initializeEmpty_framed input W P B s hB hspace h0 h1 h2 h3 h4
  refine ⟨out, k, hrun, hk, hinv, ?_, hframe⟩
  intro v hv
  have hm := hinv.2.2.2.2.2.2 v hv (by omega)
  rw [heapTruth_const]
  simp [readRecord, hm.1, hm.2.1]

private theorem represented_root_firstMin (h W : ℕ) (leaf : ℕ → Record) (s : Store)
    (hrep : Represents (2 ^ h) W leaf s) (xs : List ℕ) (encode : ℕ → Record)
    (hslots : leafRecords leaf (2 ^ h) (2 ^ h) = xs.map encode)
    (fallback : ℕ) (hne : xs ≠ []) :
    (readRecord s (W + 1)).decode =
      some (encode (firstMin (fun v => (encode v).key) xs fallback)) := by
  have hB : 0 < 2 ^ h := by positivity
  rw [hrep 1 (by omega)]
  exact heapTruth_firstMin h leaf xs encode hslots fallback hne

private theorem prefixLeaf_zero (B : ℕ) (key : ℕ → ℝ) : prefixLeaf B key 0 = fun _ => ⟨0, 0⟩ := by
  funext v
  simp [prefixLeaf, show ¬(B ≤ v ∧ v < B + 0) by omega]

private theorem prefixLeaf_succ (B k : ℕ) (key : ℕ → ℝ) :
    Function.update (prefixLeaf B key k) (B + k) ⟨k + 1, key k⟩ = prefixLeaf B key (k + 1) := by
  funext v
  by_cases heq : v = B + k
  · subst v
    simp [prefixLeaf]
  · rw [Function.update_of_ne heq]
    unfold prefixLeaf
    have hequiv : (B ≤ v ∧ v < B + k) ↔ (B ≤ v ∧ v < B + (k + 1)) := by omega
    simp only [hequiv]

private theorem buildSetup_eval (input : RAMInput) (s : Store) :
    Queue.evalAtoms input buildSetup s = buildSetupState s := by
  ext a <;> simp [Queue.evalAtoms, buildSetup, Atom.eval, ramStep, Store.at, Store.ofRAM,
    buildSetupState, evalNat, Function.update]

private theorem prepareInsert_eval (input : RAMInput) (s : Store) :
    Queue.evalAtoms input prepareInsert s = preparedInsert s := by
  ext a <;> simp [Queue.evalAtoms, prepareInsert, Atom.eval, ramStep, Store.at, Store.ofRAM,
    preparedInsert, evalNat, Function.update]

private theorem insertIncrement_eval (input : RAMInput) (s : Store) :
    insertIncrement.eval input s = inserted s := by rfl

private theorem initializeEmpty_high_register {input : RAMInput} {s t : Store} {k r : ℕ}
    (h : Run input initializeEmpty s t k) (hr : 10 ≤ r) : t.nr r = s.nr r := by
  apply h.nat_frame r
  simp [initializeEmpty, Cmd.natWrites, atoms, initPrefix, initPair, Atom.natWrites]
  omega

private theorem updateLeaf_high_register {input : RAMInput} {s t : Store} {k r : ℕ}
    (h : Run input updateLeaf s t k) (hr : 10 ≤ r) : t.nr r = s.nr r := by
  apply h.nat_frame r
  simp [updateLeaf, repairAncestors, repairBody, refreshNode, selectChild,
    Cmd.natWrites, atoms, writeLeaf, parentHop, loadChildren, storeLeft, storeRight, Atom.natWrites]
  omega

private theorem WinnerFrame.initFrame (W P B : ℕ) (s t : Store)
    (h : WinnerFrame W (2 * B) s t) : InitFrame W P B s t :=
  ⟨fun a ha _ => (h a ha).1, fun a ha => (h a ha).2⟩

private theorem insertBody_run (input : RAMInput) (B N W P R k : ℕ) (initial s : Store)
    (hB : 0 < B) (hN : N ≤ B) (hk : k < N)
    (hkeys : ∀ i < N, R + i < W ∨ W + 2 * B ≤ R + i)
    (h : BuildInv B N W P R initial k s) :
    ∃ out cost, Run input insertBody s out cost ∧ BuildInv B N W P R initial (k + 1) out ∧
      cost ≤ 19 * Nat.clog 2 (2 * B) + 11 := by
  let mid := preparedInsert s
  have hmW : mid.nr 1 = W := by simp [mid, preparedInsert, h.hW]
  have hmP : mid.nr 2 = P := by simp [mid, preparedInsert, h.hP]
  have hmzero : mid.nr 3 = 0 := by simp [mid, preparedInsert, h.hzero]
  have hmone : mid.nr 4 = 1 := by simp [mid, preparedInsert, h.hone]
  have hmnode : mid.nr 0 = B + k := by simp [mid, preparedInsert, h.hB, h.hk]
  have hmtoken : mid.nr 10 = k + 1 := by simp [mid, preparedInsert, h.hk, h.hone]
  have hmkey : mid.rr 2 = initial.rm (R + k) := by
    simpa [mid, preparedInsert, h.hR, h.hk] using h.frame.2 (R + k) (hkeys k hk)
  have hmparent : ParentLayout (2 * B) mid := by
    refine ⟨by rw [hmnode]; omega, ?_, hmzero, ?_⟩
    · rw [hmW, hmP]
      simpa only [h.hW, h.hP] using h.parents.2.1
    · intro u hu
      rw [hmP]
      exact (show s.nm (P + u) = u / 2 by simpa only [h.hP] using h.parents.2.2.2 u hu)
  have hmrep : Represents B (mid.nr 1) (prefixLeaf B (fun i => initial.rm (R + i)) k) mid := by
    rw [hmW]
    exact h.represents
  obtain ⟨out, updateCost, hupdate, hcost, hz, hheader, hparents, hrep, hframe⟩ :=
    updateLeaf_refines input B (prefixLeaf B (fun i => initial.rm (R + i)) k) mid hmparent hmone
      (by rw [hmnode]; omega) (by rw [hmnode]; omega) hmrep
  rw [hmW, hmnode, hmtoken, hmkey, prefixLeaf_succ] at hrep
  have houtW : out.nr 1 = W := (hheader 1 (by omega) (by omega)).trans hmW
  have houtP : out.nr 2 = P := (hheader 2 (by omega) (by omega)).trans hmP
  have houtzero : out.nr 3 = 0 := (hheader 3 (by omega) (by omega)).trans hmzero
  have houtone : out.nr 4 = 1 := (hheader 4 (by omega) (by omega)).trans hmone
  have houtB : out.nr 11 = B := by
    rw [updateLeaf_high_register hupdate (by omega)]
    simp [mid, preparedInsert, h.hB]
  have houtN : out.nr 12 = N := by
    rw [updateLeaf_high_register hupdate (by omega)]
    simp [mid, preparedInsert, h.hN]
  have houtR : out.nr 13 = R := by
    rw [updateLeaf_high_register hupdate (by omega)]
    simp [mid, preparedInsert, h.hR]
  have houtk : out.nr 14 = k := by
    rw [updateLeaf_high_register hupdate (by omega)]
    simp [mid, preparedInsert, h.hk]
  have houtframe : InitFrame W P B initial out := by
    rw [hmW] at hframe
    exact InitFrame.trans W P B initial mid out h.frame
      (WinnerFrame.initFrame W P B mid out hframe)
  have hprep := Queue.run_atoms input prepareInsert s
  rw [prepareInsert_eval] at hprep
  have hinc := Run.atom insertIncrement out (input := input)
  rw [insertIncrement_eval] at hinc
  refine ⟨inserted out, 4 + (updateCost + 1), Run.seq hprep (Run.seq hupdate hinc), ?_, by omega⟩
  refine ⟨by simp [inserted, houtW], by simp [inserted, houtP],
    by simp [inserted, houtzero], by simp [inserted, houtone],
    by simp [inserted, houtB], by simp [inserted, houtN], by simp [inserted, houtR],
    by simp [inserted, houtk, houtone], ?_, hrep, houtframe⟩
  simpa [ParentLayout, inserted] using hparents

private theorem buildQueue_run (input : RAMInput) (B N W P R : ℕ) (s : Store)
    (hB : 0 < B) (hN : N ≤ B) (hspace : W + 2 * B ≤ P)
    (hkeys : ∀ i < N, R + i < W ∨ W + 2 * B ≤ R + i)
    (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1)
    (h11 : s.nr 11 = B) (h12 : s.nr 12 = N) (h13 : s.nr 13 = R) :
    ∃ out cost, Run input buildQueue s out cost ∧ BuildInv B N W P R s N out ∧
      cost ≤ 15 * B + (19 * Nat.clog 2 (2 * B) + 13) * N + 3 := by
  let start := buildSetupState s
  obtain ⟨ready, initCost, hinit, hinitCost, hinv, hrep, hframe⟩ :=
    initializeEmpty_represents input W P B start hB hspace
      (by simp [start, buildSetupState, h11, h4])
      (by simp [start, buildSetupState, h1]) (by simp [start, buildSetupState, h2])
      (by simp [start, buildSetupState, h3]) (by simp [start, buildSetupState, h4])
  have hparents : ParentLayout (2 * B) ready := by
    refine ⟨by rw [hinv.1]; omega, ?_, hinv.2.2.2.1, ?_⟩
    · simpa only [hinv.2.1, hinv.2.2.1] using hspace
    · intro u hu
      rw [hinv.2.2.1]
      exact (hinv.2.2.2.2.2.2 u hu (by omega)).2.2
  have hready : BuildInv B N W P R s 0 ready := by
    refine ⟨hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2.1,
      ?_, ?_, ?_, ?_, hparents, ?_, hframe⟩
    · rw [initializeEmpty_high_register hinit (by omega)]
      simp [start, buildSetupState, h11]
    · rw [initializeEmpty_high_register hinit (by omega)]
      simp [start, buildSetupState, h12]
    · rw [initializeEmpty_high_register hinit (by omega)]
      simp [start, buildSetupState, h13]
    · rw [initializeEmpty_high_register hinit (by omega)]
      simp [start, buildSetupState]
    · simpa only [prefixLeaf_zero] using hrep
  obtain ⟨out, loopCost, hloop, hout, hloopCost⟩ := run_bounded_loop input
    (Guard.nat .lt 14 12) insertBody N (19 * Nat.clog 2 (2 * B) + 11)
    (BuildInv B N W P R s)
    (by intro k t hk ht; simp [Guard.eval, natTest, ht.hk, ht.hN])
    (fun k t hk ht => insertBody_run input B N W P R k s t hB hN hk hkeys ht)
    0 ready (by omega) hready
  have hsetup := Queue.run_atoms input buildSetup s
  rw [buildSetup_eval] at hsetup
  refine ⟨out, 2 + (initCost + loopCost), Run.seq hsetup (Run.seq hinit hloop), hout, ?_⟩
  simp only [Nat.sub_zero] at hloopCost
  have hbound : 19 * Nat.clog 2 (2 * B) + 11 + 2 = 19 * Nat.clog 2 (2 * B) + 13 := by omega
  rw [hbound] at hloopCost
  omega

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

private theorem activeLeaf_initial (xs : List ℕ) (key : ℕ → ℝ) (B : ℕ) :
    activeLeaf xs xs key B =
      prefixLeaf B (fun k => key (slotVertex xs k)) xs.length := by
  funext node
  by_cases hn : B ≤ node ∧ node < B + xs.length
  · have hk : node-B < xs.length := by omega
    have hv : slotVertex xs (node-B) ∈ xs := by
      simp only [slotVertex,List.getElem?_eq_getElem hk,Option.getD_some]
      exact List.getElem_mem hk
    simp only [activeLeaf,prefixLeaf,if_pos hn]
    change (⟨if slotVertex xs (node-B) ∈ xs then node-B+1 else 0,
      key (slotVertex xs (node-B))⟩ : Record) = _
    rw [if_pos hv]
  · simp [activeLeaf,prefixLeaf,hn]

private theorem prefixLeaf_records (B N : ℕ) (key : ℕ → ℝ) (hN : N ≤ B) :
    leafRecords (prefixLeaf B key N) B B =
      (List.range N).map (fun k => (⟨k+1,key k⟩ : Record)) := by
  have hleaf : activeLeaf (List.range N) (List.range N) key B = prefixLeaf B key N := by
    funext node
    by_cases hn : B ≤ node ∧ node < B+N
    · have hk : node-B<N := by omega
      simp [activeLeaf,prefixLeaf,hn,List.getElem?_range,hk]
    · simp [activeLeaf,prefixLeaf,hn]
  rw [←hleaf,activeLeaf_records (List.range N) (List.range N) key B
    (List.nodup_range (n := N)) (List.Sublist.refl _) (by simpa using hN)]
  apply List.map_congr_left
  intro k hk
  have hi : (List.range N).idxOf k=k := by
    have hkl : k<N := List.mem_range.mp hk
    have hidx := slotVertex_idxOf (List.range N) List.nodup_range k (by simpa using hkl)
    simpa only [slotVertex,List.getElem?_range hkl,Option.getD_some] using hidx
  simp [vertexRecord,hi]

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem seed_prefixLeaf (xs : List ℕ) (A R source off B : ℕ) (top : ℝ) (s : Store)
    (h : TreeSeedInv xs A R source off top xs.length s) :
    Queue.prefixLeaf B (fun k => s.rm (R+k)) xs.length =
      Queue.activeLeaf xs xs (fun v => if v=source then 0 else top) B := by
  rw [Queue.activeLeaf_initial]
  funext node
  by_cases hn : B ≤ node ∧ node < B+xs.length
  · have hk : node-B < xs.length := by omega
    have hv : xs[node-B]? = some xs[node-B] := List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩
    have hh := h.key (node-B) xs[node-B] hv hk
    simp [Queue.prefixLeaf, hn, hh, Queue.slotVertex, hv]
  · simp [Queue.prefixLeaf, hn]

private theorem treeInitializeQueue_run (input : RAMInput) (xs : List ℕ)
    (A R source off B W P : ℕ) (top : ℝ) (s : Store)
    (hB : 0 < B) (hfit : xs.length ≤ B) (hWP : W+2*B ≤ P) (hPR : P+2*B ≤ R)
    (hAW : A+xs.length ≤ W)
    (hW : s.nr 1 = W) (hP : s.nr 2 = P) (hz : s.nr 3 = 0) (hone : s.nr 4 = 1)
    (hcapacity : s.nr 11 = B) (hlen : s.nr 12 = xs.length)
    (hA : s.nr 171 = A) (hR : s.nr 13 = R) (hsource : s.nr 123 = source)
    (hoff : s.nr 173 = off) (htop : s.rr 170 = top)
    (harray : ∀ j v, xs[j]? = some v → s.nm (A+j) = v)
    (hspace : ∀ v ∈ xs, targetAddress v + off < A) :
    ∃ out steps, Run input treeInitializeQueue s out steps ∧
      steps ≤ 15*B + (19*Nat.clog 2 (2*B)+31)*xs.length + 5 ∧
      TreeSeedInv xs A R source off top xs.length out ∧
      Queue.ParentLayout (2*B) out ∧
      Queue.Represents B W
        (Queue.activeLeaf xs xs (fun v => if v=source then 0 else top) B) out ∧
      (∀ a, (∀ v ∈ xs, a ≠ targetAddress v + off) →
        (a < R ∨ R+xs.length ≤ a) →
        (a < W ∨ W+2*B ≤ a) → (a < P ∨ P+2*B ≤ a) →
        out.nm a = s.nm a ∧ out.rm a = s.rm a) := by
  obtain ⟨seed, ns, hseed, hns, hs, hsf⟩ := treeSeed_framed input xs A R source off top s
    hlen hA hR hsource hoff hz hone htop harray hspace
  have hn (r : ℕ) (hr : r ∉ ({0,10,172,174,175,176,177,178} : Finset ℕ)) :
      seed.nr r = s.nr r := treeSeed_register_frame hseed hr
  obtain ⟨out, nq, hqueue, hq, hnq⟩ := Queue.buildQueue_run input B xs.length W P R seed
    hB hfit hWP (by intro k hk; exact Or.inr (by omega))
    ((hn 1 (by decide)).trans hW) ((hn 2 (by decide)).trans hP)
    hs.zero_reg hs.one_reg ((hn 11 (by decide)).trans hcapacity) hs.length_reg hs.key_reg
  have hheap := hq.represents
  rw [seed_prefixLeaf xs A R source off B top seed hs] at hheap
  have hout : TreeSeedInv xs A R source off top xs.length out := by
    refine ⟨le_rfl, ?_, hq.hN, ?_, hq.hR, ?_, ?_, hq.hzero, hq.hone, ?_, ?_, ?_, ?_⟩
    · exact (hqueue.nat_frame 172 (by decide)).trans hs.counter
    · exact (hqueue.nat_frame 171 (by decide)).trans hs.array_reg
    · exact (hqueue.nat_frame 123 (by decide)).trans hs.source_reg
    · exact (hqueue.nat_frame 173 (by decide)).trans hs.offset_reg
    · exact (hqueue.real_frame 170 (by decide)).trans hs.top_reg
    · intro k v hv
      have hk := (List.getElem?_eq_some_iff.mp hv).choose
      rw [hq.frame.1 (A+k) (Or.inl (by omega)) (Or.inl (by omega))]
      exact hs.array k v hv
    · intro k v hv hk
      rw [hq.frame.2 (R+k) (Or.inr (by omega))]
      exact hs.key k v hv hk
    · intro k v hv hk
      have hvA := hspace v (List.mem_of_getElem? hv)
      rw [hq.frame.1 (targetAddress v+off) (Or.inl (by omega)) (Or.inl (by omega))]
      exact hs.parent k v hv hk
  refine ⟨out, ns+nq, Run.seq hseed hqueue, ?_, hout, hq.parents, hheap, ?_⟩
  · nlinarith
  · intro a hparent hR hW hP
    have hf := hsf a hparent hR
    exact ⟨(hq.frame.1 a hW hP).trans hf.1, (hq.frame.2 a hW).trans hf.2⟩

private theorem activeProbe_eval (input : RAMInput) (s : Store) :
    evalAtoms input activeProbe s = activeProbed s := by
  ext a <;> simp [evalAtoms, activeProbe, activeProbed, Atom.eval, Store.at, Store.ofRAM,
    ramStep, evalNat, Function.update]

private theorem activeAppend_eval (input : RAMInput) (s : Store) :
    evalAtoms input activeAppend s = activeAppended s := by
  ext a <;> simp [evalAtoms, activeAppend, activeAppended, Atom.eval, Store.at, Store.ofRAM,
    ramStep, evalNat, Function.update]

private theorem activeInsert_run (input : RAMInput) (s : Store) (hz : s.nr 125 = 0) :
    ∃ steps ≤ 8, Run input activeInsert s (activeResult s) steps := by
  have hp := run_atoms input activeProbe s
  rw [activeProbe_eval] at hp
  by_cases hm : s.nm (s.nr 141 + s.nr 140) = 0
  · have ha := run_atoms input activeAppend (activeProbed s)
    rw [activeAppend_eval] at ha
    have hb := Run.branchTrue (g := Guard.nat .eq 145 125) (b := Cmd.skip)
      (by simp [Guard.eval, natTest, activeProbed, hz, hm]) ha
    refine ⟨8, le_rfl, ?_⟩
    simpa [activeInsert, activeResult, hm, activeProbe, activeAppend] using Run.seq hp hb
  · have hb := Run.branchFalse (input := input) (g := Guard.nat .eq 145 125) (a := Cmd.atoms activeAppend)
      (by simp [Guard.eval, natTest, activeProbed, hz, hm]) (Run.skip (activeProbed s))
    refine ⟨3, by omega, ?_⟩
    simpa [activeInsert, activeResult, hm, activeProbe] using Run.seq hp hb

private theorem activeResult_frame_register (s : Store) (r : ℕ)
    (h143 : r ≠ 143) (h144 : r ≠ 144) (h145 : r ≠ 145) (h146 : r ≠ 146) :
    (activeResult s).nr r = s.nr r := by
  unfold activeResult
  split <;> simp [activeAppended, activeProbed, h143, h144, h145, h146]

private theorem activeResult_frame_memory (s : Store) (a : ℕ)
    (hflag : a ≠ s.nr 141 + s.nr 140) (hlist : a ≠ s.nr 142 + s.nr 143) :
    (activeResult s).nm a = s.nm a := by
  unfold activeResult
  split <;> simp [activeAppended, activeProbed, hflag, hlist]

private theorem activeResult_frame_reals (s : Store) :
    (activeResult s).rr = s.rr ∧ (activeResult s).rm = s.rm := by
  unfold activeResult
  split <;> exact ⟨rfl, rfl⟩

private theorem activeResult_present (s : Store) (hm : s.nm (s.nr 141 + s.nr 140) ≠ 0) :
    (activeResult s).nm = s.nm ∧ (activeResult s).nr 143 = s.nr 143 := by
  simp [activeResult, hm, activeProbed]

private theorem activeResult_absent (s : Store) (hm : s.nm (s.nr 141 + s.nr 140) = 0)
    (hone : s.nr 126 = 1)
    (hsep : s.nr 141 + s.nr 140 ≠ s.nr 142 + s.nr 143) :
    (activeResult s).nr 143 = s.nr 143 + 1 ∧
    (activeResult s).nm (s.nr 141 + s.nr 140) = s.nr 143 + 1 ∧
    (activeResult s).nm (s.nr 142 + s.nr 143) = s.nr 140 := by
  simp [activeResult, hm, activeAppended, activeProbed, hone, Ne.symm hsep]

private theorem active_regions_disjoint (base n v count : ℕ) (hv : v < n) :
    base + v ≠ (base + 2 * n) + count := by omega

private theorem stableInsert_mem (xs : List ℕ) (v x : ℕ) :
    x ∈ stableInsert xs v ↔ x ∈ xs ∨ x = v := by
  unfold stableInsert
  split <;> simp_all

private theorem stableInsert_nodup (xs : List ℕ) (v : ℕ) (hx : xs.Nodup) :
    (stableInsert xs v).Nodup := by
  unfold stableInsert
  split
  · exact hx
  · rename_i hv
    simp only [List.nodup_append, hx, List.nodup_singleton, true_and, List.mem_singleton]
    intro a ha b hb he
    subst b
    subst a
    exact hv ha

private theorem standalone_Mission_RAMActiveList__stableFold_loop (xs acc : List ℕ) :
    xs.foldl stableInsert acc.reverse = List.eraseDupsBy.loop (· == ·) xs acc := by
  induction xs generalizing acc with
  | nil => simp [List.eraseDupsBy.loop]
  | cons v xs ih =>
      simp only [List.foldl_cons, List.eraseDupsBy.loop]
      by_cases hv : v ∈ acc
      · have ha : acc.any (fun x => v == x) = true := by
          apply List.any_eq_true.mpr
          exact ⟨v, hv, by simp⟩
        simp only [ha, Bool.true_eq, ↓reduceIte]
        simpa [stableInsert, hv] using ih acc
      · have ha : acc.any (fun x => v == x) = false := by
          apply Bool.eq_false_iff.mpr
          intro hh
          obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
          have : v = x := by simpa using he
          exact hv (this.symm ▸ hx)
        simp only [ha, Bool.false_eq_true, ↓reduceIte]
        simpa [stableInsert, hv] using ih (v :: acc)

private theorem stableFold_eq_eraseDups (xs : List ℕ) :
    xs.foldl stableInsert [] = xs.eraseDups := by
  exact standalone_Mission_RAMActiveList__stableFold_loop xs []

private theorem activeVertices_eq_stableFold (I : Instance) :
    activeVertices I = (I.source :: I.graph.edges.flatMap (fun e => [e.1,e.2])).foldl
      stableInsert [] := (stableFold_eq_eraseDups _).symm

private theorem ActiveRep.flag_zero_iff {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v < n) :
    s.nm (base + v) = 0 ↔ v ∉ xs := by
  constructor
  · intro hz hm
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
    have hi := h.index k v hk
    omega
  · exact h.absent v hv

private theorem ActiveRep.empty (n base array : ℕ) (s : Store)
    (hb : s.nr 141 = base) (ha : s.nr 142 = array) (hc : s.nr 143 = 0)
    (hsep : base + n ≤ array) (hz : ∀ v < n, s.nm (base + v) = 0) :
    ActiveRep n base array [] s := by
  refine ⟨by simp, by simp, hb, ha, hc, hsep, ?_, ?_, ?_⟩
  · intro v hv _; exact hz v hv
  · intro k v h; simp at h
  · intro k v h; simp at h

private theorem ActiveRep.insert {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (hv : s.nr 140 < n) (hone : s.nr 126 = 1) :
    ActiveRep n base array (stableInsert xs (s.nr 140)) (activeResult s) := by
  have hbase : (activeResult s).nr 141 = base :=
    (activeResult_frame_register s 141 (by decide) (by decide) (by decide) (by decide)).trans h.base_reg
  have harray : (activeResult s).nr 142 = array :=
    (activeResult_frame_register s 142 (by decide) (by decide) (by decide) (by decide)).trans h.array_reg
  by_cases hm : s.nr 140 ∈ xs
  · have hz : s.nm (s.nr 141 + s.nr 140) ≠ 0 := by
      rw [h.base_reg]
      exact fun hz => (h.flag_zero_iff _ hv).mp hz hm
    have hp := activeResult_present s hz
    rw [stableInsert, if_pos hm]
    refine ⟨h.nodup, h.valid, hbase, harray, hp.2.trans h.count_reg, h.separation, ?_, ?_, ?_⟩
    · intro v hv hn; rw [hp.1]; exact h.absent v hv hn
    · intro k v hk; rw [hp.1]; exact h.index k v hk
    · intro k v hk; rw [hp.1]; exact h.value k v hk
  · have hz : s.nm (s.nr 141 + s.nr 140) = 0 := by
      rw [h.base_reg]; exact h.absent _ hv hm
    have hsep : s.nr 141 + s.nr 140 ≠ s.nr 142 + s.nr 143 := by
      rw [h.base_reg, h.array_reg]; have := h.separation; omega
    have ha := activeResult_absent s hz hone hsep
    rw [stableInsert, if_neg hm]
    refine ⟨(by simpa [stableInsert, hm] using stableInsert_nodup xs (s.nr 140) h.nodup),
      ?_, hbase, harray, ?_, h.separation, ?_, ?_, ?_⟩
    · intro v hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact h.valid v hmem
      · have he : v = s.nr 140 := by simpa using hmem
        simpa [he] using hv
    · simpa [h.count_reg] using ha.1
    · intro v hv' hn
      have hvold : v ∉ xs := by intro hh; exact hn (List.mem_append_left _ hh)
      have hne : v ≠ s.nr 140 := by intro he; subst v; simp at hn
      rw [activeResult_frame_memory]
      · exact h.absent v hv' hvold
      · rw [h.base_reg]; omega
      · rw [h.array_reg]; have := h.separation; omega
    · intro k v hk
      by_cases hkold : k < xs.length
      · rw [List.getElem?_append_left hkold] at hk
        have hvold : v ∈ xs := List.mem_of_getElem? hk
        have hne : v ≠ s.nr 140 := by intro he; subst v; exact hm hvold
        have hvn := h.valid v hvold
        rw [activeResult_frame_memory]
        · exact h.index k v hk
        · rw [h.base_reg]; omega
        · rw [h.array_reg]; have := h.separation; omega
      · rw [List.getElem?_append_right (by omega)] at hk
        have hkv : k = xs.length ∧ v = s.nr 140 := by
          obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hk
          simp only [List.length_singleton] at hbound
          have he : k - xs.length = 0 := by omega
          simp [he] at hk
          exact ⟨by omega, hk.symm⟩
        rcases hkv with ⟨rfl, rfl⟩
        simpa [h.base_reg, h.count_reg] using ha.2.1
    · intro k v hk
      by_cases hkold : k < xs.length
      · rw [List.getElem?_append_left hkold] at hk
        rw [activeResult_frame_memory]
        · exact h.value k v hk
        · rw [h.base_reg]; have := h.separation; omega
        · rw [h.array_reg, h.count_reg]; omega
      · rw [List.getElem?_append_right (by omega)] at hk
        have hkv : k = xs.length ∧ v = s.nr 140 := by
          obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hk
          simp only [List.length_singleton] at hbound
          have he : k - xs.length = 0 := by omega
          simp [he] at hk
          exact ⟨by omega, hk.symm⟩
        rcases hkv with ⟨rfl, rfl⟩
        simpa [h.array_reg, h.count_reg] using ha.2.2

private theorem ActiveRep.indexOf {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs) :
    s.nm (base + v) = xs.idxOf v + 1 :=
  h.index (xs.idxOf v) v (List.getElem?_idxOf hv)

private theorem ActiveRep.index_bounds {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs) :
    0 < s.nm (base + v) ∧ s.nm (base + v) ≤ xs.length := by
  rw [h.indexOf v hv]
  have hi := List.idxOf_lt_length_of_mem hv
  omega

private theorem ActiveRep.inverse {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (v : ℕ) (hv : v ∈ xs) :
    s.nm (array + (s.nm (base + v) - 1)) = v := by
  rw [h.indexOf v hv, Nat.add_sub_cancel]
  exact h.value (xs.idxOf v) v (List.getElem?_idxOf hv)

private theorem ActiveRep.vertex_at {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (k : ℕ) (hk : k < xs.length) :
    s.nm (array + k) = xs[k]?.getD 0 := by
  have he : xs[k]? = some xs[k] := List.getElem?_eq_some_iff.mpr ⟨hk, rfl⟩
  simpa only [he, Option.getD_some] using h.value k xs[k] he

private theorem ActiveRep.length_le {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) : xs.length ≤ n := by
  have hsub : xs ⊆ List.range n := by
    intro v hv; exact List.mem_range.mpr (h.valid v hv)
  simpa using h.nodup.length_le_of_subset hsub

private theorem ActiveRep.congr {n base array : ℕ} {xs : List ℕ} {s t : Store}
    (h : ActiveRep n base array xs s)
    (hb : t.nr 141 = s.nr 141) (ha : t.nr 142 = s.nr 142) (hc : t.nr 143 = s.nr 143)
    (hmap : ∀ v < n, t.nm (base + v) = s.nm (base + v))
    (harray : ∀ k < xs.length, t.nm (array + k) = s.nm (array + k)) :
    ActiveRep n base array xs t := by
  refine ⟨h.nodup, h.valid, hb.trans h.base_reg, ha.trans h.array_reg,
    hc.trans h.count_reg, h.separation, ?_, ?_, ?_⟩
  · intro v hv hn; rw [hmap v hv]; exact h.absent v hv hn
  · intro k v hk
    rw [hmap v (h.valid v (List.mem_of_getElem? hk))]
    exact h.index k v hk
  · intro k v hk
    obtain ⟨hkl, _⟩ := List.getElem?_eq_some_iff.mp hk
    rw [harray k hkl]
    exact h.value k v hk

private theorem TreeMode.weight_nonneg (mode : TreeMode) (I : Instance) (u v : ℕ) :
    0 ≤ mode.weight I u v := (mode.resource I u v).coe_nonneg

private theorem TreeMode.top_pos (mode : TreeMode) (I : Instance) : 0 < mode.top I := by
  have h := edgeWeightSum_nonneg I (mode.resource I)
  unfold TreeMode.top
  positivity

private theorem TreeMode.offset_lt_four (mode : TreeMode) : mode.offset < 4 := by
  cases mode <;> decide

private theorem TreeAllocation.capacity_pos {I : Instance} (E : TreeAllocation I) : 0 < E.B := by
  rw [E.capacity]; positivity

private theorem TreeAllocation.target_lt_map {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (v : ℕ) (hv : v < I.graph.n) : targetAddress v + mode.offset < E.map := by
  have hm := E.target_map
  cases mode <;> simp only [TreeMode.offset,targetAddress] <;> omega

private theorem TreeAllocation.map_le_array {I : Instance} (E : TreeAllocation I) : E.map ≤ E.array := by
  have h1 := E.map_heads; have h2 := E.heads_array; omega

private theorem TreeAllocation.array_end_le_winner {I : Instance} (E : TreeAllocation I) :
    E.array + I.graph.n ≤ E.W := by
  have h1 := E.array_links; have h2 := E.links_winner; omega

private theorem TreeAllocation.target_lt_winner {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (v : ℕ) (hv : v < I.graph.n) : targetAddress v + mode.offset < E.W := by
  have h := E.target_lt_map mode v hv
  have h1 := E.map_le_array; have h2 := E.array_end_le_winner; omega

private theorem TreeRegisters.transfer {I : Instance} {B W P R map array heads links off mode : ℕ}
    {top : ℝ} {s t : Store} (h : TreeRegisters I B W P R map array heads links off mode top s)
    (hn : ∀ r ∈ treeNatConstants, t.nr r = s.nr r) (hr : t.rr 170 = s.rr 170) :
    TreeRegisters I B W P R map array heads links off mode top t := by
  exact ⟨(hn 1 (by decide)).trans h.winner,
    (hn 2 (by decide)).trans h.parent,
    (hn 3 (by decide)).trans h.zero,
    (hn 4 (by decide)).trans h.one,
    (hn 11 (by decide)).trans h.capacity,
    (hn 12 (by decide)).trans h.count,
    (hn 13 (by decide)).trans h.keys,
    (hn 123 (by decide)).trans h.source,
    (hn 137 (by decide)).trans h.heads,
    (hn 139 (by decide)).trans h.links,
    (hn 141 (by decide)).trans h.map,
    (hn 142 (by decide)).trans h.array,
    (hn 143 (by decide)).trans h.active_count,
    (hn 170 (by decide)).trans h.saved_capacity,
    (hn 171 (by decide)).trans h.saved_array,
    (hn 173 (by decide)).trans h.offset,
    (hn 264 (by decide)).trans h.mode,
    hr.trans h.sentinel⟩

private theorem TreeRegisters.after_run {I : Instance} {B W P R map array heads links off mode : ℕ}
    {top : ℝ} {s t : Store} (h : TreeRegisters I B W P R map array heads links off mode top s)
    {input : RAMInput} {cmd : Cmd} {steps : ℕ} (hrun : Run input cmd s t steps)
    (hn : Disjoint treeNatConstants cmd.natWrites) (hr : 170 ∉ cmd.realWrites) :
    TreeRegisters I B W P R map array heads links off mode top t :=
  h.transfer (fun r hm => hrun.nat_frame r (fun hw => Finset.disjoint_left.mp hn hm hw))
    (hrun.real_frame 170 hr)

private theorem treeInitializeQueue_rep {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s : Store) (hr : E.Registers mode s)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s) :
    ∃ out steps, Run input treeInitializeQueue s out steps ∧
      E.Registers mode out ∧ E.Memory mode (treeInitial I) out ∧
      steps ≤ 15*E.B + (19*Nat.clog 2 (2*E.B)+31)*(activeVertices I).length + 5 ∧
      (∀ a, (∀ v ∈ activeVertices I, a ≠ targetAddress v + mode.offset) →
        (a < E.R ∨ E.R+(activeVertices I).length ≤ a) →
        (a < E.W ∨ E.W+2*E.B ≤ a) → (a < E.P ∨ E.P+2*E.B ≤ a) →
        out.nm a = s.nm a ∧ out.rm a = s.rm a) := by
  have hlen := activeVertices_length_le_vertices I
  have hmap := E.map_le_array
  have hAW := E.array_end_le_winner
  have hWP := E.winner_parent
  have hPR := E.parent_temp
  obtain ⟨out, steps, hrun, hcost, hs, hp, hheap, hf⟩ := treeInitializeQueue_run input
    (activeVertices I) E.array E.R I.source mode.offset E.B E.W E.P (mode.top I) s
    E.capacity_pos E.fit E.winner_parent E.parent_temp (by omega)
    hr.winner hr.parent hr.zero hr.one hr.capacity hr.count hr.saved_array hr.keys
    hr.source hr.offset hr.sentinel ha.value
    (by
      intro v hv
      exact (E.target_lt_map mode v (activeVertices_valid I v hv)).trans_le E.map_le_array)
  have hrout : E.Registers mode out := hr.after_run hrun (by decide) (by decide)
  have hmem (a : ℕ) (hlo : E.map ≤ a) (hhi : a < E.W) : out.nm a = s.nm a := by
    apply (hf a ?_ (Or.inl (by omega)) (Or.inl hhi) (Or.inl (by omega))).1
    intro v hv
    have htarget := E.target_lt_map mode v (activeVertices_valid I v hv)
    omega
  have haout : ActiveRep I.graph.n E.map E.array (activeVertices I) out := by
    apply ha.congr (hrun.nat_frame 141 (by decide)) (hrun.nat_frame 142 (by decide))
      (hrun.nat_frame 143 (by decide))
    · intro v hv
      apply hmem (E.map+v) (by omega)
      have hm := E.map_heads
      have hh := E.heads_array
      omega
    · intro k hk
      exact hmem (E.array+k) (by omega) (by omega)
  have hkeys : (fun v => if v = I.source then (0:ℝ) else mode.top I) =
      sentinelKey (mode.top I) (treeInitial I).tree := by
    funext v
    by_cases hv : v = I.source <;> simp [sentinelKey, treeInitial, hv]
  have hmout : E.Memory mode (treeInitial I) out := by
    refine ⟨haout, List.Sublist.refl _, ?_, ?_, ?_, ?_⟩
    · change Queue.Represents E.B E.W
        (Queue.activeLeaf (activeVertices I) (activeVertices I)
          (sentinelKey (mode.top I) (treeInitial I).tree) E.B) out
      rw [←hkeys]
      exact hheap
    · intro node hnode
      simpa only [hrout.parent] using hp.2.2.2 node hnode
    · intro v hv
      have hi := List.getElem?_idxOf hv
      have hk := List.idxOf_lt_length_of_mem hv
      simpa [treeInitial] using hs.parent _ v hi hk
    · intro v hv hn
      exact False.elim (hn hv)
  exact ⟨out, steps, hrun, hrout, hmout, hcost, hf⟩

private theorem treeExtractAtoms_eval (input : RAMInput) (s : Store) :
    evalAtoms input treeExtractAtoms s = treeExtractPrepared s := by
  ext a <;> simp [evalAtoms, treeExtractAtoms, treeExtractPrepared, Atom.eval,
    Store.at, Store.ofRAM, ramStep, evalNat, Function.update]

private theorem treeExtractPrepared_values (s : Store) (hone : s.nr 4 = 1) :
    (treeExtractPrepared s).nr 0 = s.nr 170 + (s.nm (s.nr 1 + 1) - 1) ∧
    (treeExtractPrepared s).nr 10 = 0 ∧
    (treeExtractPrepared s).nr 260 = s.nm (s.nr 1 + 1) ∧
    (treeExtractPrepared s).nr 261 = s.nm (s.nr 1 + 1) - 1 ∧
    (treeExtractPrepared s).nr 262 = s.nm (s.nr 171 + (s.nm (s.nr 1 + 1) - 1)) ∧
    (treeExtractPrepared s).rr 260 = s.rm (s.nr 1 + 1) ∧
    (treeExtractPrepared s).rr 2 = s.rm (s.nr 1 + 1) := by
  simp [treeExtractPrepared, hone]

private theorem treeExtractPrepared_header (s : Store) (r : ℕ) (hr : 0 < r) (hr' : r < 5) :
    (treeExtractPrepared s).nr r = s.nr r := by
  have h0 : r ≠ 0 := by omega
  have h7 : r ≠ 7 := by omega
  have h10 : r ≠ 10 := by omega
  have h260 : r ≠ 260 := by omega
  have h261 : r ≠ 261 := by omega
  have h262 : r ≠ 262 := by omega
  simp [treeExtractPrepared, h0, h7, h10, h260, h261, h262]

private theorem standalone_Mission_RAMTreeExtract__updateLeaf_nat_frame {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input Queue.updateLeaf s out steps) (hr : 11 ≤ r) : out.nr r = s.nr r := by
  apply h.nat_frame
  simp [Queue.updateLeaf, Queue.writeLeaf, Queue.parentHop, Queue.repairAncestors,
    Queue.repairBody, Queue.refreshNode, Queue.loadChildren, Queue.selectChild,
    Queue.storeLeft, Queue.storeRight, Queue.atoms, Cmd.natWrites, Atom.natWrites]
  omega

private theorem standalone_Mission_RAMTreeExtract__updateLeaf_real_frame {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input Queue.updateLeaf s out steps) (hr : 2 ≤ r) : out.rr r = s.rr r := by
  apply h.real_frame
  simp [Queue.updateLeaf, Queue.writeLeaf, Queue.parentHop, Queue.repairAncestors,
    Queue.repairBody, Queue.refreshNode, Queue.loadChildren, Queue.selectChild,
    Queue.storeLeft, Queue.storeRight, Queue.atoms, Cmd.realWrites, Atom.realWrites]
  omega

private theorem treeExtract_run (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeExtractPrepared s))
    (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 170 + (s.nm (s.nr 1 + 1) - 1))
    (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeExtractPrepared s))
    (hnew : truth (s.nr 170 + (s.nm (s.nr 1 + 1) - 1)) = ⟨0, s.rm (s.nr 1 + 1)⟩) :
    ∃ out steps, Run input treeExtract s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 15 ∧
      Queue.ParentLayout (2 * B) out ∧
      (∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v) ∧
      out.nr 260 = s.nm (s.nr 1 + 1) ∧
      out.nr 261 = s.nm (s.nr 1 + 1) - 1 ∧
      out.nr 262 = s.nm (s.nr 171 + (s.nm (s.nr 1 + 1) - 1)) ∧
      out.rr 260 = s.rm (s.nr 1 + 1) := by
  have hprep := run_atoms input treeExtractAtoms s
  rw [treeExtractAtoms_eval] at hprep
  obtain ⟨out, queueSteps, hqueue, hcost, _, _, hpout, hrecords⟩ :=
    Queue.updateLeaf_correct input B truth (treeExtractPrepared s) hp
      (by simpa only [treeExtractPrepared_header s 4 (by decide) (by decide)] using hone)
      (by simpa [treeExtractPrepared, hone] using hpositive) hc hr
      (by simpa [treeExtractPrepared, hone] using hnew)
  refine ⟨out, 9 + queueSteps, Run.seq hprep hqueue, by omega, hpout, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [treeExtractPrepared_header s 1 (by decide) (by decide)] using hrecords
  · rw [standalone_Mission_RAMTreeExtract__updateLeaf_nat_frame hqueue (by decide)]
    simp [treeExtractPrepared, hone]
  · rw [standalone_Mission_RAMTreeExtract__updateLeaf_nat_frame hqueue (by decide)]
    simp [treeExtractPrepared, hone]
  · rw [standalone_Mission_RAMTreeExtract__updateLeaf_nat_frame hqueue (by decide)]
    simp [treeExtractPrepared, hone]
  · rw [standalone_Mission_RAMTreeExtract__updateLeaf_real_frame hqueue (by decide)]
    simp [treeExtractPrepared, hone]

private theorem treeRecordDistance_run (input : RAMInput) (s : Store) :
    Run input (.atoms treeRecordDistanceAtoms) s (treeRecordedDistance s) 6 := by
  have he : evalAtoms input treeRecordDistanceAtoms s = treeRecordedDistance s := by
    ext a <;> by_cases ha : a = 275 <;> simp [ha,evalAtoms, treeRecordDistanceAtoms, treeRecordedDistance,
      Atom.eval, Store.at, Store.ofRAM, ramStep, evalNat, targetAddress, Function.update,
      show ∀ n : ℕ, n + n + (n + n) = 4 * n by omega]
  have h := run_atoms input treeRecordDistanceAtoms s
  rw [he] at h
  exact h

private theorem treeRecordedDistance_value (s : Store) :
    (treeRecordedDistance s).rm (targetAddress (s.nr 262) + s.nr 173) = s.rr 260 := by
  simp [treeRecordedDistance]

private theorem treeRecordedDistance_frame (s : Store) (a : ℕ)
    (ha : a ≠ targetAddress (s.nr 262) + s.nr 173) :
    (treeRecordedDistance s).nm = s.nm ∧ (treeRecordedDistance s).rm a = s.rm a := by
  simp [treeRecordedDistance, ha]

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem encodeInput_edge_left (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e) :
    (encodeInput I ε).naturals (3+2*k) = e.1 := by
  have h0 : 3+2*k ≠ 0 := by omega
  have h1 : 3+2*k ≠ 1 := by omega
  have h2 : 3+2*k ≠ 2 := by omega
  have hd : (3+2*k-3)/2 = k := by omega
  have hm : (3+2*k-3)%2 = 0 := by omega
  simp [encodeInput,h0,h1,h2,hd,hm,he]

private theorem encodeInput_edge_right (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e) :
    (encodeInput I ε).naturals (3+2*k+1) = e.2 := by
  have h0 : 3+2*k+1 ≠ 0 := by omega
  have h1 : 3+2*k+1 ≠ 1 := by omega
  have h2 : 3+2*k+1 ≠ 2 := by omega
  have hd : (3+2*k+1-3)/2 = k := by omega
  have hm : (3+2*k+1-3)%2 = 1 := by omega
  simp only [encodeInput,h0,h1,h2,if_false,hd,hm,he]
  rfl

private theorem encodeInput_length (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e) :
    (encodeInput I ε).reals (2+2*k) = (I.length e.1 e.2 : ℝ) := by
  have h0 : 2+2*k ≠ 0 := by omega
  have h1 : 2+2*k ≠ 1 := by omega
  have hd : (2+2*k-2)/2 = k := by omega
  have hm : (2+2*k-2)%2 = 0 := by omega
  simp [encodeInput,h0,h1,hd,hm,he]

private theorem encodeInput_cost (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e) :
    (encodeInput I ε).reals (2+2*k+1) = (I.cost e.1 e.2 : ℝ) := by
  have h0 : 2+2*k+1 ≠ 0 := by omega
  have h1 : 2+2*k+1 ≠ 1 := by omega
  have hd : (2+2*k+1-2)/2 = k := by omega
  have hm : (2+2*k+1-2)%2 = 1 := by omega
  simp only [encodeInput,h0,h1,if_false,hd,hm,he]
  rfl

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem treeEdgeAtoms_eval (input : RAMInput) (s : Store) :
    evalAtoms input treeEdgeAtoms s = treeEdgeLoaded input s := by
  ext a <;> by_cases ha : a = 267 <;> simp [evalAtoms, treeEdgeAtoms, treeEdgeLoaded, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update, two_mul, ha]

private theorem treeEdgeLoaded_values (I : Instance) (ε : ℝ) (s : Store) (e : ℕ × ℕ)
    (he : I.graph.edges[s.nr 265]? = some e) (hone : s.nr 4 = 1) :
    (treeEdgeLoaded (encodeInput I ε) s).nr 268 = e.2 ∧
    (treeEdgeLoaded (encodeInput I ε) s).rr 261 = (I.length e.1 e.2 : ℝ) ∧
    (treeEdgeLoaded (encodeInput I ε) s).rr 262 = (I.cost e.1 e.2 : ℝ) := by
  have hv := encodeInput_edge_right I ε (s.nr 265) e he
  have hl := encodeInput_length I ε (s.nr 265) e he
  have hc := encodeInput_cost I ε (s.nr 265) e he
  simpa [treeEdgeLoaded, hone, show 4 + 2 * s.nr 265 = 3 + 2 * s.nr 265 + 1 by omega]
    using And.intro hv (And.intro hl hc)

private theorem treeTargetAtoms_eval (input : RAMInput) (s : Store) :
    evalAtoms input treeTargetAtoms s = treeTargetLoaded s := by
  ext a <;> simp [evalAtoms, treeTargetAtoms, treeTargetLoaded, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update]

private theorem treeDecreaseAtoms_eval (input : RAMInput) (s : Store) :
    evalAtoms input treeDecreaseAtoms s = treeDecreased s := by
  ext a <;> by_cases ha : a = 272 <;> simp [evalAtoms, treeDecreaseAtoms, treeDecreased, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update, targetAddress, ha,
    show ∀ n : ℕ, n + n + (n + n) = 4 * n by omega]

private theorem treeDecreased_header (s : Store) (r : ℕ) (hr : r < 11) :
    (treeDecreased s).nr r = s.nr r := by
  have h272 : r ≠ 272 := by omega
  have h273 : r ≠ 273 := by omega
  have h274 : r ≠ 274 := by omega
  simp [treeDecreased, h272, h273, h274]

private theorem treeApplyDecrease_run (input : RAMInput) (B : ℕ)
    (truth : ℕ → Queue.Record) (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeDecreased s)) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hc : Queue.Coherent (2 * B) truth)
    (hr : Queue.Ready (2 * B) truth (treeDecreased s))
    (hnew : truth (s.nr 0) = ⟨s.nr 10, s.rr 264⟩) :
    ∃ out steps, Run input treeApplyDecrease s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 14 ∧
      Queue.ParentLayout (2 * B) out ∧
      ∀ v < 2 * B, Queue.readRecord out (s.nr 1 + v) = truth v := by
  have hprep := run_atoms input treeDecreaseAtoms s
  rw [treeDecreaseAtoms_eval] at hprep
  obtain ⟨out, queueSteps, hqueue, hcost, _, _, hpout, hrecords⟩ :=
    Queue.updateLeaf_correct input B truth (treeDecreased s) hp
      (by simpa only [treeDecreased_header s 4 (by decide)] using hone)
      (by simpa only [treeDecreased_header s 0 (by decide)] using hpositive) hc hr
      (by simpa [treeDecreased] using hnew)
  refine ⟨out, 8 + queueSteps, Run.seq hprep hqueue, by omega, hpout, ?_⟩
  simpa only [treeDecreased_header s 1 (by decide)] using hrecords

private theorem adjacencyAtoms_eval (input : RAMInput) (s : Store) :
    evalAtoms input adjacencyAtoms s = adjacencyResult s := by
  ext a <;> simp [evalAtoms, adjacencyAtoms, adjacencyResult, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update]

private theorem adjacencyInsert_run (input : RAMInput) (s : Store) :
    Run input adjacencyInsert s (adjacencyResult s) 6 := by
  have h := run_atoms input adjacencyAtoms s
  rw [adjacencyAtoms_eval] at h
  exact h

private theorem adjacencyResult_head (s : Store) (hone : s.nr 126 = 1) :
    (adjacencyResult s).nm (s.nr 163 + s.nr 161) = s.nr 160 + 1 := by
  simp [adjacencyResult, hone]

private theorem adjacencyResult_link (s : Store)
    (hsep : s.nr 164 + s.nr 160 ≠ s.nr 163 + s.nr 161) :
    (adjacencyResult s).nm (s.nr 164 + s.nr 160) = s.nm (s.nr 163 + s.nr 161) := by
  simp [adjacencyResult, hsep]

private theorem adjacencyResult_memory_frame (s : Store) (a : ℕ)
    (hh : a ≠ s.nr 163 + s.nr 161) (hl : a ≠ s.nr 164 + s.nr 160) :
    (adjacencyResult s).nm a = s.nm a := by simp [adjacencyResult, hh, hl]

private theorem adjacencyResult_register_frame (s : Store) (r : ℕ)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168) :
    (adjacencyResult s).nr r = s.nr r := by simp [adjacencyResult, h165, h166, h167, h168]

private theorem adjacencyResult_real_frame (s : Store) :
    (adjacencyResult s).rr = s.rr ∧ (adjacencyResult s).rm = s.rm := ⟨rfl, rfl⟩

private theorem AdjacencyChain.frame {mem mem' : ℕ → ℕ} {links token : ℕ} {es : List ℕ}
    (h : AdjacencyChain mem links token es)
    (hf : ∀ e ∈ es, mem' (links + e) = mem (links + e)) :
    AdjacencyChain mem' links token es := by
  induction h with
  | nil => exact AdjacencyChain.nil
  | @cons e next es he hs ih =>
      exact AdjacencyChain.cons ((hf e (by simp)).trans he)
        (ih (fun x hx => hf x (by simp [hx])))

private theorem adjacencyInsert_chain (s : Store) (es : List ℕ)
    (hone : s.nr 126 = 1)
    (hold : AdjacencyChain s.nm (s.nr 164) (s.nm (s.nr 163 + s.nr 161)) es)
    (hfresh : s.nr 160 ∉ es)
    (hsep : ∀ e, s.nr 164 + e ≠ s.nr 163 + s.nr 161) :
    AdjacencyChain (adjacencyResult s).nm (s.nr 164)
      ((adjacencyResult s).nm (s.nr 163 + s.nr 161)) (s.nr 160 :: es) := by
  rw [adjacencyResult_head s hone]
  apply AdjacencyChain.cons (adjacencyResult_link s (hsep _))
  apply hold.frame
  intro e he
  apply adjacencyResult_memory_frame
  · exact hsep e
  · intro hh
    have : e = s.nr 160 := by omega
    exact hfresh (this ▸ he)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem treeAdjacencyPrepared_scratch (input : RAMInput) (s : Store) :
    TreeIteratorScratch s (treeAdjacencyPrepared input s) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro r he _ hn
  simp [treeAdjacencyPrepared,evalAtoms,treeAdjacencyPrepare,Atom.eval,Store.ofRAM,
    Store.at,ramStep,evalNat,he,hn]

private theorem treeAdjacencyAdvanced_scratch (input : RAMInput) (s : Store) :
    TreeIteratorScratch s (treeAdjacencyAdvanced input s) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro r _ hc _
  simp [treeAdjacencyAdvanced,Atom.eval,Store.ofRAM,Store.at,ramStep,hc]

private theorem treeAdjacencyPrepared_values (input : RAMInput) (s : Store) :
    (treeAdjacencyPrepared input s).nr 265 = s.nr 278-s.nr 4 ∧
    (treeAdjacencyPrepared input s).nr 279 = s.nm (s.nr 139+(s.nr 278-s.nr 4)) := by
  simp [treeAdjacencyPrepared,evalAtoms,treeAdjacencyPrepare,Atom.eval,Store.ofRAM,
    Store.at,ramStep,evalNat]

private theorem treeAdjacencyLoop_run_of_edge_contract {α : Type*}
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
    (htoken : s.nr 278 = token) :
    ∃ out n, Run input treeAdjacencyLoop s out n ∧ Inv (es.foldl step S) out ∧
      out.nr 278 = 0 ∧ n ≤ (C+6)*es.length+1 ∧
      (∀ a, protect a → out.nm a = s.nm a ∧ out.rm a = s.rm a) := by
  induction es generalizing S s token with
  | nil =>
      cases hchain
      refine ⟨s,1,Run.loopFalse ?_,hInv,htoken,by simp,?_⟩
      · simp [Guard.eval,natTest,hz,htoken]
      · intro a _
        exact ⟨rfl,rfl⟩
  | cons e es ih =>
      cases hchain with
      | @cons _ next _ hnext htail =>
          let p := treeAdjacencyPrepared input s
          have hprep : Run input (.atoms treeAdjacencyPrepare) s p 3 :=
            run_atoms input treeAdjacencyPrepare s
          have hpInv : Inv S p := htransfer S s p hInv (treeAdjacencyPrepared_scratch input s)
          obtain ⟨hpe,hpn⟩ := treeAdjacencyPrepared_values input s
          rw [htoken,ho,Nat.add_sub_cancel] at hpe hpn
          rw [hl,hnext] at hpn
          obtain ⟨t,nE,hE,htInv,hnE,hlinks,hprotect⟩ := hedge S e p
            (hvalid e (by simp)) hpInv hpe
          let q := treeAdjacencyAdvanced input t
          have hinc : Run input (.atom ⟨.natCopy 278 279,trivial⟩) t q 1 :=
            Run.atom _ t
          have hbody : Run input treeAdjacencyBody s q (3+(nE+1)) :=
            Run.seq hprep (Run.seq hE hinc)
          have hqInv : Inv (step S e) q :=
            htransfer _ t q htInv (treeAdjacencyAdvanced_scratch input t)
          have hqt : q.nr 278 = next := by
            change t.nr 279 = next
            rw [hE.nat_frame 279 (by decide)]
            exact hpn
          have hqchain : AdjacencyChain q.nm links next es := by
            apply htail.frame
            intro k hk
            exact hlinks k (hvalid k (by simp [hk]))
          obtain ⟨out,nT,hT,houtInv,houtToken,hnT,houtFrame⟩ := ih (step S e) q next hqchain
            (fun k hk => hvalid k (by simp [hk])) hqInv
            ((hbody.nat_frame 3 (by decide)).trans hz)
            ((hbody.nat_frame 4 (by decide)).trans ho)
            ((hbody.nat_frame 139 (by decide)).trans hl) hqt
          refine ⟨out,1+(3+(nE+1))+1+nT,Run.loopTrue ?_ hbody hT,houtInv,houtToken,?_,?_⟩
          · simp [Guard.eval,natTest,hz,htoken]
          · simp only [List.length_cons,Nat.mul_succ]
            omega
          · intro a ha
            exact ⟨(houtFrame a ha).1.trans (hprotect a ha).1,
              (houtFrame a ha).2.trans (hprotect a ha).2⟩

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem treeCheckTarget_run (input : RAMInput) (B : ℕ) (leaf : ℕ → Queue.Record)
    (s : Store)
    (hp : Queue.ParentLayout (2 * B) (treeTargetLoaded s)) (hone : s.nr 4 = 1)
    (hpositive : 0 < (treeTargetLoaded s).nr 0) (hleaf : B ≤ (treeTargetLoaded s).nr 0)
    (hrep : Queue.Represents B ((treeTargetLoaded s).nr 1) leaf (treeTargetLoaded s))
    (hparent : targetAddress ((treeTargetLoaded s).nr 268) + (treeTargetLoaded s).nr 173 < (treeTargetLoaded s).nr 1) :
    ∃ out steps, Run input treeCheckTarget s out steps ∧
      steps ≤ 19 * Nat.clog 2 (2 * B) + 25 ∧
      Queue.ParentLayout (2 * B) out ∧
      Queue.Represents B ((treeTargetLoaded s).nr 1) (treeCheckedLeaf leaf (treeTargetLoaded s)) out ∧
      (∀ a, a < (treeTargetLoaded s).nr 1 ∨ (treeTargetLoaded s).nr 1 + 2 * B ≤ a →
        out.nm a = treeCheckedNatMemory (treeTargetLoaded s) a ∧ out.rm a = (treeTargetLoaded s).rm a) := by
  classical
  let p := treeTargetLoaded s
  change Queue.ParentLayout (2*B) p at hp
  change 0 < p.nr 0 at hpositive
  change B ≤ p.nr 0 at hleaf
  change Queue.Represents B (p.nr 1) leaf p at hrep
  change targetAddress (p.nr 268)+p.nr 173 < p.nr 1 at hparent
  change ∃ out steps, Run input treeCheckTarget s out steps ∧
    steps ≤ 19*Nat.clog 2 (2*B)+25 ∧ Queue.ParentLayout (2*B) out ∧
    Queue.Represents B (p.nr 1) (treeCheckedLeaf leaf p) out ∧
    (∀ a, a < p.nr 1 ∨ p.nr 1+2*B ≤ a →
      out.nm a=treeCheckedNatMemory p a ∧ out.rm a=p.rm a)
  have hprep := run_atoms input treeTargetAtoms s
  rw [treeTargetAtoms_eval] at hprep
  have hpone : p.nr 4 = 1 := by simpa [p, treeTargetLoaded] using hone
  have hpzero : p.nr 3 = 0 := hp.2.2.1
  by_cases ht : p.nr 10 = 0
  · have hb := Run.branchTrue (input := input) (g := Guard.nat .eq 10 3)
      (b := Cmd.branch (.real .lt 264 265) treeApplyDecrease .skip)
      (by simp [Guard.eval, natTest, ht, hpzero]) (Run.skip p)
    refine ⟨p, 9, Run.seq hprep hb, by omega, hp, ?_, ?_⟩
    · simpa [treeCheckedLeaf, ht] using hrep
    · intro a ha; simp [treeCheckedNatMemory, ht]
  · by_cases hd : p.rr 264 < p.rr 265
    · let d := treeDecreased p
      have hdheader (r : ℕ) (hr : r < 11) : d.nr r = p.nr r :=
        treeDecreased_header p r hr
      have hdparent : Queue.ParentLayout (2 * B) d := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hdheader 0 (by decide)]; exact hp.1
        · rw [hdheader 1 (by decide), hdheader 2 (by decide)]; exact hp.2.1
        · rw [hdheader 3 (by decide)]; exact hpzero
        · intro u hu
          rw [hdheader 2 (by decide)]
          change Function.update p.nm (targetAddress (p.nr 268) + p.nr 173)
            (p.nr 262 + p.nr 4) (p.nr 2 + u) = u / 2
          rw [Function.update_of_ne (by have := hp.2.1; omega)]
          exact hp.2.2.2 u hu
      have hdrep : Queue.Represents B (d.nr 1) leaf d := by
        rw [hdheader 1 (by decide)]
        intro node hnode
        have hh := hrep node hnode
        unfold Queue.readRecord at hh ⊢
        change (⟨Function.update p.nm (targetAddress (p.nr 268) + p.nr 173)
          (p.nr 262 + p.nr 4) (p.nr 1 + node), p.rm (p.nr 1 + node)⟩ : Queue.Record) = _
        rw [Function.update_of_ne (by omega)]
        exact hh
      obtain ⟨out, k, hrun, hk, hz, hh, hpout, hrout, hf⟩ :=
        Queue.updateLeaf_refines input B leaf d hdparent
          ((hdheader 4 (by decide)).trans hpone)
          (by rw [hdheader 0 (by decide)]; exact hpositive)
          (by rw [hdheader 0 (by decide)]; exact hleaf) hdrep
      have hdec := run_atoms input treeDecreaseAtoms p
      rw [treeDecreaseAtoms_eval] at hdec
      have hbody : Run input treeApplyDecrease p out (8 + k) := Run.seq hdec hrun
      have hinner := Run.branchTrue (g := Guard.real .lt 264 265) (b := Cmd.skip)
        (by simp [Guard.eval, realTest, hd]) hbody
      have houter := Run.branchFalse (g := Guard.nat .eq 10 3) (a := Cmd.skip)
        (by simp [Guard.eval, natTest, ht, hpzero]) hinner
      refine ⟨out, 7 + (1 + (1 + (8 + k) + 1)), Run.seq hprep houter,
        by omega, hpout, ?_, ?_⟩
      · simpa [treeCheckedLeaf, ht, hd, d, treeDecreased] using hrout
      · intro a ha
        have hf' := hf a (by simpa only [hdheader 1 (by decide)] using ha)
        simpa [treeCheckedNatMemory, ht, hd, d, treeDecreased] using hf'
    · have hinner := Run.branchFalse (input := input) (g := Guard.real .lt 264 265)
        (a := treeApplyDecrease) (by simp [Guard.eval, realTest, hd]) (Run.skip p)
      have houter := Run.branchFalse (g := Guard.nat .eq 10 3) (a := Cmd.skip)
        (by simp [Guard.eval, natTest, ht, hpzero]) hinner
      refine ⟨p, 9, Run.seq hprep houter, by omega, hp, ?_, ?_⟩
      · simpa [treeCheckedLeaf, ht, hd] using hrep
      · intro a ha; simp [treeCheckedNatMemory, ht, hd]

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem treePolicy_candidate_sentinel (I : Instance) (allow : ℕ→ℕ→Bool)
    (w : ℕ→ℕ→ℝ≥0) (S : TreeQueue)
    (h : TreePolicy I allow (fun u v=>(w u v:ℝ)) S)
    (hs : (S.tree I.source).distance=some 0) (u v : ℕ) (d : ℝ)
    (hd : (S.tree u).distance=some d) (he : (u,v)∈I.graph.edges) :
    d+(w u v:ℝ) < ((I.graph.n:ℝ)+1)*(1+edgeWeightSum I w) := by
  have hW := edgeWeightSum_nonneg I w
  have hb := treePolicy_distance_bound I allow _ S h hs (edgeWeightSum I w) hW
    (weight_le_edgeWeightSum I w) u d hd
  have hrank : S.rank≤I.graph.n := by
    have hbal := h.balance
    have hn := activeVertices_length_le_vertices I
    omega
  have hnr : (S.rank:ℝ)≤(I.graph.n:ℝ) := by exact_mod_cast hrank
  have hm := mul_le_mul_of_nonneg_right hnr hW
  have hw := weight_le_edgeWeightSum I w u v he
  have hc : d+(w u v:ℝ) ≤ ((I.graph.n:ℝ)+1)*edgeWeightSum I w := by
    calc
      _ ≤ (I.graph.n:ℝ)*edgeWeightSum I w+edgeWeightSum I w := by linarith
      _ = _ := by ring
  have hn : (0:ℝ)<(I.graph.n:ℝ)+1 := by positivity
  apply hc.trans_lt
  calc
    _ < ((I.graph.n:ℝ)+1)*edgeWeightSum I w+((I.graph.n:ℝ)+1) := lt_add_of_pos_right _ hn
    _ = _ := by ring

private theorem sentinelKey_le (top : ℝ) (T : ShortestTree) (v : ℕ)
    (h : ∀ d, (T v).distance=some d → d<top) : sentinelKey top T v≤top := by
  cases hd : (T v).distance with
  | none => simp [sentinelKey,hd]
  | some d => simpa [sentinelKey,hd] using (h d hd).le

private theorem sentinel_source_none_no_decrease (top : ℝ) (T : ShortestTree) (u v : ℕ)
    (hu : (T u).distance=none) (weight : ℝ) (hw : 0≤weight)
    (hv : ∀ d, (T v).distance=some d → d<top) :
    ¬ sentinelKey top T u+weight < sentinelKey top T v := by
  have htarget := sentinelKey_le top T v hv
  have hsum : top≤top+weight := le_add_of_nonneg_right hw
  simpa [sentinelKey,hu] using not_lt.mpr (htarget.trans hsum)

private theorem sentinel_finite_candidate_comparison (top : ℝ) (T : ShortestTree) (v : ℕ)
    (candidate : ℝ) (hc : candidate<top)
    (hv : ∀ d, (T v).distance=some d → d<top) :
    distanceLess (some candidate) (T v).distance = decide (candidate<sentinelKey top T v) := by
  have h := distanceLess_eq_sentinel top (some candidate) (T v).distance
    (by intro d hd; have := Option.some.inj hd; simpa [←this] using hc) hv
  exact h.trans (Bool.decide_congr (by rfl))

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem treeRelax_eq_real_test (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (u v : ℕ) (top : ℝ)
    (hu : u ∉ S.queue) (hw : 0 ≤ w u v)
    (hfinite : ∀ x d, (S.tree x).distance = some d → d < top)
    (hcandidate : ∀ d, (S.tree u).distance = some d → d + w u v < top) :
    treeRelax I allow w u S (u,v) =
      if v ∈ S.queue ∧ allow u v = true ∧
          sentinelKey top S.tree u + w u v < sentinelKey top S.tree v then
        { S with tree := Function.update S.tree v ⟨some (sentinelKey top S.tree u + w u v), some u, 0⟩ }
      else S := by
  classical
  by_cases hv : v ∈ S.queue
  · have huv : u ≠ v := by intro he; subst v; exact hu hv
    by_cases ha : allow u v = true
    · cases hd : (S.tree u).distance with
      | none =>
          have hn := sentinel_source_none_no_decrease top S.tree u v hd (w u v) hw
            (hfinite v)
          simp [treeRelax, hv, huv, ha, hd, hn]
      | some d =>
          have hcmp := sentinel_finite_candidate_comparison top S.tree v (d + w u v)
            (hcandidate d hd) (hfinite v)
          have hs : sentinelKey top S.tree u = d := by simp [sentinelKey, hd]
          have hg : (u,v).1 = u ∧ (u,v).1 ≠ (u,v).2 ∧
              (u,v).2 ∈ S.queue ∧ allow (u,v).1 (u,v).2 = true :=
            ⟨rfl, huv, hv, ha⟩
          simp only [treeRelax, if_pos hg, hd, hcmp, hs, hv, huv, ha, true_and, and_true,
            decide_eq_true_eq]
          rw [if_pos huv]

    · simp [treeRelax, hv, ha]
  · simp [treeRelax, hv]

private theorem sentinelKey_update (top : ℝ) (T : ShortestTree) (v : ℕ) (d : ℝ)
    (parent rank : ℕ) :
    sentinelKey top (Function.update T v ⟨some d, some parent, rank⟩) =
      Function.update (sentinelKey top T) v d := by
  funext x
  by_cases hx : x = v
  · subst x; simp [sentinelKey]
  · simp [sentinelKey, hx]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem TreeMemoryRep.congr {I : Instance} {B W P map array off : ℕ} {top : ℝ}
    {S : TreeQueue} {s t : Store} (h : TreeMemoryRep I B W P map array off top S s)
    (hmap : t.nr 141 = s.nr 141) (harray : t.nr 142 = s.nr 142)
    (hcount : t.nr 143 = s.nr 143) (hn : t.nm = s.nm) (hr : t.rm = s.rm) :
    TreeMemoryRep I B W P map array off top S t := by
  refine ⟨h.active.congr hmap harray hcount (fun _ _ => congrFun hn _) (fun _ _ => congrFun hn _),
    h.queued,?_,?_,?_,?_⟩
  · simpa only [Queue.Represents,Queue.readRecord,hn,hr] using h.heap
  · simpa only [hn] using h.links
  · simpa only [hn] using h.parents
  · simpa only [hr] using h.settled

private theorem TreeMemoryRep.after_readonly {I : Instance} {B W P map array off : ℕ} {top : ℝ}
    {S : TreeQueue} {s t : Store} (h : TreeMemoryRep I B W P map array off top S s)
    {input : RAMInput} {cmd : Cmd} {steps : ℕ} (hrun : Run input cmd s t steps)
    (h141 : 141 ∉ cmd.natWrites) (h142 : 142 ∉ cmd.natWrites) (h143 : 143 ∉ cmd.natWrites)
    (hn : cmd.writesNatMemory = false) (hr : cmd.writesRealMemory = false) :
    TreeMemoryRep I B W P map array off top S t :=
  h.congr (hrun.nat_frame 141 h141) (hrun.nat_frame 142 h142) (hrun.nat_frame 143 h143)
    (hrun.natMemory_frame hn) (hrun.realMemory_frame hr)

private theorem treeTarget_values {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (s : Store) (v : ℕ) (hm : E.Memory mode S s)
    (hr : E.Registers mode s) (hv : v ∈ activeVertices I) (hhead : s.nr 268 = v) :
    let k := (activeVertices I).idxOf v
    let p := treeTargetLoaded s
    p.nr 0 = E.B+k ∧ p.nr 10 = (if v ∈ S.queue then k+1 else 0) ∧
    p.rr 265 = sentinelKey (mode.top I) S.tree v := by
  let k := (activeVertices I).idxOf v
  have hi := hm.active.indexOf v hv
  have hkn : k < (activeVertices I).length := List.idxOf_lt_length_of_mem hv
  have hfit := E.fit
  have hrecord := hm.heap (E.B+k) (by omega)
  rw [Queue.heapTruth_leaf _ _ _ (by omega),Queue.activeLeaf_at _ _ _ _ _ hkn] at hrecord
  have hslot : Queue.slotVertex (activeVertices I) k = v := by
    simp only [Queue.slotVertex,k,List.getElem?_idxOf hv,Option.getD_some]
  rw [hslot] at hrecord
  have ht := congrArg Queue.Record.token hrecord
  have hk := congrArg Queue.Record.key hrecord
  change s.nm (E.W+(E.B+k)) = _ at ht
  change s.rm (E.W+(E.B+k)) = _ at hk
  dsimp [k] at ht hk
  simp [treeTargetLoaded,hr.map,hhead,hi,hr.one,hr.saved_capacity,hr.winner,ht,hk]

private theorem treeTarget_correct {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (input : RAMInput) (s : Store) (u v : ℕ) (d : ℝ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (hv : v ∈ activeVertices I) (hu : s.nr 262 = u) (hhead : s.nr 268 = v)
    (hd : s.rr 264 = d) :
    ∃ out steps, Run input treeCheckTarget s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+25 ∧
      E.Memory mode (treeTargetState (mode.top I) S u v d) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out := by
  let k := (activeVertices I).idxOf v
  let p := treeTargetLoaded s
  have hpRun := run_atoms input treeTargetAtoms s
  rw [treeTargetAtoms_eval] at hpRun
  have hpMem : E.Memory mode S p := hm.after_readonly hpRun
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpReg : E.Registers mode p := hr.after_run hpRun (by decide) (by decide)
  obtain ⟨hpnode,hptoken,hpkey⟩ := treeTarget_values E mode S s v hm hr hv hhead
  change p.nr 0 = E.B+k at hpnode
  change p.nr 10 = (if v ∈ S.queue then k+1 else 0) at hptoken
  change p.rr 265 = sentinelKey (mode.top I) S.tree v at hpkey
  have hkn : k < (activeVertices I).length := List.idxOf_lt_length_of_mem hv
  have hfit := E.fit
  have hBpos := E.capacity_pos
  have hparent : Queue.ParentLayout (2*E.B) p :=
    ⟨by rw [hpnode]; omega,by rw [hpReg.winner,hpReg.parent]; exact E.winner_parent,
      hpReg.zero,by intro node hn; rw [hpReg.parent]; exact hpMem.links node hn⟩
  have hvn := activeVertices_valid I v hv
  have hpa : targetAddress (p.nr 268)+p.nr 173 < p.nr 1 := by
    rw [hpRun.nat_frame 268 (by decide),hhead,hpReg.offset,hpReg.winner]
    exact E.target_lt_winner mode v hvn
  obtain ⟨out,n,hrun,hn,hparents,hheap,hframe⟩ := treeCheckTarget_run input E.B
    (Queue.activeLeaf (activeVertices I) S.queue (sentinelKey (mode.top I) S.tree) E.B) s
    hparent hr.one (by rw [hpnode]; omega) (by rw [hpnode]; omega)
    (by rw [hpReg.winner]; exact hpMem.heap) hpa
  change Queue.Represents E.B (p.nr 1)
    (treeCheckedLeaf (Queue.activeLeaf (activeVertices I) S.queue
      (sentinelKey (mode.top I) S.tree) E.B) p) out at hheap
  change (∀ a, a < p.nr 1 ∨ p.nr 1+2*E.B ≤ a →
    out.nm a = treeCheckedNatMemory p a ∧ out.rm a = p.rm a) at hframe
  have houtReg : E.Registers mode out := hr.after_run hrun (by decide) (by decide)
  have hphead : p.nr 268 = v := (hpRun.nat_frame 268 (by decide)).trans hhead
  have hpu : p.nr 262 = u := (hpRun.nat_frame 262 (by decide)).trans hu
  have hpd : p.rr 264 = d := (hpRun.real_frame 264 (by decide)).trans hd
  have hpnm : p.nm = s.nm := hpRun.natMemory_frame (by decide)
  have hprm : p.rm = s.rm := hpRun.realMemory_frame (by decide)
  have heq : (p.nr 10 ≠ 0 ∧ p.rr 264 < p.rr 265) ↔
      (v ∈ S.queue ∧ d < sentinelKey (mode.top I) S.tree v) := by
    rw [hptoken,hpd,hpkey]
    by_cases hq : v ∈ S.queue <;> simp [hq]
  have hf : ∀ a, a < E.W ∨ E.W+2*E.B ≤ a →
      out.nm a = (if v ∈ S.queue ∧ d < sentinelKey (mode.top I) S.tree v then
        Function.update s.nm (targetAddress v+mode.offset) (u+1) else s.nm) a ∧
      out.rm a = s.rm a := by
    intro a ha
    have hh := hframe a (by simpa only [hpReg.winner] using ha)
    simpa only [treeCheckedNatMemory,heq,hphead,hpReg.offset,hpu,hpReg.one,hpnm,hprm] using hh
  have hedgeFrame : TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out := by
    intro a ha hne
    have hh := hf a ha
    by_cases htest : v ∈ S.queue ∧ d < sentinelKey (mode.top I) S.tree v
    · simpa only [if_pos htest,Function.update_of_ne hne] using hh
    · simpa only [if_neg htest] using hh
  refine ⟨out,n,hrun,hn,?_,houtReg,hedgeFrame⟩
  have active : ActiveRep I.graph.n E.map E.array (activeVertices I) out := by
    apply hm.active.congr (hrun.nat_frame 141 (by decide)) (hrun.nat_frame 142 (by decide))
      (hrun.nat_frame 143 (by decide))
    · intro w hw
      have htarget := E.target_lt_map mode v hvn
      have hm := E.map_le_array
      have ha := E.array_end_le_winner
      exact (hedgeFrame _ (Or.inl (by omega)) (by omega)).1
    · intro l hl
      have hn := activeVertices_length_le_vertices I
      have htarget := E.target_lt_map mode v hvn
      have hm := E.map_le_array
      have ha := E.array_end_le_winner
      exact (hedgeFrame _ (Or.inl (by omega)) (by omega)).1
  by_cases htest : v ∈ S.queue ∧ d < sentinelKey (mode.top I) S.tree v
  · rw [treeTargetState,if_pos htest]
    have hleaf := Queue.activeLeaf_update_vertex (activeVertices I) S.queue
      (sentinelKey (mode.top I) S.tree) E.B v d (activeVertices_nodup I) hv htest.1
    refine ⟨active,hm.queued,?_,?_,?_,?_⟩
    · change Queue.Represents E.B E.W
        (Queue.activeLeaf (activeVertices I) S.queue (sentinelKey (mode.top I)
          (Function.update S.tree v ⟨some d,some u,0⟩)) E.B) out
      rw [sentinelKey_update,hleaf]
      rw [treeCheckedLeaf,if_pos (heq.mpr htest)] at hheap
      simpa only [hpReg.winner,hpnode,hptoken,if_pos htest.1,hpd,k] using hheap
    · intro node hn
      simpa only [houtReg.parent] using hparents.2.2.2 node hn
    · intro w hw
      have hf' := (hf (targetAddress w+mode.offset)
        (Or.inl (E.target_lt_winner mode w (activeVertices_valid I w hw)))).1
      rw [if_pos htest] at hf'
      by_cases hwv : w=v
      · subst w
        simpa only [Function.update_self,treeTargetState,if_pos htest,treeUpdated,
          Option.map_some,Option.getD_some] using hf'
      · have haddr : targetAddress w+mode.offset ≠ targetAddress v+mode.offset := by
          unfold targetAddress; omega
        rw [Function.update_of_ne haddr] at hf'
        simpa only [treeTargetState,if_pos htest,treeUpdated,Function.update_of_ne hwv]
          using hf'.trans (hm.parents w hw)
    · intro w hw hwq
      have hwq' : w ∉ S.queue := hwq
      have hwv : w ≠ v := by intro he; subst w; exact hwq' htest.1
      have hf' := (hf (targetAddress w+mode.offset)
        (Or.inl (E.target_lt_winner mode w (activeVertices_valid I w hw)))).2
      simpa only [treeTargetState,if_pos htest,treeUpdated,sentinelKey,
        Function.update_of_ne hwv] using hf'.trans (hm.settled w hw hwq')
  · have hheap' : Queue.Represents E.B E.W
        (Queue.activeLeaf (activeVertices I) S.queue (sentinelKey (mode.top I) S.tree) E.B) out := by
      simpa only [treeCheckedLeaf,if_neg (fun h => htest (heq.mp h)),hpReg.winner] using hheap
    have hresult : E.Memory mode S out := by
      refine ⟨active,hm.queued,hheap',?_,?_,?_⟩
      · intro node hn; simpa only [houtReg.parent] using hparents.2.2.2 node hn
      · intro w hw
        have hf' := (hf (targetAddress w+mode.offset)
          (Or.inl (E.target_lt_winner mode w (activeVertices_valid I w hw)))).1
        rw [if_neg htest] at hf'
        exact hf'.trans (hm.parents w hw)
      · intro w hw hwq
        exact ((hf (targetAddress w+mode.offset)
          (Or.inl (E.target_lt_winner mode w (activeVertices_valid I w hw)))).2).trans
          (hm.settled w hw hwq)
    simpa only [treeTargetState,if_neg htest] using hresult

private theorem TreeMode.sentinel_bounds (mode : TreeMode) (I : Instance) (S : TreeQueue)
    (h : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0) (u v : ℕ) (he : (u,v) ∈ I.graph.edges) :
    (∀ x d, (S.tree x).distance = some d → d < mode.top I) ∧
    (∀ d, (S.tree u).distance = some d → d + mode.weight I u v < mode.top I) := by
  constructor
  · intro x d hd
    have hW := edgeWeightSum_nonneg I (mode.resource I)
    have hb := treePolicy_distance_bound I (mode.allow I) (mode.weight I) S h hs
      (edgeWeightSum I (mode.resource I)) hW (weight_le_edgeWeightSum I (mode.resource I)) x d hd
    have hrank : S.rank ≤ I.graph.n := by
      have hb := h.balance
      have hn := activeVertices_length_le_vertices I
      omega
    have hrank' : (S.rank : ℝ) ≤ I.graph.n := by exact_mod_cast hrank
    have hm := mul_le_mul_of_nonneg_right hrank' hW
    have hn : (0 : ℝ) ≤ I.graph.n := Nat.cast_nonneg _
    unfold TreeMode.top
    nlinarith
  · intro d hd
    exact treePolicy_candidate_sentinel I (mode.allow I) (mode.resource I) S h hs u v d hd he

private theorem standalone_Mission_RAMTreeEdge__edgeGuard_value (I : Instance) (mode : TreeMode) (s : Store) (u v : ℕ)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v) (hz : s.rr 263 = 0) :
    (standalone_Mission_RAMTreeEdge__edgeGuard mode).eval s = mode.allow I u v := by
  cases mode <;> simp [standalone_Mission_RAMTreeEdge__edgeGuard,Guard.eval,realTest,TreeMode.allow,hL,hC,hz]

private theorem standalone_Mission_RAMTreeEdge__candidate_value (I : Instance) (mode : TreeMode) (input : RAMInput)
    (s : Store) (u v : ℕ) (key : ℝ) (hkey : s.rr 260 = key)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v) :
    ((standalone_Mission_RAMTreeEdge__candidateAtom mode).eval input s).rr 264 = key + mode.weight I u v := by
  cases mode <;> simp [standalone_Mission_RAMTreeEdge__candidateAtom,Atom.eval,Store.ofRAM,Store.at,ramStep,evalReal,
    hkey,hL,hC,TreeMode.weight,TreeMode.resource]

private theorem standalone_Mission_RAMTreeEdge__modeBody_correct {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (input : RAMInput) (s : Store) (u v : ℕ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (he : (u,v) ∈ I.graph.edges) (huq : u ∉ S.queue)
    (hpolicy : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0)
    (hu : s.nr 262 = u) (hv : s.nr 268 = v)
    (hkey : s.rr 260 = sentinelKey (mode.top I) S.tree u)
    (hL : s.rr 261 = I.length u v) (hC : s.rr 262 = I.cost u v) (hz : s.rr 263 = 0) :
    ∃ out steps, Run input (standalone_Mission_RAMTreeEdge__modeBody mode) s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+28 ∧
      E.Memory mode (treeRelax I (mode.allow I) (mode.weight I) u S (u,v)) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out := by
  have hguard := standalone_Mission_RAMTreeEdge__edgeGuard_value I mode s u v hL hC hz
  by_cases ha : mode.allow I u v = true
  · let added := (standalone_Mission_RAMTreeEdge__candidateAtom mode).eval input s
    have hadd : Run input (.atom (standalone_Mission_RAMTreeEdge__candidateAtom mode)) s added 1 := Run.atom _ _
    have ham : E.Memory mode S added := hm.after_readonly hadd
      (by cases mode <;> decide) (by cases mode <;> decide) (by cases mode <;> decide)
      (by cases mode <;> decide) (by cases mode <;> decide)
    have har : E.Registers mode added := hr.after_run hadd
      (by cases mode <;> decide) (by cases mode <;> decide)
    have hd := standalone_Mission_RAMTreeEdge__candidate_value I mode input s u v _ hkey hL hC
    obtain ⟨out,n,hrun,hn,hmout,hrout,hframe⟩ := treeTarget_correct E mode S input added u v
      (sentinelKey (mode.top I) S.tree u + mode.weight I u v) ham har
      (activeVertices_edge_right I u v he)
      ((hadd.nat_frame 262 (by cases mode <;> decide)).trans hu)
      ((hadd.nat_frame 268 (by cases mode <;> decide)).trans hv) hd
    have hwhole : Run input (standalone_Mission_RAMTreeEdge__modeBody mode) s out (1+(1+n)+1) :=
      Run.branchTrue (hguard.trans ha) (Run.seq hadd hrun)
    obtain ⟨hfinite,hcandidate⟩ := mode.sentinel_bounds I S hpolicy hs u v he
    have heq := treeRelax_eq_real_test I (mode.allow I) (mode.weight I) S u v (mode.top I)
      huq (mode.resource I u v).coe_nonneg hfinite hcandidate
    refine ⟨out,_,hwhole,by omega,?_,hrout,?_⟩
    · rw [heq]
      simpa [ha,treeTargetState,treeUpdated] using hmout
    · intro a hwhere hne
      have hf := hframe a hwhere hne
      exact ⟨hf.1.trans (congrFun (hadd.natMemory_frame (by cases mode <;> decide)) a),
        hf.2.trans (congrFun (hadd.realMemory_frame (by cases mode <;> decide)) a)⟩
  · have hfalse : (standalone_Mission_RAMTreeEdge__edgeGuard mode).eval s = false := by rw [hguard]; simpa using ha
    refine ⟨s,1,Run.branchFalse hfalse (Run.skip s),by omega,?_,hr,?_⟩
    · simpa [treeRelax,ha] using hm
    · intro a hwhere hne; exact ⟨rfl,rfl⟩

private theorem treeEdge_correct {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (S : TreeQueue) (ε : ℝ) (s : Store) (u v : ℕ)
    (hm : E.Memory mode S s) (hr : E.Registers mode s)
    (he : I.graph.edges[s.nr 265]? = some (u,v)) (huq : u ∉ S.queue)
    (hpolicy : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hs : (S.tree I.source).distance = some 0)
    (hu : s.nr 262 = u) (hkey : s.rr 260 = sentinelKey (mode.top I) S.tree u) :
    ∃ out steps, Run (encodeInput I ε) treeRelaxEdgeCmd s out steps ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+40 ∧
      E.Memory mode (treeRelax I (mode.allow I) (mode.weight I) u S (u,v)) out ∧
      E.Registers mode out ∧ TreeEdgeFrame E.W E.B (targetAddress v+mode.offset) s out := by
  let loaded := treeEdgeLoaded (encodeInput I ε) s
  have hload := run_atoms (encodeInput I ε) treeEdgeAtoms s
  rw [treeEdgeAtoms_eval] at hload
  have hlm : E.Memory mode S loaded := hm.after_readonly hload
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hlr : E.Registers mode loaded := hr.after_run hload (by decide) (by decide)
  obtain ⟨hlv,hL,hC⟩ := treeEdgeLoaded_values I ε s (u,v) he hr.one
  obtain ⟨out,n,hbody,hn,hmout,hrout,hframe⟩ := standalone_Mission_RAMTreeEdge__modeBody_correct E mode S (encodeInput I ε) loaded u v
    hlm hlr (List.mem_of_getElem? he) huq hpolicy hs
    ((hload.nat_frame 262 (by decide)).trans hu) hlv
    ((hload.real_frame 260 (by decide)).trans hkey) hL hC
    (by simp [loaded,treeEdgeLoaded])
  have hmodeRun : ∃ c ≤ n+2, Run (encodeInput I ε) treeRelaxLoaded loaded out c := by
    cases mode with
    | zeroLength =>
        exact ⟨1+n+1,by omega,Run.branchTrue
          (by simp [Guard.eval,natTest,hlr.mode,hlr.zero,TreeMode.tag]) hbody⟩
    | zeroBudget =>
        exact ⟨1+n,by omega,Run.branchFalse
          (by simp [Guard.eval,natTest,hlr.mode,hlr.zero,TreeMode.tag]) hbody⟩
  obtain ⟨c,hc,hrun⟩ := hmodeRun
  refine ⟨out,10+c,Run.seq hload hrun,by omega,hmout,hrout,?_⟩
  intro a hwhere hne
  have hf := hframe a hwhere hne
  exact ⟨hf.1.trans (congrFun (hload.natMemory_frame (by decide)) a),
    hf.2.trans (congrFun (hload.realMemory_frame (by decide)) a)⟩

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem treeRelax_source_zero (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (hw : ∀ u v, 0 ≤ w u v) (u : ℕ) (S : TreeQueue)
    (hn : ∀ v, 0 ≤ treeDist S.tree v) (hs : (S.tree I.source).distance = some 0)
    (e : ℕ × ℕ) : ((treeRelax I allow w u S e).tree I.source).distance = some 0 := by
  have hge := treeRelax_dist_nonneg I allow w hw u S hn e I.source
  have hle := treeRelax_dist_le I allow w u I.source S e
  have hzero : treeDist S.tree I.source = 0 := by simp [treeDist, optionDist, hs]
  rw [hzero] at hle
  have heq := le_antisymm hle hge
  unfold treeDist at heq
  cases hd : ((treeRelax I allow w u S e).tree I.source).distance with
  | none => simp [hd, optionDist] at heq
  | some d => simpa [hd, optionDist] using heq

private theorem TreeScanMath.step {I : Instance} {allow : ℕ → ℕ → Bool} {w : ℕ → ℕ → ℝ}
    {u : ℕ} {S : TreeQueue} (h : TreeScanMath I allow w u S)
    (hw : ∀ u v, 0 ≤ w u v) (e : ℕ × ℕ) (he : e ∈ I.graph.edges) :
    TreeScanMath I allow w u (treeRelax I allow w u S e) := by
  refine ⟨treeRelax_policy I allow w u S e he h.removed h.rank_bound h.policy,
    treeRelax_dist_nonneg I allow w hw u S h.nonnegative e,
    treeRelax_source_zero I allow w hw u S h.nonnegative h.source_zero e, ?_, ?_⟩
  · simpa only [treeRelax_queue] using h.removed
  · rw [treeRelax_outside I allow w u u S e h.removed, treeRelax_rank]
    exact h.rank_bound

private theorem TreeScanMath.start (I : Instance) (allow : ℕ → ℕ → Bool) (w : ℕ → ℕ → ℝ)
    (S : TreeQueue) (u : ℕ) (hu : u ∈ S.queue) (hq : S.queue.Nodup)
    (hp : TreePolicy I allow w S) (hn : ∀ v, 0 ≤ treeDist S.tree v)
    (hs : (S.tree I.source).distance = some 0) :
    TreeScanMath I allow w u (treeSettle S u) := by
  refine ⟨treeSettle_policy I allow w S u hu hp, ?_, ?_, ?_, ?_⟩
  · intro v; rw [treeSettle_dist]; exact hn v
  · by_cases hsu : I.source = u
    · simpa [treeSettle, hsu] using hs
    · simpa [treeSettle, hsu] using hs
  · exact hq.not_mem_erase
  · simp [treeSettle]

private theorem relaxEdge_nonoutgoing (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (he : e.1 ≠ u) : relaxEdge A i j u S e = S := by
  simp [relaxEdge, he]

private theorem relaxFold_filter_outgoing (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (es : List (ℕ × ℕ)) :
    (es.filter (fun e => e.1 == u)).foldl (relaxEdge A i j u) S =
      es.foldl (relaxEdge A i j u) S := by
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
      by_cases he : e.1 = u
      · simp only [List.filter_cons, he, beq_self_eq_true, Bool.true_eq, ↓reduceIte,
          List.foldl_cons, ih]
      · simp only [List.filter_cons, beq_iff_eq, he, ↓reduceIte, List.foldl_cons,
          relaxEdge_nonoutgoing A i j u S e he, ih]

private theorem relaxAll_eq_outgoingFold (A : InnerInput) (i j u : ℕ) (S : LayerState) :
    relaxAll A i j u S = (outgoingEdges A.I u).foldl (relaxEdge A i j u) S :=
  (relaxFold_filter_outgoing A i j u S A.I.graph.edges).symm

private theorem treeRelax_nonoutgoing (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : e.1 ≠ u) : treeRelax I allow w u S e = S := by
  simp [treeRelax, he]

private theorem treeRelaxFold_filter_outgoing (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (es : List (ℕ × ℕ)) :
    (es.filter (fun e => e.1 == u)).foldl (treeRelax I allow w u) S =
      es.foldl (treeRelax I allow w u) S := by
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
      by_cases he : e.1 = u
      · simp only [List.filter_cons, he, beq_self_eq_true, Bool.true_eq, ↓reduceIte,
          List.foldl_cons, ih]
      · simp only [List.filter_cons, beq_iff_eq, he, ↓reduceIte, List.foldl_cons,
          treeRelax_nonoutgoing I allow w u S e he, ih]

private theorem treeRelaxAll_eq_outgoingFold (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) :
    treeRelaxAll I allow w u S =
      (outgoingEdges I u).foldl (treeRelax I allow w u) S :=
  (treeRelaxFold_filter_outgoing I allow w u S I.graph.edges).symm

private theorem relaxEdge_disabled (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (he : ¬ (e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue)) :
    relaxEdge A i j u S e = S := by simp [relaxEdge, he]

private theorem treeRelax_disabled (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e : ℕ × ℕ)
    (he : ¬ (e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue ∧ allow e.1 e.2 = true)) :
    treeRelax I allow w u S e = S := by simp [treeRelax, he]

private theorem relaxEdge_comm (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e f : ℕ × ℕ) :
    relaxEdge A i j u (relaxEdge A i j u S e) f =
      relaxEdge A i j u (relaxEdge A i j u S f) e := by
  rcases e with ⟨a,v⟩
  rcases f with ⟨b,w⟩
  by_cases ha : a = u
  · subst a
    by_cases hb : b = u
    · subst b
      by_cases hvw : v = w
      · subst w; rfl
      · have hwv : w ≠ v := Ne.symm hvw
        by_cases hv : u ≠ v ∧ v ∈ S.queue
        · by_cases hw : u ≠ w ∧ w ∈ S.queue
          · by_cases hec : edgeExpectation A S.table u v i j < S.keys v <;>
              by_cases hfc : edgeExpectation A S.table u w i j < S.keys w <;>
              simp [relaxEdge, hv.1, hw.1, hv.2, hw.2, hvw, hwv, hec, hfc,
                Function.update_comm hvw]
          · have hS := relaxEdge_disabled A i j u S (u,w) (by simpa using hw)
            have hafter := relaxEdge_disabled A i j u (relaxEdge A i j u S (u,v))
              (u,w) (by simpa only [relaxEdge_queue, true_and] using hw)
            rw [hS,hafter]
        · have hS := relaxEdge_disabled A i j u S (u,v) (by simpa using hv)
          have hafter := relaxEdge_disabled A i j u (relaxEdge A i j u S (u,w))
            (u,v) (by simpa only [relaxEdge_queue, true_and] using hv)
          rw [hS,hafter]
    · simp only [relaxEdge_nonoutgoing A i j u _ (b,w) hb]
  · simp only [relaxEdge_nonoutgoing A i j u _ (a,v) ha]

private theorem relaxFold_perm (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (es fs : List (ℕ × ℕ)) (h : es.Perm fs) :
    es.foldl (relaxEdge A i j u) S = fs.foldl (relaxEdge A i j u) S := by
  letI : RightCommutative (relaxEdge A i j u) := ⟨relaxEdge_comm A i j u⟩
  exact h.foldl_eq S

private theorem relaxAll_eq_reversedOutgoingFold (A : InnerInput) (i j u : ℕ) (S : LayerState) :
    relaxAll A i j u S = (outgoingEdges A.I u).reverse.foldl (relaxEdge A i j u) S := by
  rw [relaxAll_eq_outgoingFold]
  exact relaxFold_perm A i j u S _ _ (List.reverse_perm _).symm

private theorem treeRelax_comm (I : Instance) (allow : ℕ → ℕ → Bool)
    (weight : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) (e f : ℕ × ℕ) :
    treeRelax I allow weight u (treeRelax I allow weight u S e) f =
      treeRelax I allow weight u (treeRelax I allow weight u S f) e := by
  rcases e with ⟨a,v⟩
  rcases f with ⟨b,w⟩
  by_cases ha : a = u
  · subst a
    by_cases hb : b = u
    · subst b
      by_cases hvw : v = w
      · subst w; rfl
      · have hwv : w ≠ v := Ne.symm hvw
        by_cases hv : u ≠ v ∧ v ∈ S.queue ∧ allow u v = true
        · by_cases hw : u ≠ w ∧ w ∈ S.queue ∧ allow u w = true
          · cases hd : (S.tree u).distance with
            | none => simp [treeRelax, hv, hw, hd]
            | some d =>
                by_cases hec : distanceLess (some (d + weight u v)) (S.tree v).distance = true <;>
                  by_cases hfc : distanceLess (some (d + weight u w)) (S.tree w).distance = true <;>
                  simp [treeRelax, hv.1, hw.1, hv.2.1, hw.2.1, hv.2.2, hw.2.2,
                    hvw, hwv, hd, hec, hfc, Function.update_comm hvw]
          · have hS := treeRelax_disabled I allow weight u S (u,w) (by simpa using hw)
            have hafter := treeRelax_disabled I allow weight u (treeRelax I allow weight u S (u,v))
              (u,w) (by simpa only [treeRelax_queue, true_and] using hw)
            rw [hS,hafter]
        · have hS := treeRelax_disabled I allow weight u S (u,v) (by simpa using hv)
          have hafter := treeRelax_disabled I allow weight u (treeRelax I allow weight u S (u,w))
            (u,v) (by simpa only [treeRelax_queue, true_and] using hv)
          rw [hS,hafter]
    · simp only [treeRelax_nonoutgoing I allow weight u _ (b,w) hb]
  · simp only [treeRelax_nonoutgoing I allow weight u _ (a,v) ha]

private theorem treeRelaxFold_perm (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue)
    (es fs : List (ℕ × ℕ)) (h : es.Perm fs) :
    es.foldl (treeRelax I allow w u) S = fs.foldl (treeRelax I allow w u) S := by
  letI : RightCommutative (treeRelax I allow w u) := ⟨treeRelax_comm I allow w u⟩
  exact h.foldl_eq S

private theorem treeRelaxAll_eq_reversedOutgoingFold (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (u : ℕ) (S : TreeQueue) :
    treeRelaxAll I allow w u S =
      (outgoingEdges I u).reverse.foldl (treeRelax I allow w u) S := by
  rw [treeRelaxAll_eq_outgoingFold]
  exact treeRelaxFold_perm I allow w u S _ _ (List.reverse_perm _).symm

private theorem popLayer_reversed_refinement (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []) :
    popLayer A i j S = (outgoingEdges A.I (pickedVertex S)).reverse.foldl
      (relaxEdge A i j (pickedVertex S)) (settleState S i j (pickedVertex S)) := by
  rw [popLayer_eq_relaxAll A i j S hne, relaxAll_eq_reversedOutgoingFold]

private theorem treePop_reversed_refinement (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []) :
    treePop I allow w S = (outgoingEdges I (treePick S)).reverse.foldl
      (treeRelax I allow w (treePick S)) (treeSettle S (treePick S)) := by
  rw [treePop_eq_relaxAll I allow w S hne, treeRelaxAll_eq_reversedOutgoingFold]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

@[simp] private theorem adjacencyStep_index (input : RAMInput) (s : Store) :
    (adjacencyStep input s).nr 160 = s.nr 160 + 1 := by simp [adjacencyStep]

@[simp] private theorem adjacencyStep_inputPointer (input : RAMInput) (s : Store) :
    (adjacencyStep input s).nr 162 = s.nr 162 + 2 := by simp [adjacencyStep]

private theorem adjacencyStep_register (input : RAMInput) (s : Store) (r : ℕ)
    (h160 : r ≠ 160) (h161 : r ≠ 161) (h162 : r ≠ 162)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168) :
    (adjacencyStep input s).nr r = s.nr r := by
  simp only [adjacencyStep, Function.update_of_ne h160, Function.update_of_ne h162]
  rw [adjacencyResult_register_frame _ r h165 h166 h167 h168]
  simp [adjacencyLoaded,h161]

private theorem adjacencyScanBody_run (input : RAMInput) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2) :
    Run input adjacencyScanBody s (adjacencyStep input s) 9 := by
  have hload : Run input (.atom ⟨.inputNat 161 162,trivial⟩) s (adjacencyLoaded input s) 1 :=
    Run.atom _ s
  have hins := adjacencyInsert_run input (adjacencyLoaded input s)
  have htail := run_atoms input
    [⟨.natOp .add 160 160 126,trivial⟩,⟨.natOp .add 162 162 127,trivial⟩]
    (adjacencyResult (adjacencyLoaded input s))
  have heval : evalAtoms input
      [⟨.natOp .add 160 160 126,trivial⟩,⟨.natOp .add 162 162 127,trivial⟩]
      (adjacencyResult (adjacencyLoaded input s)) = adjacencyStep input s := by
    ext r <;> simp [evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,
      adjacencyResult,adjacencyLoaded,adjacencyStep,hone,htwo,Function.update]
  rw [heval] at htail
  exact Run.seq hload (Run.seq hins htail)

private theorem adjacencyScanLoop_run (input : RAMInput) (remaining : ℕ) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2)
    (hend : s.nr 160 + remaining = s.nr 122) :
    Run input adjacencyScanLoop s (adjacencyScanResult input remaining s) (11*remaining+1) := by
  induction remaining generalizing s with
  | zero =>
      apply Run.loopFalse
      simp [Guard.eval,natTest,show s.nr 160=s.nr 122 by omega]
  | succ k ih =>
      have h126 : (adjacencyStep input s).nr 126 = 1 := by
        rw [adjacencyStep_register input s 126 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hone
      have h127 : (adjacencyStep input s).nr 127 = 2 := by
        rw [adjacencyStep_register input s 127 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact htwo
      have h122 : (adjacencyStep input s).nr 122 = s.nr 122 :=
        adjacencyStep_register input s 122 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      have htail := ih (adjacencyStep input s) h126 h127 (by simp [h122]; omega)
      have hg : (Guard.nat .lt 160 122).eval s = true := by
        simp [Guard.eval,natTest,show s.nr 160<s.nr 122 by omega]
      have hrun := Run.loopTrue hg (adjacencyScanBody_run input s hone htwo) htail
      convert hrun using 1 <;> first | rfl | omega

private theorem adjacencyScanCmd_run (input : RAMInput) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2) :
    Run input adjacencyScanCmd s
      (adjacencyScanResult input (s.nr 122) (adjacencyPrepared s)) (11*s.nr 122+3) := by
  have hp : Run input
      (Cmd.atoms [⟨.natConst 160 0,trivial⟩,⟨.natConst 162 3,trivial⟩])
      s (adjacencyPrepared s) 2 := run_atoms input _ s
  have hl := adjacencyScanLoop_run input (s.nr 122) (adjacencyPrepared s)
    (by simpa [adjacencyPrepared] using hone) (by simpa [adjacencyPrepared] using htwo)
    (by simp [adjacencyPrepared])
  convert Run.seq hp hl using 1 <;> first | rfl | omega

private theorem outgoingIndices_lt (I : Instance) (count v e : ℕ)
    (he : e ∈ outgoingIndices I count v) : e < count := by
  simp only [outgoingIndices,List.mem_reverse,List.mem_filter,List.mem_range] at he
  exact he.1

private theorem outgoingIndices_succ (I : Instance) (count v : ℕ) :
    outgoingIndices I (count+1) v =
      if (edgeAt I count).1 = v then count :: outgoingIndices I count v
      else outgoingIndices I count v := by
  by_cases h : (edgeAt I count).1 = v <;>
    simp [outgoingIndices,List.range_succ,List.filter_append,h]

private theorem adjacencyPrefix_zero (I : Instance) (heads links : ℕ) (mem : ℕ → ℕ)
    (hz : ∀ v<I.graph.n, mem (heads+v)=0) : AdjacencyPrefix I 0 heads links mem := by
  intro v hv
  rw [hz v hv]
  exact AdjacencyChain.nil

private theorem edgeAt_valid (I : Instance) (e : ℕ) (he : e < I.graph.edges.length) :
    (edgeAt I e).1 < I.graph.n ∧ (edgeAt I e).2 < I.graph.n := by
  have hget : I.graph.edges[e]? = some I.graph.edges[e] := List.getElem?_eq_getElem he
  have hm : edgeAt I e ∈ I.graph.edges := by
    simp only [edgeAt,hget,Option.getD_some]
    exact List.getElem_mem he
  exact I.graph.endpoints _ hm

private theorem adjacencyStep_prefix (I : Instance) (ε : ℝ) (s : Store) (count heads links : ℕ)
    (hone : s.nr 126=1) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hvalid : count<I.graph.edges.length)
    (hsep : heads+I.graph.n ≤ links) (h : AdjacencyPrefix I count heads links s.nm) :
    AdjacencyPrefix I (count+1) heads links (adjacencyStep (encodeInput I ε) s).nm := by
  let u := (edgeAt I count).1
  have hu : u < I.graph.n := (edgeAt_valid I count hvalid).1
  have htail : (encodeInput I ε).naturals (s.nr 162) = u := by
    rw [hp]
    apply encodeInput_edge_left I ε count (edgeAt I count)
    simp only [edgeAt,List.getElem?_eq_getElem hvalid,Option.getD_some]
  let U := adjacencyLoaded (encodeInput I ε) s
  have hUone : U.nr 126=1 := by simpa [U,adjacencyLoaded] using hone
  have hUcount : U.nr 160=count := by simpa [U,adjacencyLoaded] using hcount
  have hUtail : U.nr 161=u := by simp [U,adjacencyLoaded,htail]
  have hUheads : U.nr 163=heads := by simpa [U,adjacencyLoaded] using hh
  have hUlinks : U.nr 164=links := by simpa [U,adjacencyLoaded] using hl
  intro v hv
  rw [outgoingIndices_succ]
  change AdjacencyChain (adjacencyResult U).nm links
    ((adjacencyResult U).nm (heads+v)) _
  by_cases hvu : u=v
  · have hnew := adjacencyInsert_chain U (outgoingIndices I count v) hUone
      (by rw [hUlinks,hUheads,hUtail,hvu]; exact h v hv)
      (by intro hm; rw [hUcount] at hm; have := outgoingIndices_lt I count v count hm; omega)
      (by intro e; rw [hUlinks,hUheads,hUtail]; omega)
    simpa [hUlinks,hUheads,hUtail,hUcount,hvu,u] using hnew
  · have hvu' : v≠u := Ne.symm hvu
    have hhead : (adjacencyResult U).nm (heads+v) = s.nm (heads+v) := by
      apply adjacencyResult_memory_frame U (heads+v)
      · rw [hUheads,hUtail]; omega
      · rw [hUlinks,hUcount]; omega
    rw [if_neg hvu,hhead]
    apply (h v hv).frame
    intro e he
    have hecount := outgoingIndices_lt I count v e he
    change (adjacencyResult U).nm (links+e) = U.nm (links+e)
    apply adjacencyResult_memory_frame
    · rw [hUheads,hUtail]; omega
    · rw [hUlinks,hUcount]; omega

private theorem adjacencyScanResult_register (input : RAMInput) (n : ℕ) (s : Store) (r : ℕ)
    (h160 : r ≠ 160) (h161 : r ≠ 161) (h162 : r ≠ 162)
    (h165 : r ≠ 165) (h166 : r ≠ 166) (h167 : r ≠ 167) (h168 : r ≠ 168) :
    (adjacencyScanResult input n s).nr r = s.nr r := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [adjacencyScanResult,ih]
      exact adjacencyStep_register input s r h160 h161 h162 h165 h166 h167 h168

private theorem adjacencyScanResult_reals (input : RAMInput) (n : ℕ) (s : Store) :
    (adjacencyScanResult input n s).rr = s.rr ∧
      (adjacencyScanResult input n s).rm = s.rm := by
  induction n generalizing s with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => exact ih (adjacencyStep input s)

private theorem adjacencyScanResult_prefix (I : Instance) (ε : ℝ) (remaining : ℕ)
    (s : Store) (count heads links : ℕ)
    (hone : s.nr 126=1) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links)
    (hvalid : count+remaining≤I.graph.edges.length)
    (hsep : heads+I.graph.n≤links) (h : AdjacencyPrefix I count heads links s.nm) :
    AdjacencyPrefix I (count+remaining) heads links
      (adjacencyScanResult (encodeInput I ε) remaining s).nm := by
  induction remaining generalizing s count with
  | zero => exact h
  | succ n ih =>
      have hstep := adjacencyStep_prefix I ε s count heads links hone hcount hp hh hl
        (by omega) hsep h
      have h126 : (adjacencyStep (encodeInput I ε) s).nr 126=1 := by
        rw [adjacencyStep_register _ s 126 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hone
      have h163 : (adjacencyStep (encodeInput I ε) s).nr 163=heads := by
        rw [adjacencyStep_register _ s 163 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hh
      have h164 : (adjacencyStep (encodeInput I ε) s).nr 164=links := by
        rw [adjacencyStep_register _ s 164 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hl
      have hrec := ih (adjacencyStep (encodeInput I ε) s) (count+1) h126
        (by simp [hcount]) (by simp [hp]; omega) h163 h164 (by omega) hstep
      simpa only [adjacencyScanResult,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hrec

private theorem adjacencyStep_memory_outside (I : Instance) (ε : ℝ) (s : Store)
    (count heads links a : ℕ) (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hk : count<I.graph.edges.length)
    (hahead : a<heads ∨ heads+I.graph.n≤a)
    (halink : a<links ∨ links+I.graph.edges.length≤a) :
    (adjacencyStep (encodeInput I ε) s).nm a = s.nm a := by
  have hv := (edgeAt_valid I count hk).1
  have htail : (encodeInput I ε).naturals (s.nr 162) = (edgeAt I count).1 := by
    rw [hp]
    apply encodeInput_edge_left I ε count (edgeAt I count)
    simp only [edgeAt,List.getElem?_eq_getElem hk,Option.getD_some]
  change (adjacencyResult (adjacencyLoaded (encodeInput I ε) s)).nm a = s.nm a
  apply adjacencyResult_memory_frame
  · simp only [adjacencyLoaded,Function.update_self,Function.update_of_ne (by decide : 163≠161)]
    rw [hh,htail]
    omega
  · simp only [adjacencyLoaded,Function.update_of_ne (by decide : 164≠161),
      Function.update_of_ne (by decide : 160≠161)]
    rw [hl,hcount]
    omega

private theorem adjacencyScanResult_memory_outside (I : Instance) (ε : ℝ) (remaining : ℕ)
    (s : Store) (count heads links a : ℕ)
    (hcount : s.nr 160=count) (hp : s.nr 162=3+2*count)
    (hh : s.nr 163=heads) (hl : s.nr 164=links)
    (hvalid : count+remaining≤I.graph.edges.length)
    (hahead : a<heads ∨ heads+I.graph.n≤a)
    (halink : a<links ∨ links+I.graph.edges.length≤a) :
    (adjacencyScanResult (encodeInput I ε) remaining s).nm a = s.nm a := by
  induction remaining generalizing s count with
  | zero => rfl
  | succ n ih =>
      have h163 : (adjacencyStep (encodeInput I ε) s).nr 163=heads := by
        rw [adjacencyStep_register _ s 163 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hh
      have h164 : (adjacencyStep (encodeInput I ε) s).nr 164=links := by
        rw [adjacencyStep_register _ s 164 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]; exact hl
      change (adjacencyScanResult (encodeInput I ε) n (adjacencyStep (encodeInput I ε) s)).nm a = _
      rw [ih (adjacencyStep (encodeInput I ε) s) (count+1) (by simp [hcount])
        (by simp [hp]; omega) h163 h164 (by omega)]
      exact adjacencyStep_memory_outside I ε s count heads links a hcount hp hh hl
        (by omega) hahead halink

private theorem adjacencyScanCmd_correct (I : Instance) (ε : ℝ) (s : Store) (heads links : ℕ)
    (hm : s.nr 122=I.graph.edges.length) (hone : s.nr 126=1) (htwo : s.nr 127=2)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hsep : heads+I.graph.n≤links)
    (hzero : ∀ v<I.graph.n, s.nm (heads+v)=0) :
    ∃ out, Run (encodeInput I ε) adjacencyScanCmd s out (11*I.graph.edges.length+3) ∧
      AdjacencyPrefix I I.graph.edges.length heads links out.nm ∧
      out.rr=s.rr ∧ out.rm=s.rm ∧
      (∀ a, (a<heads ∨ heads+I.graph.n≤a) →
        (a<links ∨ links+I.graph.edges.length≤a) → out.nm a=s.nm a) ∧
      (∀ r, r≠160 → r≠161 → r≠162 → r≠165 → r≠166 → r≠167 → r≠168 → out.nr r=s.nr r) := by
  let out := adjacencyScanResult (encodeInput I ε) I.graph.edges.length (adjacencyPrepared s)
  have hrun := adjacencyScanCmd_run (encodeInput I ε) s hone htwo
  rw [hm] at hrun
  have hprefix := adjacencyScanResult_prefix I ε I.graph.edges.length (adjacencyPrepared s)
    0 heads links (by simpa [adjacencyPrepared] using hone) (by simp [adjacencyPrepared])
    (by simp [adjacencyPrepared]) (by simpa [adjacencyPrepared] using hh)
    (by simpa [adjacencyPrepared] using hl) (by omega) hsep (adjacencyPrefix_zero I heads links s.nm hzero)
  have hreals := adjacencyScanResult_reals (encodeInput I ε) I.graph.edges.length (adjacencyPrepared s)
  refine ⟨out,hrun,by simpa only [Nat.zero_add] using hprefix,hreals.1,hreals.2,?_,?_⟩
  · intro a ha hb
    exact adjacencyScanResult_memory_outside I ε I.graph.edges.length (adjacencyPrepared s)
      0 heads links a (by simp [adjacencyPrepared]) (by simp [adjacencyPrepared])
      (by simpa [adjacencyPrepared] using hh) (by simpa [adjacencyPrepared] using hl)
      (by omega) ha hb
  · intro r h160 h161 h162 h165 h166 h167 h168
    rw [adjacencyScanResult_register _ _ _ r h160 h161 h162 h165 h166 h167 h168]
    simp [adjacencyPrepared,h160,h162]

private theorem standalone_Mission_RAMAdjacencyScan__map_filter_compat {α β : Type} (f : α→β) (p : β→Bool) (xs : List α) :
    (xs.filter (fun x=>p (f x))).map f = (xs.map f).filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases hp : p (f x)=true <;> simp [hp,ih]

private theorem edgeAt_map_range (I : Instance) :
    (List.range I.graph.edges.length).map (edgeAt I) = I.graph.edges := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [edgeAt,List.getElem?_eq_getElem hj]

private theorem outgoingIndices_edges (I : Instance) (v : ℕ) :
    (outgoingIndices I I.graph.edges.length v).map (edgeAt I) = (outgoingEdges I v).reverse := by
  rw [outgoingIndices,List.map_reverse,
    standalone_Mission_RAMAdjacencyScan__map_filter_compat (edgeAt I) (fun e : ℕ×ℕ=>e.1==v) (List.range I.graph.edges.length),
    edgeAt_map_range]
  rfl

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem TreeScanInvariant.transfer {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {u : ℕ} {S : TreeQueue} {s t : Store} (h : TreeScanInvariant E mode u S s)
    (hf : TreeIteratorScratch s t) : TreeScanInvariant E mode u S t := by
  refine ⟨h.memory.congr (hf.2.2.2 141 (by decide) (by decide) (by decide))
    (hf.2.2.2 142 (by decide) (by decide) (by decide))
    (hf.2.2.2 143 (by decide) (by decide) (by decide)) hf.2.1 hf.2.2.1,
    h.registers.transfer ?_ (congrFun hf.1 170), h.math,
    (hf.2.2.2 262 (by decide) (by decide) (by decide)).trans h.vertex,
    (congrFun hf.1 260).trans h.key⟩
  intro r hr
  simp only [treeNatConstants,Finset.mem_insert,Finset.mem_singleton] at hr
  exact hf.2.2.2 r (by omega) (by omega) (by omega)

private theorem TreeAllocation.link_protected {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (k : ℕ) (hk : k < I.graph.edges.length) :
    TreeProtected E mode (E.links+k) := by
  have hLW := E.links_winner
  have hMA := E.map_le_array
  have hAL := E.array_links
  refine ⟨Or.inl (by omega), ?_⟩
  intro v hv
  have ht := E.target_lt_map mode v (activeVertices_valid I v hv)
  omega

private theorem TreeAllocation.graph_protected {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (a : ℕ) (hlo : E.map ≤ a) (hhi : a < E.W) :
    TreeProtected E mode a := by
  refine ⟨Or.inl hhi, ?_⟩
  intro v hv
  have ht := E.target_lt_map mode v (activeVertices_valid I v hv)
  omega

private theorem AdjacencyPrefix.protected_frame {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) {s t : Store}
    (h : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm)
    (hf : ∀ a, TreeProtected E mode a → t.nm a = s.nm a) :
    AdjacencyPrefix I I.graph.edges.length E.heads E.links t.nm := by
  intro v hv
  have hMH := E.map_heads
  have hHA := E.heads_array
  have hAW := E.array_end_le_winner
  have hh : t.nm (E.heads+v) = s.nm (E.heads+v) :=
    hf _ (E.graph_protected mode _ (by omega) (by omega))
  rw [hh]
  apply (h v hv).frame
  intro e he
  exact hf _ (E.link_protected mode e (outgoingIndices_lt I _ v e he))

private theorem outgoingIndices_valid (I : Instance) (u e : ℕ)
    (he : e ∈ outgoingIndices I I.graph.edges.length u) :
    ∃ v, I.graph.edges[e]? = some (u,v) := by
  have hk := outgoingIndices_lt I I.graph.edges.length u e he
  let edge := I.graph.edges[e]
  have hget : I.graph.edges[e]? = some edge := List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩
  have hleft : edge.1 = u := by
    simpa [outgoingIndices, edgeAt, hget] using (List.mem_filter.mp (List.mem_reverse.mp he)).2
  refine ⟨edge.2, ?_⟩
  have hp : (u,edge.2) = edge := by rw [←hleft]
  rw [hp]
  exact hget

private theorem treeScan_run {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (u : ℕ) (S : TreeQueue) (s : Store) (es : List ℕ) (token : ℕ)
    (hchain : AdjacencyChain s.nm E.links token es)
    (hvalid : ∀ e ∈ es, ∃ v, I.graph.edges[e]? = some (u,v))
    (hInv : TreeScanInvariant E mode u S s) (htoken : s.nr 278 = token) :
    ∃ out steps, Run (encodeInput I ε) treeAdjacencyLoop s out steps ∧
      TreeScanInvariant E mode u
        (es.foldl (fun T e => treeRelax I (mode.allow I) (mode.weight I) u T (edgeAt I e)) S) out ∧
      out.nr 278 = 0 ∧ steps ≤ (19*Nat.clog 2 (2*E.B)+46)*es.length+1 ∧
      (∀ a, TreeProtected E mode a → out.nm a = s.nm a ∧ out.rm a = s.rm a) := by
  let valid := fun (e : ℕ) => ∃ v : ℕ, I.graph.edges[e]? = some (u,v)
  let step := fun (T : TreeQueue) (e : ℕ) => treeRelax I (mode.allow I) (mode.weight I) u T (edgeAt I e)
  have hedge : ∀ T e t, valid e → TreeScanInvariant E mode u T t → t.nr 265=e →
      ∃ out n, Run (encodeInput I ε) treeRelaxEdgeCmd t out n ∧
        TreeScanInvariant E mode u (step T e) out ∧ n ≤ 19*Nat.clog 2 (2*E.B)+40 ∧
        (∀ k, valid k → out.nm (E.links+k)=t.nm (E.links+k)) ∧
        (∀ a, TreeProtected E mode a → out.nm a=t.nm a ∧ out.rm a=t.rm a) := by
    intro T e t he hi hindex
    obtain ⟨v, hv⟩ := he
    obtain ⟨out,n,hrun,hn,hm,hr,hf⟩ := treeEdge_correct E mode T ε t u v
      hi.memory hi.registers (by simpa only [hindex] using hv) hi.math.removed
      hi.math.policy hi.math.source_zero hi.vertex hi.key
    have hem := List.mem_of_getElem? hv
    have hvn := (I.graph.endpoints (u,v) hem).2
    have hed : edgeAt I e=(u,v) := by simp [edgeAt,hv]
    have hout : TreeScanInvariant E mode u (step T e) out := by
      rw [show step T e = treeRelax I (mode.allow I) (mode.weight I) u T (u,v) by
        change treeRelax I (mode.allow I) (mode.weight I) u T (edgeAt I e) = _
        rw [hed]]
      refine ⟨hm,hr,hi.math.step (fun a b => (mode.resource I a b).coe_nonneg) (u,v) hem,
        (hrun.nat_frame 262 (by decide)).trans hi.vertex,?_⟩
      rw [hrun.real_frame 260 (by decide),hi.key]
      unfold sentinelKey
      rw [treeRelax_outside I (mode.allow I) (mode.weight I) u u T (u,v) hi.math.removed]
    have hprotect : ∀ a, TreeProtected E mode a → out.nm a=t.nm a ∧ out.rm a=t.rm a := by
      intro a ha
      exact hf a ha.1 (ha.2 v (activeVertices_edge_right I u v hem))
    refine ⟨out,n,hrun,hout,hn,?_,hprotect⟩
    intro k hk
    obtain ⟨w,hw⟩ := hk
    exact (hprotect _ (E.link_protected mode k (List.getElem?_eq_some_iff.mp hw).choose)).1
  obtain ⟨out,n,hrun,hout,ht,hcost,hframe⟩ := treeAdjacencyLoop_run_of_edge_contract
    (encodeInput I ε) E.links (19*Nat.clog 2 (2*E.B)+40) valid (TreeProtected E mode)
    step (TreeScanInvariant E mode u) (fun _ _ _ h hf => h.transfer hf) hedge
    es S s token hchain hvalid hInv hInv.registers.zero hInv.registers.one
    hInv.registers.links htoken
  exact ⟨out,n,hrun,hout,ht,by simpa only [Nat.add_assoc] using hcost,hframe⟩

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured Queue

private theorem standalone_Mission_RAMTreeExtractRefinement__queue_update_nat_high {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input updateLeaf s out steps) (hr : 11 ≤ r) : out.nr r=s.nr r := by
  apply h.nat_frame
  simp [updateLeaf,writeLeaf,parentHop,repairAncestors,repairBody,refreshNode,
    loadChildren,selectChild,storeLeft,storeRight,Queue.atoms,Cmd.natWrites,Atom.natWrites]
  omega

private theorem standalone_Mission_RAMTreeExtractRefinement__queue_update_real_high {input : RAMInput} {s out : Store} {steps r : ℕ}
    (h : Run input updateLeaf s out steps) (hr : 2 ≤ r) : out.rr r=s.rr r := by
  apply h.real_frame
  simp [updateLeaf,writeLeaf,parentHop,repairAncestors,repairBody,refreshNode,
    loadChildren,selectChild,storeLeft,storeRight,Queue.atoms,Cmd.realWrites,Atom.realWrites]
  omega

private theorem treeExtract_refines (input : RAMInput) (B height : ℕ)
    (xs q : List ℕ) (key : ℕ→ℝ) (s : Store)
    (hB : B=2^height) (hfit : xs.length ≤ B)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hne : q ≠ [])
    (hp : s.nr 1+2*B ≤ s.nr 2 ∧ s.nr 3=0 ∧
      ∀ node < 2*B,s.nm (s.nr 2+node)=node/2)
    (hone : s.nr 4=1) (hbase : s.nr 170=B)
    (harray : ∀ k v, xs[k]?=some v → s.nm (s.nr 171+k)=v)
    (hrep : Represents B (s.nr 1) (activeLeaf xs q key B) s) :
    let u := firstMin key q 0
    ∃ out cost, Run input treeExtract s out cost ∧
      cost ≤ 19*Nat.clog 2 (2*B)+15 ∧ ParentLayout (2*B) out ∧
      Represents B (s.nr 1) (activeLeaf xs (q.erase u) key B) out ∧
      WinnerFrame (s.nr 1) (2*B) s out ∧
      out.nr 0=0 ∧ (∀ r,0 < r → r < 5 → out.nr r=s.nr r) ∧
      out.nr 260=xs.idxOf u+1 ∧ out.nr 261=xs.idxOf u ∧
      out.nr 262=u ∧ out.rr 260=key u := by
  dsimp only
  let u := firstMin key q 0
  have hBpos : 0 < B := by rw [hB]; positivity
  have huq : u∈q := firstMin_mem key q 0 hne
  have huxs : u∈xs := hq.subset huq
  have hidx : xs.idxOf u < xs.length := List.idxOf_lt_length_of_mem huxs
  have hdecode : (readRecord s (s.nr 1+1)).decode=some (vertexRecord xs key u) := by
    rw [hrep 1 (by omega),hB]
    exact activeLeaf_firstMin xs q key height hxs hq (by simpa only [hB] using hfit) 0 hne
  have hnonzero : (readRecord s (s.nr 1+1)).token ≠ 0 := by
    intro hz
    simp [Record.decode,hz] at hdecode
  have hrecord : readRecord s (s.nr 1+1)=vertexRecord xs key u := by
    simpa only [Record.decode,if_neg hnonzero,Option.some.injEq] using hdecode
  have htoken : s.nm (s.nr 1+1)=xs.idxOf u+1 := congrArg Record.token hrecord
  have hkey : s.rm (s.nr 1+1)=key u := congrArg Record.key hrecord
  have hvertex : s.nm (s.nr 171+xs.idxOf u)=u :=
    harray _ _ (List.getElem?_idxOf huxs)
  have hn0 : (treeExtractPrepared s).nr 0=B+xs.idxOf u := by
    simp [treeExtractPrepared,hone,hbase,htoken]
  have hn10 : (treeExtractPrepared s).nr 10=0 := by simp [treeExtractPrepared]
  have hr2 : (treeExtractPrepared s).rr 2=key u := by
    simp [treeExtractPrepared,hone,hkey]
  have hprepared : ParentLayout (2*B) (treeExtractPrepared s) := by
    refine ⟨by rw [hn0]; omega,?_,?_,?_⟩
    · simpa only [treeExtractPrepared_header s 1 (by decide) (by decide),
        treeExtractPrepared_header s 2 (by decide) (by decide)] using hp.1
    · simpa only [treeExtractPrepared_header s 3 (by decide) (by decide)] using hp.2.1
    · intro a ha
      change s.nm ((treeExtractPrepared s).nr 2+a)=a/2
      rw [treeExtractPrepared_header s 2 (by decide) (by decide)]
      exact hp.2.2 a ha
  have hrepPrepared : Represents B ((treeExtractPrepared s).nr 1)
      (activeLeaf xs q key B) (treeExtractPrepared s) := by
    intro node hn
    change readRecord s ((treeExtractPrepared s).nr 1+node)=_
    rw [treeExtractPrepared_header s 1 (by decide) (by decide)]
    exact hrep node hn
  obtain ⟨out,cost,hrun,hcost,hzero,hheaders,hparents,hout,hframe⟩ :=
    updateLeaf_refines input B (activeLeaf xs q key B) (treeExtractPrepared s)
      hprepared (by simpa only [treeExtractPrepared_header s 4 (by decide) (by decide)] using hone)
      (by rw [hn0]; omega) (by rw [hn0]; omega) hrepPrepared
  have hnew : Represents B (s.nr 1) (activeLeaf xs (q.erase u) key B) out := by
    rw [activeLeaf_delete_vertex xs q key B u hxs (List.Nodup.sublist hq hxs) huxs]
    simpa only [treeExtractPrepared_header s 1 (by decide) (by decide),hn0,hn10,hr2] using hout
  have hfullFrame : WinnerFrame (s.nr 1) (2*B) s out := by
    intro a ha
    have hf := hframe a (by simpa only [treeExtractPrepared_header s 1 (by decide) (by decide)] using ha)
    exact hf
  have hprefix := Structured.run_atoms input treeExtractAtoms s
  rw [treeExtractAtoms_eval] at hprefix
  refine ⟨out,9+cost,Run.seq hprefix hrun,by omega,hparents,hnew,hfullFrame,hzero,?_,?_,?_,?_,?_⟩
  · intro r hr hr'
    exact (hheaders r hr hr').trans (treeExtractPrepared_header s r hr hr')
  · rw [standalone_Mission_RAMTreeExtractRefinement__queue_update_nat_high hrun (by decide)]
    simp [treeExtractPrepared,hone,htoken,u]
  · rw [standalone_Mission_RAMTreeExtractRefinement__queue_update_nat_high hrun (by decide)]
    simp [treeExtractPrepared,hone,htoken,u]
  · rw [standalone_Mission_RAMTreeExtractRefinement__queue_update_nat_high hrun (by decide)]
    simp [treeExtractPrepared,hone,htoken,hvertex,u]
  · rw [standalone_Mission_RAMTreeExtractRefinement__queue_update_real_high hrun (by decide)]
    simp [treeExtractPrepared,hone,hkey,u]

private theorem treeExtract_high_register (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input treeExtract s out cost) (hr : 11 ≤ r)
    (h260 : r ≠ 260) (h261 : r ≠ 261) (h262 : r ≠ 262) : out.nr r=s.nr r := by
  apply h.nat_frame
  simp [treeExtract,treeExtractAtoms,Cmd.atoms,updateLeaf,writeLeaf,parentHop,
    repairAncestors,repairBody,refreshNode,loadChildren,selectChild,storeLeft,storeRight,
    Queue.atoms,Cmd.natWrites,Atom.natWrites,h260,h261,h262]
  omega

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem sentinelKey_treeSettle (top : ℝ) (S : TreeQueue) (u : ℕ) :
    sentinelKey top (treeSettle S u).tree=sentinelKey top S.tree := by
  funext v
  by_cases hv : v=u <;> simp [sentinelKey,treeSettle,hv]

private theorem treeSettle_parent_unchanged (S : TreeQueue) (u v : ℕ) :
    ((treeSettle S u).tree v).parent=(S.tree v).parent := by
  by_cases hv : v=u <;> simp [treeSettle,hv]

private theorem treeExtract_registers (I : Instance) (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s out : Store) (cost : ℕ)
    (hR : E.Registers mode s) (h : Run input treeExtract s out cost) :
    E.Registers mode out :=
  hR.after_run h (by decide) (by decide)

private theorem treeSettle_registers (I : Instance) (E : TreeAllocation I) (mode : TreeMode)
    (input : RAMInput) (s out : Store) (cost : ℕ)
    (hR : E.Registers mode s) (h : Run input treeSettleCmd s out cost) :
    E.Registers mode out :=
  hR.after_run h (by decide) (by decide)

private theorem treeSettle_run (input : RAMInput) (I : Instance) (E : TreeAllocation I)
    (mode : TreeMode) (S : TreeQueue) (s : Store)
    (hM : E.Memory mode S s) (hR : E.Registers mode s) (hne : S.queue ≠ [])
    (hfinite : ∀ v d,(S.tree v).distance=some d → d < mode.top I) :
    ∃ out cost, Run input treeSettleCmd s out cost ∧
      cost ≤ 19*Nat.clog 2 (2*E.B)+21 ∧
      E.Memory mode (treeSettle S (treePick S)) out ∧ E.Registers mode out ∧
      out.nr 262=treePick S ∧ out.rr 260=sentinelKey (mode.top I) S.tree (treePick S) ∧
      (∀ a,(a < E.W ∨ E.W+2*E.B ≤ a) → out.nm a=s.nm a) ∧
      (∀ a,(a < E.W ∨ E.W+2*E.B ≤ a) →
        a ≠ targetAddress (treePick S)+mode.offset → out.rm a=s.rm a) := by
  let u := treePick S
  have huq : u∈S.queue := treePick_mem S hne
  have huxs : u∈activeVertices I := hM.queued.subset huq
  have huvalid : u < I.graph.n := hM.active.valid u huxs
  have hpick : firstMin (sentinelKey (mode.top I) S.tree) S.queue 0=u :=
    (treePick_eq_sentinel_firstMin (mode.top I) S hfinite).symm
  have hparent : s.nr 1+2*E.B ≤ s.nr 2 ∧ s.nr 3=0 ∧
      ∀ node < 2*E.B,s.nm (s.nr 2+node)=node/2 := by
    refine ⟨?_,hR.zero,?_⟩
    · simpa only [hR.winner,hR.parent] using E.winner_parent
    · intro node hn
      rw [hR.parent]
      exact hM.links node hn
  have harray : ∀ k v,(activeVertices I)[k]?=some v → s.nm (s.nr 171+k)=v := by
    intro k v hv
    rw [hR.saved_array]
    exact hM.active.value k v hv
  have hrep : Queue.Represents E.B (s.nr 1)
      (Queue.activeLeaf (activeVertices I) S.queue (sentinelKey (mode.top I) S.tree) E.B) s := by
    simpa only [hR.winner] using hM.heap
  obtain ⟨popped,steps,hextract,hcost,hparents,hheap,hframe,hzero,hheaders,
      htoken,hordinal,hvertex,hkey⟩ :=
    treeExtract_refines input E.B E.height (activeVertices I) S.queue
      (sentinelKey (mode.top I) S.tree) s E.capacity E.fit
      (activeVertices_nodup I) hM.queued hne hparent hR.one hR.saved_capacity harray hrep
  simp only [hpick,hR.winner] at hheap hframe hvertex hkey
  have hRp := treeExtract_registers I E mode input s popped steps hR hextract
  let out := treeRecordedDistance popped
  have hrecord := treeRecordDistance_run input popped
  have hrun : Run input treeSettleCmd s out (steps+6) := Run.seq hextract hrecord
  have hRf := treeSettle_registers I E mode input s out (steps+6) hR hrun
  have haddr : targetAddress u+mode.offset < E.W := E.target_lt_winner mode u huvalid
  have hnat : ∀ a,(a < E.W ∨ E.W+2*E.B ≤ a) → out.nm a=s.nm a := by
    intro a ha
    exact (hframe a ha).1
  have hreal : ∀ a,(a < E.W ∨ E.W+2*E.B ≤ a) →
      a ≠ targetAddress u+mode.offset → out.rm a=s.rm a := by
    intro a ha hneq
    have hf := (treeRecordedDistance_frame popped a
      (by simpa only [hvertex,hRp.offset] using hneq)).2
    exact hf.trans (hframe a ha).2
  have hvalue : out.rm (targetAddress u+mode.offset)=sentinelKey (mode.top I) S.tree u := by
    simpa only [hvertex,hRp.offset,hkey] using treeRecordedDistance_value popped
  have hMemory : E.Memory mode (treeSettle S u) out := by
    constructor
    · apply hM.active.congr
      · exact hRf.map.trans hR.map.symm
      · exact hRf.array.trans hR.array.symm
      · exact hRf.active_count.trans hR.active_count.symm
      · intro v hv
        apply hnat _ (Or.inl ?_)
        have h1 := E.map_heads
        have h2 := E.heads_array
        have h3 := E.array_end_le_winner
        omega
      · intro k hk
        apply hnat _ (Or.inl ?_)
        have h1 := E.array_end_le_winner
        have h2 := hM.active.length_le
        omega
    · exact List.erase_sublist.trans hM.queued
    · change Queue.Represents E.B E.W
        (Queue.activeLeaf (activeVertices I) (S.queue.erase u)
          (sentinelKey (mode.top I) (treeSettle S u).tree) E.B) out
      rw [sentinelKey_treeSettle]
      intro node hn
      have hneq : E.W+node ≠ targetAddress u+mode.offset := by omega
      have hf := (treeRecordedDistance_frame popped (E.W+node)
        (by simpa only [hvertex,hRp.offset] using hneq)).2
      have hread : Queue.readRecord out (E.W+node)=Queue.readRecord popped (E.W+node) := by
        change (⟨popped.nm (E.W+node),(treeRecordedDistance popped).rm (E.W+node)⟩ : Queue.Record)=_
        rw [hf]
        rfl
      rw [hread]
      exact hheap node hn
    · intro node hn
      rw [hnat _ (Or.inr (by have := E.winner_parent; omega))]
      exact hM.links node hn
    · intro v hv
      rw [hnat _ (Or.inl (E.target_lt_winner mode v (hM.active.valid v hv))),
        treeSettle_parent_unchanged]
      exact hM.parents v hv
    · intro v hv hvq
      rw [sentinelKey_treeSettle]
      by_cases hvu : v=u
      · simpa only [hvu] using hvalue
      · have hvold : v∉S.queue := by
          intro hq
          exact hvq ((List.mem_erase_of_ne hvu).mpr hq)
        have hneq : targetAddress v+mode.offset ≠ targetAddress u+mode.offset := by
          simp only [targetAddress]
          omega
        rw [hreal _ (Or.inl (E.target_lt_winner mode v (hM.active.valid v hv))) hneq]
        exact hM.settled v hv hvold
  refine ⟨out,steps+6,hrun,by omega,hMemory,hRf,?_,?_,hnat,hreal⟩
  · change (treeRecordedDistance popped).nr 262=treePick S
    simp [treeRecordedDistance,hvertex,u]
  · change popped.rr 260=sentinelKey (mode.top I) S.tree (treePick S)
    simpa only [u] using hkey

private theorem treeSettle_counter277 (input : RAMInput) (s out : Store) (cost : ℕ)
    (h : Run input treeSettleCmd s out cost) : out.nr 277=s.nr 277 :=
  h.nat_frame 277 (by decide)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

private theorem outgoingWork_erase (I : Instance) (vertices : List ℕ) (u : ℕ) (hu : u ∈ vertices) :
    (outgoingEdges I u).length + outgoingWork I (vertices.erase u) = outgoingWork I vertices :=
  List.sum_map_erase (fun v => (outgoingEdges I v).length) hu

private theorem standalone_Mission_OutgoingWork__indicator_sum (xs : List ℕ) (u : ℕ) :
    (xs.map (fun v => if u = v then 1 else 0)).sum = xs.count u := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
      by_cases h : u = v
      · subst v
        simp [ih, Nat.add_comm]
      · simp [h, Ne.symm h, ih]

private theorem standalone_Mission_OutgoingWork__outgoing_filter_count (edges : List (ℕ × ℕ)) (vertices : List ℕ)
    (hnd : vertices.Nodup) (hs : ∀ e ∈ edges, e.1 ∈ vertices) :
    (vertices.map (fun u => (edges.filter (fun e => e.1 == u)).length)).sum = edges.length := by
  induction edges generalizing vertices with
  | nil => simp
  | cons e es ih =>
      have he : e.1 ∈ vertices := hs e (by simp)
      have htail : ∀ f ∈ es, f.1 ∈ vertices := by
        intro f hf
        exact hs f (by simp [hf])
      have hpoint (u : ℕ) :
          ((e :: es).filter (fun f => f.1 == u)).length =
            (if e.1 = u then 1 else 0) + (es.filter (fun f => f.1 == u)).length := by
        by_cases h : e.1 = u <;> simp [h, Nat.add_comm]
      simp_rw [hpoint]
      rw [List.sum_map_add, standalone_Mission_OutgoingWork__indicator_sum, List.count_eq_one_of_mem hnd he, ih vertices hnd htail]
      simp [Nat.add_comm]

private theorem outgoingWork_active (I : Instance) :
    outgoingWork I (activeVertices I) = I.graph.edges.length := by
  unfold outgoingWork outgoingEdges
  exact standalone_Mission_OutgoingWork__outgoing_filter_count I.graph.edges (activeVertices I) (activeVertices_nodup I)
    (fun e he => activeVertices_edge_left I e.1 e.2 he)

private theorem outgoingWork_settle (I : Instance) (S : LayerState) (i j u : ℕ) (hu : u ∈ S.queue) :
    (outgoingEdges I u).length + outgoingWork I (settleState S i j u).queue =
      outgoingWork I S.queue := outgoingWork_erase I S.queue u hu

private theorem queueRun_succ_front (A : InnerInput) (i j n : ℕ) (S : LayerState) :
    queueRun A i j (n+1) S = queueRun A i j n (popLayer A i j S) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [queueRun_succ A i j (n+1) S,ih,queueRun_succ]

private theorem popLayer_nextRank_of_ne (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue≠[]) : (popLayer A i j S).nextRank=S.nextRank+1 := by
  rw [popLayer_eq_relaxAll A i j S hne,relaxAll_nextRank]
  rfl

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem standalone_Mission_RAMTreePop__seq_attach {input : RAMInput} {a b c : Cmd} {s t out : Store} {n m : ℕ}
    (hab : Run input (.seq a b) s t n) (hc : Run input c t out m) :
    Run input (.seq a (.seq b c)) s out (n+m) := by
  cases hab with
  | seq ha hb => simpa only [Nat.add_assoc] using Run.seq ha (Run.seq hb hc)

private theorem treeHeadStore_token (input : RAMInput) (s : Store) :
    (treeHeadStore input s).nr 278 = s.nm (s.nr 137+s.nr 262) := by
  simp [treeHeadStore, treeAdjacencyHead, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat]

private theorem treePopCmd_run {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (S : TreeQueue) (s : Store)
    (hm : E.Memory mode S s) (hr : E.Registers mode s) (hne : S.queue ≠ [])
    (hp : TreePolicy I (mode.allow I) (mode.weight I) S)
    (hn : ∀ v, 0 ≤ treeDist S.tree v) (hs : (S.tree I.source).distance = some 0)
    (hfinite : ∀ v d, (S.tree v).distance=some d → d < mode.top I)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm) :
    ∃ out steps, Run (encodeInput I ε) treePopCmd s out steps ∧
      E.Memory mode (treePop I (mode.allow I) (mode.weight I) S) out ∧
      E.Registers mode out ∧ out.nr 277 = s.nr 277+1 ∧
      steps ≤ 19*Nat.clog 2 (2*E.B)+25 +
        (19*Nat.clog 2 (2*E.B)+46)*(outgoingEdges I (treePick S)).length ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a) := by
  let input := encodeInput I ε
  let u := treePick S
  have hu : u ∈ S.queue := treePick_mem S hne
  have hua : u ∈ activeVertices I := hm.queued.subset hu
  have hun : u < I.graph.n := activeVertices_valid I u hua
  have hq : S.queue.Nodup := (activeVertices_nodup I).sublist hm.queued
  obtain ⟨settled,nS,hSet,hns,hmS,hrS,huS,hkeyS,hfnS,hfrS⟩ :=
    treeSettle_run input I E mode S s hm hr hne hfinite
  have hSetFrame : ∀ a, TreeProtected E mode a →
      settled.nm a=s.nm a ∧ settled.rm a=s.rm a := by
    intro a ha
    exact ⟨hfnS a ha.1,hfrS a ha.1 (ha.2 u hua)⟩
  have hAdjS := hAdj.protected_frame E mode (fun a ha => (hSetFrame a ha).1)
  let head := treeHeadStore input settled
  have hHead : Run input (.atoms treeAdjacencyHead) settled head 2 :=
    run_atoms input treeAdjacencyHead settled
  have hmH : E.Memory mode (treeSettle S u) head :=
    hmS.after_readonly hHead (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrH : E.Registers mode head := hrS.after_run hHead (by decide) (by decide)
  have hmath := TreeScanMath.start I (mode.allow I) (mode.weight I) S u hu hq hp hn hs
  have hkeyH : head.rr 260 = sentinelKey (mode.top I) (treeSettle S u).tree u := by
    rw [hHead.real_frame 260 (by decide), hkeyS]
    simp [sentinelKey, treeSettle, u]
  have hiH : TreeScanInvariant E mode u (treeSettle S u) head :=
    ⟨hmH,hrH,hmath,(hHead.nat_frame 262 (by decide)).trans huS,hkeyH⟩
  have htoken : head.nr 278 = settled.nm (E.heads+u) := by
    rw [treeHeadStore_token,hrS.heads,huS]
  have hchain : AdjacencyChain head.nm E.links (settled.nm (E.heads+u))
      (outgoingIndices I I.graph.edges.length u) := hAdjS u hun
  obtain ⟨scanned,nE,hScan,hiE,hzero,hnE,hfE⟩ := treeScan_run E mode ε u (treeSettle S u) head
    (outgoingIndices I I.graph.edges.length u) _ hchain
    (fun e he => outgoingIndices_valid I u e he) hiH htoken
  have hfold : (outgoingIndices I I.graph.edges.length u).foldl
      (fun T e => treeRelax I (mode.allow I) (mode.weight I) u T (edgeAt I e)) (treeSettle S u) =
      treePop I (mode.allow I) (mode.weight I) S := by
    rw [treePop_reversed_refinement I (mode.allow I) (mode.weight I) S hne]
    rw [←outgoingIndices_edges I u, List.foldl_map]
  rw [hfold] at hiE
  have hlen : (outgoingIndices I I.graph.edges.length u).length = (outgoingEdges I u).length := by
    simpa using congrArg List.length (outgoingIndices_edges I u)
  rw [hlen] at hnE
  dsimp only [u] at hnE
  let out := treePopIncremented input scanned
  have hInc : Run input (.atom ⟨.natOp .add 277 277 4,trivial⟩) scanned out 1 := Run.atom _ _
  have hmout := hiE.memory.after_readonly hInc (by decide) (by decide) (by decide) (by decide) (by decide)
  have hrout := hiE.registers.after_run hInc (by decide) (by decide)
  have htail := Run.seq hHead (Run.seq hScan hInc)
  have hrun : Run input treePopCmd s out (nS+(2+(nE+1))) := standalone_Mission_RAMTreePop__seq_attach hSet htail
  have hcounter : out.nr 277=s.nr 277+1 := by
    change scanned.nr 277+scanned.nr 4=s.nr 277+1
    rw [hiE.registers.one,hScan.nat_frame 277 (by decide),hHead.nat_frame 277 (by decide),
      hSet.nat_frame 277 (by decide)]
  have hframe : ∀ a, TreeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a := by
    intro a ha
    have hF := hfE a ha
    have hS := hSetFrame a ha
    exact ⟨hF.1.trans hS.1,hF.2.trans hS.2⟩
  exact ⟨out,_,hrun,hmout,hrout,hcounter,by omega,
    hAdj.protected_frame E mode (fun a ha => (hframe a ha).1),hframe⟩

private theorem treePop_outgoingWork (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (S : TreeQueue) (hne : S.queue ≠ []) :
    (outgoingEdges I (treePick S)).length + outgoingWork I (treePop I allow w S).queue =
      outgoingWork I S.queue := by
  rw [treePop_eq_relaxAll I allow w S hne, treeRelaxAll_queue]
  exact outgoingWork_erase I S.queue (treePick S) (treePick_mem S hne)

private theorem treeLoop_run {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (remaining k : ℕ) (s : Store)
    (hend : k+remaining=(activeVertices I).length)
    (hm : E.Memory mode (treeState I mode k) s) (hr : E.Registers mode s)
    (hcounter : s.nr 277=k)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm) :
    ∃ out steps, Run (encodeInput I ε) treeLoopCmd s out steps ∧
      E.Memory mode (treeState I mode (activeVertices I).length) out ∧
      E.Registers mode out ∧ out.nr 277=(activeVertices I).length ∧
      steps ≤ (19*Nat.clog 2 (2*E.B)+27)*remaining +
        (19*Nat.clog 2 (2*E.B)+46)*outgoingWork I (treeState I mode k).queue+1 ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a) := by
  induction remaining generalizing k s with
  | zero =>
      have hk : k=(activeVertices I).length := by omega
      rw [hk] at hm hcounter
      refine ⟨s,1,Run.loopFalse ?_,hm,hr,hcounter,by omega,hAdj,?_⟩
      · simp [Guard.eval,natTest,hcounter,hr.count]
      · intro a ha; exact ⟨rfl,rfl⟩
  | succ remaining ih =>
      have hk : k < (activeVertices I).length := by omega
      have hne : (treeState I mode k).queue ≠ [] := by
        have hl := treeRun_queue_length I (mode.allow I) (mode.weight I) k (treeInitial I)
        change (treeState I mode k).queue.length = (activeVertices I).length-k at hl
        intro he
        rw [he] at hl
        simp only [List.length_nil] at hl
        omega
      have hp : TreePolicy I (mode.allow I) (mode.weight I) (treeState I mode k) :=
        treeRun_policy I (mode.allow I) (mode.weight I) k (treeInitial I)
          (activeVertices_nodup I) (treeInitial_policy I (mode.allow I) (mode.weight I))
      have hn : ∀ v, 0 ≤ treeDist (treeState I mode k).tree v :=
        treeRun_dist_nonneg I (mode.allow I) (mode.weight I) (mode.weight_nonneg I) k
          (treeInitial I) (by
            intro v; by_cases hv : v=I.source <;> simp [treeDist,treeInitial,optionDist,hv])
      have hs : ((treeState I mode k).tree I.source).distance=some 0 :=
        treeRun_source_zero I (mode.allow I) (mode.weight I) (mode.weight_nonneg I) k
      have hfinite : ∀ v d, ((treeState I mode k).tree v).distance=some d → d < mode.top I := by
        intro v d hd
        exact treeRun_sentinel_bound I (mode.allow I) (mode.resource I) k v d hd
      obtain ⟨next,nP,hPop,hmP,hrP,hcounterP,hnP,hAdjP,hfP⟩ :=
        treePopCmd_run E mode ε (treeState I mode k) s hm hr hne hp hn hs hfinite hAdj
      have hstate : treePop I (mode.allow I) (mode.weight I) (treeState I mode k) =
          treeState I mode (k+1) := (treeRun_succ I (mode.allow I) (mode.weight I) k (treeInitial I)).symm
      rw [hstate] at hmP
      have hcounter' : next.nr 277=k+1 := by rw [hcounterP,hcounter]
      obtain ⟨out,nT,hTail,hmT,hrT,hcounterT,hnT,hAdjT,hfT⟩ :=
        ih (k+1) next (by omega) hmP hrP hcounter' hAdjP
      have hwork := treePop_outgoingWork I (mode.allow I) (mode.weight I) (treeState I mode k) hne
      rw [hstate] at hwork
      refine ⟨out,1+nP+1+nT,Run.loopTrue ?_ hPop hTail,hmT,hrT,hcounterT,?_,hAdjT,?_⟩
      · simp [Guard.eval,natTest,hcounter,hr.count,hk]
      · have hweighted := congrArg (fun x => (19*Nat.clog 2 (2*E.B)+46)*x) hwork
        simp only [Nat.mul_add,Nat.mul_succ] at hweighted ⊢
        omega
      · intro a ha
        exact ⟨(hfT a ha).1.trans (hfP a ha).1,(hfT a ha).2.trans (hfP a ha).2⟩

private theorem standalone_Mission_RAMTreeRun__seq_attach {input : RAMInput} {a b c : Cmd} {s t out : Store} {n m : ℕ}
    (hab : Run input (.seq a b) s t n) (hc : Run input c t out m) :
    Run input (.seq a (.seq b c)) s out (n+m) := by
  cases hab with
  | seq ha hb => simpa only [Nat.add_assoc] using Run.seq ha (Run.seq hb hc)

private theorem treeCmd_run {I : Instance} (E : TreeAllocation I) (mode : TreeMode)
    (ε : ℝ) (s : Store) (hr : E.Registers mode s)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm) :
    ∃ out steps, Run (encodeInput I ε) treeCmd s out steps ∧
      E.Memory mode (treeState I mode (activeVertices I).length) out ∧
      E.Registers mode out ∧
      steps ≤ 15*E.B+(38*Nat.clog 2 (2*E.B)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*E.B)+46)*I.graph.edges.length+7 ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      (∀ a, TreeWholeProtected E mode a → out.nm a=s.nm a ∧ out.rm a=s.rm a) := by
  let input := encodeInput I ε
  obtain ⟨ready,nI,hInit,hrI,hmI,hnI,hfI⟩ := treeInitializeQueue_rep E mode input s hr ha
  have hMW := E.array_end_le_winner
  have hWP := E.winner_parent
  have hPR := E.parent_temp
  have hMP := E.map_le_array
  have hgraph (a : ℕ) (hlo : E.map ≤ a) (hhi : a < E.W) : ready.nm a=s.nm a := by
    apply (hfI a ?_ (Or.inl (by omega)) (Or.inl hhi) (Or.inl (by omega))).1
    intro v hv
    have ht := E.target_lt_map mode v (activeVertices_valid I v hv)
    omega
  have hAdjI : AdjacencyPrefix I I.graph.edges.length E.heads E.links ready.nm := by
    intro v hv
    have hMH := E.map_heads
    have hHA := E.heads_array
    have hAL := E.array_links
    have hLW := E.links_winner
    rw [hgraph (E.heads+v) (by omega) (by omega)]
    apply (hAdj v hv).frame
    intro e he
    have he' := outgoingIndices_lt I I.graph.edges.length v e he
    exact hgraph (E.links+e) (by omega) (by omega)
  let start := Atom.eval (⟨.natConst 277 0,trivial⟩ : Atom) input ready
  have hStart : Run input (.atom ⟨.natConst 277 0,trivial⟩) ready start 1 := Run.atom _ _
  have hrStart : E.Registers mode start := hrI.after_run hStart (by decide) (by decide)
  have hmStart : E.Memory mode (treeState I mode 0) start :=
    hmI.after_readonly hStart (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨out,nL,hLoop,hmL,hrL,hcounter,hnL,hAdjL,hfL⟩ := treeLoop_run E mode ε
    (activeVertices I).length 0 start (by omega) hmStart hrStart rfl hAdjI
  have hTail := Run.seq hStart hLoop
  have hrun : Run input treeCmd s out (nI+(1+nL)) := standalone_Mission_RAMTreeRun__seq_attach hInit hTail
  have hwork : outgoingWork I (treeState I mode 0).queue=I.graph.edges.length :=
    outgoingWork_active I
  rw [hwork] at hnL
  refine ⟨out,_,hrun,hmL,hrL,?_,hAdjL,?_⟩
  · nlinarith
  · intro a ha
    have hi := hfI a ha.1.2 ha.2.2 ha.1.1 ha.2.1
    have hl := hfL a ha.1
    exact ⟨hl.1.trans hi.1,hl.2.trans hi.2⟩

private theorem treeState_final_tree (I : Instance) (mode : TreeMode) :
    (treeState I mode (activeVertices I).length).tree =
      shortestTree I (mode.allow I) (mode.weight I) := by
  exact (shortestTree_eq_treeRun I (mode.allow I) (mode.weight I)).symm

private theorem treeState_final_queue (I : Instance) (mode : TreeMode) :
    (treeState I mode (activeVertices I).length).queue=[] := by
  exact shortestTree_queue_exhausted I (mode.allow I) (mode.weight I)

private theorem TreeMemoryRep.final_distances {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {s : Store} (h : E.Memory mode (treeState I mode (activeVertices I).length) s)
    (v : ℕ) (hv : v ∈ activeVertices I) :
    s.rm (targetAddress v+mode.offset) =
      sentinelKey (mode.top I) (shortestTree I (mode.allow I) (mode.weight I)) v := by
  have hh := h.settled v hv (by rw [treeState_final_queue]; simp)
  rwa [treeState_final_tree] at hh

private theorem TreeMemoryRep.final_parents {I : Instance} {E : TreeAllocation I} {mode : TreeMode}
    {s : Store} (h : E.Memory mode (treeState I mode (activeVertices I).length) s)
    (v : ℕ) (hv : v ∈ activeVertices I) :
    s.nm (targetAddress v+mode.offset) =
      (((shortestTree I (mode.allow I) (mode.weight I)) v).parent.map (·+1)).getD 0 := by
  have hh := h.parents v hv
  rwa [treeState_final_tree] at hh

private theorem zeroTreeSetup_run (input : RAMInput) (mode : TreeMode) (s : Store) :
    Run input (zeroTreeSetup mode) s (zeroTreePrepared mode s) 3 := by
  cases mode with
  | zeroLength =>
      change Run input (.atoms zeroLengthSetup) s (zeroTreePrepared .zeroLength s) 3
      have h := run_atoms input zeroLengthSetup s
      convert h using 1 <;> try rfl
  | zeroBudget =>
      change Run input (.atoms zeroBudgetSetup) s (zeroTreePrepared .zeroBudget s) 3
      have h := run_atoms input zeroBudgetSetup s
      convert h using 1 <;> try rfl

private theorem TreeRegisters.prepare {I : Instance} {E : TreeAllocation I} {old : TreeMode}
    {s : Store} (h : E.Registers old s) (mode : TreeMode)
    (hs : s.rr mode.sentinelRegister=mode.top I) : E.Registers mode (zeroTreePrepared mode s) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [zeroTreePrepared] using h.winner
  · simpa [zeroTreePrepared] using h.parent
  · simpa [zeroTreePrepared] using h.zero
  · simpa [zeroTreePrepared] using h.one
  · simpa [zeroTreePrepared] using h.capacity
  · simpa [zeroTreePrepared] using h.count
  · simpa [zeroTreePrepared] using h.keys
  · simpa [zeroTreePrepared] using h.source
  · simpa [zeroTreePrepared] using h.heads
  · simpa [zeroTreePrepared] using h.links
  · simpa [zeroTreePrepared] using h.map
  · simpa [zeroTreePrepared] using h.array
  · simpa [zeroTreePrepared] using h.active_count
  · simpa [zeroTreePrepared] using h.saved_capacity
  · simpa [zeroTreePrepared] using h.saved_array
  · simp [zeroTreePrepared]
  · simp [zeroTreePrepared]
  · simpa [zeroTreePrepared] using hs

private theorem TreeAllocation.length_field_protected {I : Instance} (E : TreeAllocation I)
    (v : ℕ) (hv : v < I.graph.n) : TreeWholeProtected E .zeroBudget (targetAddress v+2) := by
  have ht := E.target_lt_map .zeroLength v hv
  change targetAddress v + 2 < E.map at ht
  have hm := E.map_le_array
  have ha := E.array_end_le_winner
  have hp := E.winner_parent
  have hr := E.parent_temp
  refine ⟨⟨Or.inl (by simpa only [TreeMode.offset] using (show targetAddress v+2<E.W by omega)),?_⟩,
    Or.inl (by omega),Or.inl (by omega)⟩
  intro w hw
  simp only [targetAddress,TreeMode.offset]
  omega

private theorem TreeMode.zeroLength_tree (I : Instance) :
    shortestTree I (TreeMode.zeroLength.allow I) (TreeMode.zeroLength.weight I) = zeroLengthTree I := by
  unfold zeroLengthTree
  apply congrArg₂ (shortestTree I) ?_ rfl
  funext u v
  by_cases hz : I.length u v = 0 <;> simp [TreeMode.allow, hz]

private theorem TreeMode.zeroBudget_tree (I : Instance) :
    shortestTree I (TreeMode.zeroBudget.allow I) (TreeMode.zeroBudget.weight I) = zeroBudgetTree I := by
  unfold zeroBudgetTree
  apply congrArg₂ (shortestTree I) ?_ rfl
  funext u v
  by_cases hz : I.cost u v = 0 <;> simp [TreeMode.allow, hz]

private theorem zeroTreesCmd_run {I : Instance} (E : TreeAllocation I) (ε : ℝ) (s : Store)
    (hstart : E.Registers .zeroLength (zeroTreePrepared .zeroLength s))
    (hsentinel : s.rr 281=TreeMode.zeroBudget.top I)
    (ha : ActiveRep I.graph.n E.map E.array (activeVertices I) s)
    (hAdj : AdjacencyPrefix I I.graph.edges.length E.heads E.links s.nm) :
    ∃ out steps, Run (encodeInput I ε) zeroTreesCmd s out steps ∧
      ZeroTreeMemory I out ∧ E.Registers .zeroBudget out ∧
      AdjacencyPrefix I I.graph.edges.length E.heads E.links out.nm ∧
      steps ≤ 2*(15*E.B+(38*Nat.clog 2 (2*E.B)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*E.B)+46)*I.graph.edges.length+7)+6 ∧
      (∀ a, TreeWholeProtected E .zeroLength a → TreeWholeProtected E .zeroBudget a →
        out.nm a=s.nm a ∧ out.rm a=s.rm a) := by
  let input := encodeInput I ε
  have hpL := zeroTreeSetup_run input .zeroLength s
  have haL : ActiveRep I.graph.n E.map E.array (activeVertices I) (zeroTreePrepared .zeroLength s) :=
    ha.congr rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨length,nL,hL,hmL,hrL,hnL,hAdjL,hfL⟩ :=
    treeCmd_run E .zeroLength ε _ hstart haL hAdj
  have hsB : length.rr TreeMode.zeroBudget.sentinelRegister=TreeMode.zeroBudget.top I := by
    change length.rr 281 = TreeMode.zeroBudget.top I
    rw [hL.real_frame 281 (by decide), hpL.real_frame 281 (by decide)]
    exact hsentinel
  have hpB := zeroTreeSetup_run input .zeroBudget length
  have hrB := hrL.prepare .zeroBudget hsB
  have haB : ActiveRep I.graph.n E.map E.array (activeVertices I) (zeroTreePrepared .zeroBudget length) :=
    hmL.active.congr rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
  obtain ⟨out,nB,hB,hmB,hrB',hnB,hAdjB,hfB⟩ :=
    treeCmd_run E .zeroBudget ε _ hrB haB hAdjL
  have hrun : Run input zeroTreesCmd s out (3+(nL+(3+nB))) :=
    Run.seq hpL (Run.seq hL (Run.seq hpB hB))
  have hmem : ZeroTreeMemory I out := by
    constructor
    · intro v hv
      rw [(hfB _ (E.length_field_protected v (activeVertices_valid I v hv))).1]
      simpa only [TreeMode.offset, TreeMode.zeroLength_tree, zeroTreePrepared] using hmL.final_parents v hv
    · intro v hv
      simpa only [TreeMode.offset, TreeMode.zeroBudget_tree] using hmB.final_parents v hv
    · intro v hv
      rw [(hfB _ (E.length_field_protected v (activeVertices_valid I v hv))).2]
      simpa only [TreeMode.offset, TreeMode.zeroLength_tree, zeroTreePrepared] using hmL.final_distances v hv
    · intro v hv
      simpa only [TreeMode.offset, TreeMode.zeroBudget_tree] using hmB.final_distances v hv
  refine ⟨out,_,hrun,hmem,hrB',hAdjB,by omega,?_⟩
  intro a haL haB
  exact ⟨(hfB a haB).1.trans (hfL a haL).1,(hfB a haB).2.trans (hfL a haL).2⟩

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem standalone_Mission_Guesses__min_fold_le_seed (xs : List ℝ) (a : ℝ) : xs.foldl min a ≤ a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (ih (min a x)).trans (min_le_left a x)

private theorem standalone_Mission_Guesses__min_fold_le_member (xs : List ℝ) (a x : ℝ) (hx : x ∈ xs) :
    xs.foldl min a ≤ x := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (standalone_Mission_Guesses__min_fold_le_seed ys (min a x)).trans (min_le_right a x)
      · exact ih (min a y) hx

private theorem standalone_Mission_Guesses__seed_le_max_fold (xs : List ℝ) (a : ℝ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

private theorem standalone_Mission_Guesses__member_le_max_fold (xs : List ℝ) (a x : ℝ) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (le_max_right a x).trans (standalone_Mission_Guesses__seed_le_max_fold ys (max a x))
      · exact ih (max a y) hx

private theorem firstPositiveLength_le_member (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I) : firstPositiveLength I ≤ x :=
  standalone_Mission_Guesses__min_fold_le_member _ _ _ hx

private theorem member_le_largestLength (I : Instance) (x : ℝ)
    (hx : x ∈ positiveLengths I) : x ≤ largestLength I :=
  standalone_Mission_Guesses__member_le_max_fold _ _ _ hx

private theorem largestLength_nonneg (I : Instance) : 0 ≤ largestLength I :=
  standalone_Mission_Guesses__seed_le_max_fold _ _

private theorem firstPositiveLength_le_largestLength (I : Instance)
    (h : positiveLengths I ≠ []) : firstPositiveLength I ≤ largestLength I := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ h
  exact (firstPositiveLength_le_member I x hx).trans (member_le_largestLength I x hx)

private theorem largestLength_pos (I : Instance) (h : positiveLengths I ≠ []) :
    0 < largestLength I :=
  (firstPositiveLength_pos I).trans_le (firstPositiveLength_le_largestLength I h)

private theorem one_le_aspectRatio (I : Instance) : 1 ≤ aspectRatio I := by
  unfold aspectRatio
  split
  · exact le_rfl
  · rename_i h
    have hn : positiveLengths I ≠ [] := by simpa using h
    apply (le_div_iff₀ (firstPositiveLength_pos I)).mpr
    simpa using firstPositiveLength_le_largestLength I hn

private theorem crossing_exists (a r top : ℝ) (ha : 0 < a) (hr : 1 < r) :
    ∃ k : ℕ, top ≤ a * r ^ k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (top / a) hr
  refine ⟨k, ?_⟩
  have := (div_lt_iff₀ ha).mp hk
  nlinarith

private theorem firstCrossing_spec (a r top : ℝ) (ha : 0 < a) (hr : 1 < r) :
    top ≤ a * r ^ firstCrossing a r top := by
  have hex := crossing_exists a r top ha hr
  simpa [firstCrossing, hex] using Nat.find_spec hex

private theorem firstCrossing_minimal (a r top : ℝ) (ha : 0 < a) (hr : 1 < r)
    (i : ℕ) (hi : i < firstCrossing a r top) : a * r ^ i < top := by
  have hex := crossing_exists a r top ha hr
  have hh : i < Nat.find hex := by simpa [firstCrossing, hex] using hi
  exact lt_of_not_ge (Nat.find_min hex hh)

private theorem firstCrossing_le (a r top : ℝ) (ha : 0 < a) (hr : 1 < r)
    (i : ℕ) (hi : top ≤ a * r ^ i) : firstCrossing a r top ≤ i := by
  have hex := crossing_exists a r top ha hr
  simpa [firstCrossing, hex] using Nat.find_min' hex hi

private theorem firstCrossing_mono_top (a r x y : ℝ) (ha : 0 < a) (hr : 1 < r)
    (hxy : x ≤ y) : firstCrossing a r x ≤ firstCrossing a r y := by
  exact firstCrossing_le a r x ha hr _ (hxy.trans (firstCrossing_spec a r y ha hr))

private theorem firstCrossing_approx (a r x : ℝ) (ha : 0 < a) (hr : 1 < r)
    (hax : a ≤ x) : a * r ^ firstCrossing a r x ≤ r * x := by
  cases he : firstCrossing a r x with
  | zero =>
      simp only [pow_zero, mul_one]
      have hx : 0 ≤ x := ha.le.trans hax
      exact hax.trans (by nlinarith)
  | succ n =>
      have hn : n < firstCrossing a r x := by omega
      have hp := firstCrossing_minimal a r x ha hr n hn
      have hm := mul_le_mul_of_nonneg_left hp.le (show 0 ≤ r by linarith)
      rw [pow_succ]
      nlinarith

private theorem geometricGuesses_cover (I : Instance) (ε x : ℝ)
    (hε : 0 < ε) (hne : positiveLengths I ≠ [])
    (hlo : firstPositiveLength I ≤ x)
    (hhi : x ≤ I.graph.n * largestLength I) :
    ∃ L ∈ geometricGuesses I ε, x ≤ L ∧ L ≤ (1 + ε / 4) * x := by
  have ha := firstPositiveLength_pos I
  have hr : 1 < 1 + ε / 4 := by linarith
  let k := firstCrossing (firstPositiveLength I) (1 + ε / 4) x
  refine ⟨firstPositiveLength I * (1 + ε / 4) ^ k, ?_,
    firstCrossing_spec _ _ _ ha hr, firstCrossing_approx _ _ _ ha hr hlo⟩
  unfold geometricGuesses
  have hne' : (positiveLengths I).isEmpty = false := by simpa using hne
  simp only [hne', Bool.false_eq_true, ↓reduceIte, List.mem_map]
  refine ⟨k, ?_, rfl⟩
  apply List.mem_range.mpr
  have hk := firstCrossing_mono_top (firstPositiveLength I) (1 + ε / 4) x
    (I.graph.n * largestLength I) ha hr hhi
  dsimp [k]
  omega

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.GuessLoop
open Structured

private theorem step_run (input : RAMInput) (s : Store) (k : ℕ) :
    Run input (.atoms stepOps) (gridState s k) (gridState s (k+1)) 2 := by
  have he : evalAtoms input stepOps (gridState s k) = gridState s (k+1) := by
    apply Store.ext
    · funext r
      by_cases h70 : r = 70 <;> by_cases h71 : r = 71 <;>
        simp_all [evalAtoms,stepOps,Atom.eval,Store.ofRAM,Store.at,ramStep,
          evalNat,evalReal,gridState,Function.update_apply]
    · funext r
      by_cases h73 : r = 73 <;>
        simp_all [evalAtoms,stepOps,Atom.eval,Store.ofRAM,Store.at,ramStep,
          evalNat,evalReal,gridState,Function.update_apply,pow_succ] <;> ring
    · rfl
    · rfl
  have h := run_atoms input stepOps (gridState s k)
  rw [he] at h
  exact h

private theorem loop_run (input : RAMInput) (s : Store)
    (ha : 0 < s.rr 70) (hr : 1 < s.rr 71) (j d : ℕ)
    (hk : j+d = firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)) :
    Run input loopCmd (gridState s j) (gridState s (j+d)) (4*d+1) := by
  induction d generalizing j with
  | zero =>
      have hcross := firstCrossing_spec (s.rr 70) (s.rr 71) (s.rr 72) ha hr
      rw [← hk] at hcross
      simp only [Nat.add_zero] at hcross ⊢
      apply Run.loopFalse
      simpa [Guard.eval,realTest,gridState] using not_lt.mpr hcross
  | succ d ih =>
      have hj : j < firstCrossing (s.rr 70) (s.rr 71) (s.rr 72) := by omega
      have hlt := firstCrossing_minimal (s.rr 70) (s.rr 71) (s.rr 72) ha hr j hj
      have hg : (Guard.real .lt 73 72).eval (gridState s j) = true := by
        simpa [Guard.eval,realTest,gridState] using hlt
      have htail := ih (j+1) (by omega)
      have h := Run.loopTrue hg (step_run input s j) htail
      simpa only [loopCmd,show j+(d+1)=(j+1)+d by omega,
        show 4*(d+1)+1=1+2+1+(4*d+1) by omega] using h

private theorem crossingCmd_run (input : RAMInput) (s : Store)
    (ha : 0 < s.rr 70) (hr : 1 < s.rr 71) :
    Run input crossingCmd s
      (gridState s (firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)))
      (4*firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)+4) := by
  have hi : evalAtoms input initOps s = gridState s 0 := by
    apply Store.ext
    · rfl
    · simp [evalAtoms,initOps,Atom.eval,Store.ofRAM,Store.at,ramStep,gridState]
    · rfl
    · rfl
  have hl := loop_run input s ha hr 0 (firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)) (by omega)
  simp only [Nat.zero_add] at hl
  have h := Run.seq (run_atoms input initOps s) (by simpa only [hi] using hl)
  change Run input crossingCmd s
      (gridState s (firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)))
      (3+(4*firstCrossing (s.rr 70) (s.rr 71) (s.rr 72)+1)) at h
  convert h using 1 <;> omega

private theorem crossing_result (s : Store) (k : ℕ) :
    (gridState s k).nr 70 = k ∧ (gridState s k).rr 73 = s.rr 70*s.rr 71^k := by
  simp [gridState]

private theorem crossing_frame (s : Store) (k : ℕ) :
    (∀ r, r ≠ 70 → r ≠ 71 → (gridState s k).nr r = s.nr r) ∧
    (∀ r, r ≠ 73 → (gridState s k).rr r = s.rr r) ∧
    (gridState s k).nm = s.nm ∧ (gridState s k).rm = s.rm := by
  refine ⟨?_,?_,rfl,rfl⟩
  · intro r h70 h71
    simp [gridState,h70,h71]
  · intro r h73
    simp [gridState,h73]

end NearLinearRSP.TwoResources.Mission.GuessLoop
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

private theorem acceptedIndex_spec (I : Instance) (ε : ℝ) (t r : ℕ)
    (h : acceptedIndex I ε t = some r) :
    ∃ A, (outerInputs I ε)[r]? = some A ∧ accepted A t := by
  have hp := List.find?_some h
  cases he : (outerInputs I ε)[r]? with
  | none => simp [he] at hp
  | some A => exact ⟨A, rfl, by simpa [he] using hp⟩

private theorem acceptedIndex_le (I : Instance) (ε : ℝ) (t r s : ℕ) (A : InnerInput)
    (hr : acceptedIndex I ε t = some r)
    (hs : (outerInputs I ε)[s]? = some A) (ha : accepted A t) : r ≤ s := by
  obtain ⟨_, k, hk, hkr, hprev⟩ := List.find?_eq_some_iff_getElem.mp hr
  have hkr' : k = r := by simpa using hkr
  subst k
  by_contra hlt
  have hsr : s < r := by omega
  have hp := hprev s hsr
  simp [hs, ha] at hp

private theorem acceptedIndex_exists (I : Instance) (ε : ℝ) (t : ℕ) (A : InnerInput)
    (hA : A ∈ outerInputs I ε) (ha : accepted A t) :
    ∃ r, acceptedIndex I ε t = some r := by
  obtain ⟨s, hs⟩ := List.mem_iff_getElem?.mp hA
  obtain ⟨hsl, _⟩ := List.getElem?_eq_some_iff.mp hs
  cases he : acceptedIndex I ε t with
  | some r => exact ⟨r, rfl⟩
  | none =>
      have hn := List.find?_eq_none.mp he s (List.mem_range.mpr hsl)
      simp [hs, ha] at hn

private theorem answerBranch_inner_iff (I : Instance) (ε : ℝ) (t r : ℕ) :
    answerBranch I ε t = .inner r ↔
      t ≠ I.source ∧
      (∀ d, (zeroLengthTree I t).distance = some d → (I.budget : ℝ) < d) ∧
      I.budget ≠ 0 ∧ acceptedIndex I ε t = some r := by
  by_cases hs : t = I.source
  · simp [answerBranch, hs]
  · cases hz : (zeroLengthTree I t).distance with
    | none =>
        by_cases hb : I.budget = 0
        · cases hd : (zeroBudgetTree I t).distance <;>
            simp [answerBranch, hs, hz, hb, hd]
        · cases hf : acceptedIndex I ε t <;>
            simp only [acceptedIndex] at hf <;>
            simp [answerBranch, hs, hz, hb, acceptedIndex, hf]
    | some d =>
        by_cases hd : d ≤ I.budget
        · simp [answerBranch, hs, hz, hd, not_lt_of_ge hd]
        · by_cases hb : I.budget = 0
          · have hd0 : ¬ d ≤ (0 : ℝ) := by simpa [hb] using hd
            cases hc : (zeroBudgetTree I t).distance <;>
              simp [answerBranch, hs, hz, hb, hc, hd0]
          · have hlt : (I.budget : ℝ) < d := lt_of_not_ge hd
            cases hf : acceptedIndex I ε t <;>
              simp only [acceptedIndex] at hf <;>
              simp [answerBranch, hs, hz, hd, hb, hlt, acceptedIndex, hf]

private theorem answerBranch_inner_input (I : Instance) (ε : ℝ) (t r : ℕ)
    (h : answerBranch I ε t = .inner r) :
    ∃ A, (outerInputs I ε)[r]? = some A ∧ accepted A t :=
  acceptedIndex_spec I ε t r ((answerBranch_inner_iff I ε t r).mp h).2.2.2

private theorem answerBranch_zeroLength_spec (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t = .zeroLength) :
    t = I.source ∨ ∃ d, (zeroLengthTree I t).distance = some d ∧ d ≤ I.budget := by
  by_cases hs : t = I.source
  · exact Or.inl hs
  · right
    cases hz : (zeroLengthTree I t).distance with
    | none =>
        by_cases hb : I.budget = 0
        · cases hc : (zeroBudgetTree I t).distance <;>
            simp [answerBranch, hs, hz, hb, hc] at h
        · cases hf : acceptedIndex I ε t <;>
            simp only [acceptedIndex] at hf <;>
            simp [answerBranch, hs, hz, hb, acceptedIndex, hf] at h
    | some d =>
        by_cases hd : d ≤ I.budget
        · exact ⟨d, rfl, hd⟩
        · by_cases hb : I.budget = 0
          · have hd0 : ¬ d ≤ (0 : ℝ) := by simpa [hb] using hd
            cases hc : (zeroBudgetTree I t).distance <;>
              simp [answerBranch, hs, hz, hb, hc, hd0] at h
          · cases hf : acceptedIndex I ε t <;>
              simp only [acceptedIndex] at hf <;>
              simp [answerBranch, hs, hz, hd, hb, hf] at h

private theorem answerBranch_zeroBudget_spec (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t = .zeroBudget) :
    I.budget = 0 ∧ (zeroBudgetTree I t).distance.isSome = true := by
  unfold answerBranch at h
  split at h
  · contradiction
  · split at h
    · split at h
      · contradiction
      · split at h
        · rename_i hb
          split at h
          · rename_i hd; exact ⟨hb, hd⟩
          · contradiction
        · split at h <;> contradiction
    · split at h
      · rename_i hb
        split at h
        · rename_i hd; exact ⟨hb, hd⟩
        · contradiction
      · split at h <;> contradiction

private theorem outerInputs_mem_fields (I : Instance) (ε : ℝ) (A : InnerInput)
    (hA : A ∈ outerInputs I ε) : A.I = I ∧ A.δ = ε / 4 ∧ A.L ∈ geometricGuesses I ε := by
  unfold outerInputs at hA
  split at hA
  · obtain ⟨L, hL, he⟩ := List.mem_filterMap.mp hA
    split at he
    · cases he
      exact ⟨rfl, rfl, hL⟩
    · contradiction
  · simp at hA

private theorem geometricGuesses_ordered (I : Instance) (ε : ℝ) (hε : 0 ≤ ε) :
    (geometricGuesses I ε).Pairwise (· ≤ ·) := by
  unfold geometricGuesses
  split
  · simp
  · apply List.pairwise_map.mpr
    apply (List.pairwise_lt_range : (List.range _).Pairwise (· < ·)).imp
    intro i j hij
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + ε / 4) hij.le)
      (firstPositiveLength_pos I).le

private theorem outerInputs_ordered (I : Instance) (ε : ℝ) (hε : 0 ≤ ε) :
    (outerInputs I ε).Pairwise (fun A B => A.L ≤ B.L) := by
  unfold outerInputs
  split
  · apply List.pairwise_filterMap.mpr
    apply (geometricGuesses_ordered I ε hε).imp
    intro x y hxy A hA B hB
    split at hA
    · cases hA
      split at hB
      · cases hB; exact hxy
      · contradiction
    · contradiction
  · simp

private theorem outerInputs_get_length_le (I : Instance) (ε : ℝ) (hε : 0 ≤ ε)
    (r s : ℕ) (A B : InnerInput) (hr : (outerInputs I ε)[r]? = some A)
    (hs : (outerInputs I ε)[s]? = some B) (hrs : r ≤ s) : A.L ≤ B.L := by
  obtain ⟨hrl, hrA⟩ := List.getElem?_eq_some_iff.mp hr
  obtain ⟨hsl, hsB⟩ := List.getElem?_eq_some_iff.mp hs
  by_cases he : r = s
  · subst s
    have hAB : A = B := hrA.symm.trans hsB
    simpa [hAB]
  · have hlt : r < s := by omega
    have hp := List.pairwise_iff_getElem.mp (outerInputs_ordered I ε hε) r s hrl hsl hlt
    simpa [hrA, hsB] using hp

private theorem answerDistance_eq_none_iff (I : Instance) (ε : ℝ) (t : ℕ) :
    answerDistance I ε t = none ↔ answerBranch I ε t = .absent := by
  cases hb : answerBranch I ε t with
  | absent => simp [answerDistance, hb]
  | zeroLength => simp [answerDistance, hb]
  | zeroBudget =>
      have hsome := (answerBranch_zeroBudget_spec I ε t hb).2
      cases hd : (zeroBudgetTree I t).distance <;> simp_all [answerDistance]
  | inner r =>
      obtain ⟨A, hA, _⟩ := answerBranch_inner_input I ε t r hb
      simp [answerDistance, hb, hA]

private theorem EncodesOutput.readDistance_eq (I : Instance) (ε : ℝ) (S : RAMState)
    (h : EncodesOutput I ε S) (t : ℕ) (ht : t < I.graph.n) :
    readDistance S t = answerDistance I ε t := by
  have hm := h.2.2.2.2.1 t ht
  unfold readDistance
  rw [hm.1]
  cases hd : answerDistance I ε t with
  | none =>
      have hb := (answerDistance_eq_none_iff I ε t).mp hd
      simp [hb, branchTag]
  | some d =>
      have hb : answerBranch I ε t ≠ .absent := by
        intro he
        have hn := (answerDistance_eq_none_iff I ε t).mpr he
        rw [hd] at hn
        contradiction
      have htag : branchTag (answerBranch I ε t) ≠ 0 := by
        cases he : answerBranch I ε t <;> simp_all [branchTag]
      simp [htag, hm.2.1 d hd]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem outerInputs_length_exact (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (outerInputs I ε).length = if (positiveLengths I).isEmpty ∨ I.budget = 0 then 0
      else firstCrossing (firstPositiveLength I) (1+ε/4) (I.graph.n * largestLength I)+1 := by
  by_cases hC : I.budget = 0
  · simp [outerInputs,hC]
  · have hCp : 0 < (I.budget : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < I.budget)
    rw [outerInputs_eq_grid I ε hε hε1 hCp]
    cases (positiveLengths I).isEmpty <;> simp [hC]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem countCmd_run (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (s : Store) (hs : CountReady I ε s) :
    ∃ out steps, Run (encodeInput I ε) countCmd s out steps ∧
      out.nr 132 = (outerInputs I ε).length ∧
      steps ≤ 4*(outerInputs I ε).length+13 := by
  let input := encodeInput I ε
  let start := evalAtoms input countPrepare s
  have hstart := run_atoms input countPrepare s
  have hflag : start.nr 150 = if (positiveLengths I).isEmpty then 0 else 1 := hs.found
  have hz : start.nr 125 = 0 := hs.zero
  have hc : start.rr 121 = (I.budget : ℝ) := hs.budget
  have hrzero : start.rr 74 = 0 := rfl
  by_cases hempty : (positiveLengths I).isEmpty = true
  · have hg : (Guard.nat .eq 150 125).eval start = true := by
      simp [Guard.eval,natTest,hflag,hz,hempty]
    have hrun := Run.seq hstart (Run.branchTrue (b := .branch (.real .lt 74 121)
      countPositive .skip) hg (Run.skip start))
    refine ⟨start,4,hrun,?_,by omega⟩
    rw [outerInputs_length_exact I ε hε hε1]
    simp [hempty,start,evalAtoms,countPrepare,Atom.eval,Store.ofRAM,Store.at,ramStep]
  · have hefalse : (positiveLengths I).isEmpty = false := Bool.eq_false_iff.mpr hempty
    have hg : (Guard.nat .eq 150 125).eval start = false := by
      simp [Guard.eval,natTest,hflag,hz,hefalse]
    by_cases hb : I.budget = 0
    · have hbudget : (Guard.real .lt 74 121).eval start = false := by
        simp [Guard.eval,realTest,hrzero,hc,hb]
      have hrun := Run.seq hstart (Run.branchFalse (a := Cmd.skip) hg
        (Run.branchFalse (a := countPositive) hbudget (Run.skip start)))
      refine ⟨start,4,hrun,?_,by omega⟩
      rw [outerInputs_length_exact I ε hε hε1]
      simp [hb,start,evalAtoms,countPrepare,Atom.eval,Store.ofRAM,Store.at,ramStep]
    · have hbp : 0 < (I.budget : ℝ) := by
        exact_mod_cast (pos_iff_ne_zero.mpr hb : 0 < I.budget)
      have hbudget : (Guard.real .lt 74 121).eval start = true := by
        simp [Guard.eval,realTest,hrzero,hc,hbp]
      let prepared := evalAtoms input countPositivePrepare start
      have hp70 : prepared.rr 70 = firstPositiveLength I := hs.minimum
      have hp71 : prepared.rr 71 = 1+ε/4 := hs.ratio
      have hp72 : prepared.rr 72 = I.graph.n * largestLength I := by
        change s.rr 129 * s.rr 151 = _
        rw [hs.vertices,hs.maximum]
      have hp126 : prepared.nr 126 = 1 := hs.one
      have hpos := GuessLoop.crossingCmd_run input prepared
        (hp70.symm ▸ firstPositiveLength_pos I) (by rw [hp71]; linarith)
      let c := firstCrossing (firstPositiveLength I) (1+ε/4)
        (I.graph.n * largestLength I)
      rw [hp70,hp71,hp72] at hpos
      let crossed := GuessLoop.gridState prepared c
      let out := Atom.eval (⟨.natOp .add 132 70 126,trivial⟩ : Atom) input crossed
      have hpositive : Run input countPositive start out (3+((4*c+4)+1)) :=
        Run.seq (run_atoms input countPositivePrepare start)
          (Run.seq hpos (Run.atom _ crossed))
      have hrun := Run.seq hstart (Run.branchFalse (a := Cmd.skip) hg
        (Run.branchTrue (b := Cmd.skip) hbudget hpositive))
      have hlength : (outerInputs I ε).length = c+1 := by
        rw [outerInputs_length_exact I ε hε hε1]
        simp [hefalse,hb,c]
      refine ⟨out,2+(1+(1+(3+((4*c+4)+1))+1)),hrun,?_,by omega⟩
      rw [hlength]
      change crossed.nr 70 + crossed.nr 126 = c+1
      simp [crossed,GuessLoop.gridState,hp126]

private theorem countCmd_nat_frame {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k) (r : ℕ)
    (h70 : r ≠ 70) (h71 : r ≠ 71) (h132 : r ≠ 132) : out.nr r = s.nr r := by
  apply h.nat_frame
  simp [countCmd,countCases,countPositive,countPrepare,countPositivePrepare,
    GuessLoop.crossingCmd,GuessLoop.initOps,GuessLoop.loopCmd,GuessLoop.stepOps,
    Cmd.atoms,Cmd.natWrites,Atom.natWrites,h70,h71,h132]

private theorem countCmd_real_frame {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k) (r : ℕ) (hr : r < 70 ∨ 74 < r) :
    out.rr r = s.rr r := by
  apply h.real_frame
  have h70 : r ≠ 70 := by omega
  have h71 : r ≠ 71 := by omega
  have h72 : r ≠ 72 := by omega
  have h73 : r ≠ 73 := by omega
  have h74 : r ≠ 74 := by omega
  simp [countCmd,countCases,countPositive,countPrepare,countPositivePrepare,
    GuessLoop.crossingCmd,GuessLoop.initOps,GuessLoop.loopCmd,GuessLoop.stepOps,
    Cmd.atoms,Cmd.realWrites,Atom.realWrites,h70,h71,h72,h73,h74]

private theorem countCmd_memory_frame {input : RAMInput} {s out : Store} {k : ℕ}
    (h : Run input countCmd s out k) : out.nm = s.nm ∧ out.rm = s.rm := by
  constructor
  · apply h.natMemory_frame
    rfl
  · apply h.realMemory_frame
    rfl

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

private theorem headerPrepared_values (input : RAMInput) (s : Store) :
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
    (headerPrepared input s).rr 128 = (1 + input.reals 0 / 8) / (1 + input.reals 0 / 4) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  · change input.naturals 0 + input.naturals 0 + (input.naturals 0 + input.naturals 0) =
      4 * input.naturals 0
    omega
  · change 16 + (input.naturals 0 + input.naturals 0 + (input.naturals 0 + input.naturals 0)) =
      16 + 4 * input.naturals 0
    omega
  · change 512 / ((input.reals 0 / 4) * (input.reals 0 / 4)) =
      512 / (input.reals 0 / 4) ^ 2
    rw [pow_two]

private theorem headerLoopStore_zero (input : RAMInput) (s : Store) :
    headerLoopStore (headerPrepared input s) 0 = headerPrepared input s := by
  obtain ⟨hn, hm, hs, hq, hone, hn4, hbase, he, hc, hr, hx, hrone, hzero, hz⟩ :=
    headerPrepared_values input s
  apply Store.ext
  · funext r
    by_cases hr : r = 124
    · subst r; simpa [headerLoopStore] using hq.symm
    · simp [headerLoopStore, hr]
  · funext r
    by_cases hr : r = 127
    · subst r; simpa [headerLoopStore] using hzero.symm
    · simp [headerLoopStore, hr]
  · rfl
  · rfl

private theorem headerBody_run (input : RAMInput) (s : Store) (k : ℕ)
    (hone : s.nr 126 = 1) (hrone : s.rr 125 = 1) :
    Run input headerBody (headerLoopStore s k) (headerLoopStore s (k + 1)) 2 := by
  have h := Run.seq (input := input)
    (Run.atom (⟨.natOp .add 124 124 126, trivial⟩ : Atom) (headerLoopStore s k))
    (Run.atom (⟨.realOp .add 127 127 125, trivial⟩ : Atom) _)
  have heq : Atom.eval (⟨.realOp .add 127 127 125, trivial⟩ : Atom) input
      (Atom.eval (⟨.natOp .add 124 124 126, trivial⟩ : Atom) input
        (headerLoopStore s k)) = headerLoopStore s (k + 1) := by
    ext r <;> simp [headerLoopStore, Atom.eval, Store.ofRAM, Store.at, ramStep,
      evalNat, evalReal, hone, hrone, Function.update, Nat.cast_add, Nat.cast_one]
  rw [heq] at h
  exact h

private theorem headerLoop_run (input : RAMInput) (s : Store) (x : ℝ)
    (hone : s.nr 126 = 1) (hrone : s.rr 125 = 1) (hx : s.rr 124 = x)
    (k remaining : ℕ) (hcount : k + remaining = Nat.ceil x) :
    Run input headerLoop (headerLoopStore s k)
      (headerLoopStore s (Nat.ceil x)) (4 * remaining + 1) := by
  induction remaining generalizing k with
  | zero =>
      have hk : k = Nat.ceil x := by omega
      subst k
      apply Run.loopFalse
      simp [Guard.eval, realTest, headerLoopStore, hx, not_lt.mpr (Nat.le_ceil x)]
  | succ remaining ih =>
      have hk : (k : ℝ) < x := Nat.lt_ceil.mp (by omega)
      have hg : (Guard.real .lt 127 124).eval (headerLoopStore s k) = true := by
        simp [Guard.eval, realTest, headerLoopStore, hx, hk]
      have hr := Run.loopTrue hg (headerBody_run input s k hone hrone)
        (ih (k + 1) (by omega))
      simpa only [headerLoop, show 1 + 2 + 1 + (4 * remaining + 1) =
        4 * (remaining + 1) + 1 by omega] using hr

private theorem headerCmd_run (input : RAMInput) (s : Store) :
    Run input headerCmd s (headerResult input s)
      (37 + 4 * Nat.ceil (512 / (input.reals 0 / 4) ^ 2)) := by
  obtain ⟨hn, hm, hs, hq, hone, hn4, hbase, he, hc, hr, hx, hrone, hzero, hz⟩ :=
    headerPrepared_values input s
  have hloop := headerLoop_run input (headerPrepared input s)
    (512 / (input.reals 0 / 4) ^ 2)
    hone hrone hx
    0 (Nat.ceil (512 / (input.reals 0 / 4) ^ 2)) (by omega)
  rw [headerLoopStore_zero] at hloop
  have hr := Run.seq (run_atoms input headerAtoms s)
    (Run.seq hloop (run_atoms input headerStores _))
  convert hr using 1 <;> simp [headerCmd, headerResult, headerPrepared, headerAtoms, headerStores] <;> omega

private theorem headerResult_header (I : Instance) (ε : ℝ) (s : Store) :
    (headerResult (encodeInput I ε) s).nm 0 = outerQ ε ∧
    (headerResult (encodeInput I ε) s).nm 1 = I.source ∧
    (headerResult (encodeInput I ε) s).nm 2 = I.graph.n ∧
    (headerResult (encodeInput I ε) s).rm 0 = (1 + ε / 8) / (1 + ε / 4) := by
  have h := headerPrepared_values (encodeInput I ε) s
  simp only [encodeInput] at h
  simp [headerResult, headerStores, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
    headerLoopStore, encodeInput, outerQ, h.1, h.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2]

private theorem headerResult_memory_frame (input : RAMInput) (s : Store) (a : ℕ)
    (h0 : a ≠ 0) (h1 : a ≠ 1) (h2 : a ≠ 2) :
    (headerResult input s).nm a = s.nm a ∧ (headerResult input s).rm a = s.rm a := by
  constructor
  · change Function.update (Function.update (Function.update s.nm 0
      (Nat.ceil (512 / (input.reals 0 / 4) ^ 2))) 1 (input.naturals 2))
      2 (input.naturals 0) a = s.nm a
    simp [h0, h1, h2]
  · change Function.update s.rm 0 ((1 + input.reals 0 / 8) / (1 + input.reals 0 / 4)) a = s.rm a
    simp [h0]

end Preprocess
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.NatToReal
open Structured

private theorem run_atoms (input : RAMInput) (as : List Atom) (s : Store) :
    Run input (atoms as) s (evalAtoms input as s) as.length := by
  induction as generalizing s with
  | nil => exact Run.skip s
  | cons a as ih =>
      simpa [atoms,evalAtoms,List.foldl_cons,Nat.add_comm] using
        Run.seq (Run.atom a s) (ih (a.eval input s))

private theorem powerBody_run (input : RAMInput) (s : Store) (k : ℕ) :
    Run input powerBody (powerState s k) (powerState s (k+1)) 3 := by
  have he : evalAtoms input powerOps (powerState s k) = powerState s (k+1) := by
    apply Store.ext
    · funext r
      by_cases h62 : r = 62 <;> by_cases h63 : r = 63 <;>
        simp_all [evalAtoms,powerOps,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,
          evalReal,powerState,Function.update_apply,pow_succ] <;> ring
    · funext r
      by_cases hr : r = 61 <;>
        simp_all [evalAtoms,powerOps,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,
          evalReal,powerState,Function.update_apply,pow_succ] <;> ring
    · rfl
    · rfl
  have h := run_atoms input powerOps (powerState s k)
  rw [he] at h
  exact h

private theorem powerLoop_run (input : RAMInput) (s : Store) (n k d : ℕ)
    (hn : s.nr 66 = n+1) (hlo : 2 ^ (k+d) ≤ n) (hhi : n < 2 ^ (k+d+1)) :
    Run input powerLoop (powerState s k) (powerState s (k+d)) (5*d+1) := by
  induction d generalizing k with
  | zero =>
      simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add]
      apply Run.loopFalse
      simp [Guard.eval,natTest,powerState,hn]
      omega
  | succ d ih =>
      have hp : 2 ^ (k+1) ≤ n :=
        (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : k+1 ≤ k+(d+1))).trans hlo
      have hg : (Guard.nat .lt 63 66).eval (powerState s k) = true := by
        simp [Guard.eval,natTest,powerState,hn]
        omega
      have ht := ih (k+1) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hlo)
        (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hhi)
      have h := Run.loopTrue hg (powerBody_run input s k) ht
      simpa only [powerLoop,
        show k+(d+1)=(k+1)+d by omega,
        show 5*(d+1)+1=1+3+1+(5*d+1) by omega] using h

private theorem convertBody_run (input : RAMInput) (s : Store) (hone : s.nr 65 = 1)
    (hpos : 0 < s.nr 61) :
    Run input convertBody s (bodyResult s (Nat.log 2 (s.nr 61)))
      (7 + 5 * Nat.log 2 (s.nr 61)) := by
  have hp : evalAtoms input prepare s = powerState (prepared s) 0 := by
    apply Store.ext
    · funext r
      by_cases h62 : r = 62 <;> by_cases h63 : r = 63 <;> by_cases h66 : r = 66 <;>
        simp_all [evalAtoms,prepare,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,
          powerState,prepared,hone,Function.update_apply]
    · simp [evalAtoms,prepare,Atom.eval,Store.ofRAM,Store.at,ramStep,powerState,prepared]
    · rfl
    · rfl
  have hl := powerLoop_run input (prepared s) (s.nr 61) 0 (Nat.log 2 (s.nr 61))
    (by simp [prepared]) (by simpa using Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos))
    (by simpa using Nat.lt_pow_succ_log_self (by decide : 1 < 2) (s.nr 61))
  have hf : evalAtoms input finish (powerState (prepared s) (Nat.log 2 (s.nr 61))) =
      bodyResult s (Nat.log 2 (s.nr 61)) := by
    simp [evalAtoms,finish,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,evalReal,
      powerState,prepared,bodyResult]
  have h := Run.seq (run_atoms input prepare s)
    (Run.seq (by simpa only [hp,Nat.zero_add] using hl)
      (run_atoms input finish _))
  rw [hf] at h
  change Run input convertBody s (bodyResult s (Nat.log 2 (s.nr 61)))
    (4 + (5 * Nat.log 2 (s.nr 61) + 1 + 2)) at h
  convert h using 1 <;> omega

private theorem Frame.refl (s : Store) : Frame s s := ⟨fun _ _ => rfl,fun _ _ _ => rfl,rfl,rfl⟩

private theorem Frame.trans {s t u : Store} (h : Frame s t) (h' : Frame t u) : Frame s u := by
  exact ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr),
    fun r h60 h61 => (h'.2.1 r h60 h61).trans (h.2.1 r h60 h61),
    h'.2.2.1.trans h.2.2.1,h'.2.2.2.trans h.2.2.2⟩

private theorem bodyResult_frame (s : Store) (k : ℕ) : Frame s (bodyResult s k) := by
  refine ⟨?_,?_,rfl,rfl⟩
  · intro r hr
    have h61 : r ≠ 61 := by omega
    have h62 : r ≠ 62 := by omega
    have h63 : r ≠ 63 := by omega
    have h66 : r ≠ 66 := by omega
    simp [bodyResult,powerState,prepared,h61,h62,h63,h66]
  · intro r h60 h61
    simp [bodyResult,powerState,prepared,h60,h61]

private theorem convertLoop_run (input : RAMInput) (h : ℕ) (s : Store)
    (hz : s.nr 64 = 0) (hone : s.nr 65 = 1) (hb : s.nr 61 < 2 ^ h) :
    ∃ (t : Store) (steps : ℕ), Run input convertLoop s t steps ∧
      t.nr 61 = 0 ∧ t.rr 60 = s.rr 60 + s.nr 61 ∧
      steps ≤ 14 * h ^ 2 + 1 ∧ Frame s t := by
  induction h generalizing s with
  | zero =>
      have hn : s.nr 61 = 0 := by simpa using hb
      refine ⟨s,1,Run.loopFalse ?_,hn,?_,by simp,Frame.refl s⟩
      · simp [Guard.eval,natTest,hz,hn]
      · simp [hn]
  | succ h ih =>
      by_cases hn : s.nr 61 = 0
      · refine ⟨s,1,Run.loopFalse ?_,hn,?_,by omega,Frame.refl s⟩
        · simp [Guard.eval,natTest,hz,hn]
        · simp [hn]
      · let k := Nat.log 2 (s.nr 61)
        let u := bodyResult s k
        have hp : 0 < s.nr 61 := Nat.pos_of_ne_zero hn
        have hk : k < h+1 := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hn).mpr hb
        have hpk : 2 ^ k ≤ s.nr 61 := Nat.pow_log_le_self 2 hn
        have hhi : s.nr 61 < 2 ^ (k+1) := Nat.lt_pow_succ_log_self (by decide) _
        have hu : u.nr 61 < 2 ^ h := by
          have hk' : 2 ^ k ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
          change s.nr 61 - 2 ^ k < 2 ^ h
          rw [pow_succ] at hhi
          omega
        have uz : u.nr 64 = 0 := by simp [u,bodyResult,powerState,prepared,hz]
        have uone : u.nr 65 = 1 := by simp [u,bodyResult,powerState,prepared,hone]
        obtain ⟨t,n,ht,htzero,htreal,htcost,htframe⟩ := ih u uz uone hu
        refine ⟨t,1+(7+5*k)+1+n,Run.loopTrue ?_ (convertBody_run input s hone hp) ht,
          htzero,?_,?_,(bodyResult_frame s k).trans htframe⟩
        · simp [Guard.eval,natTest,hz,hp]
        · rw [htreal]
          change s.rr 60 + (2 : ℝ)^k + ((s.nr 61 - 2^k : ℕ) : ℝ) = _
          rw [Nat.cast_sub hpk, Nat.cast_pow, Nat.cast_ofNat]
          ring
        · nlinarith

private theorem convertCmd_run (input : RAMInput) (s : Store) :
    ∃ (t : Store) (steps : ℕ), Run input convertCmd s t steps ∧
      t.rr 60 = (s.nr 60 : ℝ) ∧
      steps ≤ 14 * (Nat.log 2 (s.nr 60) + 1) ^ 2 + 5 ∧ Frame s t := by
  let u := evalAtoms input initOps s
  have un : u.nr 61 = s.nr 60 := by
    simp [u,evalAtoms,initOps,Atom.eval,Store.ofRAM,Store.at,ramStep]
  have ur : u.rr 60 = 0 := by
    simp [u,evalAtoms,initOps,Atom.eval,Store.ofRAM,Store.at,ramStep]
  have uz : u.nr 64 = 0 := by
    simp [u,evalAtoms,initOps,Atom.eval,Store.ofRAM,Store.at,ramStep]
  have uone : u.nr 65 = 1 := by
    simp [u,evalAtoms,initOps,Atom.eval,Store.ofRAM,Store.at,ramStep]
  have uframe : Frame s u := by
    refine ⟨?_,?_,rfl,rfl⟩
    · intro r hr
      have h61 : r ≠ 61 := by omega
      have h64 : r ≠ 64 := by omega
      have h65 : r ≠ 65 := by omega
      simp [u,evalAtoms,initOps,Atom.eval,Store.ofRAM,Store.at,ramStep,h61,h64,h65]
    · intro r h60 h61
      simp [u,evalAtoms,initOps,Atom.eval,Store.ofRAM,Store.at,ramStep,h60]
  obtain ⟨t,n,ht,_,htreal,htcost,htframe⟩ :=
    convertLoop_run input (Nat.log 2 (s.nr 60)+1) u uz uone
      (by rw [un]; exact Nat.lt_pow_succ_log_self (by decide) _)
  refine ⟨t,4+n,?_,?_,by omega,uframe.trans htframe⟩
  · exact Run.seq (run_atoms input initOps s) ht
  · simpa [ur,un] using htreal

end NearLinearRSP.TwoResources.Mission.NatToReal
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Scan

private theorem positives_append (xs ys : List (ℝ × ℝ)) :
    positives (xs++ys) = positives xs ++ positives ys := by
  simp [positives]

private theorem minimum_append (xs : List ℝ) (x : ℝ) :
    (xs++[x]).foldl min ((xs++[x]).headD 1) =
      if xs.isEmpty then x else min (xs.foldl min (xs.headD 1)) x := by
  cases xs with
  | nil => simp
  | cons a xs => simp [List.foldl_append]

private theorem addSample_summarize (xs : List (ℝ × ℝ)) (x : ℝ × ℝ) :
    addSample (summarize xs) x = summarize (xs++[x]) := by
  by_cases hx : 0 < x.1
  · have hp : positives (xs++[x]) = positives xs ++ [x.1] := by
      simp [positives_append,positives,hx]
    cases he : positives xs with
    | nil => simp [addSample,summarize,hx,hp,List.foldl_append,he]
    | cons a ys => simp [addSample,summarize,hx,hp,List.foldl_append,he]
  · have hp : positives (xs++[x]) = positives xs := by
      simp [positives_append,positives,hx]
    simp [addSample,summarize,hx,hp,List.foldl_append]

private theorem prefixSummary_succ (input : RAMInput) (k : ℕ) :
    prefixSummary input (k+1) = addSample (prefixSummary input k) (sample input k) := by
  unfold prefixSummary
  rw [List.range_succ,List.map_append,List.map_singleton]
  exact (addSample_summarize _ _).symm

private theorem encoded_samples (I : Instance) (ε : ℝ) :
    (List.range I.graph.edges.length).map (sample (encodeInput I ε)) = edgeSamples I := by
  apply List.ext_getElem
  · simp [edgeSamples]
  · intro k hk hk'
    have hk0 : k < I.graph.edges.length := by simpa using hk
    have he : I.graph.edges[k]? = some I.graph.edges[k] := List.getElem?_eq_getElem hk0
    have hl := encodeInput_length I ε k I.graph.edges[k] he
    have hc := encodeInput_cost I ε k I.graph.edges[k] he
    simp only [edgeSamples, List.getElem_map, List.getElem_range]
    exact Prod.ext hl hc

private theorem max_fold_filter_positive (xs : List ℝ) (a : ℝ) (ha : 0 ≤ a) :
    xs.foldl max a = (xs.filter (0 < ·)).foldl max a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : 0 < x
      · simpa [hx] using ih (max a x) (ha.trans (le_max_left _ _))
      · have hxa : x ≤ a := (le_of_not_gt hx).trans ha
        simpa [hx,max_eq_left hxa] using ih a ha

private theorem summarize_edgeSamples (I : Instance) :
    (summarize (edgeSamples I)).found = !(positiveLengths I).isEmpty ∧
    (summarize (edgeSamples I)).minimum = firstPositiveLength I ∧
    (summarize (edgeSamples I)).maximum = largestLength I ∧
    (summarize (edgeSamples I)).sumLength =
      (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum ∧
    (summarize (edgeSamples I)).sumCost =
      (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum := by
  have hp : positives (edgeSamples I) = positiveLengths I := by
    simp [positives,edgeSamples,positiveLengths,List.map_map,Function.comp_def]
  refine ⟨by simp [summarize,hp],by simp [summarize,hp,firstPositiveLength],?_,
    by simp [summarize,edgeSamples,List.map_map,Function.comp_def],
    by simp [summarize,edgeSamples,List.map_map,Function.comp_def]⟩
  simp only [summarize,edgeSamples,List.map_map,Function.comp_def,largestLength,positiveLengths]
  exact max_fold_filter_positive _ 0 le_rfl

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Scan
open Structured

private theorem minCmd_run (input : RAMInput) (s : Store) (dst src : ℕ) :
    ∃ n ≤ 3, Run input (minCmd dst src) s (minResult s dst src) n := by
  by_cases h : s.rr src < s.rr dst
  · refine ⟨3,by omega,?_⟩
    have hg : (Guard.real .lt src dst).eval s = true := by simp [Guard.eval,realTest,h]
    simpa [minCmd,minResult,min_eq_right h.le,Atom.eval,Store.ofRAM,ramStep,Store.at] using
      Run.branchTrue (input := input) (b := Cmd.skip) hg (Run.atom (⟨.realCopy dst src,trivial⟩ : Atom) s)
  · refine ⟨1,by omega,?_⟩
    have hg : (Guard.real .lt src dst).eval s = false := by simp [Guard.eval,realTest,h]
    simpa [minCmd,minResult,min_eq_left (le_of_not_gt h),Function.update_eq_self] using
      Run.branchFalse (a := Cmd.atom ⟨.realCopy dst src,trivial⟩) hg (Run.skip (input := input) s)

private theorem maxCmd_run (input : RAMInput) (s : Store) (dst src : ℕ) :
    ∃ n ≤ 3, Run input (maxCmd dst src) s (maxResult s dst src) n := by
  by_cases h : s.rr dst < s.rr src
  · refine ⟨3,by omega,?_⟩
    have hg : (Guard.real .lt dst src).eval s = true := by simp [Guard.eval,realTest,h]
    simpa [maxCmd,maxResult,max_eq_right h.le,Atom.eval,Store.ofRAM,ramStep,Store.at] using
      Run.branchTrue (input := input) (b := Cmd.skip) hg (Run.atom (⟨.realCopy dst src,trivial⟩ : Atom) s)
  · refine ⟨1,by omega,?_⟩
    have hg : (Guard.real .lt dst src).eval s = false := by simp [Guard.eval,realTest,h]
    simpa [maxCmd,maxResult,max_eq_left (le_of_not_gt h),Function.update_eq_self] using
      Run.branchFalse (a := Cmd.atom ⟨.realCopy dst src,trivial⟩) hg (Run.skip (input := input) s)

private theorem positiveCmd_run (input : RAMInput) (s : Store)
    (hz : s.nr 153 = 0) (hrz : s.rr 156 = 0) :
    ∃ n ≤ 6, Run input positiveCmd s (positiveResult input s) n := by
  by_cases hp : 0 < s.rr 154
  · have hguard : (Guard.real .lt 156 154).eval s = true := by
      simp [Guard.eval,realTest,hrz,hp]
    by_cases hf : s.nr 150 = 0
    · have hflag : (Guard.nat .eq 150 153).eval s = true := by
        simp [Guard.eval,natTest,hz,hf]
      refine ⟨6,by omega,?_⟩
      simpa [positiveCmd,positiveResult,hp,hf,firstPositiveOps] using
        Run.branchTrue hguard (Run.branchTrue hflag (run_atoms input firstPositiveOps s))
    · have hflag : (Guard.nat .eq 150 153).eval s = false := by
        simp [Guard.eval,natTest,hz,hf]
      obtain ⟨n,hn,hrun⟩ := minCmd_run input s 150 154
      refine ⟨1+(1+n)+1,by omega,?_⟩
      simpa only [positiveCmd,positiveResult,if_pos hp,if_neg hf] using
        Run.branchTrue hguard (Run.branchFalse hflag hrun)
  · have hguard : (Guard.real .lt 156 154).eval s = false := by
      simp [Guard.eval,realTest,hrz,hp]
    refine ⟨1,by omega,?_⟩
    simpa only [positiveCmd,positiveResult,if_neg hp] using
      Run.branchFalse hguard (Run.skip (input := input) s)

private theorem scanBody_run (input : RAMInput) (s : Store)
    (hz : s.nr 153 = 0) (hrz : s.rr 156 = 0) :
    ∃ n ≤ 16, Run input scanBody s (scanBodyResult input s) n := by
  let a := evalAtoms input loadSampleOps s
  have az : a.nr 153 = 0 := by
    simp [a,evalAtoms,loadSampleOps,Atom.eval,Store.ofRAM,ramStep,Store.at,hz]
  have arz : a.rr 156 = 0 := by
    simp [a,evalAtoms,loadSampleOps,Atom.eval,Store.ofRAM,ramStep,Store.at,hrz]
  obtain ⟨np,hp,hprun⟩ := positiveCmd_run input a az arz
  obtain ⟨nm,hm,hmrun⟩ := maxCmd_run input (positiveResult input a) 151 154
  refine ⟨6+(np+(nm+1)),by omega,?_⟩
  exact Run.seq (run_atoms input loadSampleOps s)
    (Run.seq hprun (Run.seq hmrun (Run.atom _ _)))

private theorem scanBody_values (input : RAMInput) (s : Store) (hone : s.nr 154 = 1)
    (hflag : s.nr 150 = 0 ∨ s.nr 150 = 1) :
    let t := scanBodyResult input s
    let l := input.reals (s.nr 151)
    let c := input.reals (s.nr 151+1)
    t.nr 151 = s.nr 151+2 ∧ t.nr 152 = s.nr 152+1 ∧
    t.nr 150 = (if 0 < l then 1 else s.nr 150) ∧
    t.rr 150 = (if 0 < l then if s.nr 150 = 0 then l else min (s.rr 150) l else s.rr 150) ∧
    t.rr 151 = max (s.rr 151) l ∧ t.rr 152 = s.rr 152+l ∧ t.rr 153 = s.rr 153+c := by
  by_cases hp : 0 < input.reals (s.nr 151) <;>
    by_cases hf : s.nr 150 = 0 <;>
    simp [scanBodyResult,evalAtoms,loadSampleOps,positiveResult,firstPositiveOps,
      minResult,maxResult,Atom.eval,Store.ofRAM,ramStep,Store.at,evalNat,evalReal,
      hone,hp,hf]
  all_goals omega

private theorem scan_init_rep (input : RAMInput) (s : Store) :
    ScanRep input (input.naturals 1) 0 (evalAtoms input scanInitOps s) := by
  constructor <;> simp [evalAtoms,scanInitOps,Atom.eval,Store.ofRAM,ramStep,Store.at,
    prefixSummary,summarize,positives]

private theorem scan_step_rep (input : RAMInput) (m k : ℕ) (s : Store)
    (h : ScanRep input m k s) :
    ∃ n ≤ 16, Run input scanBody s (scanBodyResult input s) n ∧
      ScanRep input m (k+1) (scanBodyResult input s) := by
  obtain ⟨n,hn,hrun⟩ := scanBody_run input s h.zero h.realZero
  refine ⟨n,hn,hrun,?_⟩
  have hflag : s.nr 150 = 0 ∨ s.nr 150 = 1 := by
    rw [h.found]
    split <;> simp
  obtain ⟨hp,hi,hf,hmin,hmax,hL,hC⟩ := scanBody_values input s h.one hflag
  have hnframe (r : ℕ) (hr : r ≠ 150 ∧ r ≠ 151 ∧ r ≠ 152) :
      (scanBodyResult input s).nr r = s.nr r := by
    apply hrun.nat_frame
    simp [scanBody,positiveCmd,minCmd,maxCmd,incrementCmd,Cmd.atoms,loadSampleOps,
      firstPositiveOps,Cmd.natWrites,Atom.natWrites,hr.1,hr.2.1,hr.2.2]
  have hrframe : (scanBodyResult input s).rr 156 = s.rr 156 := by
    apply hrun.real_frame
    simp [scanBody,positiveCmd,minCmd,maxCmd,incrementCmd,Cmd.atoms,loadSampleOps,
      firstPositiveOps,Cmd.realWrites,Atom.realWrites]
  refine ⟨by rw [hi,h.index],by rw [hp,h.pointer]; omega,
    (hnframe 159 (by omega)).trans h.bound,
    (hnframe 153 (by omega)).trans h.zero,
    (hnframe 154 (by omega)).trans h.one,
    hrframe.trans h.realZero,?_,?_,?_,?_,?_⟩
  · rw [hf,h.pointer,prefixSummary_succ]
    simp only [addSample,sample]
    rw [h.found]
    split_ifs <;> simp_all
  · rw [hmin,h.pointer,prefixSummary_succ]
    simp only [addSample,sample]
    rw [h.found,h.minimum]
    cases (prefixSummary input k).found <;> simp
  · rw [hmax,h.pointer,prefixSummary_succ]
    simp only [addSample,sample,h.maximum]
  · rw [hL,h.pointer,prefixSummary_succ]
    simp only [addSample,sample,h.lengthSum]
  · rw [hC,h.pointer,prefixSummary_succ]
    simp only [addSample,sample,h.costSum]

private theorem scanCmd_run (input : RAMInput) (s : Store) :
    ∃ out steps, Run input scanCmd s out steps ∧
      ScanRep input (input.naturals 1) (input.naturals 1) out ∧
      steps ≤ 18*input.naturals 1+13 ∧ out.nm = s.nm ∧ out.rm = s.rm := by
  let start := evalAtoms input scanInitOps s
  obtain ⟨out,n,hrun,hfinal,hcost⟩ := run_bounded_loop input (.nat .lt 152 159)
    scanBody (input.naturals 1) 16 (ScanRep input (input.naturals 1))
    (by intro k u _ hu; simp [Guard.eval,natTest,hu.index,hu.bound])
    (by
      intro k u _ hu
      obtain ⟨n,hn,hrun,hnext⟩ := scan_step_rep input (input.naturals 1) k u hu
      exact ⟨scanBodyResult input u,n,hrun,hnext,hn⟩)
    0 start (by omega) (scan_init_rep input s)
  have hfull : Run input scanCmd s out (12+n) :=
    Run.seq (run_atoms input scanInitOps s) hrun
  refine ⟨out,12+n,hfull,hfinal,by omega,?_,?_⟩
  · apply hfull.natMemory_frame
    simp [scanCmd,scanLoop,scanBody,positiveCmd,minCmd,maxCmd,incrementCmd,
      Cmd.atoms,scanInitOps,loadSampleOps,firstPositiveOps,
      Cmd.writesNatMemory,Atom.writesNatMemory]
  · apply hfull.realMemory_frame
    simp [scanCmd,scanLoop,scanBody,positiveCmd,minCmd,maxCmd,incrementCmd,
      Cmd.atoms,scanInitOps,loadSampleOps,firstPositiveOps,
      Cmd.writesRealMemory,Atom.writesRealMemory]

private theorem scan_encoded_correct (I : Instance) (ε : ℝ) (s : Store) :
    ∃ out steps, Run (encodeInput I ε) scanCmd s out steps ∧
      out.rr 150 = firstPositiveLength I ∧ out.rr 151 = largestLength I ∧
      out.rr 152 = (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum ∧
      out.rr 153 = (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum ∧
      out.nr 150 = (if (positiveLengths I).isEmpty then 0 else 1) ∧
      steps ≤ 20*(I.graph.edges.length+1) ∧ out.nm = s.nm ∧ out.rm = s.rm := by
  obtain ⟨out,n,hrun,hrep,hcost,hnm,hrm⟩ := scanCmd_run (encodeInput I ε) s
  have hm : (encodeInput I ε).naturals 1 = I.graph.edges.length := by simp [encodeInput]
  rw [hm] at hrep hcost
  have hs : prefixSummary (encodeInput I ε) I.graph.edges.length = summarize (edgeSamples I) := by
    rw [prefixSummary,encoded_samples]
  obtain ⟨hf,hmin,hmax,hL,hC⟩ := summarize_edgeSamples I
  refine ⟨out,n,hrun,?_,?_,?_,?_,?_,by omega,hnm,hrm⟩
  · exact hrep.minimum.trans ((congrArg Summary.minimum hs).trans hmin)
  · exact hrep.maximum.trans ((congrArg Summary.maximum hs).trans hmax)
  · exact hrep.lengthSum.trans ((congrArg Summary.sumLength hs).trans hL)
  · exact hrep.costSum.trans ((congrArg Summary.sumCost hs).trans hC)
  · rw [hrep.found,hs,hf]
    cases (positiveLengths I).isEmpty <;> rfl

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Scan
open Structured

private theorem scan_nat_frame (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input scanCmd s t steps) (hr : r < 150 ∨ 159 < r) : t.nr r = s.nr r := by
  apply h.nat_frame
  simp [scanCmd,scanLoop,scanBody,positiveCmd,minCmd,maxCmd,incrementCmd,
    Cmd.atoms,scanInitOps,loadSampleOps,firstPositiveOps,Cmd.natWrites,Atom.natWrites]
  omega

private theorem scan_real_frame (input : RAMInput) (s t : Store) (steps r : ℕ)
    (h : Run input scanCmd s t steps) (hr : r < 150 ∨ 156 < r) : t.rr r = s.rr r := by
  apply h.real_frame
  simp [scanCmd,scanLoop,scanBody,positiveCmd,minCmd,maxCmd,incrementCmd,
    Cmd.atoms,scanInitOps,loadSampleOps,firstPositiveOps,Cmd.realWrites,Atom.realWrites]
  omega

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem CoreRegs.transfer {I : Instance} {ε : ℝ} {s t : Store} (h : CoreRegs I ε s)
    (hn : ∀r, 121 ≤ r → r ≤ 130 → t.nr r = s.nr r)
    (hr : ∀r, 121 ≤ r → r ≤ 128 → t.rr r = s.rr r) : CoreRegs I ε t := by
  exact ⟨(hn 121 (by omega) (by omega)).trans h.vertices,
    (hn 122 (by omega) (by omega)).trans h.edges,
    (hn 123 (by omega) (by omega)).trans h.source,
    (hn 124 (by omega) (by omega)).trans h.q,
    (hn 125 (by omega) (by omega)).trans h.zero,
    (hn 126 (by omega) (by omega)).trans h.one,
    (hn 127 (by omega) (by omega)).trans h.two,
    (hn 129 (by omega) (by omega)).trans h.vertexStride,
    (hn 130 (by omega) (by omega)).trans h.targetEnd,
    (hr 121 (by omega) (by omega)).trans h.budget,
    (hr 123 (by omega) (by omega)).trans h.ratio,
    (hr 125 (by omega) (by omega)).trans h.realOne,
    (hr 127 (by omega) (by omega)).trans h.realQ,
    (hr 128 (by omega) (by omega)).trans h.z⟩

private theorem headerResult_core (I : Instance) (ε : ℝ) (s : Store) :
    CoreRegs I ε (headerResult (encodeInput I ε) s) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · change I.graph.n+I.graph.n+(I.graph.n+I.graph.n) = 4*I.graph.n
    omega
  · change 16+(I.graph.n+I.graph.n+(I.graph.n+I.graph.n)) = 16+4*I.graph.n
    omega

private theorem scalarCmd_run (I : Instance) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ out steps, Run (encodeInput I ε) scalarCmd initialStore out steps ∧
      ScalarReady I ε out ∧
      steps ≤ 4*outerQ ε + 14*(Nat.log 2 I.graph.n+1)^2 +
        20*I.graph.edges.length + 4*(outerInputs I ε).length + 80 := by
  let input := encodeInput I ε
  have hhead := headerCmd_run input initialStore
  have hcore : CoreRegs I ε (headerResult input initialStore) := headerResult_core I ε initialStore
  generalize hheader : headerResult input initialStore = header at hhead hcore
  let copied := scalarCopyN.eval input header
  have hcopy := Run.atom scalarCopyN header (input := input)
  have hcopied : CoreRegs I ε copied := hcore.transfer
    (by intro r hlo hhi; apply scalarCopyN.nat_frame; simp [scalarCopyN,Atom.natWrites]; omega)
    (by intro r hlo hhi; rfl)
  have hc60 : copied.nr 60 = I.graph.n := hcore.vertices
  obtain ⟨converted,cn,hconv,hreal,hccost,hcframe⟩ := NatToReal.convertCmd_run input copied
  have hconverted : CoreRegs I ε converted := hcopied.transfer
    (by intro r hlo hhi; exact hcframe.1 r (by omega))
    (by intro r hlo hhi; exact hcframe.2.1 r (by omega) (by omega))
  let kept := scalarKeepN.eval input converted
  have hkeep := Run.atom scalarKeepN converted (input := input)
  have hkept : CoreRegs I ε kept := hconverted.transfer
    (by intro r hlo hhi; rfl)
    (by intro r hlo hhi; apply scalarKeepN.real_frame; simp [scalarKeepN,Atom.realWrites]; omega)
  have hrealN : kept.rr 129 = I.graph.n := hreal.trans (by rw [hc60])
  obtain ⟨scanned,sn,hscan,hmin,hmax,hL,hC,hfound,hscost,hsnm,hsrm⟩ :=
    Scan.scan_encoded_correct I ε kept
  have hscanNat : ∀r, r < 150 → scanned.nr r = kept.nr r := by
    intro r hr
    exact Scan.scan_nat_frame input kept scanned sn r hscan (Or.inl hr)
  have hscanReal : ∀r, r < 150 → scanned.rr r = kept.rr r := by
    intro r hr
    exact Scan.scan_real_frame input kept scanned sn r hscan (Or.inl hr)
  have hscanned : CoreRegs I ε scanned := hkept.transfer
    (by intro r hlo hhi; exact hscanNat r (by omega))
    (by intro r hlo hhi; exact hscanReal r (by omega))
  have hscanN : scanned.rr 129 = I.graph.n := (hscanReal 129 (by omega)).trans hrealN
  obtain ⟨out,gn,hcount,hG,hgcost⟩ := countCmd_run I ε hε hε1 scanned
    ⟨hscanned.zero,hscanned.one,hfound,hscanned.budget,hscanned.ratio,hscanN,hmin,hmax⟩
  have hout : CoreRegs I ε out := hscanned.transfer
    (by intro r hlo hhi; exact countCmd_nat_frame hcount r (by omega) (by omega) (by omega))
    (by intro r hlo hhi; exact countCmd_real_frame hcount r (by omega))
  have hnm : out.nm = header.nm :=
    (countCmd_memory_frame hcount).1.trans (hsnm.trans hcframe.2.2.1)
  have hrm : out.rm = header.rm :=
    (countCmd_memory_frame hcount).2.trans (hsrm.trans hcframe.2.2.2)
  obtain ⟨hq,hs,hn,hz⟩ := headerResult_header I ε initialStore
  change headerResult (encodeInput I ε) initialStore = header at hheader
  rw [hheader] at hq hs hn hz
  have hready : ScalarReady I ε out := {
    toCoreRegs := hout
    realVertices := (countCmd_real_frame hcount 129 (by omega)).trans hscanN
    minimum := (countCmd_real_frame hcount 150 (by omega)).trans hmin
    maximum := (countCmd_real_frame hcount 151 (by omega)).trans hmax
    lengthSum := (countCmd_real_frame hcount 152 (by omega)).trans hL
    costSum := (countCmd_real_frame hcount 153 (by omega)).trans hC
    found := (countCmd_nat_frame hcount 150 (by omega) (by omega) (by omega)).trans hfound
    count := hG
    headerQ := (congrFun hnm 0).trans hq
    headerSource := (congrFun hnm 1).trans hs
    headerVertices := (congrFun hnm 2).trans hn
    headerZ := (congrFun hrm 0).trans hz
    naturalZero := by
      intro a ha
      rw [congrFun hnm a]
      have hf := (headerResult_memory_frame input initialStore a (by omega) (by omega) (by omega)).1
      rw [hheader] at hf
      exact hf
    realZero := by
      intro a ha
      rw [congrFun hrm a,←hheader]
      change Function.update (initialStore.rm) 0 _ a = 0
      simp [show a ≠ 0 by omega,initialStore] }
  have hrun := Run.seq hhead (Run.seq hcopy (Run.seq hconv (Run.seq hkeep (Run.seq hscan hcount))))
  refine ⟨out,(37+4*outerQ ε)+(1+(cn+(1+(sn+gn)))),hrun,hready,?_⟩
  rw [hc60] at hccost
  omega

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission
namespace Address
open Structured

private theorem standalone_Mission_RAMAddress__store_eq (s t : Store) (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm) : s = t := by
  cases s
  cases t
  simp_all

private theorem standalone_Mission_RAMAddress__body_run (input : RAMInput) (s : Store) (addr k : ℕ)
    (hone : s.nr 47 = 1) :
    Run input addressBody (loopStore s addr (k + 1))
      (loopStore s (addr + s.nr 41) k) 2 := by
  have heval : Atom.eval (⟨.natOp .sub 46 46 47, trivial⟩ : Atom) input
      (Atom.eval (⟨.natOp .add 44 44 41, trivial⟩ : Atom) input
        (loopStore s addr (k + 1))) = loopStore s (addr + s.nr 41) k := by
    apply standalone_Mission_RAMAddress__store_eq
    · funext r
      by_cases h46 : r = 46
      · subst r
        simp [Atom.eval, Store.ofRAM, ramStep, Store.at, loopStore, evalNat, hone]
      · by_cases h44 : r = 44
        · subst r
          simp [Atom.eval, Store.ofRAM, ramStep, Store.at, loopStore, evalNat, hone]
        · simp [Atom.eval, Store.ofRAM, ramStep, Store.at, loopStore, evalNat, hone, h44, h46]
    · rfl
    · rfl
    · rfl
  have h := Run.seq (input := input)
    (Run.atom (⟨.natOp .add 44 44 41, trivial⟩ : Atom) (loopStore s addr (k + 1)))
    (Run.atom (⟨.natOp .sub 46 46 47, trivial⟩ : Atom) _)
  rw [heval] at h
  exact h

private theorem loop_run (input : RAMInput) (s : Store) (addr k : ℕ)
    (hone : s.nr 47 = 1) (hzero : s.nr 48 = 0) :
    Run input addressLoop (loopStore s addr k)
      (loopStore s (addr + s.nr 41 * k) 0) (4 * k + 1) := by
  induction k generalizing addr with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      apply Run.loopFalse
      simp [Guard.eval, natTest, loopStore, hzero]
  | succ k ih =>
      have hg : (Guard.nat .lt 48 46).eval (loopStore s addr (k + 1)) = true := by
        simp [Guard.eval, natTest, loopStore, hzero]
      have h := Run.loopTrue hg (standalone_Mission_RAMAddress__body_run input s addr k hone) (ih (addr + s.nr 41))
      have ha : addr + s.nr 41 * (k + 1) = (addr + s.nr 41) + s.nr 41 * k := by ring
      have hn : 4 * (k + 1) + 1 = 1 + 2 + 1 + (4 * k + 1) := by omega
      rw [ha, hn]
      exact h

private theorem addressCmd_run (input : RAMInput) (s : Store) :
    Run input addressCmd s (addressResult s) (8 + 4 * s.nr 42) := by
  let s₁ := Atom.eval (⟨.natCopy 44 40, trivial⟩ : Atom) input s
  let s₂ := Atom.eval (⟨.natCopy 46 42, trivial⟩ : Atom) input s₁
  let s₃ := Atom.eval (⟨.natConst 47 1, trivial⟩ : Atom) input s₂
  let s₄ := Atom.eval (⟨.natConst 48 0, trivial⟩ : Atom) input s₃
  let s₅ := Atom.eval (⟨.natOp .add 45 43 43, trivial⟩ : Atom) input s₄
  let s₆ := Atom.eval (⟨.natOp .add 45 45 45, trivial⟩ : Atom) input s₅
  let s₇ := Atom.eval (⟨.natOp .add 44 44 45, trivial⟩ : Atom) input s₆
  have hprep : s₇ = loopStore (preparedStore s)
      (s.nr 40 + 4 * s.nr 43) (s.nr 42) := by
    apply standalone_Mission_RAMAddress__store_eq
    · funext r
      by_cases h44 : r = 44 <;> by_cases h45 : r = 45 <;>
        by_cases h46 : r = 46 <;> by_cases h47 : r = 47 <;> by_cases h48 : r = 48 <;>
        simp_all [s₇, s₆, s₅, s₄, s₃, s₂, s₁, Atom.eval, Store.ofRAM, ramStep,
          Store.at, evalNat, loopStore, preparedStore] <;> omega
    · rfl
    · rfl
    · rfl
  have hl := loop_run input (preparedStore s) (s.nr 40 + 4 * s.nr 43) (s.nr 42)
    (by simp [preparedStore]) (by simp [preparedStore])
  have hl' : Run input addressLoop s₇ (addressResult s) (4 * s.nr 42 + 1) := by
    simpa only [hprep, preparedStore, Function.update_of_ne (by decide : 41 ≠ 48),
      Function.update_of_ne (by decide : 41 ≠ 47),
      Function.update_of_ne (by decide : 41 ≠ 45), addressResult] using hl
  have h := Run.seq (Run.atom (⟨.natCopy 44 40, trivial⟩ : Atom) s)
    (Run.seq (Run.atom (⟨.natCopy 46 42, trivial⟩ : Atom) s₁)
    (Run.seq (Run.atom (⟨.natConst 47 1, trivial⟩ : Atom) s₂)
    (Run.seq (Run.atom (⟨.natConst 48 0, trivial⟩ : Atom) s₃)
    (Run.seq (Run.atom (⟨.natOp .add 45 43 43, trivial⟩ : Atom) s₄)
    (Run.seq (Run.atom (⟨.natOp .add 45 45 45, trivial⟩ : Atom) s₅)
    (Run.seq (Run.atom (⟨.natOp .add 44 44 45, trivial⟩ : Atom) s₆) hl'))))))
  have hn : 8 + 4 * s.nr 42 = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (4 * s.nr 42 + 1))))))) := by omega
  rw [hn]
  exact h

private theorem addressResult_value (s : Store) :
    (addressResult s).nr 44 = s.nr 40 + s.nr 41 * s.nr 42 + 4 * s.nr 43 := by
  simp [addressResult, loopStore]
  omega

private theorem addressResult_frame (s : Store) (r : ℕ)
    (h44 : r ≠ 44) (h45 : r ≠ 45) (h46 : r ≠ 46)
    (h47 : r ≠ 47) (h48 : r ≠ 48) :
    (addressResult s).nr r = s.nr r := by
  simp [addressResult, loopStore, preparedStore, h44, h45, h46, h47, h48]

private theorem addressResult_memory (s : Store) :
    (addressResult s).rr = s.rr ∧ (addressResult s).nm = s.nm ∧
      (addressResult s).rm = s.rm := ⟨rfl, rfl, rfl⟩

private theorem rectangle_index_lt (q i j : ℕ) (hi : i < q) (hj : j < q) :
    i * q + j < q ^ 2 := by
  have h := Nat.mul_le_mul_right q (show i + 1 ≤ q by omega)
  nlinarith

private theorem address_cost_le_rectangle (q i j : ℕ) (hi : i < q) (hj : j < q) :
    8 + 4 * (i * q + j) ≤ 8 + 4 * q ^ 2 := by
  have h := rectangle_index_lt q i j hi hj
  omega

private theorem tableAddress_stride (I : Instance) (ε : ℝ) (r v i j : ℕ) :
    tableAddress I ε r v i j = tableBase I ε r +
      (4 * I.graph.n) * (i * outerQ ε + j) + 4 * v := by
  unfold tableAddress
  ring

private theorem tableAddress_next_cost (I : Instance) (ε : ℝ) (r v i j : ℕ) :
    tableAddress I ε r v i (j + 1) = tableAddress I ε r v i j + 4 * I.graph.n := by
  unfold tableAddress
  ring

private theorem tableAddress_next_length (I : Instance) (ε : ℝ) (r v i j : ℕ) :
    tableAddress I ε r v (i + 1) j = tableAddress I ε r v i j +
      4 * I.graph.n * outerQ ε := by
  unfold tableAddress
  ring

private theorem tableAddress_change_vertex (I : Instance) (ε : ℝ) (r v u i j : ℕ) :
    tableAddress I ε r v i j - 4 * v + 4 * u = tableAddress I ε r u i j := by
  rw [tableAddress_stride, tableAddress_stride, Nat.add_sub_cancel]

end Address
end NearLinearRSP.TwoResources.Mission
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem layoutFirst_eval (input : RAMInput) (s : Store) :
    evalAtoms input layoutFirst s = layoutFirstResult s := by
  ext r <;> simp [evalAtoms, layoutFirst, layoutFirstResult, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update]

private theorem layoutSecond_eval (input : RAMInput) (s : Store) :
    evalAtoms input layoutSecond s = layoutSecondResult s := by
  ext r <;> simp [evalAtoms, layoutSecond, layoutSecondResult, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update]

private theorem layoutThird_eval (input : RAMInput) (s : Store) :
    evalAtoms input layoutThird s = layoutThirdResult s := by
  ext r <;> simp [evalAtoms, layoutThird, layoutThirdResult, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update]

private theorem layoutFinish_eval (input : RAMInput) (s : Store) :
    evalAtoms input layoutFinish s = layoutFinishResult s := by
  ext r <;> simp [evalAtoms, layoutFinish, layoutFinishResult, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, two_mul, show ∀ n : ℕ, 3*n=n+n+n by omega]

private theorem layout_counts (input : RAMInput) (s : Store) :
    (layoutState1 input s).nr 42 = s.nr 124 ∧
    (layoutState2 input s).nr 42 = s.nr 124 ∧
    (layoutState3 input s).nr 42 = s.nr 132 := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

private theorem layoutCmd_run (input : RAMInput) (s : Store) :
    Run input layoutCmd s (layoutResult input s)
      (55 + 8 * s.nr 124 + 4 * s.nr 132) := by
  have h1 := run_atoms input layoutFirst s
  rw [layoutFirst_eval] at h1
  have ha1 := Address.addressCmd_run input (layoutState1 input s)
  have hr2 := run_atoms input layoutSecond (Address.addressResult (layoutState1 input s))
  rw [layoutSecond_eval] at hr2
  have ha2 := Address.addressCmd_run input (layoutState2 input s)
  have hr3 := run_atoms input layoutThird (Address.addressResult (layoutState2 input s))
  rw [layoutThird_eval] at hr3
  have ha3 := Address.addressCmd_run input (layoutState3 input s)
  have hf := run_atoms input layoutFinish (Address.addressResult (layoutState3 input s))
  rw [layoutFinish_eval] at hf
  have hr := Run.seq h1 (Run.seq ha1 (Run.seq hr2 (Run.seq ha2 (Run.seq hr3 (Run.seq ha3 hf)))))
  change Run input layoutCmd s (layoutResult input s)
    (4 + ((8 + 4 * (layoutState1 input s).nr 42) +
      (5 + ((8 + 4 * (layoutState2 input s).nr 42) +
        (5 + ((8 + 4 * (layoutState3 input s).nr 42) + 17)))))) at hr
  rcases layout_counts input s with ⟨hc1, hc2, hc3⟩
  rw [hc1, hc2, hc3] at hr
  convert hr using 1 <;> omega

private theorem layoutResult_values (input : RAMInput) (s : Store) :
    (layoutResult input s).nr 133 = s.nr 129 * s.nr 124 ^ 2 ∧
    (layoutResult input s).nr 134 = s.nr 130 + s.nr 129 * s.nr 124 ^ 2 * s.nr 132 ∧
    (layoutResult input s).nr 135 = (layoutResult input s).nr 134 ∧
    (layoutResult input s).nr 141 = (layoutResult input s).nr 134 + s.nr 124 + 64 ∧
    (layoutResult input s).nr 137 = (layoutResult input s).nr 141 + s.nr 121 ∧
    (layoutResult input s).nr 142 = (layoutResult input s).nr 141 + 2 * s.nr 121 ∧
    (layoutResult input s).nr 139 = (layoutResult input s).nr 141 + 3 * s.nr 121 ∧
    (layoutResult input s).nm 6 = (layoutResult input s).nr 135 ∧
    (layoutResult input s).nm 7 = (layoutResult input s).nr 141 := by
  have h1 : (Address.addressResult (layoutState1 input s)).nr 44 = s.nr 129 * s.nr 124 := by
    rw [Address.addressResult_value]
    simp [layoutState1, layoutFirstResult]
  have h2 : (Address.addressResult (layoutState2 input s)).nr 44 = s.nr 129 * s.nr 124 ^ 2 := by
    rw [Address.addressResult_value]
    change 0 + (Address.addressResult (layoutState1 input s)).nr 44 *
      (Address.addressResult (layoutState1 input s)).nr 124 + 4 * 0 = _
    rw [h1]
    have hq : (Address.addressResult (layoutState1 input s)).nr 124 = s.nr 124 := rfl
    rw [hq]
    ring
  have h3 : (Address.addressResult (layoutState3 input s)).nr 44 =
      s.nr 130 + s.nr 129 * s.nr 124 ^ 2 * s.nr 132 := by
    rw [Address.addressResult_value]
    change (Address.addressResult (layoutState2 input s)).nr 130 +
      (Address.addressResult (layoutState2 input s)).nr 44 *
      (Address.addressResult (layoutState2 input s)).nr 132 + 4 * 0 = _
    rw [h2]
    have ht : (Address.addressResult (layoutState2 input s)).nr 130 = s.nr 130 := rfl
    have hg : (Address.addressResult (layoutState2 input s)).nr 132 = s.nr 132 := rfl
    rw [ht, hg]
    omega
  have h133 : (Address.addressResult (layoutState3 input s)).nr 133 =
      s.nr 129 * s.nr 124 ^ 2 := by
    rw [Address.addressResult_frame _ 133 (by decide) (by decide) (by decide) (by decide) (by decide)]
    change (Address.addressResult (layoutState2 input s)).nr 44 = _
    exact h2
  have hq : (Address.addressResult (layoutState3 input s)).nr 124 = s.nr 124 := rfl
  have hn : (Address.addressResult (layoutState3 input s)).nr 121 = s.nr 121 := rfl
  refine ⟨?_, ?_, rfl, ?_, rfl, ?_, ?_, rfl, rfl⟩
  · exact h133
  · exact h3
  · change (Address.addressResult (layoutState3 input s)).nr 44 +
      (Address.addressResult (layoutState3 input s)).nr 124 + 64 =
      (Address.addressResult (layoutState3 input s)).nr 44 + s.nr 124 + 64
    rw [hq]
  · change (Address.addressResult (layoutState3 input s)).nr 44 +
      (Address.addressResult (layoutState3 input s)).nr 124 + 64 +
      2 * (Address.addressResult (layoutState3 input s)).nr 121 = _
    rw [hn]
    rfl
  · change (Address.addressResult (layoutState3 input s)).nr 44 +
      (Address.addressResult (layoutState3 input s)).nr 124 + 64 +
      3 * (Address.addressResult (layoutState3 input s)).nr 121 = _
    rw [hn]
    rfl

private theorem layoutResult_headers (input : RAMInput) (s : Store) :
    (layoutResult input s).nr 138 = s.nr 129 * s.nr 124 ∧
    (layoutResult input s).nm 4 = s.nr 129 ∧
    (layoutResult input s).nm 5 = s.nr 129 * s.nr 124 := by
  have h1 : (Address.addressResult (layoutState1 input s)).nr 44 = s.nr 129 * s.nr 124 := by
    rw [Address.addressResult_value]
    simp [layoutState1, layoutFirstResult]
  exact ⟨h1, rfl, h1⟩

private theorem layoutResult_memory_frame (input : RAMInput) (s : Store) (a : ℕ)
    (h4 : a ≠ 4) (h5 : a ≠ 5) (h6 : a ≠ 6) (h7 : a ≠ 7) :
    (layoutResult input s).nm a = s.nm a ∧ (layoutResult input s).rm a = s.rm a := by
  constructor
  · change Function.update (Function.update (Function.update (Function.update s.nm 4 _) 5 _) 6 _) 7 _ a = s.nm a
    simp [h4, h5, h6, h7]
  · rfl

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem powerCacheBody_eval (input : RAMInput) (s : Store) (k : ℕ) :
    evalAtoms input powerCacheBodyOps (powerCacheState s k) = powerCacheState s (k+1) := by
  apply Store.ext
  · funext r
    by_cases h240 : r = 240 <;> by_cases h241 : r = 241 <;> by_cases h242 : r = 242 <;>
      simp_all [evalAtoms,powerCacheBodyOps,powerCacheState,Atom.eval,Store.ofRAM,
        Store.at,ramStep,evalNat,Function.update_apply,Nat.add_assoc]
  · funext r
    by_cases h240 : r = 240 <;>
      simp_all [evalAtoms,powerCacheBodyOps,powerCacheState,Atom.eval,Store.ofRAM,
        Store.at,ramStep,evalNat,evalReal,Function.update_apply,pow_succ]
  · rfl
  · funext a
    simp only [evalAtoms,powerCacheBodyOps,List.foldl_cons,List.foldl_nil]
    simp only [Structured.evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,
      evalReal,powerCacheState]
    by_cases he : a = s.nr 135+k
    · subst a
      simp
    · have hlt : (a < s.nr 135+(k+1)) ↔ a < s.nr 135+k := by omega
      simp [Function.update_apply,he,hlt]

private theorem powerCacheBody_run (input : RAMInput) (s : Store) (k : ℕ) :
    Run input (.atoms powerCacheBodyOps) (powerCacheState s k) (powerCacheState s (k+1)) 4 := by
  have h := run_atoms input powerCacheBodyOps (powerCacheState s k)
  rw [powerCacheBody_eval] at h
  exact h

private theorem powerCacheLoop_run (input : RAMInput) (s : Store) (k d : ℕ)
    (he : k+d = s.nr 124) :
    Run input powerCacheLoop (powerCacheState s k) (powerCacheState s (k+d)) (6*d+1) := by
  induction d generalizing k with
  | zero =>
      have hk : k = s.nr 124 := by omega
      simp only [Nat.add_zero]
      apply Run.loopFalse
      simp [Guard.eval,natTest,powerCacheState,hk]
  | succ d ih =>
      have hg : (Guard.nat .lt 240 124).eval (powerCacheState s k) = true := by
        simp [Guard.eval,natTest,powerCacheState]
        omega
      have h := Run.loopTrue hg (powerCacheBody_run input s k) (ih (k+1) (by omega))
      simpa only [powerCacheLoop,show k+(d+1)=(k+1)+d by omega,
        show 6*(d+1)+1=1+4+1+(6*d+1) by omega] using h

private theorem powerCacheCmd_run (input : RAMInput) (s : Store) :
    Run input powerCacheCmd s (powerCacheState s (s.nr 124)) (6*s.nr 124+5) := by
  have hi : evalAtoms input powerCacheInit s = powerCacheState s 0 := by
    apply Store.ext <;> simp [evalAtoms,powerCacheInit,powerCacheState,Atom.eval,
      Store.ofRAM,Store.at,ramStep]
    funext a
    have hn : ¬ (s.nr 135 ≤ a ∧ a < s.nr 135) := by omega
    simp [hn]
  have hl := powerCacheLoop_run input s 0 (s.nr 124) (by omega)
  simp only [Nat.zero_add] at hl
  have h := Run.seq (run_atoms input powerCacheInit s) (by simpa only [hi] using hl)
  change Run input powerCacheCmd s (powerCacheState s (s.nr 124)) (4+(6*s.nr 124+1)) at h
  convert h using 1 <;> omega

private theorem powerCache_values (s : Store) (a : ℕ) (ha : a < s.nr 124) :
    (powerCacheState s (s.nr 124)).rm (s.nr 135+a) = s.rr 128^a := by
  simp [powerCacheState,ha]

private theorem powerCache_frame (s : Store) (a : ℕ)
    (ha : a < s.nr 135 ∨ s.nr 135+s.nr 124 ≤ a) :
    (powerCacheState s (s.nr 124)).rm a = s.rm a := by
  have hn : ¬(s.nr 135 ≤ a ∧ a < s.nr 135+s.nr 124) := by omega
  simp [powerCacheState,hn]

private theorem powerCache_natMemory (s : Store) :
    (powerCacheState s (s.nr 124)).nm = s.nm := rfl

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query
open Structured

private theorem prepend_run (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) :
    Run input prependCmd s (prependResult s) 3 := by
  have heval : evalAtoms input prependAtoms s = prependResult s := by
    apply Store.ext <;>
      simp [evalAtoms, prependAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
        evalNat, prependResult, hone]
  have h := run_atoms input prependAtoms s
  rw [heval] at h
  exact h

private theorem storesList_cons (mem : ℕ → ℕ) (base u : ℕ) (xs : List ℕ)
    (hb : 0 < base) (h : StoresList mem base xs) :
    StoresList (Function.update mem (base - 1) u) (base - 1) (u :: xs) := by
  intro k hk
  cases k with
  | zero => simp
  | succ k =>
      have hk' : k < xs.length := by simpa using hk
      have ha : base - 1 + (k + 1) = base + k := by omega
      have hne : base + k ≠ base - 1 := by omega
      simpa [ha, hne] using h k hk'

private theorem storesList_map (mem : ℕ → ℕ) (base : ℕ) (xs : List ℕ)
    (h : StoresList mem base xs) :
    (List.range xs.length).map (fun k => mem (base + k)) = xs := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simpa using h k hk'

private theorem prepend_stores (s : Store) (xs : List ℕ)
    (hlen : s.nr 2 = xs.length) (hbase : 0 < s.nr 3)
    (hmem : StoresList s.nm (s.nr 3) xs) :
    (prependResult s).nr 2 = (s.nr 0 :: xs).length ∧
    StoresList (prependResult s).nm ((prependResult s).nr 3) (s.nr 0 :: xs) := by
  constructor
  · simp [prependResult, hlen]
  · simpa [prependResult] using storesList_cons s.nm (s.nr 3) (s.nr 0) xs hbase hmem

private theorem prepend_memory_frame (s : Store) (a : ℕ) (ha : a < s.nr 3 - 1) :
    (prependResult s).nm a = s.nm a := by
  simp [prependResult, ne_of_lt ha]

private theorem score_run (input : RAMInput) (s : Store) :
    Run input scoreCmd s (scoreResult input s) 13 := by
  exact run_atoms input scoreAtoms s

private theorem score_value (input : RAMInput) (s : Store) :
    (scoreResult input s).rr 5 =
      (1 - s.rm (s.nr 27)) +
        s.rm (s.nr 21 + s.nr 16) * s.rr 1 / s.rr 3 +
        s.rm (s.nr 21 + s.nr 17) * s.rr 2 / s.rr 4 := by
  simp [scoreResult, evalAtoms, scoreAtoms, Atom.eval, Store.ofRAM, ramStep,
    Store.at, evalNat, evalReal]

private theorem score_nat_frame (input : RAMInput) (s : Store) (r : ℕ) (h : r ≠ 39) :
    (scoreResult input s).nr r = s.nr r := by
  simp [scoreResult, evalAtoms, scoreAtoms, Atom.eval, Store.ofRAM, ramStep,
    Store.at, evalNat, evalReal, h]

private theorem score_real_frame (input : RAMInput) (s : Store) (r : ℕ)
    (h5 : r ≠ 5) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9)
    (h10 : r ≠ 10) (h13 : r ≠ 13) (h14 : r ≠ 14) :
    (scoreResult input s).rr r = s.rr r := by
  simp [scoreResult, evalAtoms, scoreAtoms, Atom.eval, Store.ofRAM, ramStep,
    Store.at, evalNat, evalReal, h5, h7, h8, h9, h10, h13, h14]

private theorem score_memory_frame (input : RAMInput) (s : Store) :
    (scoreResult input s).nm = s.nm ∧ (scoreResult input s).rm = s.rm := by
  constructor <;> rfl

private theorem choose_run (input : RAMInput) (s : Store) :
    Run input chooseCmd s (chooseResult input s) (chooseCost s) := by
  by_cases h : s.rr 5 < s.rr 6
  · simp only [chooseResult, chooseCost, if_pos h]
    exact Run.branchTrue (by simpa [Guard.eval, realTest] using h)
      (run_atoms input chooseAtoms s)
  · simp only [chooseResult, chooseCost, if_neg h]
    exact Run.branchFalse (by simpa [Guard.eval, realTest] using h) (Run.skip s)

private theorem choose_cost_le (s : Store) : chooseCost s ≤ 6 := by
  unfold chooseCost
  split_ifs <;> omega

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Query

private theorem header_lt_outputEnd (I : Instance) (ε : ℝ) (a : ℕ) (ha : a < 16) :
    a < outputEnd I ε := by
  unfold outputEnd
  omega

private theorem target_lt_outputEnd (I : Instance) (ε : ℝ) (v off : ℕ)
    (hv : v < I.graph.n) (hoff : off < 4) :
    targetAddress v + off < outputEnd I ε := by
  unfold targetAddress outputEnd
  omega

private theorem table_lt_outputEnd (I : Instance) (ε : ℝ) (r v i j off : ℕ)
    (hr : r < (outerInputs I ε).length) (hv : v < I.graph.n)
    (hi : i < outerQ ε) (hj : j < outerQ ε) (hoff : off < 4) :
    tableAddress I ε r v i j + off < outputEnd I ε := by
  have hc := Address.rectangle_index_lt (outerQ ε) i j hi hj
  have hindex : (i * outerQ ε + j) * I.graph.n + v <
      outerQ ε ^ 2 * I.graph.n := by
    have hle := Nat.mul_le_mul_right I.graph.n (show i * outerQ ε + j + 1 ≤ outerQ ε ^ 2 by omega)
    nlinarith
  have hrow := Nat.mul_le_mul_left (4 * I.graph.n * outerQ ε ^ 2)
    (show r + 1 ≤ (outerInputs I ε).length by omega)
  unfold tableAddress tableBase outputEnd
  nlinarith

end NearLinearRSP.TwoResources.Mission.Query
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem ScalarReady.numeric {I : Instance} {ε : ℝ} {s : Store}
    (h : ScalarReady I ε s) : NumericRegs I ε s :=
  ⟨h.toCoreRegs,h.realVertices,h.minimum,h.maximum,h.lengthSum,h.costSum,h.found,h.count⟩

private theorem NumericRegs.transfer {I : Instance} {ε : ℝ} {s t : Store} (h : NumericRegs I ε s)
    (hn : ∀r, (121 ≤ r ∧ r ≤ 132) ∨ r = 150 → t.nr r = s.nr r)
    (hr : ∀r, 121 ≤ r → r ≤ 153 → t.rr r = s.rr r) : NumericRegs I ε t := by
  refine ⟨h.toCoreRegs.transfer (by intro r hlo hhi; exact hn r (by omega))
    (by intro r hlo hhi; exact hr r hlo (by omega)),?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hr 129 (by omega) (by omega)).trans h.realVertices
  · exact (hr 150 (by omega) (by omega)).trans h.minimum
  · exact (hr 151 (by omega) (by omega)).trans h.maximum
  · exact (hr 152 (by omega) (by omega)).trans h.lengthSum
  · exact (hr 153 (by omega) (by omega)).trans h.costSum
  · exact (hn 150 (by omega)).trans h.found
  · exact (hn 132 (by omega)).trans h.count

private theorem layoutResult_numeric {I : Instance} {ε : ℝ} {s : Store} (h : NumericRegs I ε s) :
    NumericRegs I ε (layoutResult (encodeInput I ε) s) := by
  apply h.transfer
  · intro r hr
    apply (layoutCmd_run (encodeInput I ε) s).nat_frame
    simp [layoutCmd,layoutFirst,layoutSecond,layoutThird,layoutFinish,
      Address.addressCmd,Address.addressLoop,Address.addressBody,
      Cmd.atoms,Cmd.natWrites,Atom.natWrites]
    omega
  · intro r hlo hhi
    rfl

private theorem layoutResult_layout {I : Instance} {ε : ℝ} {s : Store} (h : NumericRegs I ε s) :
    LayoutRegs I ε (layoutResult (encodeInput I ε) s) := by
  obtain ⟨hspan,he,hpower,hm,hh,ha,hl,_,_⟩ := layoutResult_values (encodeInput I ε) s
  have hout : (layoutResult (encodeInput I ε) s).nr 134 = Query.outputEnd I ε := by
    simpa only [h.targetEnd,h.vertexStride,h.q,h.count,Query.outputEnd] using he
  refine ⟨?_,hout,hpower.trans hout,?_,?_,?_,?_,?_⟩
  · simpa only [h.vertexStride,h.q] using hspan
  · simpa only [h.vertexStride,h.q] using (layoutResult_headers (encodeInput I ε) s).1
  · simpa only [hout,h.q,graphBase] using hm
  · rw [hh,hm,hout,h.q,h.vertices]
    rfl
  · rw [ha,hm,hout,h.q,h.vertices]
    rfl
  · rw [hl,hm,hout,h.q,h.vertices]
    rfl

private theorem layoutCacheCmd_run (I : Instance) (ε : ℝ) (s : Store) (hs : ScalarReady I ε s) :
    ∃ out steps, Run (encodeInput I ε) layoutCacheCmd s out steps ∧
      LayoutReady I ε out ∧ steps = 60+14*outerQ ε+4*(outerInputs I ε).length := by
  let input := encodeInput I ε
  let laid := layoutResult input s
  let out := powerCacheState laid (laid.nr 124)
  have hn : NumericRegs I ε laid := layoutResult_numeric hs.numeric
  have hl : LayoutRegs I ε laid := layoutResult_layout hs.numeric
  have hon : NumericRegs I ε out := hn.transfer
    (by
      intro r hr
      have h240 : r≠240 := by omega
      have h241 : r≠241 := by omega
      have h242 : r≠242 := by omega
      simp [out,powerCacheState,h240,h241,h242])
    (by intro r hlo hhi; simp [out,powerCacheState,show r ≠ 240 by omega])
  have hol : LayoutRegs I ε out := ⟨hl.span,hl.outputEnd,hl.powerBase,hl.rowStride,
    hl.map,hl.heads,hl.array,hl.links⟩
  have hheader : OutputHeaders I ε laid := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (layoutResult_memory_frame input s 0 (by omega) (by omega) (by omega) (by omega)).1.trans hs.headerQ
    · exact (layoutResult_memory_frame input s 1 (by omega) (by omega) (by omega) (by omega)).1.trans hs.headerSource
    · exact (layoutResult_memory_frame input s 2 (by omega) (by omega) (by omega) (by omega)).1.trans hs.headerVertices
    · exact (layoutResult_headers input s).2.1.trans hs.vertexStride
    · simpa only [hs.vertexStride,hs.q] using (layoutResult_headers input s).2.2
    · exact hl.powerBase
    · exact hl.map
    · exact hs.headerZ
  have hepos : 0 < Query.outputEnd I ε := by unfold Query.outputEnd; omega
  have hoh : OutputHeaders I ε out := ⟨hheader.q,hheader.source,hheader.vertices,
    hheader.vertexStride,hheader.rowStride,hheader.powerBase,hheader.map,
    (powerCache_frame laid 0 (Or.inl (hl.powerBase.symm ▸ hepos))).trans hheader.z⟩
  have hready : LayoutReady I ε out := {
    numeric := hon, layout := hol, headers := hoh
    powers := by
      intro a ha
      have hv := powerCache_values laid a (hn.q.symm ▸ ha)
      simpa only [hl.powerBase,hn.z] using hv
    naturalZero := by
      intro a ha
      exact (layoutResult_memory_frame input s a (by omega) (by omega) (by omega) (by omega)).1.trans
        (hs.naturalZero a (by omega))
    realZero := by
      intro a ha houtside
      have hf := powerCache_frame laid a (by simpa only [hl.powerBase,hn.q] using houtside)
      exact hf.trans (hs.realZero a ha) }
  have hrun := Run.seq (layoutCmd_run input s) (powerCacheCmd_run input laid)
  refine ⟨out,60+14*outerQ ε+4*(outerInputs I ε).length,?_,hready,rfl⟩
  convert hrun using 1 <;> simp only [layoutCacheCmd,hs.q,hs.count,hn.q] <;> omega

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem activeStep_register (input : RAMInput) (s : Store) (r : ℕ)
    (h140 : r ≠ 140) (h143 : r ≠ 143) (h144 : r ≠ 144)
    (h145 : r ≠ 145) (h146 : r ≠ 146) (h147 : r ≠ 147) :
    (activeStep input s).nr r = s.nr r := by
  simp only [activeStep, Function.update_of_ne h147]
  rw [activeResult_frame_register _ r h143 h144 h145 h146]
  simp [activeLoaded, h140]

@[simp] private theorem activeStep_pointer (input : RAMInput) (s : Store) :
    (activeStep input s).nr 147 = s.nr 147 + 1 := by simp [activeStep]

private theorem activeScanBody_run (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1) :
    ∃ steps ≤ 10, Run input activeScanBody s (activeStep input s) steps := by
  have hload : Run input (.atom ⟨.inputNat 140 147, trivial⟩) s (activeLoaded input s) 1 :=
    Run.atom _ s
  obtain ⟨steps, hsteps, hins⟩ := activeInsert_run input (activeLoaded input s)
    (by simpa [activeLoaded] using hz)
  have hinc : Run input (.atom ⟨.natOp .add 147 147 126, trivial⟩)
      (activeResult (activeLoaded input s)) (activeStep input s) 1 := by
    have h := Run.atom (input := input) (⟨.natOp .add 147 147 126, trivial⟩ : Atom)
      (activeResult (activeLoaded input s))
    have hr147 : (activeResult (activeLoaded input s)).nr 147 = s.nr 147 := by
      rw [activeResult_frame_register _ 147 (by decide) (by decide) (by decide) (by decide)]
      simp [activeLoaded]
    have hr126 : (activeResult (activeLoaded input s)).nr 126 = 1 := by
      rw [activeResult_frame_register _ 126 (by decide) (by decide) (by decide) (by decide)]
      simpa [activeLoaded] using hone
    simpa [Atom.eval, Store.at, Store.ofRAM, ramStep, evalNat, activeStep, hr147, hr126] using h
  exact ⟨1 + (steps + 1), by omega, Run.seq hload (Run.seq hins hinc)⟩

private theorem activeScan_run (input : RAMInput) (remaining : ℕ) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1)
    (hend : s.nr 147 + remaining = s.nr 148) :
    ∃ steps ≤ 12 * remaining + 1,
      Run input activeScan s (activeScanResult input remaining s) steps := by
  induction remaining generalizing s with
  | zero =>
      refine ⟨1, le_rfl, Run.loopFalse ?_⟩
      simp [Guard.eval, natTest, show s.nr 147 = s.nr 148 by omega]
  | succ remaining ih =>
      obtain ⟨bodySteps, hb, hbody⟩ := activeScanBody_run input s hz hone
      have hz' : (activeStep input s).nr 125 = 0 := by
        rw [activeStep_register input s 125 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]; exact hz
      have hone' : (activeStep input s).nr 126 = 1 := by
        rw [activeStep_register input s 126 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]; exact hone
      have hend' : (activeStep input s).nr 147 + remaining = (activeStep input s).nr 148 := by
        rw [activeStep_pointer, activeStep_register input s 148 (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]
        omega
      obtain ⟨tailSteps, ht, htail⟩ := ih (activeStep input s) hz' hone' hend'
      refine ⟨1 + bodySteps + 1 + tailSteps, by omega, ?_⟩
      exact Run.loopTrue (by simp [Guard.eval, natTest, show s.nr 147 < s.nr 148 by omega]) hbody htail

private theorem ActiveRep.loaded {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (input : RAMInput) :
    ActiveRep n base array xs (activeLoaded input s) := by
  refine ⟨h.nodup, h.valid, ?_, ?_, ?_, h.separation, h.absent, h.index, h.value⟩
  · simpa [activeLoaded] using h.base_reg
  · simpa [activeLoaded] using h.array_reg
  · simpa [activeLoaded] using h.count_reg

private theorem ActiveRep.step {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (input : RAMInput)
    (hv : input.naturals (s.nr 147) < n) (hone : s.nr 126 = 1) :
    ActiveRep n base array (stableInsert xs (input.naturals (s.nr 147))) (activeStep input s) := by
  have hi := (h.loaded input).insert (by simpa [activeLoaded] using hv)
    (by simpa [activeLoaded] using hone)
  refine ⟨hi.nodup, hi.valid, ?_, ?_, ?_, hi.separation, hi.absent, hi.index, hi.value⟩
  · simpa [activeStep] using hi.base_reg
  · simpa [activeStep] using hi.array_reg
  · simpa [activeStep, activeLoaded] using hi.count_reg

private theorem activeScan_rep (input : RAMInput) (remaining : ℕ) (s : Store)
    (n base array : ℕ) (xs : List ℕ) (h : ActiveRep n base array xs s)
    (hone : s.nr 126 = 1)
    (hv : ∀ v ∈ scannedVertices input (s.nr 147) remaining, v < n) :
    ActiveRep n base array
      ((scannedVertices input (s.nr 147) remaining).foldl stableInsert xs)
      (activeScanResult input remaining s) := by
  induction remaining generalizing s xs with
  | zero => exact h
  | succ remaining ih =>
      have hhead := hv (input.naturals (s.nr 147)) (by simp [scannedVertices])
      have hstep := h.step input hhead hone
      have hone' : (activeStep input s).nr 126 = 1 := by
        rw [activeStep_register input s 126 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]; exact hone
      have htail : ∀ v ∈ scannedVertices input ((activeStep input s).nr 147) remaining, v < n := by
        intro v hmem
        apply hv v
        simpa [scannedVertices, activeStep_pointer] using Or.inr hmem
      simpa [scannedVertices, activeScanResult, activeStep_pointer] using
        ih (activeStep input s) _ hstep hone' htail

private theorem scannedVertices_pairs (input : RAMInput) (start : ℕ) (edges : List (ℕ × ℕ))
    (hinput : ∀ k e, edges[k]? = some e →
      input.naturals (start + 2 * k) = e.1 ∧ input.naturals (start + 2 * k + 1) = e.2) :
    scannedVertices input start (2 * edges.length) = edges.flatMap (fun e => [e.1,e.2]) := by
  induction edges generalizing start with
  | nil => rfl
  | cons e edges ih =>
      have hhead := hinput 0 e (by simp)
      have htail : ∀ k e', edges[k]? = some e' →
          input.naturals (start + 2 + 2 * k) = e'.1 ∧
          input.naturals (start + 2 + 2 * k + 1) = e'.2 := by
        intro k e' he
        simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hinput (k + 1) e' (by simpa using he)
      rw [show 2 * (e :: edges).length = (2 * edges.length + 1) + 1 by simp; omega]
      simp only [scannedVertices, List.flatMap_cons, List.cons_append, List.nil_append]
      rw [show start + 1 + 1 = start + 2 by omega, ih (start + 2) htail]
      simpa using hhead

private theorem encoded_scannedVertices (I : Instance) (ε : ℝ) :
    scannedVertices (encodeInput I ε) 3 (2 * I.graph.edges.length) =
      I.graph.edges.flatMap (fun e => [e.1,e.2]) := by
  apply scannedVertices_pairs
  intro k e he
  simp [encodeInput, show 3 + 2 * k ≠ 0 by omega, show 3 + 2 * k ≠ 1 by omega,
    show 3 + 2 * k ≠ 2 by omega, show 3 + 2 * k + 1 ≠ 0 by omega,
    show 3 + 2 * k + 1 ≠ 1 by omega, show 3 + 2 * k + 1 ≠ 2 by omega,
    show 3 + 2 * k - 3 = 2 * k by omega,
    show 3 + 2 * k + 1 - 3 = 2 * k + 1 by omega, Nat.add_div, Nat.add_mod, he]

private theorem activeInitAtoms_eval (input : RAMInput) (s : Store) :
    evalAtoms input activeInitAtoms s = activeInitPrepared s := by
  ext r <;> simp [evalAtoms, activeInitAtoms, activeInitPrepared, Atom.eval, Store.ofRAM,
    Store.at, ramStep, evalNat, Function.update, two_mul]

private theorem activeInit_run (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1) :
    ∃ steps ≤ 24 * s.nr 122 + 14,
      Run input activeInit s (activeInitResult input s) steps := by
  have hp := run_atoms input activeInitAtoms s
  rw [activeInitAtoms_eval] at hp
  obtain ⟨insertSteps, hi, hins⟩ := activeInsert_run input (activeInitPrepared s)
    (by simpa [activeInitPrepared] using hz)
  have hz' : (activeResult (activeInitPrepared s)).nr 125 = 0 := by
    rw [activeResult_frame_register _ 125 (by decide) (by decide) (by decide) (by decide)]
    simpa [activeInitPrepared] using hz
  have hone' : (activeResult (activeInitPrepared s)).nr 126 = 1 := by
    rw [activeResult_frame_register _ 126 (by decide) (by decide) (by decide) (by decide)]
    simpa [activeInitPrepared] using hone
  have hend : (activeResult (activeInitPrepared s)).nr 147 + 2 * s.nr 122 =
      (activeResult (activeInitPrepared s)).nr 148 := by
    rw [activeResult_frame_register _ 147 (by decide) (by decide) (by decide) (by decide),
      activeResult_frame_register _ 148 (by decide) (by decide) (by decide) (by decide)]
    simp [activeInitPrepared, Nat.add_comm]
  obtain ⟨scanSteps, hs, hscan⟩ := activeScan_run input (2 * s.nr 122)
    (activeResult (activeInitPrepared s)) hz' hone' hend
  exact ⟨5 + (insertSteps + scanSteps), by omega, Run.seq hp (Run.seq hins hscan)⟩

private theorem activeInit_rep (I : Instance) (ε : ℝ) (s : Store) (base array : ℕ)
    (hm : s.nr 122 = I.graph.edges.length) (hsource : s.nr 123 = I.source)
    (hbase : s.nr 141 = base) (harray : s.nr 142 = array)
    (hsep : base + I.graph.n ≤ array) (hone : s.nr 126 = 1)
    (hzero : ∀ v < I.graph.n, s.nm (base + v) = 0) :
    ActiveRep I.graph.n base array (activeVertices I)
      (activeInitResult (encodeInput I ε) s) := by
  have he : ActiveRep I.graph.n base array [] (activeInitPrepared s) := by
    apply ActiveRep.empty
    · simpa [activeInitPrepared] using hbase
    · simpa [activeInitPrepared] using harray
    · simp [activeInitPrepared]
    · exact hsep
    · exact hzero
  have hi := he.insert (by simpa [activeInitPrepared, hsource] using I.source_valid)
    (by simpa [activeInitPrepared] using hone)
  have hone' : (activeResult (activeInitPrepared s)).nr 126 = 1 := by
    rw [activeResult_frame_register _ 126 (by decide) (by decide) (by decide) (by decide)]
    simpa [activeInitPrepared] using hone
  have hptr : (activeResult (activeInitPrepared s)).nr 147 = 3 := by
    rw [activeResult_frame_register _ 147 (by decide) (by decide) (by decide) (by decide)]
    simp [activeInitPrepared]
  have hvalid : ∀ v ∈ scannedVertices (encodeInput I ε)
      ((activeResult (activeInitPrepared s)).nr 147) (2 * s.nr 122), v < I.graph.n := by
    rw [hptr, hm, encoded_scannedVertices]
    intro v hv
    obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    have hend := I.graph.endpoints e he
    simp at hv
    rcases hv with rfl | rfl
    · exact hend.1
    · exact hend.2
  have hr := activeScan_rep (encodeInput I ε) (2 * s.nr 122)
    (activeResult (activeInitPrepared s)) I.graph.n base array _ hi hone' hvalid
  have horder : (scannedVertices (encodeInput I ε) 3 (2 * I.graph.edges.length)).foldl
      stableInsert (stableInsert [] I.source) = activeVertices I := by
    rw [encoded_scannedVertices, activeVertices_eq_stableFold]
    rfl
  have hsv : (activeInitPrepared s).nr 140 = I.source := by simp [activeInitPrepared, hsource]
  rw [hsv, hptr, hm, horder] at hr
  simpa only [activeInitResult, hm] using hr

private theorem ActiveRep.insert_memory_frame {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (hv : s.nr 140 < n) (hone : s.nr 126 = 1)
    (a : ℕ) (hb : a < base ∨ base + n ≤ a) (ha : a < array ∨ array + n ≤ a) :
    (activeResult s).nm a = s.nm a := by
  by_cases hm : s.nr 140 ∈ xs
  · have hz : s.nm (s.nr 141 + s.nr 140) ≠ 0 := by
      rw [h.base_reg]
      exact fun he => (h.flag_zero_iff _ hv).mp he hm
    exact congrFun (activeResult_present s hz).1 a
  · have hn := (h.insert hv hone).length_le
    simp only [stableInsert, if_neg hm, List.length_append, List.length_singleton] at hn
    apply activeResult_frame_memory
    · rw [h.base_reg]; omega
    · rw [h.array_reg, h.count_reg]; omega

private theorem activeScan_memory_frame (input : RAMInput) (remaining : ℕ) (s : Store)
    (n base array : ℕ) (xs : List ℕ) (h : ActiveRep n base array xs s)
    (hone : s.nr 126 = 1)
    (hv : ∀ v ∈ scannedVertices input (s.nr 147) remaining, v < n)
    (a : ℕ) (hb : a < base ∨ base + n ≤ a) (ha : a < array ∨ array + n ≤ a) :
    (activeScanResult input remaining s).nm a = s.nm a := by
  induction remaining generalizing s xs with
  | zero => rfl
  | succ remaining ih =>
      have hhead := hv (input.naturals (s.nr 147)) (by simp [scannedVertices])
      have hstep := h.step input hhead hone
      have hone' : (activeStep input s).nr 126 = 1 := by
        rw [activeStep_register input s 126 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        exact hone
      have htail : ∀ v ∈ scannedVertices input ((activeStep input s).nr 147) remaining, v < n := by
        intro v hmem
        apply hv v
        simpa [scannedVertices, activeStep_pointer] using Or.inr hmem
      have hi := ih (activeStep input s) _ hstep hone' htail
      have hs := (h.loaded input).insert_memory_frame
        (by simpa [activeLoaded] using hhead) (by simpa [activeLoaded] using hone) a hb ha
      exact hi.trans hs

private theorem activeInit_memory_frame (I : Instance) (ε : ℝ) (s : Store) (base array : ℕ)
    (hm : s.nr 122 = I.graph.edges.length) (hsource : s.nr 123 = I.source)
    (hbase : s.nr 141 = base) (harray : s.nr 142 = array)
    (hsep : base + I.graph.n ≤ array) (hone : s.nr 126 = 1)
    (hzero : ∀ v < I.graph.n, s.nm (base + v) = 0)
    (a : ℕ) (hb : a < base ∨ base + I.graph.n ≤ a)
    (ha : a < array ∨ array + I.graph.n ≤ a) :
    (activeInitResult (encodeInput I ε) s).nm a = s.nm a := by
  have he : ActiveRep I.graph.n base array [] (activeInitPrepared s) := by
    apply ActiveRep.empty
    · simpa [activeInitPrepared] using hbase
    · simpa [activeInitPrepared] using harray
    · simp [activeInitPrepared]
    · exact hsep
    · exact hzero
  have hsv : (activeInitPrepared s).nr 140 < I.graph.n := by
    simpa [activeInitPrepared, hsource] using I.source_valid
  have hone0 : (activeInitPrepared s).nr 126 = 1 := by
    simpa [activeInitPrepared] using hone
  have hi := he.insert hsv hone0
  have hone' : (activeResult (activeInitPrepared s)).nr 126 = 1 := by
    rw [activeResult_frame_register _ 126 (by decide) (by decide) (by decide) (by decide)]
    exact hone0
  have hptr : (activeResult (activeInitPrepared s)).nr 147 = 3 := by
    rw [activeResult_frame_register _ 147 (by decide) (by decide) (by decide) (by decide)]
    simp [activeInitPrepared]
  have hvalid : ∀ v ∈ scannedVertices (encodeInput I ε)
      ((activeResult (activeInitPrepared s)).nr 147) (2 * s.nr 122), v < I.graph.n := by
    rw [hptr, hm, encoded_scannedVertices]
    intro v hv
    obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    have hend := I.graph.endpoints e he
    simp at hv
    rcases hv with rfl | rfl
    · exact hend.1
    · exact hend.2
  exact (activeScan_memory_frame (encodeInput I ε) (2 * s.nr 122) _
    I.graph.n base array _ hi hone' hvalid a hb ha).trans
      (he.insert_memory_frame hsv hone0 a hb ha)

private theorem activeInit_register_frame (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1) (r : ℕ)
    (hr : r ∉ ({140, 143, 144, 145, 146, 147, 148} : Finset ℕ)) :
    (activeInitResult input s).nr r = s.nr r := by
  obtain ⟨steps, _, hrun⟩ := activeInit_run input s hz hone
  apply hrun.nat_frame
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  simp_all [activeInit, activeInitAtoms, activeScan, activeScanBody, activeInsert,
    activeProbe, activeAppend, Cmd.atoms, Cmd.natWrites, Atom.natWrites]

private theorem activeInit_real_frame (input : RAMInput) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1) :
    (activeInitResult input s).rr = s.rr ∧ (activeInitResult input s).rm = s.rm := by
  obtain ⟨steps, _, hrun⟩ := activeInit_run input s hz hone
  constructor
  · funext r
    apply hrun.real_frame
    simp [activeInit, activeInitAtoms, activeScan, activeScanBody, activeInsert,
      activeProbe, activeAppend, Cmd.atoms, Cmd.realWrites, Atom.realWrites]
  · apply hrun.realMemory_frame
    rfl

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem LayoutRegs.transfer {I : Instance} {ε : ℝ} {s t : Store} (h : LayoutRegs I ε s)
    (hn : ∀r, r ∈ ({133,134,135,137,138,139,141,142} : Finset ℕ) → t.nr r=s.nr r) :
    LayoutRegs I ε t :=
  ⟨(hn 133 (by decide)).trans h.span,(hn 134 (by decide)).trans h.outputEnd,
   (hn 135 (by decide)).trans h.powerBase,(hn 138 (by decide)).trans h.rowStride,
   (hn 141 (by decide)).trans h.map,(hn 137 (by decide)).trans h.heads,
   (hn 142 (by decide)).trans h.array,(hn 139 (by decide)).trans h.links⟩

private theorem OutputHeaders.transfer {I : Instance} {ε : ℝ} {s t : Store} (h : OutputHeaders I ε s)
    (hn : ∀a, a<8 → a≠3 → t.nm a=s.nm a) (hr : t.rm 0=s.rm 0) :
    OutputHeaders I ε t :=
  ⟨(hn 0 (by omega) (by omega)).trans h.q,(hn 1 (by omega) (by omega)).trans h.source,
   (hn 2 (by omega) (by omega)).trans h.vertices,(hn 4 (by omega) (by omega)).trans h.vertexStride,
   (hn 5 (by omega) (by omega)).trans h.rowStride,(hn 6 (by omega) (by omega)).trans h.powerBase,
   (hn 7 (by omega) (by omega)).trans h.map,hr.trans h.z⟩

private theorem graphCmd_run (I : Instance) (ε : ℝ) (s : Store) (hs : LayoutReady I ε s) :
    ∃ out steps, Run (encodeInput I ε) graphCmd s out steps ∧
      GraphReady I ε out ∧ steps ≤ 35*I.graph.edges.length+21 := by
  let input := encodeInput I ε
  let active := activeInitResult input s
  have hbase8 : 8 ≤ graphBase I ε := by unfold graphBase; omega
  have hsep : graphBase I ε+I.graph.n ≤ arrayBase I ε := by unfold arrayBase; omega
  have hzero : ∀v<I.graph.n, s.nm (graphBase I ε+v)=0 := by
    intro v hv
    exact hs.naturalZero _ (by omega)
  have hactive : ActiveRep I.graph.n (graphBase I ε) (arrayBase I ε) (activeVertices I) active :=
    activeInit_rep I ε s (graphBase I ε) (arrayBase I ε) hs.numeric.edges
      hs.numeric.source hs.layout.map hs.layout.array hsep hs.numeric.one hzero
  obtain ⟨an,hacost,harun⟩ := activeInit_run input s hs.numeric.zero hs.numeric.one
  have haframe : ∀r, r ∉ ({140,143,144,145,146,147,148}:Finset ℕ) → active.nr r=s.nr r :=
    activeInit_register_frame input s hs.numeric.zero hs.numeric.one
  have hareal := activeInit_real_frame input s hs.numeric.zero hs.numeric.one
  have hamem : ∀a, (a<graphBase I ε ∨ graphBase I ε+I.graph.n≤a) →
      (a<arrayBase I ε ∨ arrayBase I ε+I.graph.n≤a) → active.nm a=s.nm a :=
    activeInit_memory_frame I ε s (graphBase I ε) (arrayBase I ε) hs.numeric.edges
      hs.numeric.source hs.layout.map hs.layout.array hsep hs.numeric.one hzero
  have han : NumericRegs I ε active := hs.numeric.transfer
    (by intro r hr; apply haframe; simp; omega)
    (by intro r hlo hhi; exact congrFun hareal.1 r)
  have hal : LayoutRegs I ε active := hs.layout.transfer (by
    intro r hr; apply haframe; simp only [Finset.mem_insert,Finset.mem_singleton] at hr ⊢; omega)
  let prepared := evalAtoms input graphAdjPrepare active
  have hprepNat : ∀r, r≠120 → r≠163 → r≠164 → prepared.nr r=active.nr r := by
    intro r h120 h163 h164
    simp [prepared,graphAdjPrepare,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,h120,h163,h164]
  have hprepMem : ∀a, a≠3 → prepared.nm a=active.nm a := by
    intro a ha
    change Function.update active.nm 3 (active.nr 143) a=active.nm a
    simp [ha]
  have hprepared : ActiveRep I.graph.n (graphBase I ε) (arrayBase I ε)
      (activeVertices I) prepared := hactive.congr
    (hprepNat 141 (by omega) (by omega) (by omega))
    (hprepNat 142 (by omega) (by omega) (by omega))
    (hprepNat 143 (by omega) (by omega) (by omega))
    (by intro v hv; exact hprepMem _ (by omega))
    (by intro k hk; exact hprepMem _ (by unfold arrayBase; omega))
  have hpn : NumericRegs I ε prepared := han.transfer
    (by intro r hr; exact hprepNat r (by omega) (by omega) (by omega))
    (by intro r hlo hhi; rfl)
  have hpl : LayoutRegs I ε prepared := hal.transfer (by
    intro r hr; simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    exact hprepNat r (by omega) (by omega) (by omega))
  have hphead : prepared.nr 163 = headsBase I ε := hal.heads
  have hplink : prepared.nr 164 = linksBase I ε := hal.links
  have hhzero : ∀v<I.graph.n, prepared.nm (headsBase I ε+v)=0 := by
    intro v hv
    rw [hprepMem _ (by unfold headsBase; omega)]
    rw [hamem _ (by unfold headsBase; omega) (by unfold headsBase arrayBase; omega)]
    exact hs.naturalZero _ (by unfold headsBase; omega)
  obtain ⟨out,hadrun,hadj,hadreal,hadrm,hadmem,hadnat⟩ :=
    adjacencyScanCmd_correct I ε prepared (headsBase I ε) (linksBase I ε)
      hpn.edges hpn.one hpn.two hphead hplink
      (by unfold headsBase linksBase; omega) hhzero
  have hresult : ActiveRep I.graph.n (graphBase I ε) (arrayBase I ε)
      (activeVertices I) out := hprepared.congr
    (hadnat 141 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (hadnat 142 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (hadnat 143 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (by intro v hv; apply hadmem <;> simp only [headsBase,linksBase] <;> omega)
    (by
      intro k hk
      have hN := activeVertices_length_le_vertices I
      apply hadmem <;> simp only [headsBase,linksBase,arrayBase] <;> omega)
  have hon : NumericRegs I ε out := hpn.transfer
    (by intro r hr; apply hadnat <;> omega)
    (by intro r hlo hhi; exact congrFun hadreal r)
  have hol : LayoutRegs I ε out := hpl.transfer (by
    intro r hr; simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    apply hadnat <;> omega)
  have hlow : ∀a, a<graphBase I ε → a≠3 → out.nm a=s.nm a := by
    intro a ha h3
    exact (hadmem a (by unfold headsBase; omega) (by unfold linksBase; omega)).trans
      ((hprepMem a h3).trans (hamem a (Or.inl ha) (by unfold arrayBase; omega)))
  have hrealmem : out.rm=s.rm := hadrm.trans hareal.2
  have hoh : OutputHeaders I ε out := hs.headers.transfer
    (by intro a ha h3; exact hlow a (by omega) h3) (congrFun hrealmem 0)
  have hcount : out.nm 3=(activeVertices I).length := by
    rw [hadmem 3 (by unfold headsBase; omega) (by unfold linksBase; omega)]
    exact hactive.count_reg
  have hready : GraphReady I ε out := {
    numeric := hon, layout := hol, headers := hoh, activeCount := hcount, active := hresult,
    adjacency := hadj
    powers := by intro a ha; rw [hrealmem]; exact hs.powers a ha
    naturalZero := by
      intro a ha hb
      exact (hlow a hb (by omega)).trans (hs.naturalZero a ha)
    realZero := by intro a ha hb; rw [hrealmem]; exact hs.realZero a ha hb }
  have hrun := Run.seq harun (Run.seq (run_atoms input graphAdjPrepare active) hadrun)
  refine ⟨out,an+(4+(11*I.graph.edges.length+3)),hrun,hready,?_⟩
  rw [hs.numeric.edges] at hacost
  omega

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

private theorem capacityStart_eval (input : RAMInput) (s : Store) :
    capacityStart.eval input s = capacityState s 0 := by rfl

private theorem capacityDouble_eval (input : RAMInput) (s : Store) (k : ℕ) :
    capacityDouble.eval input (capacityState s k) = capacityState s (k + 1) := by
  apply Store.ext <;> try rfl
  funext a
  simp [capacityDouble, Atom.eval, ramStep, Store.at, Store.ofRAM,
    capacityState, evalNat, Function.update, pow_succ, Nat.mul_two]

private theorem chooseCapacity_run (input : RAMInput) (s : Store) :
    ∃ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2,
      Run input chooseCapacity s (capacityState s (Nat.clog 2 (s.nr 10))) k := by
  let h := Nat.clog 2 (s.nr 10)
  have hloop := run_bounded_loop input (Guard.nat .lt 11 10) (.atom capacityDouble)
    h 1 (fun k t => t = capacityState s k)
    (by
      intro k t hk ht
      subst t
      simp only [Guard.eval, capacityState, Function.update_self, natTest]
      simp only [Function.update_of_ne (show (10 : ℕ) ≠ 11 by omega)]
      exact Bool.decide_congr
        ((Nat.lt_clog_iff_pow_lt (b := 2) (x := s.nr 10) (y := k) (by decide)).symm))
    (by
      intro k t hk ht
      subst t
      refine ⟨capacityState s (k + 1), 1, ?_, rfl, le_rfl⟩
      simpa only [capacityDouble_eval] using Run.atom capacityDouble (capacityState s k))
    0 (capacityState s 0) (by omega) rfl
  obtain ⟨out, cost, hrun, hout, hcost⟩ := hloop
  subst out
  have hstart := Run.atom capacityStart s (input := input)
  rw [capacityStart_eval] at hstart
  refine ⟨1 + cost, by simp only [Nat.sub_zero] at hcost; omega, ?_⟩
  exact Run.seq hstart hrun

private theorem chooseCapacity_bounds (input : RAMInput) (s : Store) (hn : 0 < s.nr 10) :
    ∃ out k, Run input chooseCapacity s out k ∧ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2 ∧
      s.nr 10 ≤ out.nr 11 ∧ out.nr 11 < 2 * s.nr 10 ∧
      out.nm = s.nm ∧ out.rm = s.rm ∧ out.rr = s.rr ∧
      ∀ a, a ≠ 11 → out.nr a = s.nr a := by
  obtain ⟨k, hk, hrun⟩ := chooseCapacity_run input s
  have hb := capacity_bounds (s.nr 10) hn
  refine ⟨capacityState s (Nat.clog 2 (s.nr 10)), k, hrun, hk, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · exact hb.1
  · exact hb.2
  · intro a ha
    simp [capacityState, ha]

private theorem chooseCapacity_exact (input : RAMInput) (s : Store) :
    ∃ out k, Run input chooseCapacity s out k ∧ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2 ∧
      out.nr 11 = 2 ^ Nat.clog 2 (s.nr 10) ∧
      out.nm = s.nm ∧ out.rm = s.rm ∧ out.rr = s.rr ∧
      ∀ a, a ≠ 11 → out.nr a = s.nr a := by
  obtain ⟨k, hk, hrun⟩ := chooseCapacity_run input s
  refine ⟨capacityState s (Nat.clog 2 (s.nr 10)), k, hrun, hk, rfl, rfl, rfl, rfl, ?_⟩
  intro a ha
  simp [capacityState, ha]

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem GraphReady.transfer {I : Instance} {ε : ℝ} {s t : Store} (h : GraphReady I ε s)
    (hn : ∀r, 121≤r → r≤153 → t.nr r=s.nr r)
    (hr : ∀r, 121≤r → r≤153 → t.rr r=s.rr r)
    (hm : t.nm=s.nm) (hrm : t.rm=s.rm) : GraphReady I ε t := by
  refine { numeric := h.numeric.transfer (by intro r hh; apply hn <;> omega) hr
           layout := h.layout.transfer (by
             intro r hh; simp only [Finset.mem_insert,Finset.mem_singleton] at hh
             apply hn <;> omega)
           headers := h.headers.transfer (by intro a ha h3; exact congrFun hm a) (congrFun hrm 0)
           activeCount := (congrFun hm 3).trans h.activeCount
           active := h.active.congr (hn 141 (by omega) (by omega))
             (hn 142 (by omega) (by omega)) (hn 143 (by omega) (by omega))
             (by intro v hv; exact congrFun hm _) (by intro k hk; exact congrFun hm _)
           adjacency := hm.symm ▸ h.adjacency
           powers := by intro a ha; rw [hrm]; exact h.powers a ha
           naturalZero := by intro a ha hb; rw [hm]; exact h.naturalZero a ha hb
           realZero := by intro a ha hb; rw [hrm]; exact h.realZero a ha hb }

private theorem heapCmd_run (I : Instance) (ε : ℝ) (s : Store) (hs : GraphReady I ε s) :
    ∃ out steps, Run (encodeInput I ε) heapCmd s out steps ∧ SetupReady I ε out ∧
      steps≤3*Nat.clog 2 (activeVertices I).length+21 := by
  let input := encodeInput I ε
  let copied := Atom.eval (⟨.natCopy 10 143,trivial⟩:Atom) input s
  have hcN : copied.nr 10=(activeVertices I).length := hs.active.count_reg
  have hcopyframe : ∀r, r≠10 → copied.nr r=s.nr r := by
    intro r hr
    simp [copied,Atom.eval,Store.ofRAM,Store.at,ramStep,hr]
  obtain ⟨cap,cn,hcap,hcost,hc,hm,hrm,hrr,hnr⟩ := Queue.chooseCapacity_exact input copied
  have hcapN : cap.nr 11=queueCapacity I := by simpa only [hcN,queueCapacity] using hc
  have hg : GraphReady I ε cap := hs.transfer
    (by intro r hlo hhi; exact (hnr r (by omega)).trans (hcopyframe r (by omega)))
    (by intro r hlo hhi; exact congrFun hrr r) hm hrm
  let out := evalAtoms input heapFinish cap
  have hf := run_atoms input heapFinish cap
  have hfo : GraphReady I ε out := hg.transfer
    (by
      intro r hlo hhi
      apply hf.nat_frame
      simp [heapFinish,Cmd.atoms,Cmd.natWrites,Atom.natWrites]
      omega)
    (by
      intro r hlo hhi
      apply hf.real_frame
      simp [heapFinish,Cmd.atoms,Cmd.realWrites,Atom.realWrites]
      omega)
    (hf.natMemory_frame rfl) (hf.realMemory_frame rfl)
  have hready : SetupReady I ε out := {
    graph := hfo
    capacity := hcapN
    winner := by
      change cap.nr 139+cap.nr 122+16=queueWinnerBase I ε
      rw [hg.layout.links,hg.numeric.edges]
      rfl
    parents := by
      change cap.nr 139+cap.nr 122+16+(cap.nr 11+cap.nr 11)=queueParentBase I ε
      rw [hg.layout.links,hg.numeric.edges,hcapN]
      simp [queueParentBase,queueWinnerBase,two_mul]
    temporary := by
      change cap.nr 139+cap.nr 122+16+(cap.nr 11+cap.nr 11)+(cap.nr 11+cap.nr 11)=queueTempBase I ε
      rw [hg.layout.links,hg.numeric.edges,hcapN]
      simp [queueTempBase,queueParentBase,queueWinnerBase,two_mul]
    activeCount := hg.active.count_reg
    zero := rfl
    one := rfl
    treeCapacity := hcapN
    treeArray := hg.layout.array
    costSentinel := by
      change (cap.rr 129+cap.rr 125)*(cap.rr 153+cap.rr 125)=_
      rw [hg.numeric.realVertices,hg.numeric.realOne,hg.numeric.costSum]
      ring
    lengthSentinel := by
      change (cap.rr 129+cap.rr 125)*(cap.rr 152+cap.rr 125)=_
      rw [hg.numeric.realVertices,hg.numeric.realOne,hg.numeric.lengthSum]
      ring }
  have hrun := Run.seq (Run.atom (⟨.natCopy 10 143,trivial⟩:Atom) s)
    (Run.seq hcap hf)
  refine ⟨out,1+(cn+18),hrun,hready,?_⟩
  rw [hcN] at hcost
  omega

private theorem setupCmd_run (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    ∃ out steps, Run (encodeInput I ε) setupCmd initialStore out steps ∧ SetupReady I ε out ∧
      steps≤18*outerQ ε+14*(Nat.log 2 I.graph.n+1)^2+55*I.graph.edges.length+
        8*(outerInputs I ε).length+3*Nat.clog 2 (activeVertices I).length+182 := by
  obtain ⟨scalar,sn,hs,hsready,hscost⟩ := scalarCmd_run I ε hε hε1
  obtain ⟨layout,ln,hl,hlready,hlcost⟩ := layoutCacheCmd_run I ε scalar hsready
  obtain ⟨graph,gn,hg,hgready,hgcost⟩ := graphCmd_run I ε layout hlready
  obtain ⟨out,hn,hh,hhready,hhcost⟩ := heapCmd_run I ε graph hgready
  refine ⟨out,sn+(ln+(gn+hn)),Run.seq hs (Run.seq hl (Run.seq hg hh)),hhready,?_⟩
  omega

private theorem SetupReady.capacity_bounds {I : Instance} {ε : ℝ} {s : Store} (h : SetupReady I ε s) :
    (activeVertices I).length ≤ s.nr 11 ∧ s.nr 11 < 2*(activeVertices I).length := by
  rw [h.capacity,queueCapacity]
  exact Queue.capacity_bounds _ (activeVertices_length_pos I)

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem GraphReady.runtime {I : Instance} {ε : ℝ} {s : Store} (h : GraphReady I ε s) :
    RuntimeReady I ε s :=
  ⟨h.numeric,h.layout,h.headers,h.activeCount,h.active,h.adjacency,h.powers⟩

private theorem SetupReady.runtime {I : Instance} {ε : ℝ} {s : Store} (h : SetupReady I ε s) :
    RuntimeReady I ε s := h.graph.runtime

private theorem RuntimeReady.transfer {I : Instance} {ε : ℝ} {s t : Store} (h : RuntimeReady I ε s)
    (hn : ∀r, 121≤r → r≤153 → t.nr r=s.nr r)
    (hr : ∀r, 121≤r → r≤153 → t.rr r=s.rr r)
    (hhead : ∀a, a<8 → t.nm a=s.nm a)
    (hgraph : ∀a, graphBase I ε≤a → a<linksBase I ε+I.graph.edges.length → t.nm a=s.nm a)
    (hz : t.rm 0=s.rm 0)
    (hcache : ∀a<outerQ ε, t.rm (Query.outputEnd I ε+a)=s.rm (Query.outputEnd I ε+a)) :
    RuntimeReady I ε t := by
  have hN := activeVertices_length_le_vertices I
  refine {
    numeric := h.numeric.transfer (by intro r hh; apply hn <;> omega) hr
    layout := h.layout.transfer (by
      intro r hh
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      apply hn <;> omega)
    headers := h.headers.transfer (by intro a ha h3; exact hhead a ha) hz
    activeCount := (hhead 3 (by omega)).trans h.activeCount
    active := h.active.congr (hn 141 (by omega) (by omega))
      (hn 142 (by omega) (by omega)) (hn 143 (by omega) (by omega))
      (by intro v hv; exact hgraph _ (by omega) (by unfold linksBase; omega))
      (by intro k hk; apply hgraph <;> simp only [arrayBase,linksBase] <;> omega)
    adjacency := ?_
    powers := by intro a ha; exact (hcache a ha).trans (h.powers a ha) }
  intro v hv
  have hh := hgraph (headsBase I ε+v) (by unfold headsBase; omega)
    (by unfold headsBase linksBase; omega)
  rw [hh]
  apply (h.adjacency v hv).frame
  intro e he
  have he' := outgoingIndices_lt I I.graph.edges.length v e he
  apply hgraph <;> simp only [linksBase] <;> omega

private theorem SetupReady.costSentinel_mode {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) : s.rr 280=TreeMode.zeroLength.top I := h.costSentinel

private theorem SetupReady.lengthSentinel_mode {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) : s.rr 281=TreeMode.zeroBudget.top I := h.lengthSentinel

private theorem RuntimeReady.treeActive {I : Instance} {ε : ℝ} {s : Store}
    (h : RuntimeReady I ε s) :
    ActiveRep I.graph.n (treeAllocation I ε).map (treeAllocation I ε).array (activeVertices I) s :=
  h.active

private theorem RuntimeReady.treeAdjacency {I : Instance} {ε : ℝ} {s : Store}
    (h : RuntimeReady I ε s) :
    AdjacencyPrefix I I.graph.edges.length (treeAllocation I ε).heads
      (treeAllocation I ε).links s.nm := h.adjacency

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

private theorem run_acyclic (input : RAMInput) (c : Cmd) (h : c.acyclic = true) (s : Store) :
    ∃ n ≤ c.size, Run input c s (c.evalAcyclic input s) n := by
  induction c generalizing s with
  | skip => exact ⟨0,le_rfl,Run.skip s⟩
  | atom a => exact ⟨1,le_rfl,Run.atom a s⟩
  | seq a b iha ihb =>
      have hh : a.acyclic = true ∧ b.acyclic = true := by simpa only [Cmd.acyclic, Bool.and_eq_true] using h
      obtain ⟨n,hn,hrun⟩ := iha hh.1 s
      obtain ⟨m,hm,hs⟩ := ihb hh.2 (a.evalAcyclic input s)
      exact ⟨n+m,Nat.add_le_add hn hm,Run.seq hrun hs⟩
  | branch g a b iha ihb =>
      have hh : a.acyclic = true ∧ b.acyclic = true := by simpa only [Cmd.acyclic, Bool.and_eq_true] using h
      cases he : g.eval s with
      | false =>
          obtain ⟨n,hn,hrun⟩ := ihb hh.2 s
          refine ⟨1+n,?_,?_⟩
          · simp only [Cmd.size]; omega
          · simpa only [Cmd.evalAcyclic,he,Bool.false_eq_true,if_false] using
              Run.branchFalse he hrun
      | true =>
          obtain ⟨n,hn,hrun⟩ := iha hh.1 s
          refine ⟨1+n+1,?_,?_⟩
          · simp only [Cmd.size]; omega
          · simpa only [Cmd.evalAcyclic,he,if_true] using Run.branchTrue he hrun
  | loop g body _ => cases h

private theorem Cmd.atoms_evalAcyclic (input : RAMInput) (as : List Atom) (s : Store) :
    (Cmd.atoms as).evalAcyclic input s = evalAtoms input as s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => exact ih (a.eval input s)

@[simp] private theorem Cmd.atoms_acyclic (as : List Atom) : (Cmd.atoms as).acyclic = true := by
  induction as with
  | nil => rfl
  | cons a as ih => simpa only [atoms,acyclic,Bool.true_and] using ih

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
attribute [local instance] Classical.propDecidable

private theorem markAccepted_fold (p : ℕ → Bool) (xs : List ℕ) (b : AnswerBranch) :
    xs.foldl (markAccepted p) b =
      if b = .absent then branchFromIndex (xs.find? p) else b := by
  induction xs generalizing b with
  | nil => cases b <;> simp [branchFromIndex]
  | cons r xs ih =>
      cases b with
      | absent =>
          cases hp : p r <;> simp [List.foldl_cons,markAccepted,hp,ih,List.find?_cons,branchFromIndex]
      | zeroLength => simp [List.foldl_cons,markAccepted,ih]
      | zeroBudget => simp [List.foldl_cons,markAccepted,ih]
      | inner k => simp [List.foldl_cons,markAccepted,ih]

private theorem acceptedIndex_zero_budget (I : Instance) (ε : ℝ) (t : ℕ)
    (hC : I.budget = 0) : acceptedIndex I ε t = none := by
  simp [acceptedIndex,outerInputs,hC]

private theorem acceptedIndex_zero_accuracy (I : Instance) (t : ℕ) :
    acceptedIndex I 0 t = none := by simp [acceptedIndex,outerInputs]

private theorem answerBranch_seed_find (I : Instance) (ε : ℝ) (t : ℕ) :
    answerBranch I ε t =
      if answerBranch I 0 t = .absent then branchFromIndex (acceptedIndex I ε t)
      else answerBranch I 0 t := by
  by_cases hs : t = I.source
  · simp [answerBranch,hs]
  · cases hz : (zeroLengthTree I t).distance with
    | none =>
        by_cases hC : I.budget = 0
        · cases hd : (zeroBudgetTree I t).distance <;>
            simp [answerBranch,hs,hz,hC,hd,acceptedIndex_zero_budget I ε t hC,branchFromIndex]
        · simp only [answerBranch,hs,if_false,hz,hC]
          have he := acceptedIndex_zero_accuracy I t
          change branchFromIndex (acceptedIndex I ε t) = if branchFromIndex (acceptedIndex I 0 t) = .absent then branchFromIndex (acceptedIndex I ε t) else branchFromIndex (acceptedIndex I 0 t)
          simp only [acceptedIndex_zero_accuracy,branchFromIndex,if_true]
    | some d =>
        by_cases hd : d ≤ I.budget
        · simp [answerBranch,hs,hz,hd]
        · by_cases hC : I.budget = 0
          · cases hb : (zeroBudgetTree I t).distance <;>
              simp [answerBranch,hs,hz,hd,hC,hb,acceptedIndex_zero_budget I ε t hC,branchFromIndex]
          · simp only [answerBranch,hs,if_false,hz,hd,hC]
            change branchFromIndex (acceptedIndex I ε t) = if branchFromIndex (acceptedIndex I 0 t) = .absent then branchFromIndex (acceptedIndex I ε t) else branchFromIndex (acceptedIndex I 0 t)
            simp only [acceptedIndex_zero_accuracy,branchFromIndex,if_true]

private theorem answerBranch_incremental (I : Instance) (ε : ℝ) (t : ℕ) :
    (List.range (outerInputs I ε).length).foldl
      (markAccepted (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A t))))
      (answerBranch I 0 t) = answerBranch I ε t := by
  rw [markAccepted_fold]
  exact (answerBranch_seed_find I ε t).symm

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

private theorem seedCmd_run (input : RAMInput) (s : Store) :
    ∃ n ≤ 40, Run input seedCmd s (seedResult input s) n := by
  obtain ⟨n,hn,hrun⟩ := run_acyclic input seedCmd
    (by simp [seedCmd,seedChoice,budgetChoice,writeLength,writeBudget,writeAbsent,Cmd.acyclic]) s
  refine ⟨n,le_trans hn ?_,hrun⟩
  norm_num [seedCmd,seedChoice,budgetChoice,writeLength,writeBudget,writeAbsent,Cmd.size,seedInit]

private theorem seedResult_values (input : RAMInput) (s : Store) :
    (seedResult input s).nm (s.nr 300) = seedTag s ∧
    (seedTag s = 1 → (seedResult input s).rm (s.nr 300) = 0) ∧
    (seedTag s = 2 → (seedResult input s).rm (s.nr 300) = s.rr 301) ∧
    (∀ a, a ≠ s.nr 300 → (seedResult input s).nm a = s.nm a ∧
      (seedResult input s).rm a = s.rm a) := by
  by_cases hs : s.nr 307 = s.nr 123
  · simp (config := { contextual := true }) [seedResult,seedCmd,seedChoice,budgetChoice,writeLength,writeBudget,writeAbsent,
          Cmd.evalAcyclic,Cmd.atoms_evalAcyclic,evalAtoms,seedInit,Atom.eval,Store.ofRAM,
          Store.at,ramStep,Guard.eval,natTest,realTest,seedTag,Function.update_apply,hs]
  · by_cases hf : s.rr 300 < s.rr 280
    · by_cases hd : s.rr 300 ≤ s.rr 121
      · have hg : ¬ s.rr 121 < s.rr 300 := not_lt.mpr hd
        simp (config := { contextual := true }) [seedResult,seedCmd,seedChoice,budgetChoice,writeLength,writeBudget,writeAbsent,
          Cmd.evalAcyclic,Cmd.atoms_evalAcyclic,evalAtoms,seedInit,Atom.eval,Store.ofRAM,
          Store.at,ramStep,Guard.eval,natTest,realTest,seedTag,Function.update_apply,hs,hf,hd,hg]
      · have hg : s.rr 121 < s.rr 300 := lt_of_not_ge hd
        by_cases hz : s.rr 121 = 0 <;> by_cases hb : s.rr 301 < s.rr 281
        all_goals
          try rw [hz] at hd hg
          simp (config := { contextual := true }) [seedResult,seedCmd,seedChoice,budgetChoice,writeLength,writeBudget,writeAbsent,
          Cmd.evalAcyclic,Cmd.atoms_evalAcyclic,evalAtoms,seedInit,Atom.eval,Store.ofRAM,
          Store.at,ramStep,Guard.eval,natTest,realTest,seedTag,Function.update_apply,hs,hf,hd,hg,hz,hb]
    · by_cases hz : s.rr 121 = 0 <;> by_cases hb : s.rr 301 < s.rr 281
      all_goals
        simp (config := { contextual := true }) [seedResult,seedCmd,seedChoice,budgetChoice,writeLength,writeBudget,writeAbsent,
          Cmd.evalAcyclic,Cmd.atoms_evalAcyclic,evalAtoms,seedInit,Atom.eval,Store.ofRAM,
          Store.at,ramStep,Guard.eval,natTest,realTest,seedTag,Function.update_apply,hs,hf,hz,hb]

private theorem markCmd_run (input : RAMInput) (s : Store) :
    ∃ n ≤ 15, Run input markCmd s (markResult input s) n := by
  obtain ⟨n,hn,hrun⟩ := run_acyclic input markCmd
    (by simp [markCmd,Cmd.acyclic]) s
  exact ⟨n,le_trans hn (by decide),hrun⟩

private theorem markResult_values (input : RAMInput) (s : Store) :
    (markResult input s).nm (s.nr 300) =
      (if s.nm (s.nr 300) = 0 ∧ (3/4 : ℝ) ≤ s.rr 305 then 3 else s.nm (s.nr 300)) ∧
    (s.nm (s.nr 300) = 0 → (3/4 : ℝ) ≤ s.rr 305 →
      (markResult input s).nm (s.nr 300+1) = s.nr 301 ∧
      (markResult input s).rm (s.nr 300) = s.rr 304) ∧
    (∀ a, a ≠ s.nr 300 → a ≠ s.nr 300+1 →
      (markResult input s).nm a = s.nm a) ∧
    (∀ a, a ≠ s.nr 300 → (markResult input s).rm a = s.rm a) := by
  by_cases hl : s.rr 305 < (3/4 : ℝ)
  · have hs : ¬ (3/4 : ℝ) ≤ s.rr 305 := not_le.mpr hl
    by_cases ht : s.nm (s.nr 300) = 0 <;>
      simp (config := { contextual := true }) [markResult,markCmd,Cmd.evalAcyclic,Cmd.atoms_evalAcyclic,markInit,markWrite,
        evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,Guard.eval,natTest,realTest,
        evalNat,evalReal,ht,hs,hl,Function.update_apply]
  · have hs : (3/4 : ℝ) ≤ s.rr 305 := le_of_not_gt hl
    by_cases ht : s.nm (s.nr 300) = 0 <;>
      simp (config := { contextual := true }) [markResult,markCmd,Cmd.evalAcyclic,Cmd.atoms_evalAcyclic,markInit,markWrite,
        evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,Guard.eval,natTest,realTest,
        evalNat,evalReal,ht,hs,hl,Function.update_apply]

private theorem markResult_unchanged (input : RAMInput) (s : Store)
    (h : s.nm (s.nr 300) ≠ 0 ∨ s.rr 305 < (3/4 : ℝ)) :
    (markResult input s).nm = s.nm ∧ (markResult input s).rm = s.rm := by
  rcases h with ht | hs
  · simp [markResult,markCmd,Cmd.evalAcyclic,Cmd.atoms_evalAcyclic,markInit,
      evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,Guard.eval,natTest,evalReal,ht]
  · by_cases ht : s.nm (s.nr 300) = 0 <;>
      simp [markResult,markCmd,Cmd.evalAcyclic,Cmd.atoms_evalAcyclic,markInit,
        evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,Guard.eval,natTest,realTest,evalReal,ht,
        not_le.mpr hs,hs]

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

private theorem LabelRep.finite_iff {d : Option ℝ} {sentinel value : ℝ}
    (h : LabelRep d sentinel value) : value < sentinel ↔ d.isSome = true := by
  rw [h.1]
  cases hd : d with
  | none => simp
  | some x =>
      have hx := h.2 x hd
      simp [hx]

private theorem seedTag_correct (I : Instance) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (hsource : s.nr 123 = I.source)
    (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)) :
    seedTag s = branchTag (answerBranch I 0 v) := by
  have hLf := hL.finite_iff
  have hCf := hC.finite_iff
  by_cases hs : v = I.source
  · simp [seedTag,hv,hsource,hs,answerBranch,branchTag]
  · cases hz : (zeroLengthTree I v).distance with
    | none =>
        have hn : ¬ s.rr 300 < s.rr 280 := by simpa [hz] using hLf
        by_cases hB : I.budget = 0 <;> by_cases hb : s.rr 301 < s.rr 281 <;>
          simp [seedTag,hv,hsource,hs,hn,hbudget,answerBranch,hz,hB,
            outerInputs,branchTag,← hCf,hb]
    | some d =>
        have hl : d < s.rr 280 := hL.2 d hz
        have hd : s.rr 300 = d := by simpa [hz] using hL.1
        by_cases hfit : d ≤ I.budget <;> by_cases hB : I.budget = 0 <;>
          by_cases hb : s.rr 301 < s.rr 281
        all_goals
          try rw [hB] at hfit
          try simp only [NNReal.coe_zero] at hfit
          simp [seedTag,hv,hsource,hs,hd,hl,hbudget,answerBranch,hz,hfit,hB,
            outerInputs,branchTag,← hCf,hb]

private theorem seedResult_correct (input : RAMInput) (I : Instance) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (hsource : s.nr 123 = I.source)
    (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)) :
    (seedResult input s).nm (s.nr 300) = branchTag (answerBranch I 0 v) ∧
    (∀ d, answerDistance I 0 v = some d → (seedResult input s).rm (s.nr 300) = d) := by
  obtain ⟨htag,hlen,hcost,hframe⟩ := seedResult_values input s
  have hs := seedTag_correct I v s hv hsource hbudget hL hC
  refine ⟨htag.trans hs,?_⟩
  intro d hd
  cases hb : answerBranch I 0 v with
  | absent => simp [answerDistance,hb] at hd
  | zeroLength =>
      have hd0 : d = 0 := by simpa [answerDistance,hb] using hd.symm
      rw [hd0]
      apply hlen
      simpa [hb,branchTag] using hs
  | zeroBudget =>
      have he : (zeroBudgetTree I v).distance = some d := by simpa [answerDistance,hb] using hd
      rw [hcost (by simpa [hb,branchTag] using hs),hC.1,he]
      rfl
  | inner r =>
      obtain ⟨A,ha,_⟩ := answerBranch_inner_input I 0 v r hb
      simp [outerInputs] at ha

private theorem mark_acceptance (A : InnerInput) (v : ℕ) (s : Store)
    (h : s.rr 305 = 1 - dpValue A (buildTable A) v 0 0) :
    (3/4 : ℝ) ≤ s.rr 305 ↔ accepted A v := by
  rw [h,accepted]
  constructor <;> intro hh <;> linarith

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

private theorem selectedDistance_answer (I : Instance) (ε : ℝ) (v : ℕ) :
    selectedDistance I ε v (answerBranch I ε v) = answerDistance I ε v := rfl

private theorem selectedDistance_seed (I : Instance) (ε : ℝ) (v : ℕ) :
    selectedDistance I ε v (answerBranch I 0 v) = answerDistance I 0 v := by
  cases hb : answerBranch I 0 v with
  | absent => simp [selectedDistance,answerDistance,hb]
  | zeroLength => simp [selectedDistance,answerDistance,hb]
  | zeroBudget => simp [selectedDistance,answerDistance,hb]
  | inner r =>
      obtain ⟨A,ha,_⟩ := answerBranch_inner_input I 0 v r hb
      simp [outerInputs] at ha

private theorem seed_record (input : RAMInput) (I : Instance) (ε : ℝ) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (ha : s.nr 300 = targetAddress v)
    (hsource : s.nr 123 = I.source) (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rr 300))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rr 301)) :
    RecordRep I ε v (answerBranch I 0 v) (seedResult input s) := by
  obtain ⟨htag,hd⟩ := seedResult_correct input I v s hv hsource hbudget hL hC
  rw [ha] at htag hd
  refine ⟨htag,?_,?_⟩
  · intro d h
    rw [selectedDistance_seed] at h
    exact hd d h
  · intro r hb
    obtain ⟨A,ha,_⟩ := answerBranch_inner_input I 0 v r hb
    simp [outerInputs] at ha

private theorem mark_record (input : RAMInput) (I : Instance) (ε : ℝ) (v r : ℕ)
    (A : InnerInput) (b : AnswerBranch) (s : Store)
    (hrec : RecordRep I ε v b s)
    (ha : s.nr 300 = targetAddress v) (hbase : s.nr 301 = tableBase I ε r)
    (hd : s.rr 304 = (1+A.δ)*A.L)
    (hsuccess : (3/4 : ℝ) ≤ s.rr 305 ↔ accepted A v)
    (hA : (outerInputs I ε)[r]? = some A) :
    RecordRep I ε v
      (markAccepted (fun j => ((outerInputs I ε)[j]?).any (fun B => decide (accepted B v))) b r)
      (markResult input s) := by
  have hpred : ((outerInputs I ε)[r]?).any (fun B => decide (accepted B v)) = decide (accepted A v) := by
    simp [hA]
  by_cases hzero : b = .absent
  · subst b
    have htag : s.nm (s.nr 300) = 0 := by simpa [ha,branchTag] using hrec.1
    by_cases hacc : accepted A v
    · have hm := markResult_values input s
      have hsucc := hsuccess.mpr hacc
      have hout := hm.2.1 htag hsucc
      simp only [markAccepted,if_true,hpred,decide_eq_true hacc]
      refine ⟨?_,?_,?_⟩
      · rw [← ha,hm.1,if_pos ⟨htag,hsucc⟩]
        rfl
      · intro d he
        have heq : (1+A.δ)*A.L = d := by simpa [selectedDistance,hA] using he
        rw [← ha,hout.2,hd,heq]
      · intro j hj
        have he : r = j := AnswerBranch.inner.inj hj
        subst j
        simpa [ha,hbase] using hout.1
    · have hlow : s.rr 305 < (3/4 : ℝ) := lt_of_not_ge (fun h => hacc (hsuccess.mp h))
      have hf := markResult_unchanged input s (Or.inr hlow)
      simp only [markAccepted,if_true,hpred,decide_eq_false hacc,Bool.false_eq_true,if_false]
      simpa only [RecordRep,hf.1,hf.2] using hrec
  · have htag : s.nm (s.nr 300) ≠ 0 := by
      rw [ha,hrec.1]
      cases b <;> simp_all [branchTag]
    have hf := markResult_unchanged input s (Or.inl htag)
    simp only [markAccepted,if_neg hzero]
    simpa only [RecordRep,hf.1,hf.2] using hrec

private theorem branchesAfter_zero (I : Instance) (ε : ℝ) (v : ℕ) :
    branchesAfter I ε 0 v = answerBranch I 0 v := rfl

private theorem branchesAfter_succ (I : Instance) (ε : ℝ) (k v : ℕ) :
    branchesAfter I ε (k+1) v =
      markAccepted (fun r => ((outerInputs I ε)[r]?).any (fun A => decide (accepted A v)))
        (branchesAfter I ε k v) k := by
  simp [branchesAfter,List.range_succ,List.foldl_append]

private theorem branchesAfter_end (I : Instance) (ε : ℝ) (v : ℕ) :
    branchesAfter I ε (outerInputs I ε).length v = answerBranch I ε v :=
  answerBranch_incremental I ε v

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

private theorem seedVisitor_run (input : RAMInput) (s : Store) :
    ∃ n ≤ 46, Run input seedVisitor s (seedVisitorResult input s) n := by
  obtain ⟨n,hn,hrun⟩ := seedCmd_run input (evalAtoms input seedLoadOps s)
  exact ⟨6+n,by omega,Run.seq (run_atoms input seedLoadOps s) hrun⟩

private theorem seedVisitor_correct (input : RAMInput) (I : Instance) (ε : ℝ) (v : ℕ) (s : Store)
    (hv : s.nr 307 = v) (ha : s.nr 300 = targetAddress v)
    (hsource : s.nr 123 = I.source) (hbudget : s.rr 121 = I.budget)
    (hL : LabelRep (zeroLengthTree I v).distance (s.rr 280) (s.rm (targetAddress v+2)))
    (hC : LabelRep (zeroBudgetTree I v).distance (s.rr 281) (s.rm (targetAddress v+3))) :
    RecordRep I ε v (answerBranch I 0 v) (seedVisitorResult input s) := by
  apply seed_record input I ε v (evalAtoms input seedLoadOps s)
  · exact hv
  · exact ha
  · exact hsource
  · exact hbudget
  · simpa [evalAtoms,seedLoadOps,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,ha] using hL
  · simpa [evalAtoms,seedLoadOps,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,ha,Nat.add_assoc] using hC

private theorem seedVisitor_memory_frame (input : RAMInput) (s : Store) (a : ℕ)
    (ha : a ≠ s.nr 300) :
    (seedVisitorResult input s).nm a = s.nm a ∧
    (seedVisitorResult input s).rm a = s.rm a := by
  exact (seedResult_values input (evalAtoms input seedLoadOps s)).2.2.2 a ha

private theorem markVisitor_run (input : RAMInput) (s : Store) :
    ∃ n ≤ 19, Run input markVisitor s (markVisitorResult input s) n := by
  obtain ⟨n,hn,hrun⟩ := markCmd_run input (evalAtoms input markLoadOps s)
  exact ⟨4+n,by omega,Run.seq (run_atoms input markLoadOps s) hrun⟩

private theorem markVisitor_correct (input : RAMInput) (I : Instance) (ε : ℝ) (v r : ℕ)
    (A : InnerInput) (b : AnswerBranch) (s : Store)
    (hrec : RecordRep I ε v b s) (hv : s.nr 307 = v)
    (ha : s.nr 300 = targetAddress v) (hbase : s.nr 301 = tableBase I ε r)
    (hd : s.rr 304 = (1+A.δ)*A.L)
    (hmass : s.rm (tableBase I ε r+4*v) = 1-dpValue A (buildTable A) v 0 0)
    (hA : (outerInputs I ε)[r]? = some A) :
    RecordRep I ε v
      (markAccepted (fun j => ((outerInputs I ε)[j]?).any (fun B => decide (accepted B v))) b r)
      (markVisitorResult input s) := by
  apply mark_record input I ε v r A b (evalAtoms input markLoadOps s)
  · exact hrec
  · exact ha
  · exact hbase
  · exact hd
  · apply mark_acceptance
    simpa [evalAtoms,markLoadOps,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,hv,hbase,
      show v+v+(v+v)=4*v by omega] using hmass
  · exact hA

private theorem markVisitor_memory_frame (input : RAMInput) (s : Store) (a : ℕ)
    (ha : a ≠ s.nr 300) (ha1 : a ≠ s.nr 300+1) :
    (markVisitorResult input s).nm a = s.nm a ∧
    (markVisitorResult input s).rm a = s.rm a := by
  have h := markResult_values input (evalAtoms input markLoadOps s)
  exact ⟨h.2.2.1 a ha ha1,h.2.2.2 a ha⟩

private theorem RecordRep.memory_congr (I : Instance) (ε : ℝ) (v : ℕ) (b : AnswerBranch)
    (s t : Store) (htag : t.nm (targetAddress v) = s.nm (targetAddress v))
    (hbase : t.nm (targetAddress v+1) = s.nm (targetAddress v+1))
    (hd : t.rm (targetAddress v) = s.rm (targetAddress v))
    (h : RecordRep I ε v b s) : RecordRep I ε v b t := by
  unfold RecordRep at h ⊢
  rw [htag,hbase,hd]
  exact h

private theorem target_record_separate (v w a b : ℕ) (hvw : v ≠ w) (ha : a < 4) (hb : b < 4) :
    targetAddress v+a ≠ targetAddress w+b := by
  unfold targetAddress
  omega

private theorem seedVisitor_nat_frame (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [302,304,308,309]) : (seedVisitorResult input s).nr r = s.nr r := by
  obtain ⟨n,_,h⟩ := seedVisitor_run input s
  apply h.nat_frame
  simp [seedVisitor,seedLoadOps,seedCmd,seedInit,seedChoice,budgetChoice,
    writeLength,writeBudget,writeAbsent,Cmd.natWrites,Cmd.atoms,Atom.natWrites] <;> simp_all

private theorem seedVisitor_real_frame (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [300,301,302]) : (seedVisitorResult input s).rr r = s.rr r := by
  obtain ⟨n,_,h⟩ := seedVisitor_run input s
  apply h.real_frame
  simp [seedVisitor,seedLoadOps,seedCmd,seedInit,seedChoice,budgetChoice,
    writeLength,writeBudget,writeAbsent,Cmd.realWrites,Cmd.atoms,Atom.realWrites] <;> simp_all

private theorem markVisitor_nat_frame (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [302,303,304,306,308,309]) : (markVisitorResult input s).nr r = s.nr r := by
  obtain ⟨n,_,h⟩ := markVisitor_run input s
  apply h.nat_frame
  simp [markVisitor,markLoadOps,markCmd,markInit,markWrite,
    Cmd.natWrites,Cmd.atoms,Atom.natWrites] <;> simp_all

private theorem markVisitor_real_frame (input : RAMInput) (s : Store) (r : ℕ)
    (hr : r ∉ [303,305,306]) : (markVisitorResult input s).rr r = s.rr r := by
  obtain ⟨n,_,h⟩ := markVisitor_run input s
  apply h.real_frame
  simp [markVisitor,markLoadOps,markCmd,markInit,markWrite,
    Cmd.realWrites,Cmd.atoms,Atom.realWrites] <;> simp_all

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.ActiveIterator
open Structured

private theorem setup_eval (input : RAMInput) (s : Store) :
    evalAtoms input setupAtoms s=setup s := by
  ext a <;> simp [evalAtoms,setupAtoms,setup,Atom.eval,Store.ofRAM,Store.at,ramStep,
    Function.update]

private theorem prepared_eval (input : RAMInput) (s : Store) :
    evalAtoms input prepareAtoms s=prepared s := by
  ext a <;> simp [evalAtoms,prepareAtoms,prepared,Atom.eval,Store.ofRAM,Store.at,ramStep,
    evalNat,Function.update]

private theorem advanced_eval (input : RAMInput) (s : Store) :
    incrementAtom.eval input s=advanced s := rfl

private theorem setup_state (array : ℕ) (xs : List ℕ) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj) : State array xs 0 (setup s) := by
  exact ⟨by simp [setup,ha],by simp [setup,hn],by simp [setup],by simp [setup],
    by simp [setup],hmem⟩

private theorem prepared_state (array : ℕ) (xs : List ℕ) (k : ℕ) (s : Store)
    (h : State array xs k s) : State array xs k (prepared s) := by
  rcases h with ⟨ha,hn,hk,h16,h1,hm⟩
  exact ⟨by simp [prepared,ha],by simp [prepared,hn],by simp [prepared,hk],
    by simp [prepared,h16],by simp [prepared,h1],hm⟩

private theorem prepared_values (array : ℕ) (xs : List ℕ) (k : ℕ) (s : Store)
    (h : State array xs k s) (hk : k<xs.length) :
    (prepared s).nr 307=xs[k] ∧ (prepared s).nr 300=16+4*xs[k] := by
  rcases h with ⟨ha,hn,hi,h16,h1,hm⟩
  constructor
  · simp [prepared,ha,hi,hm k hk]
  · simp [prepared,ha,hi,hm k hk,h16]
    omega

private theorem advanced_state (array : ℕ) (xs : List ℕ) (k : ℕ) (s out : Store)
    (h : State array xs k s) (hf : Frame array xs s out) :
    State array xs (k+1) (advanced out) := by
  rcases h with ⟨ha,hn,hk,h16,h1,hm⟩
  have hr142 := hf.1 142 (by simp)
  have hr143 := hf.1 143 (by simp)
  have hr320 := hf.1 320 (by simp)
  have hr324 := hf.1 324 (by simp)
  have hr325 := hf.1 325 (by simp)
  refine ⟨by simp [advanced,hr142,ha],by simp [advanced,hr143,hn],
    by simp [advanced,hr320,hr325,hk,h1],by simp [advanced,hr324,h16],
    by simp [advanced,hr325,h1],?_⟩
  intro j hj
  exact (hf.2 j hj).trans (hm j hj)

private theorem command_run (input : RAMInput) (visitor : Cmd) (array : ℕ) (xs : List ℕ)
    (bound : ℕ) (P : ℕ → Store → Prop) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj)
    (hstart : P 0 (setup s))
    (hvisit : ∀ k t, k<xs.length → State array xs k t → P k t →
      ∃ out cost, Run input visitor (prepared t) out cost ∧ cost≤bound ∧
        Frame array xs (prepared t) out ∧ P (k+1) (advanced out)) :
    ∃ out cost, Run input (command visitor) s out cost ∧
      State array xs xs.length out ∧ P xs.length out ∧
      cost≤(bound+8)*xs.length+4 := by
  have hinit := setup_state array xs s ha hn hmem
  have hstep : ∀ k t, k<xs.length →
      (State array xs k t ∧ P k t) →
      ∃ out cost, Run input (body visitor) t out cost ∧
        (State array xs (k+1) out ∧ P (k+1) out) ∧ cost≤bound+6 := by
    intro k t hk ht
    obtain ⟨out,cost,hrun,hcost,hframe,hP⟩ := hvisit k t hk ht.1 ht.2
    have hp := run_atoms input prepareAtoms t
    rw [prepared_eval] at hp
    have hi : Run input (.atom incrementAtom) out (advanced out) 1 := Run.atom _ _
    refine ⟨advanced out,5+(cost+1),Run.seq hp (Run.seq hrun hi),
      ⟨advanced_state array xs k (prepared t) out (prepared_state array xs k t ht.1) hframe,hP⟩,?_⟩
    omega
  obtain ⟨out,cost,hrun,hout,hcost⟩ := run_bounded_loop input
    (Guard.nat .lt 320 143) (body visitor) xs.length (bound+6)
    (fun k t=>State array xs k t ∧ P k t)
    (by
      intro k t hk ht
      rcases ht.1 with ⟨harray,hlength,hindex,h16,h1,hvalues⟩
      change decide (t.nr 320 < t.nr 143)=decide (k < xs.length)
      rw [hindex,hlength])
    hstep 0 (setup s) (by omega) ⟨hinit,hstart⟩
  have hs := run_atoms input setupAtoms s
  rw [setup_eval] at hs
  refine ⟨out,3+cost,Run.seq hs hrun,hout.1,hout.2,?_⟩
  simp only [Nat.sub_zero] at hcost
  have hcoef : bound+6+2=bound+8 := by omega
  rw [hcoef] at hcost
  omega

private theorem prefixFold_succ {α : Type} (step : α→ℕ→α) (initial : α)
    (xs : List ℕ) (k : ℕ) (hk : k<xs.length) :
    prefixFold step initial xs (k+1)=step (prefixFold step initial xs k) xs[k] := by
  unfold prefixFold
  rw [List.take_succ_eq_append_getElem hk,List.foldl_append]
  rfl

private theorem command_fold {α : Type} (input : RAMInput) (visitor : Cmd) (array : ℕ)
    (xs : List ℕ) (bound : ℕ) (step : α→ℕ→α) (initial : α)
    (Rep : α→Store→Prop) (s : Store)
    (ha : s.nr 142=array) (hn : s.nr 143=xs.length)
    (hmem : ∀ j (hj : j < xs.length),s.nm (array+j)=xs[j]'hj)
    (hstart : Rep initial (setup s))
    (hvisit : ∀ k t (hk : k<xs.length), State array xs k t →
      Rep (prefixFold step initial xs k) t →
      ∃ out cost, Run input visitor (prepared t) out cost ∧ cost≤bound ∧
        Frame array xs (prepared t) out ∧
        Rep (step (prefixFold step initial xs k) xs[k]) (advanced out)) :
    ∃ out cost, Run input (command visitor) s out cost ∧
      State array xs xs.length out ∧ Rep (xs.foldl step initial) out ∧
      cost≤(bound+8)*xs.length+4 := by
  have hresult := command_run input visitor array xs bound
    (fun k t=>Rep (prefixFold step initial xs k) t) s ha hn hmem
      (by simpa [prefixFold] using hstart)
      (by
        intro k t hk hstate hrep
        simpa only [prefixFold_succ step initial xs k hk] using hvisit k t hk hstate hrep)
  simpa [prefixFold] using hresult

private theorem command_nat_frame (input : RAMInput) (visitor : Cmd) (s out : Store) (cost r : ℕ)
    (h : Run input (command visitor) s out cost)
    (hv : r∉visitor.natWrites)
    (hr : r∉[300,307,320,321,322,323,324,325]) : out.nr r=s.nr r := by
  apply h.nat_frame r
  simp [command,body,setupAtoms,prepareAtoms,incrementAtom,Cmd.natWrites,Cmd.atoms,
    Atom.natWrites,hv] <;> simp_all

private theorem command_real_frame (input : RAMInput) (visitor : Cmd) (s out : Store) (cost r : ℕ)
    (h : Run input (command visitor) s out cost)
    (hv : r∉visitor.realWrites) : out.rr r=s.rr r := by
  apply h.real_frame r
  simp [command,body,setupAtoms,prepareAtoms,incrementAtom,Cmd.realWrites,Cmd.atoms,
    Atom.realWrites,hv]

end NearLinearRSP.TwoResources.Mission.ActiveIterator
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem standalone_Mission_QueueSource__fold_keeps {α β : Type*} (f : β → α → β) (Inv : β → Prop)
    (xs : List α) (s : β) (hs : Inv s) (hstep : ∀ s a, Inv s → Inv (f s a)) :
    Inv (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons a xs ih => exact ih (f s a) (hstep s a hs)

private theorem standalone_Mission_QueueSource__fold_sets {α β : Type*} (f : β → α → β) (Inv P : β → Prop)
    (xs : List α) (a : α) (ha : a ∈ xs) (s : β) (hs : Inv s)
    (hInv : ∀ s b, Inv s → Inv (f s b))
    (hset : ∀ s, Inv s → P (f s a))
    (hkeep : ∀ s b, Inv s → P s → P (f s b)) : P (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => simp at ha
  | cons b xs ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with hab | ha
      · subst b
        have hpair : Inv (f s a) ∧ P (f s a) := ⟨hInv s a hs, hset s hs⟩
        exact (standalone_Mission_QueueSource__fold_keeps f (fun s => Inv s ∧ P s) xs (f s a) hpair
          (fun s b h => ⟨hInv s b h.1, hkeep s b h.1 h.2⟩)).2
      · exact ih ha (f s b) (hInv s b hs)

private theorem buildRow_range (A : InnerInput) (T : Table) (i : ℕ) (hT : TableRange T) :
    TableRange (buildRow A T i) :=
  standalone_Mission_QueueSource__fold_keeps _ TableRange _ T hT (fun U j hU => buildLayer_range A U hU i j)

private theorem buildRow_other_row (A : InnerInput) (T : Table) (i v a b : ℕ)
    (h : a ≠ i) : buildRow A T i v a b = T v a b := by
  unfold buildRow
  apply standalone_Mission_QueueSource__fold_keeps (fun U j => buildLayer A U i j) (fun U => U v a b = T v a b)
  · rfl
  · intro U j hU
    rw [buildLayer_other_layer A U i j v a b (Or.inl h), hU]

private theorem buildRow_source_zero (A : InnerInput) (T : Table) (i j : ℕ)
    (hj : j < tickLimit A) (hT : TableRange T) :
    (buildRow A T i A.I.source i j).value = 0 := by
  unfold buildRow
  apply standalone_Mission_QueueSource__fold_sets (fun U b => buildLayer A U i b) TableRange
    (fun U => (U A.I.source i j).value = 0) _ j (by simpa using hj) T hT
  · intro U b hU
    exact buildLayer_range A U hU i b
  · intro U hU
    exact buildLayer_source_zero A U i j hU
  · intro U b hU hz
    by_cases hb : b = j
    · subst b
      exact buildLayer_source_zero A U i j hU
    · rw [buildLayer_other_layer A U i b A.I.source i j (Or.inr (Ne.symm hb)), hz]

private theorem buildTable_source_value (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A) :
    (buildTable A A.I.source i j).value = 0 := by
  change (((List.range (tickLimit A)).reverse).foldl (fun T a => buildRow A T a)
    (fun _ _ _ => ⟨1, .lengthTick, 0⟩) A.I.source i j).value = 0
  apply standalone_Mission_QueueSource__fold_sets (fun T a => buildRow A T a) TableRange
    (fun T => (T A.I.source i j).value = 0) _ i (by simpa using hi)
    (fun _ _ _ => ⟨1, .lengthTick, 0⟩)
  · intro v a b
    exact ⟨zero_le_one, le_rfl⟩
  · intro T a hT
    exact buildRow_range A T a hT
  · intro T hT
    exact buildRow_source_zero A T i j hj hT
  · intro T a hT hz
    by_cases ha : a = i
    · subst a
      exact buildRow_source_zero A T i j hj hT
    · rw [buildRow_other_row A T a A.I.source i j (Ne.symm ha), hz]

private theorem dpValue_buildTable_source (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A) :
    dpValue A (buildTable A) A.I.source i j = 0 := by
  simp [dpValue, Nat.not_le.mpr hi, Nat.not_le.mpr hj, buildTable_source_value A i j hi hj]

private theorem popLayer_inactive_frame (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hsub : S.queue ⊆ activeVertices A.I) (v a b : ℕ) (hv : v ∉ activeVertices A.I) :
    (popLayer A i j S).table v a b = S.table v a b := by
  unfold popLayer
  split
  · rfl
  · rename_i w ws hq
    let u := firstMin S.keys S.queue w
    have hu : u ∈ S.queue := firstMin_mem _ _ _ (by rw [hq]; simp)
    have hvu : v ≠ u := by intro heq; subst v; exact hv (hsub hu)
    change (relaxAll A i j u _).table v a b = _
    rw [relaxAll_table]
    simp [putCell, show v ≠ firstMin S.keys S.queue w from hvu]

private theorem queueRun_inactive_frame (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hsub : S.queue ⊆ activeVertices A.I) (v a b : ℕ) (hv : v ∉ activeVertices A.I) :
    (queueRun A i j n S).table v a b = S.table v a b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [queueRun_succ, popLayer_inactive_frame A i j _
        (fun x hx => hsub (queueRun_queue_subset A i j n S hx)) v a b hv, ih]

private theorem buildLayer_inactive_frame (A : InnerInput) (T : Table) (i j v a b : ℕ)
    (hv : v ∉ activeVertices A.I) : buildLayer A T i j v a b = T v a b :=
  queueRun_inactive_frame A i j _ (initLayer A T i j) (fun _ hx => hx) v a b hv

private theorem standalone_Mission_QueueInactive__fold_const {α β γ : Type*} (f : β → α → β) (p : β → γ)
    (xs : List α) (s : β) (h : ∀ s a, p (f s a) = p s) :
    p (xs.foldl f s) = p s := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => simpa only [List.foldl_cons, ih, h]

private theorem buildRow_inactive_frame (A : InnerInput) (T : Table) (i v a b : ℕ)
    (hv : v ∉ activeVertices A.I) : buildRow A T i v a b = T v a b :=
  standalone_Mission_QueueInactive__fold_const (fun U j => buildLayer A U i j) (fun U => U v a b) _ T
    (fun U j => buildLayer_inactive_frame A U i j v a b hv)

private theorem buildTable_inactive (A : InnerInput) (v i j : ℕ) (hv : v ∉ activeVertices A.I) :
    buildTable A v i j = ⟨1, .lengthTick, 0⟩ :=
  standalone_Mission_QueueInactive__fold_const (fun T a => buildRow A T a) (fun T => T v i j)
    ((List.range (tickLimit A)).reverse) (fun _ _ _ => ⟨1, .lengthTick, 0⟩)
    (fun T a => buildRow_inactive_frame A T a v i j hv)

private theorem dpValue_buildTable_inactive (A : InnerInput) (v i j : ℕ)
    (hv : v ∉ activeVertices A.I) : dpValue A (buildTable A) v i j = 1 := by
  simp [dpValue, buildTable_inactive A v i j hv]

private theorem accepted_active (A : InnerInput) (v : ℕ) (h : accepted A v) :
    v ∈ activeVertices A.I := by
  by_contra hv
  unfold accepted at h
  rw [dpValue_buildTable_inactive A v 0 0 hv] at h
  norm_num at h

private theorem shortestTree_finite_active (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ)
    (hd : (shortestTree I allow w v).distance = some d) : v ∈ activeVertices I := by
  exact (treeRun_policy I allow w (activeVertices I).length (treeInitial I)
    (activeVertices_nodup I) (treeInitial_policy I allow w)).active v d hd

private theorem shortestTree_inactive_distance (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (hv : v ∉ activeVertices I) :
    (shortestTree I allow w v).distance = none := by
  cases hd : (shortestTree I allow w v).distance with
  | none => rfl
  | some d => exact False.elim (hv (shortestTree_finite_active I allow w v d hd))

private theorem answerBranch_active (I : Instance) (ε : ℝ) (t : ℕ)
    (h : answerBranch I ε t ≠ .absent) : t ∈ activeVertices I := by
  cases hb : answerBranch I ε t with
  | absent => exact False.elim (h hb)
  | zeroLength =>
      rcases answerBranch_zeroLength_spec I ε t hb with hs | ⟨d, hd, _⟩
      · subst t; exact activeVertices_source_mem I
      · exact shortestTree_finite_active I _ _ t d hd
  | zeroBudget =>
      have hs := (answerBranch_zeroBudget_spec I ε t hb).2
      cases hd : (zeroBudgetTree I t).distance with
      | none => simp [hd] at hs
      | some d => exact shortestTree_finite_active I _ _ t d hd
  | inner r =>
      obtain ⟨A, hA, ha⟩ := answerBranch_inner_input I ε t r hb
      have hI := (outerInputs_mem_fields I ε A (List.mem_of_getElem? hA)).1
      simpa only [hI] using accepted_active A t ha

private theorem answerBranch_inactive (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I) : answerBranch I ε t = .absent := by
  by_contra h
  exact ht (answerBranch_active I ε t h)

private theorem answerDistance_inactive (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I) : answerDistance I ε t = none := by
  simp [answerDistance, answerBranch_inactive I ε t ht]

private theorem answerPath_inactive (I : Instance) (ε : ℝ) (t : ℕ)
    (ht : t ∉ activeVertices I) : answerPath I ε t = none := by
  simp [answerPath, answerBranch_inactive I ε t ht]

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

private theorem TargetFrame.refl (I : Instance) (s : Store) : TargetFrame I s s :=
  ⟨fun _ _ => rfl,fun _ _ => rfl⟩

private theorem TargetFrame.trans {I : Instance} {s t u : Store}
    (h : TargetFrame I s t) (h' : TargetFrame I t u) : TargetFrame I s u :=
  ⟨fun a ha => (h'.nat a ha).trans (h.nat a ha),
    fun a ha => (h'.real a ha).trans (h.real a ha)⟩

private theorem TargetFrame.outside {I : Instance} {s t : Store} (h : TargetFrame I s t)
    (a : ℕ) (ha : a < 16 ∨ 16+4*I.graph.n ≤ a) :
    t.nm a = s.nm a ∧ t.rm a = s.rm a := by
  constructor
  · apply h.nat
    intro v hv
    unfold targetAddress
    omega
  · apply h.real
    intro v hv
    unfold targetAddress
    omega

private theorem TargetFrame.treeParents {I : Instance} {s t : Store} (h : TargetFrame I s t)
    (v : ℕ) : t.nm (targetAddress v+2) = s.nm (targetAddress v+2) ∧
      t.nm (targetAddress v+3) = s.nm (targetAddress v+3) := by
  constructor <;> apply h.nat <;> intro w hw <;> unfold targetAddress <;> omega

private theorem seedVisitor_targetFrame (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v) :
    TargetFrame I s (seedVisitorResult input s) := by
  constructor
  · intro a hp
    exact (seedVisitor_memory_frame input s a (by rw [ha]; exact (hp v hv).1)).1
  · intro a hp
    exact (seedVisitor_memory_frame input s a (by rw [ha]; exact hp v hv)).2

private theorem markVisitor_targetFrame (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v) :
    TargetFrame I s (markVisitorResult input s) := by
  constructor
  · intro a hp
    exact (markVisitor_memory_frame input s a (by rw [ha]; exact (hp v hv).1)
      (by rw [ha]; exact (hp v hv).2)).1
  · intro a hp
    have h := markResult_values input (evalAtoms input markLoadOps s)
    exact h.2.2.2 a (by change a ≠ s.nr 300; rw [ha]; exact hp v hv)

private theorem setAnswer_fold_apply (xs : List ℕ) (f value : ℕ → AnswerBranch) (v : ℕ) :
    (xs.foldl (setAnswer value) f) v = if v ∈ xs then value v else f v := by
  induction xs generalizing f with
  | nil => simp
  | cons w xs ih =>
      rw [List.foldl_cons,ih]
      by_cases hx : v ∈ xs <;> by_cases hw : v = w <;>
        simp [setAnswer,hx,hw]

private theorem updateAnswer_fold_apply (xs : List ℕ) (hxs : xs.Nodup)
    (f : ℕ → AnswerBranch) (change : ℕ → AnswerBranch → AnswerBranch) (v : ℕ) :
    (xs.foldl (updateAnswer change) f) v = if v ∈ xs then change v (f v) else f v := by
  induction xs generalizing f with
  | nil => simp
  | cons w xs ih =>
      have htail := (List.nodup_cons.mp hxs).2
      have hnot := (List.nodup_cons.mp hxs).1
      rw [List.foldl_cons,ih htail]
      by_cases hw : v = w
      · subst v
        simp [updateAnswer,hnot]
      · by_cases hx : v ∈ xs <;> simp [updateAnswer,hx,hw]

private theorem RecordMap.initial_absent (I : Instance) (ε : ℝ) (s : Store)
    (h : ∀ v < I.graph.n, s.nm (targetAddress v) = 0) : RecordMap I ε (fun _ => .absent) s := by
  intro v hv
  exact ⟨h v hv,by simp [selectedDistance],by simp⟩

private theorem RecordMap.seed_step (input : RAMInput) (I : Instance) (ε : ℝ) (f : ℕ → AnswerBranch)
    (v : ℕ) (s : Store) (ha : s.nr 300 = targetAddress v)
    (h : RecordMap I ε f s)
    (hnew : RecordRep I ε v (answerBranch I 0 v) (seedVisitorResult input s)) :
    RecordMap I ε (setAnswer (answerBranch I 0) f v) (seedVisitorResult input s) := by
  intro w hw
  by_cases he : w = v
  · subst w
    simpa [setAnswer] using hnew
  · have ht : targetAddress w ≠ s.nr 300 := by
      rw [ha]
      exact target_record_separate w v 0 0 he (by decide) (by decide)
    have hb : targetAddress w+1 ≠ s.nr 300 := by
      rw [ha]
      exact target_record_separate w v 1 0 he (by decide) (by decide)
    have hf0 := seedVisitor_memory_frame input s (targetAddress w) ht
    have hf1 := seedVisitor_memory_frame input s (targetAddress w+1) hb
    have hm := RecordRep.memory_congr I ε w (f w) s (seedVisitorResult input s)
      hf0.1 hf1.1 hf0.2 (h w hw)
    simpa [setAnswer,he] using hm

private theorem RecordMap.mark_step (input : RAMInput) (I : Instance) (ε : ℝ) (f : ℕ → AnswerBranch)
    (v : ℕ) (change : ℕ → AnswerBranch → AnswerBranch) (s : Store)
    (ha : s.nr 300 = targetAddress v) (h : RecordMap I ε f s)
    (hnew : RecordRep I ε v (change v (f v)) (markVisitorResult input s)) :
    RecordMap I ε (updateAnswer change f v) (markVisitorResult input s) := by
  intro w hw
  by_cases he : w = v
  · subst w
    simpa [updateAnswer] using hnew
  · have hsep (a b : ℕ) (ha' : a < 4) (hb' : b < 4) :
        targetAddress w+a ≠ s.nr 300+b := by
      rw [ha]
      exact target_record_separate w v a b he ha' hb'
    have hf0 := markVisitor_memory_frame input s (targetAddress w)
      (hsep 0 0 (by decide) (by decide)) (hsep 0 1 (by decide) (by decide))
    have hf1 := markVisitor_memory_frame input s (targetAddress w+1)
      (hsep 1 0 (by decide) (by decide)) (hsep 1 1 (by decide) (by decide))
    have hm := RecordRep.memory_congr I ε w (f w) s (markVisitorResult input s)
      hf0.1 hf1.1 hf0.2 (h w hw)
    simpa [updateAnswer,he] using hm

private theorem seed_fold_exact (I : Instance) (v : ℕ) :
    ((activeVertices I).foldl (setAnswer (answerBranch I 0)) (fun _ => .absent)) v =
      answerBranch I 0 v := by
  rw [setAnswer_fold_apply]
  by_cases hv : v ∈ activeVertices I
  · simp [hv]
  · simp [hv,answerBranch_inactive I 0 v hv]

private theorem mark_fold_exact (I : Instance) (ε : ℝ) (r v : ℕ) :
    ((activeVertices I).foldl
      (updateAnswer (fun w b => markAccepted
        (fun j => ((outerInputs I ε)[j]?).any (fun A => decide (accepted A w))) b r))
      (branchesAfter I ε r)) v = branchesAfter I ε (r+1) v := by
  rw [updateAnswer_fold_apply _ (activeVertices_nodup I),branchesAfter_succ]
  by_cases hv : v ∈ activeVertices I
  · simp [hv]
  · have hf : ((outerInputs I ε)[r]?).any (fun A => decide (accepted A v)) = false := by
      cases ha : (outerInputs I ε)[r]? with
      | none => simp [ha]
      | some A =>
          have hI := (outerInputs_mem_fields I ε A (List.mem_of_getElem? ha)).1
          have hnot : ¬ accepted A v := by
            intro hac
            have hm := accepted_active A v hac
            rw [hI] at hm
            exact hv hm
          simp [ha,hnot]
    simp [hv,markAccepted,hf]

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

private theorem seedVisitor_world (input : RAMInput) (I : Instance) (s : Store) (v : ℕ)
    (ha : s.nr 300 = targetAddress v) (h : SeedWorld I s) :
    SeedWorld I (seedVisitorResult input s) := by
  refine ⟨(seedVisitor_nat_frame input s 123 (by decide)).trans h.source,
    (seedVisitor_real_frame input s 121 (by decide)).trans h.budget,?_⟩
  intro w hw
  have h2 : targetAddress w+2 ≠ s.nr 300 := by rw [ha]; unfold targetAddress; omega
  have h3 : targetAddress w+3 ≠ s.nr 300 := by rw [ha]; unfold targetAddress; omega
  rw [seedVisitor_real_frame input s 280 (by decide),
    seedVisitor_real_frame input s 281 (by decide),
    (seedVisitor_memory_frame input s _ h2).2,
    (seedVisitor_memory_frame input s _ h3).2]
  exact h.labels w hw

private theorem seedVisitor_iteratorFrame (input : RAMInput) (I : Instance) (array : ℕ) (s : Store)
    (v : ℕ) (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v)
    (hspace : 16+4*I.graph.n ≤ array) :
    ActiveIterator.Frame array (activeVertices I) s (seedVisitorResult input s) := by
  constructor
  · intro r hr
    apply seedVisitor_nat_frame
    simp only [List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hr ⊢
    omega
  · intro k hk
    exact (seedVisitor_memory_frame input s (array+k) (by rw [ha]; unfold targetAddress; omega)).1

private theorem seedRecords_run (input : RAMInput) (I : Instance) (ε : ℝ) (array : ℕ) (s : Store)
    (hworld : SeedWorld I s)
    (ha : s.nr 142 = array) (hn : s.nr 143 = (activeVertices I).length)
    (hmem : ∀ k (hk : k < (activeVertices I).length), s.nm (array+k) = (activeVertices I)[k])
    (hspace : 16+4*I.graph.n ≤ array)
    (hzero : ∀ v < I.graph.n, s.nm (targetAddress v) = 0) :
    ∃ out cost, Run input seedRecordsCmd s out cost ∧
      SeedWorld I out ∧ RecordMap I ε (answerBranch I 0) out ∧
      TargetFrame I s out ∧ cost ≤ 54*(activeVertices I).length+4 := by
  let xs := activeVertices I
  let initial : ℕ → AnswerBranch := fun _ => .absent
  let rep := fun f t => SeedWorld I t ∧ RecordMap I ε f t ∧ TargetFrame I s t
  have hstart : rep initial (ActiveIterator.setup s) :=
    ⟨⟨by simpa [ActiveIterator.setup] using hworld.source,hworld.budget,hworld.labels⟩,
      RecordMap.initial_absent I ε s hzero,⟨fun _ _ => rfl,fun _ _ => rfl⟩⟩
  have hvisit : ∀ k t (hk : k < xs.length), ActiveIterator.State array xs k t →
      rep (ActiveIterator.prefixFold (setAnswer (answerBranch I 0)) initial xs k) t →
      ∃ out cost, Run input seedVisitor (ActiveIterator.prepared t) out cost ∧ cost ≤ 46 ∧
        ActiveIterator.Frame array xs (ActiveIterator.prepared t) out ∧
        rep (setAnswer (answerBranch I 0)
          (ActiveIterator.prefixFold (setAnswer (answerBranch I 0)) initial xs k) xs[k])
          (ActiveIterator.advanced out) := by
    intro k t hk ht hp
    let u := ActiveIterator.prepared t
    let v := xs[k]
    have hv : v ∈ activeVertices I := List.getElem_mem hk
    have hvn := activeVertices_valid I v hv
    obtain ⟨hvertex,haddr⟩ := ActiveIterator.prepared_values array xs k t ht hk
    have haddr' : u.nr 300 = targetAddress v := haddr
    have hu : SeedWorld I u := ⟨by simpa [u,ActiveIterator.prepared] using hp.1.source,
      hp.1.budget,hp.1.labels⟩
    obtain ⟨cost,hcost,hrun⟩ := seedVisitor_run input u
    have hnew := seedVisitor_correct input I ε v u hvertex haddr' hu.source hu.budget
      (hu.labels v hv).1 (hu.labels v hv).2
    have hmap := RecordMap.seed_step input I ε _ v u haddr' hp.2.1 hnew
    have hframe : TargetFrame I s (ActiveIterator.advanced (seedVisitorResult input u)) := by
      have hh := seedVisitor_targetFrame input I u v hvn haddr'
      exact ⟨fun a ha => (hh.nat a ha).trans (hp.2.2.nat a ha),
        fun a ha => (hh.real a ha).trans (hp.2.2.real a ha)⟩
    refine ⟨seedVisitorResult input u,cost,hrun,hcost,
      seedVisitor_iteratorFrame input I array u v hvn haddr' hspace,?_,hmap,hframe⟩
    have hw := seedVisitor_world input I u v haddr' hu
    exact ⟨by simpa [ActiveIterator.advanced] using hw.source,hw.budget,hw.labels⟩
  obtain ⟨out,cost,hrun,_,hout,hcost⟩ := ActiveIterator.command_fold input seedVisitor array xs 46
    (setAnswer (answerBranch I 0)) initial rep s ha hn hmem hstart hvisit
  refine ⟨out,cost,hrun,hout.1,?_,hout.2.2,hcost⟩
  intro v hv
  have h := hout.2.1 v hv
  simpa only [xs,initial,seed_fold_exact] using h

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

private theorem runtime_outputs_queryReady (I : Instance) (ε : ℝ) (s : Store)
    (h : RuntimeReady I ε s) (hp : OutputParents I s)
    (hr : TargetRecords.RecordMap I ε (answerBranch I ε) s)
    (ht : CompletedTables I ε (outerInputs I ε).length s) (pc : ℕ) :
    Query.QueryReady I ε (s.at pc) := by
  refine ⟨⟨h.headers.q,h.headers.source,h.headers.vertices,h.headers.z,?_,hp,?_⟩,
    h.activeCount,h.headers.vertexStride,h.headers.rowStride,?_,?_⟩
  · intro v hv
    have hh := hr v hv
    refine ⟨hh.1,?_,hh.2.2⟩
    intro d hd
    apply hh.2.1 d
    exact hd
  · intro r A hA
    exact ht r (List.getElem?_eq_some_iff.mp hA).1 A hA
  · change Query.outputEnd I ε ≤ s.nm 7
    rw [h.headers.map]
    unfold graphBase
    omega
  · intro a ha
    change s.rm (s.nm 6+a) = _
    rw [h.headers.powerBase]
    exact h.powers a ha

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

private theorem SetupReady.treeStart {I : Instance} {ε : ℝ} {s : Store}
    (h : SetupReady I ε s) :
    (treeAllocation I ε).Registers .zeroLength (zeroTreePrepared .zeroLength s) := by
  constructor
  · simpa [zeroTreePrepared,treeAllocation] using h.winner
  · simpa [zeroTreePrepared,treeAllocation] using h.parents
  · simpa [zeroTreePrepared,treeAllocation] using h.zero
  · simpa [zeroTreePrepared,treeAllocation] using h.one
  · simpa [zeroTreePrepared,treeAllocation] using h.capacity
  · simpa [zeroTreePrepared,treeAllocation] using h.activeCount
  · simpa [zeroTreePrepared,treeAllocation] using h.temporary
  · simpa [zeroTreePrepared,treeAllocation] using h.graph.numeric.source
  · simpa [zeroTreePrepared,treeAllocation] using h.graph.layout.heads
  · simpa [zeroTreePrepared,treeAllocation] using h.graph.layout.links
  · simpa [zeroTreePrepared,treeAllocation] using h.graph.layout.map
  · simpa [zeroTreePrepared,treeAllocation] using h.graph.layout.array
  · simpa [zeroTreePrepared,treeAllocation] using h.graph.active.count_reg
  · simpa [zeroTreePrepared,treeAllocation] using h.treeCapacity
  · simpa [zeroTreePrepared,treeAllocation] using h.treeArray
  · simp [zeroTreePrepared]
  · simp [zeroTreePrepared]
  · simpa [zeroTreePrepared,TreeMode.sentinelRegister] using h.costSentinel_mode

private theorem TreeAllocation.protected_before_winner {I : Instance} (E : TreeAllocation I)
    (mode : TreeMode) (a : ℕ) (ha : a < E.W)
    (hfields : ∀ v ∈ activeVertices I,a ≠ targetAddress v+mode.offset) :
    TreeWholeProtected E mode a := by
  have hP := E.winner_parent
  have hR := E.parent_temp
  exact ⟨⟨Or.inl ha,hfields⟩,Or.inl (by omega),Or.inl (by omega)⟩

private theorem treeAllocation_protected_before_map (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < graphBase I ε)
    (hfields : ∀ v ∈ activeVertices I,a ≠ targetAddress v+mode.offset) :
    TreeWholeProtected (treeAllocation I ε) mode a := by
  change a < (treeAllocation I ε).map at ha
  have hm := (treeAllocation I ε).map_le_array
  have hw := (treeAllocation I ε).array_end_le_winner
  exact (treeAllocation I ε).protected_before_winner mode a (by omega) hfields

private theorem treeAllocation_header_protected (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < 8) : TreeWholeProtected (treeAllocation I ε) mode a := by
  apply treeAllocation_protected_before_map I ε mode a
  · unfold graphBase
    omega
  · intro v hv
    cases mode <;> simp only [TreeMode.offset,targetAddress] <;> omega

private theorem treeAllocation_graph_protected (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (hlo : graphBase I ε ≤ a)
    (hhi : a < linksBase I ε+I.graph.edges.length) :
    TreeWholeProtected (treeAllocation I ε) mode a := by
  have hW := (treeAllocation I ε).links_winner
  change a < (treeAllocation I ε).links+I.graph.edges.length at hhi
  apply (treeAllocation I ε).protected_before_winner mode a (by omega)
  intro v hv
  have ht := (treeAllocation I ε).target_lt_map mode v (activeVertices_valid I v hv)
  change targetAddress v+mode.offset < graphBase I ε at ht
  omega

private theorem treeAllocation_post_targets_protected (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (hlo : 16+4*I.graph.n ≤ a) (hhi : a < graphBase I ε) :
    TreeWholeProtected (treeAllocation I ε) mode a := by
  apply treeAllocation_protected_before_map I ε mode a hhi
  intro v hv
  have hvn := activeVertices_valid I v hv
  cases mode <;> simp only [TreeMode.offset,targetAddress] <;> omega

private theorem treeAllocation_cache_protected (I : Instance) (ε : ℝ) (mode : TreeMode)
    (a : ℕ) (ha : a < outerQ ε) :
    TreeWholeProtected (treeAllocation I ε) mode (Query.outputEnd I ε+a) := by
  apply treeAllocation_post_targets_protected
  · unfold Query.outputEnd
    omega
  · unfold graphBase
    omega

private theorem treeAllocation_tag_protected (I : Instance) (ε : ℝ) (mode : TreeMode)
    (v : ℕ) (hv : v < I.graph.n) :
    TreeWholeProtected (treeAllocation I ε) mode (targetAddress v) := by
  apply treeAllocation_protected_before_map I ε mode (targetAddress v)
  · have ht := Query.target_lt_outputEnd I ε v 0 hv (by decide)
    simp only [Nat.add_zero] at ht
    unfold graphBase
    omega
  · intro w hw
    cases mode <;> simp only [targetAddress,TreeMode.offset] <;> omega

private theorem zeroTrees_nat_scalar_frame (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input zeroTreesCmd s out cost) (hlo : 121 ≤ r) (hhi : r ≤ 153) :
    out.nr r=s.nr r := by
  have hd : Disjoint (Finset.Icc 121 153) zeroTreesCmd.natWrites := by decide
  apply h.nat_frame r
  intro hw
  exact Finset.disjoint_left.mp hd (Finset.mem_Icc.mpr ⟨hlo,hhi⟩) hw

private theorem zeroTrees_real_scalar_frame (input : RAMInput) (s out : Store) (cost r : ℕ)
    (h : Run input zeroTreesCmd s out cost) (hlo : 121 ≤ r) (hhi : r ≤ 153) :
    out.rr r=s.rr r := by
  have hd : Disjoint (Finset.Icc 121 153) zeroTreesCmd.realWrites := by decide
  apply h.real_frame r
  intro hw
  exact Finset.disjoint_left.mp hd (Finset.mem_Icc.mpr ⟨hlo,hhi⟩) hw

private theorem ZeroTreeMemory.seedWorld (I : Instance) (s : Store) (h : ZeroTreeMemory I s)
    (hs : s.nr 123=I.source) (hb : s.rr 121=I.budget)
    (hL : s.rr 280=TreeMode.zeroLength.top I)
    (hC : s.rr 281=TreeMode.zeroBudget.top I) : TargetRecords.SeedWorld I s := by
  refine ⟨hs,hb,?_⟩
  intro v hv
  constructor
  · constructor
    · rw [hL]
      exact h.length_distance v hv
    · intro d hd
      rw [hL]
      unfold zeroLengthTree at hd
      rw [shortestTree_eq_treeRun] at hd
      exact treeRun_sentinel_bound I _ I.cost (activeVertices I).length v d hd
  · constructor
    · rw [hC]
      exact h.budget_distance v hv
    · intro d hd
      rw [hC]
      unfold zeroBudgetTree at hd
      rw [shortestTree_eq_treeRun] at hd
      exact treeRun_sentinel_bound I _ I.length (activeVertices I).length v d hd

private theorem zeroTrees_ready (I : Instance) (ε : ℝ) (s : Store) (hSetup : SetupReady I ε s) :
    ∃ out steps, Run (encodeInput I ε) zeroTreesCmd s out steps ∧
      RuntimeReady I ε out ∧ OutputParents I out ∧ TargetRecords.SeedWorld I out ∧
      FutureZero I ε 0 out ∧
      (∀ v < I.graph.n,out.nm (targetAddress v)=0) ∧ out.nr 11=queueCapacity I ∧
      steps ≤ 2*(15*queueCapacity I+
        (38*Nat.clog 2 (2*queueCapacity I)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*queueCapacity I)+46)*I.graph.edges.length+7)+6 := by
  obtain ⟨out,steps,hrun,hmem,hregs,hAdj,hcost,hframe⟩ :=
    zeroTreesCmd_run (treeAllocation I ε) ε s hSetup.treeStart
      hSetup.lengthSentinel_mode hSetup.graph.active hSetup.graph.adjacency
  have hhead : ∀ a,a < 8 → out.nm a=s.nm a := by
    intro a ha
    exact (hframe a (treeAllocation_header_protected I ε .zeroLength a ha)
      (treeAllocation_header_protected I ε .zeroBudget a ha)).1
  have hgraph : ∀ a,graphBase I ε ≤ a → a < linksBase I ε+I.graph.edges.length →
      out.nm a=s.nm a := by
    intro a hlo hhi
    exact (hframe a (treeAllocation_graph_protected I ε .zeroLength a hlo hhi)
      (treeAllocation_graph_protected I ε .zeroBudget a hlo hhi)).1
  have hz : out.rm 0=s.rm 0 :=
    (hframe 0 (treeAllocation_header_protected I ε .zeroLength 0 (by decide))
      (treeAllocation_header_protected I ε .zeroBudget 0 (by decide))).2
  have hcache : ∀ a < outerQ ε,
      out.rm (Query.outputEnd I ε+a)=s.rm (Query.outputEnd I ε+a) := by
    intro a ha
    exact (hframe _ (treeAllocation_cache_protected I ε .zeroLength a ha)
      (treeAllocation_cache_protected I ε .zeroBudget a ha)).2
  have hRuntime := hSetup.runtime.transfer
    (fun r hlo hhi => zeroTrees_nat_scalar_frame _ s out steps r hrun hlo hhi)
    (fun r hlo hhi => zeroTrees_real_scalar_frame _ s out steps r hrun hlo hhi)
    hhead hgraph hz hcache
  have hL : out.rr 280=TreeMode.zeroLength.top I :=
    (hrun.real_frame 280 (by decide)).trans hSetup.costSentinel_mode
  have hC : out.rr 281=TreeMode.zeroBudget.top I :=
    (hrun.real_frame 281 (by decide)).trans hSetup.lengthSentinel_mode
  have hWorld := ZeroTreeMemory.seedWorld I out hmem
    hRuntime.numeric.source hRuntime.numeric.budget hL hC
  refine ⟨out,steps,hrun,hRuntime,?_,hWorld,?_,?_,hregs.capacity,hcost⟩
  · intro v hv
    exact ⟨hmem.length_parent v hv,hmem.budget_parent v hv⟩
  · intro a hlo hhi
    have hlo' : 16+4*I.graph.n ≤ a := by simpa [tableBase] using hlo
    have hm : a < graphBase I ε := by unfold graphBase; omega
    rw [(hframe a (treeAllocation_post_targets_protected I ε .zeroLength a hlo' hm)
      (treeAllocation_post_targets_protected I ε .zeroBudget a hlo' hm)).2]
    exact hSetup.graph.realZero a (by omega) (Or.inl hhi)
  · intro v hv
    rw [(hframe _ (treeAllocation_tag_protected I ε .zeroLength v hv)
      (treeAllocation_tag_protected I ε .zeroBudget v hv)).1]
    apply hSetup.graph.naturalZero
    · unfold targetAddress
      omega
    · have ht := Query.target_lt_outputEnd I ε v 0 hv (by decide)
      simp only [Nat.add_zero] at ht
      unfold graphBase
      omega

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured
attribute [local instance] Classical.propDecidable

private theorem markVisitor_world (input : RAMInput) (I : Instance) (ε : ℝ) (r : ℕ)
    (A : InnerInput) (s : Store) (v : ℕ) (hv : v < I.graph.n)
    (ha : s.nr 300 = targetAddress v) (h : MarkWorld I ε r A s) :
    MarkWorld I ε r A (markVisitorResult input s) := by
  refine ⟨(markVisitor_nat_frame input s 301 (by decide)).trans h.base,
    (markVisitor_real_frame input s 304 (by decide)).trans h.estimate,?_⟩
  intro w hw
  have hframe := markVisitor_targetFrame input I s v hv ha
  rw [(hframe.outside (tableBase I ε r+4*w) (Or.inr (by unfold tableBase; omega))).2]
  exact h.mass w hw

private theorem markVisitor_iteratorFrame (input : RAMInput) (I : Instance) (array : ℕ) (s : Store)
    (v : ℕ) (hv : v < I.graph.n) (ha : s.nr 300 = targetAddress v)
    (hspace : 16+4*I.graph.n ≤ array) :
    ActiveIterator.Frame array (activeVertices I) s (markVisitorResult input s) := by
  constructor
  · intro r hr
    apply markVisitor_nat_frame
    simp only [List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false] at hr ⊢
    omega
  · intro k hk
    exact (markVisitor_memory_frame input s (array+k)
      (by rw [ha]; unfold targetAddress; omega)
      (by rw [ha]; unfold targetAddress; omega)).1

private theorem markRecords_run (input : RAMInput) (I : Instance) (ε : ℝ) (r : ℕ) (A : InnerInput)
    (hA : (outerInputs I ε)[r]? = some A) (array : ℕ) (s : Store)
    (hworld : MarkWorld I ε r A s) (hrecords : RecordMap I ε (branchesAfter I ε r) s)
    (ha : s.nr 142 = array) (hn : s.nr 143 = (activeVertices I).length)
    (hmem : ∀ k (hk : k < (activeVertices I).length), s.nm (array+k) = (activeVertices I)[k])
    (hspace : 16+4*I.graph.n ≤ array) :
    ∃ out cost, Run input markRecordsCmd s out cost ∧ MarkWorld I ε r A out ∧
      RecordMap I ε (branchesAfter I ε (r+1)) out ∧ TargetFrame I s out ∧
      cost ≤ 27*(activeVertices I).length+4 := by
  let xs := activeVertices I
  let change := fun v b => markAccepted
    (fun j => ((outerInputs I ε)[j]?).any (fun B => decide (accepted B v))) b r
  let initial := branchesAfter I ε r
  let rep := fun f t => MarkWorld I ε r A t ∧ RecordMap I ε f t ∧ TargetFrame I s t
  have hstart : rep initial (ActiveIterator.setup s) :=
    ⟨⟨by simpa [ActiveIterator.setup] using hworld.base,hworld.estimate,hworld.mass⟩,
      hrecords,⟨fun _ _ => rfl,fun _ _ => rfl⟩⟩
  have hvisit : ∀ k t (hk : k < xs.length), ActiveIterator.State array xs k t →
      rep (ActiveIterator.prefixFold (updateAnswer change) initial xs k) t →
      ∃ out cost, Run input markVisitor (ActiveIterator.prepared t) out cost ∧ cost ≤ 19 ∧
        ActiveIterator.Frame array xs (ActiveIterator.prepared t) out ∧
        rep (updateAnswer change (ActiveIterator.prefixFold (updateAnswer change) initial xs k) xs[k])
          (ActiveIterator.advanced out) := by
    intro k t hk ht hp
    let u := ActiveIterator.prepared t
    let v := xs[k]
    have hv : v ∈ activeVertices I := List.getElem_mem hk
    have hvn := activeVertices_valid I v hv
    obtain ⟨hvertex,haddr⟩ := ActiveIterator.prepared_values array xs k t ht hk
    have haddr' : u.nr 300 = targetAddress v := haddr
    have hu : MarkWorld I ε r A u :=
      ⟨by simpa [u,ActiveIterator.prepared] using hp.1.base,hp.1.estimate,hp.1.mass⟩
    obtain ⟨cost,hcost,hrun⟩ := markVisitor_run input u
    have hnew := markVisitor_correct input I ε v r A _ u (hp.2.1 v hvn) hvertex haddr'
      hu.base hu.estimate (hu.mass v hv) hA
    have hmap := RecordMap.mark_step input I ε _ v change u haddr' hp.2.1 hnew
    have hframe : TargetFrame I s (ActiveIterator.advanced (markVisitorResult input u)) := by
      have hh := markVisitor_targetFrame input I u v hvn haddr'
      exact ⟨fun a ha => (hh.nat a ha).trans (hp.2.2.nat a ha),
        fun a ha => (hh.real a ha).trans (hp.2.2.real a ha)⟩
    refine ⟨markVisitorResult input u,cost,hrun,hcost,
      markVisitor_iteratorFrame input I array u v hvn haddr' hspace,?_,hmap,hframe⟩
    have hw := markVisitor_world input I ε r A u v hvn haddr' hu
    exact ⟨by simpa [ActiveIterator.advanced] using hw.base,hw.estimate,hw.mass⟩
  obtain ⟨out,cost,hrun,_,hout,hcost⟩ := ActiveIterator.command_fold input markVisitor array xs 19
    (updateAnswer change) initial rep s ha hn hmem hstart hvisit
  refine ⟨out,cost,hrun,hout.1,?_,hout.2.2,hcost⟩
  intro v hv
  have h := hout.2.1 v hv
  simpa only [xs,initial,change,mark_fold_exact] using h

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Outer
open Structured

private theorem prepared_values (input : RAMInput) (s : Store) :
    (prepared input s).nr 200 = s.nr 244 ∧ (prepared input s).nr 201 = s.nr 124 ∧
    (prepared input s).nr 202 = s.nr 125 ∧ (prepared input s).nr 203 = s.nr 244+s.nr 133 ∧
    (prepared input s).nr 204 = s.nr 143 ∧ (prepared input s).nr 205 = s.nr 247 ∧
    (prepared input s).nr 206 = s.nr 248 ∧ (prepared input s).nr 207 = s.nr 249 ∧
    (prepared input s).nr 208 = s.nr 250 ∧ (prepared input s).nr 209 = s.nr 138 ∧
    (prepared input s).rr 200 = s.rr 127/(s.rr 244*s.rr 243) ∧
    (prepared input s).rr 201 = s.rr 245 ∧ (prepared input s).rr 202 = s.rr 128 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem markPrepared_values (input : RAMInput) (s : Store) :
    (markPrepared input s).nr 301 = s.nr 244 ∧
    (markPrepared input s).rr 304 = s.rr 123*s.rr 243 := ⟨rfl,rfl⟩

private theorem advanced_values (input : RAMInput) (s : Store) :
    (advanced input s).nr 243 = s.nr 243+s.nr 126 ∧
    (advanced input s).nr 244 = s.nr 244+s.nr 133 ∧
    (advanced input s).rr 243 = s.rr 243*s.rr 123 := ⟨rfl,rfl,rfl⟩

end NearLinearRSP.TwoResources.Mission.Outer
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources
namespace Mission

private theorem poissonCountMass_recurrence (μ : ℝ) (k : ℕ) :
    ActuarialValuation.poissonCountMass μ (k + 1) =
      ActuarialValuation.poissonCountMass μ k * μ / ((k : ℝ) + 1) := by
  unfold ActuarialValuation.poissonCountMass
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hf : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private theorem poisson_prefix (input : RAMInput) :
    execute poissonProgram input 10 initialState =
      poissonLoopState (input.reals 0) (input.naturals 0) 0 := by
  simp [execute, poissonProgram, ramStep, initialState, evalReal,
    poissonLoopState, Function.update, ActuarialValuation.poissonCountMass]
  funext a
  by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;>
    by_cases h2 : a = 2 <;> by_cases h3 : a = 3 <;> simp_all

private theorem poisson_iteration (input : RAMInput) (μ : ℝ) (n k : ℕ)
    (hk : k < n) :
    execute poissonProgram input 6 (poissonLoopState μ n k) =
      poissonLoopState μ n (k + 1) := by
  simp [execute, poissonProgram, ramStep, poissonLoopState, natTest,
    evalReal, evalNat, hk, Function.update, Nat.cast_add, Nat.cast_one,
    poissonCountMass_recurrence]
  constructor <;> funext a <;>
    by_cases h0 : a = 0 <;> by_cases h1 : a = 1 <;>
    by_cases h2 : a = 2 <;> by_cases h3 : a = 3 <;> simp_all

private theorem poisson_iterations (input : RAMInput) (μ : ℝ) (n k : ℕ)
    (hk : k ≤ n) :
    execute poissonProgram input (6 * k) (poissonLoopState μ n 0) =
      poissonLoopState μ n k := by
  induction k with
  | zero => simp [execute]
  | succ k ih =>
      rw [Nat.mul_succ, execute_add, ih (by omega)]
      exact poisson_iteration input μ n k (by omega)

private theorem poisson_exit (input : RAMInput) (μ : ℝ) (n : ℕ) :
    execute poissonProgram input 4 (poissonLoopState μ n n) =
      poissonFinalState μ n := by
  simp [execute, poissonProgram, ramStep, poissonLoopState, poissonFinalState,
    natTest, Function.update]

private theorem poisson_evaluation (input : RAMInput) :
    execute poissonProgram input (14 + 6 * input.naturals 0) initialState =
      poissonFinalState (input.reals 0) (input.naturals 0) := by
  rw [show 14 + 6 * input.naturals 0 = 10 + 6 * input.naturals 0 + 4 by omega,
    execute_add, execute_add, poisson_prefix]
  rw [poisson_iterations input _ _ _ le_rfl, poisson_exit]

private theorem poissonProgram_correct (input : RAMInput) :
    ∃ (steps : ℕ) (out : RAMState),
      Execution poissonProgram input initialState out steps ∧
      steps ≤ 14 + 6 * input.naturals 0 ∧
      out.rm 0 = ActuarialValuation.poissonCountMass (input.reals 0) (input.naturals 0) := by
  have he := poisson_evaluation input
  have hh : (execute poissonProgram input (14 + 6 * input.naturals 0) initialState).halted =
      true := by rw [he]; rfl
  obtain ⟨steps, hs, hx⟩ := execution_of_bounded_halt poissonProgram input
    initialState (14 + 6 * input.naturals 0) hh
  refine ⟨steps, poissonFinalState (input.reals 0) (input.naturals 0), ?_, hs, ?_⟩
  · rwa [he] at hx
  · simp [poissonFinalState]

end Mission
end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped BigOperators
namespace NearLinearRSP.TwoResources.Mission.Expectation
open Structured

private theorem run_atoms (input : RAMInput) (as : List Atom) (s : Store) :
    Run input (atoms as) s (evalAtoms input as s) as.length := by
  induction as generalizing s with
  | nil => exact Run.skip s
  | cons a rest ih =>
      simpa only [atoms, evalAtoms, List.foldl_cons, List.length_cons, Nat.add_comm] using
        Run.seq (Run.atom a s) (ih (Atom.eval a input s))

private theorem Frame.refl (s : Store) : Frame s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

private theorem Frame.trans {s t u : Store} (h : Frame s t) (g : Frame t u) : Frame s u :=
  ⟨fun r hr => (g.natural r hr).trans (h.natural r hr),
    fun r hr => (g.real r hr).trans (h.real r hr),
    g.naturalMemory.trans h.naturalMemory, g.realMemory.trans h.realMemory⟩

private theorem ColumnFrame.refl (s : Store) : ColumnFrame s s :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, rfl, rfl⟩

private theorem ColumnFrame.trans {s t u : Store} (h : ColumnFrame s t)
    (g : ColumnFrame t u) : ColumnFrame s u :=
  ⟨fun r h92 h94 => (g.natural r h92 h94).trans (h.natural r h92 h94),
    fun r h82 h84 h86 h91 h92 => (g.real r h82 h84 h86 h91 h92).trans
      (h.real r h82 h84 h86 h91 h92),
    g.naturalMemory.trans h.naturalMemory, g.realMemory.trans h.realMemory⟩

private theorem ColumnFrame.frame {s t : Store} (h : ColumnFrame s t) : Frame s t := by
  constructor
  · intro r hr
    exact h.natural r (by omega) (by omega)
  · intro r hr
    exact h.real r (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact h.naturalMemory
  · exact h.realMemory

private theorem columnBody_inv (input : RAMInput) (c : ColumnContext) (k : ℕ)
    (total : ℝ) (s : Store) (h : ColumnInv c k total s) :
    ColumnInv c (k + 1) (total + c.term k) (evalAtoms input columnAtoms s) := by
  rcases h with ⟨hc,hs,hn,hi,ha,hm,hp,hr,hcoeff,hreal,ht,hmem⟩
  constructor <;>
    simp [evalAtoms, columnAtoms, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, hc, hs, hn, hi, ha, hm, hp, hr, hcoeff, hreal, ht, hmem,
      ColumnContext.term, poissonCountMass_recurrence, Nat.cast_add, Nat.cast_one] <;>
    ring

private theorem columnBody_frame (input : RAMInput) (s : Store) :
    ColumnFrame s (evalAtoms input columnAtoms s) := by
  constructor
  · intro r h92 h94
    simp [evalAtoms, columnAtoms, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, h92, h94]
  · intro r h82 h84 h86 h91 h92
    simp [evalAtoms, columnAtoms, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, h82, h84, h86, h91, h92]
  · rfl
  · rfl

private theorem columnLoop_run (input : RAMInput) (c : ColumnContext) (k d : ℕ)
    (total : ℝ) (s : Store) (h : ColumnInv c k total s) (hend : c.count = k + d) :
    ∃ t : Store, Run input columnLoop s t (11 * d + 1) ∧
      ColumnInv c (k + d) (total + ∑ b ∈ Finset.range d, c.term (k + b)) t ∧
      ColumnFrame s t := by
  induction d generalizing s k total with
  | zero =>
      refine ⟨s, ?_, ?_, ColumnFrame.refl s⟩
      · apply Run.loopFalse
        simp [Guard.eval, natTest, h.index, h.count, hend]
      · simpa using h
  | succ d ih =>
      have hg : (Guard.nat .lt 92 87).eval s = true := by
        simp [Guard.eval, natTest, h.index, h.count, hend]
      let u := evalAtoms input columnAtoms s
      have hu := columnBody_inv input c k total s h
      obtain ⟨t,ht,hinv,hframe⟩ := ih (k + 1) (total + c.term k) u hu (by omega)
      refine ⟨t, ?_, ?_, (columnBody_frame input s).trans hframe⟩
      · have hb : Run input columnBody s u 9 := run_atoms input columnAtoms s
        have hh := Run.loopTrue hg hb ht
        have hn : 11 * (d + 1) + 1 = 1 + 9 + 1 + (11 * d + 1) := by omega
        rw [hn]
        exact hh
      · have hsum : (∑ b ∈ Finset.range (d + 1), c.term (k + b)) =
            c.term k + ∑ b ∈ Finset.range d, c.term ((k + 1) + b) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_comm]
        simpa only [hsum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc] using hinv

private theorem rowPrepare_inv (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s) :
    ColumnInv (c.column a) 0 total (evalAtoms input rowPrepare s) := by
  rcases h with ⟨hrows,hcols,hs,hrs,hn,hi,ha,hm,hc,ho,hp,hr,hc0,ht,hmem⟩
  constructor <;>
    simp [evalAtoms, rowPrepare, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, RectangleContext.column, hrows,hcols,hs,hrs,hn,hi,ha,
      hm,hc,ho,hp,hr,hc0,ht,hmem]

private theorem rowPrepare_frame (input : RAMInput) (s : Store) :
    ColumnFrame s (evalAtoms input rowPrepare s) := by
  constructor
  · intro r h92 h94
    simp [evalAtoms, rowPrepare, Atom.eval, ramStep, Store.at, Store.ofRAM, h92,h94]
  · intro r h82 h84 h86 h91 h92
    simp [evalAtoms, rowPrepare, Atom.eval, ramStep, Store.at, Store.ofRAM, h84,h86]
  · rfl
  · rfl

private theorem RowInv.afterColumn (c : RectangleContext) (a : ℕ) (total next : ℝ)
    (s t : Store) (h : RowInv c a total s) (hf : ColumnFrame s t)
    (htotal : t.rr 82 = next) : RowInv c a next t := by
  constructor
  · exact (hf.natural 86 (by decide) (by decide)).trans h.rows
  · exact (hf.natural 87 (by decide) (by decide)).trans h.cols
  · exact (hf.natural 89 (by decide) (by decide)).trans h.stride
  · exact (hf.natural 90 (by decide) (by decide)).trans h.rowStride
  · exact (hf.natural 96 (by decide) (by decide)).trans h.oneNat
  · exact (hf.natural 91 (by decide) (by decide)).trans h.index
  · exact (hf.natural 93 (by decide) (by decide)).trans h.address
  · exact (hf.real 80 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.lengthMean
  · exact (hf.real 81 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.costMean
  · exact (hf.real 87 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.oneReal
  · exact (hf.real 83 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.coefficient
  · exact (hf.real 85 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.realIndex
  · exact (hf.real 89 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.costInitial
  · exact htotal
  · exact hf.realMemory.trans h.memory

private theorem rowFinish_inv (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s) :
    RowInv c (a + 1) total (evalAtoms input rowFinish s) := by
  rcases h with ⟨hrows,hcols,hs,hrs,hn,hi,ha,hm,hc,ho,hp,hr,hc0,ht,hmem⟩
  constructor <;>
    simp [evalAtoms, rowFinish, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, hrows,hcols,hs,hrs,hn,hi,ha,hm,hc,ho,hp,hr,hc0,ht,hmem,
      poissonCountMass_recurrence, Nat.cast_add, Nat.cast_one] <;> ring

private theorem rowFinish_frame (input : RAMInput) (s : Store) :
    Frame s (evalAtoms input rowFinish s) := by
  constructor
  · intro r hr
    have h91 : r ≠ 91 := by omega
    have h93 : r ≠ 93 := by omega
    simp [evalAtoms, rowFinish, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, h91,h93]
  · intro r hr
    have h83 : r ≠ 83 := by omega
    have h85 : r ≠ 85 := by omega
    simp [evalAtoms, rowFinish, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, h83,h85]
  · rfl
  · rfl

private theorem rowBody_run (input : RAMInput) (c : RectangleContext) (a : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s) :
    ∃ t : Store, Run input rowBody s t (10 + 11 * c.cols) ∧
      RowInv c (a + 1) (total + c.row a) t ∧ Frame s t := by
  let u := evalAtoms input rowPrepare s
  have hu := rowPrepare_inv input c a total s h
  obtain ⟨v,hv,hvi,hvf⟩ := columnLoop_run input (c.column a) 0 c.cols total u hu (by simp [RectangleContext.column])
  have hframe : ColumnFrame s v := (rowPrepare_frame input s).trans hvf
  have hsum : v.rr 82 = total + c.row a := by simpa [RectangleContext.row] using hvi.sum
  have hvrow := RowInv.afterColumn c a total (total + c.row a) s v h hframe hsum
  let t := evalAtoms input rowFinish v
  refine ⟨t, ?_, rowFinish_inv input c a _ v hvrow,
    hframe.frame.trans (rowFinish_frame input v)⟩
  have hh := Run.seq (run_atoms input rowPrepare s) (Run.seq hv (run_atoms input rowFinish v))
  have hn : 10 + 11 * c.cols = rowPrepare.length + (11 * c.cols + 1 + rowFinish.length) := by
    simp [rowPrepare, rowFinish]
    omega
  rw [hn]
  exact hh

private theorem rowLoop_run (input : RAMInput) (c : RectangleContext) (a d : ℕ)
    (total : ℝ) (s : Store) (h : RowInv c a total s) (hend : c.rows = a + d) :
    ∃ t : Store, Run input rowLoop s t ((12 + 11 * c.cols) * d + 1) ∧
      RowInv c (a + d) (total + ∑ k ∈ Finset.range d, c.row (a + k)) t ∧ Frame s t := by
  induction d generalizing s a total with
  | zero =>
      refine ⟨s, ?_, ?_, Frame.refl s⟩
      · apply Run.loopFalse
        simp [Guard.eval, natTest, h.index, h.rows, hend]
      · simpa using h
  | succ d ih =>
      have hg : (Guard.nat .lt 91 86).eval s = true := by
        simp [Guard.eval, natTest, h.index, h.rows, hend]
      obtain ⟨u,hu,hui,huf⟩ := rowBody_run input c a total s h
      obtain ⟨t,ht,hti,htf⟩ := ih (a + 1) (total + c.row a) u hui (by omega)
      refine ⟨t, ?_, ?_, huf.trans htf⟩
      · have hh := Run.loopTrue hg hu ht
        have hn : (12 + 11 * c.cols) * (d + 1) + 1 =
            1 + (10 + 11 * c.cols) + 1 + ((12 + 11 * c.cols) * d + 1) := by ring
        rw [hn]
        exact hh
      · have hsum : (∑ k ∈ Finset.range (d + 1), c.row (a + k)) =
            c.row a + ∑ k ∈ Finset.range d, c.row ((a + 1) + k) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_comm]
        simpa only [hsum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, add_assoc] using hti

private theorem corePrepare_inv (input : RAMInput) (s : Store) :
    RowInv (contextOf s) 0 0 (evalAtoms input corePrepare s) := by
  constructor <;>
    simp [evalAtoms, corePrepare, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, contextOf, mass, ActuarialValuation.poissonCountMass]

private theorem corePrepare_frame (input : RAMInput) (s : Store) :
    Frame s (evalAtoms input corePrepare s) := by
  constructor
  · intro r hr
    have h91 : r ≠ 91 := by omega
    have h93 : r ≠ 93 := by omega
    have h96 : r ≠ 96 := by omega
    simp [evalAtoms, corePrepare, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, h91,h93,h96]
  · intro r hr
    have h82 : r ≠ 82 := by omega
    have h83 : r ≠ 83 := by omega
    have h85 : r ≠ 85 := by omega
    have h87 : r ≠ 87 := by omega
    have h88 : r ≠ 88 := by omega
    have h89 : r ≠ 89 := by omega
    have h90 : r ≠ 90 := by omega
    simp [evalAtoms, corePrepare, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalNat, evalReal, h82,h83,h85,h87,h88,h89,h90]
  · rfl
  · rfl

private theorem coreFinish_frame (input : RAMInput) (s : Store) :
    Frame s (evalAtoms input coreFinish s) := by
  constructor
  · intro r hr
    rfl
  · intro r hr
    have h82 : r ≠ 82 := by omega
    simp [evalAtoms, coreFinish, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalReal, h82]
  · rfl
  · rfl

private theorem coreCmd_run (input : RAMInput) (s : Store) :
    ∃ t : Store, Run input coreCmd s t (13 + (12 + 11 * s.nr 87) * s.nr 86) ∧
      t.rr 82 = 1 - ∑ a ∈ Finset.range (s.nr 86),
        ∑ b ∈ Finset.range (s.nr 87),
          mass (s.rr 80) a * mass (s.rr 81) b *
            s.rm (s.nr 88 + s.nr 90 * a + s.nr 89 * b) ∧ Frame s t := by
  let c := contextOf s
  let u := evalAtoms input corePrepare s
  obtain ⟨v,hv,hvi,hvf⟩ := rowLoop_run input c 0 c.rows 0 u (corePrepare_inv input s) (by simp)
  let t := evalAtoms input coreFinish v
  refine ⟨t, ?_, ?_, (corePrepare_frame input s).trans (hvf.trans (coreFinish_frame input v))⟩
  · have hh := Run.seq (run_atoms input corePrepare s) (Run.seq hv (run_atoms input coreFinish v))
    have hn : 13 + (12 + 11 * s.nr 87) * s.nr 86 =
        corePrepare.length + ((12 + 11 * c.cols) * c.rows + 1 + coreFinish.length) := by
      simp [corePrepare, coreFinish, c, contextOf]
      omega
    rw [hn]
    exact hh
  · have hsum := hvi.sum
    simp only [Nat.zero_add, zero_add] at hsum
    simp [t, evalAtoms, coreFinish, Atom.eval, ramStep, Store.at, Store.ofRAM,
      evalReal, hvi.oneReal, hsum, c, contextOf, RectangleContext.row,
      RectangleContext.column, ColumnContext.term]

private theorem setupCmd_run (input : RAMInput) (s : Store) :
    Run input setupCmd s (setupResult input s)
      (41 + 4 * s.nr 81 + 4 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 80) := by
  have h := Run.seq (run_atoms input prepareIndex s)
    (Run.seq (Address.addressCmd_run input (indexPrepared input s))
    (Run.seq (run_atoms input prepareCell (indexResult input s))
    (Run.seq (Address.addressCmd_run input (cellPrepared input s))
    (Run.seq (run_atoms input prepareStride (cellResult input s))
    (Run.seq (Address.addressCmd_run input (stridePrepared input s))
      (run_atoms input prepareDimensions (strideResult input s)))))))
  convert h using 1 <;> try rfl
  simp [prepareIndex, prepareCell, prepareStride, prepareDimensions,
    stridePrepared, cellPrepared, indexPrepared, cellResult, indexResult,
    evalAtoms, Atom.eval, ramStep, Store.at, Store.ofRAM, evalNat,
    Address.addressResult, Address.loopStore, Address.preparedStore]
  ring

private theorem setupResult_values (input : RAMInput) (s : Store) :
    (setupResult input s).nr 86 = s.nr 80 - s.nr 81 ∧
    (setupResult input s).nr 87 = s.nr 80 - s.nr 82 ∧
    (setupResult input s).nr 88 = s.nr 84 + s.nr 85 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 83 ∧
    (setupResult input s).nr 89 = s.nr 85 ∧
    (setupResult input s).nr 90 = s.nr 85 * s.nr 80 := by
  simp [setupResult, strideResult, stridePrepared, cellResult, cellPrepared,
    indexResult, indexPrepared, evalAtoms, prepareIndex, prepareCell, prepareStride,
    prepareDimensions, Atom.eval, ramStep, Store.at, Store.ofRAM, evalNat,
    Address.addressResult, Address.loopStore, Address.preparedStore]
  ring

private theorem FullFrame.refl (s : Store) : FullFrame s s :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

private theorem FullFrame.trans {s t u : Store} (h : FullFrame s t) (g : FullFrame t u) : FullFrame s u :=
  ⟨fun r ha hb => (g.natural r ha hb).trans (h.natural r ha hb),
    fun r hr => (g.real r hr).trans (h.real r hr),
    g.naturalMemory.trans h.naturalMemory, g.realMemory.trans h.realMemory⟩

private theorem Frame.full {s t : Store} (h : Frame s t) : FullFrame s t :=
  ⟨fun r _ hr => h.natural r hr, h.real, h.naturalMemory, h.realMemory⟩

private theorem setupResult_frame (input : RAMInput) (s : Store) : FullFrame s (setupResult input s) := by
  constructor
  · intro r haddr hcore
    have h40 : r ≠ 40 := by omega
    have h41 : r ≠ 41 := by omega
    have h42 : r ≠ 42 := by omega
    have h43 : r ≠ 43 := by omega
    have h44 : r ≠ 44 := by omega
    have h45 : r ≠ 45 := by omega
    have h46 : r ≠ 46 := by omega
    have h47 : r ≠ 47 := by omega
    have h48 : r ≠ 48 := by omega
    have h86 : r ≠ 86 := by omega
    have h87 : r ≠ 87 := by omega
    have h88 : r ≠ 88 := by omega
    have h89 : r ≠ 89 := by omega
    have h90 : r ≠ 90 := by omega
    simp [setupResult, strideResult, stridePrepared, cellResult, cellPrepared,
      indexResult, indexPrepared, evalAtoms, prepareIndex, prepareCell, prepareStride,
      prepareDimensions, Atom.eval, ramStep, Store.at, Store.ofRAM, evalNat,
      Address.addressResult, Address.loopStore, Address.preparedStore,
      h40,h41,h42,h43,h44,h45,h46,h47,h48,h86,h87,h88,h89,h90]
  · intro r hr
    rfl
  · rfl
  · rfl

private theorem nonsaturatedCmd_run (input : RAMInput) (s : Store)
    (hi : s.nr 81 < s.nr 80) (hj : s.nr 82 < s.nr 80) :
    ∃ t : Store, Run input nonsaturatedCmd s t
      (54 + 4 * s.nr 81 + 4 * (s.nr 81 * s.nr 80 + s.nr 82) + 4 * s.nr 80 +
        (12 + 11 * (s.nr 80 - s.nr 82)) * (s.nr 80 - s.nr 81)) ∧
      t.rr 82 = expectedResult s ∧ FullFrame s t := by
  let u := setupResult input s
  have hv := setupResult_values input s
  have hf := setupResult_frame input s
  obtain ⟨t,ht,hvalue,hframe⟩ := coreCmd_run input u
  refine ⟨t, ?_, ?_, hf.trans hframe.full⟩
  · have hh := Run.seq (setupCmd_run input s) ht
    convert hh using 1 <;> try rfl
    rw [hv.1,hv.2.1]
    omega
  · rw [hvalue]
    unfold expectedResult
    rw [if_neg (by omega)]
    have hr80 : u.rr 80 = s.rr 80 := hf.real 80 (by omega)
    have hr81 : u.rr 81 = s.rr 81 := hf.real 81 (by omega)
    rw [hv.1,hv.2.1,hr80,hr81,hf.realMemory]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2]
    congr 1
    congr 1
    ring

private theorem expectationCmd_run (input : RAMInput) (s : Store) :
    ∃ (t : Store) (steps : ℕ), Run input expectationCmd s t steps ∧
      steps ≤ 100 * (s.nr 80 + 1) ^ 2 ∧
      t.rr 82 = expectedResult s ∧ FullFrame s t := by
  by_cases hi : s.nr 81 < s.nr 80
  · by_cases hj : s.nr 82 < s.nr 80
    · obtain ⟨t,ht,hvalue,hframe⟩ := nonsaturatedCmd_run input s hi hj
      refine ⟨t,_,Run.branchTrue ?_ (Run.branchTrue ?_ ht),?_,hvalue,hframe⟩
      · simpa [Guard.eval,natTest] using hi
      · simpa [Guard.eval,natTest] using hj
      · have hindex := Address.rectangle_index_lt (s.nr 80) (s.nr 81) (s.nr 82) hi hj
        have hrows : s.nr 80 - s.nr 81 ≤ s.nr 80 := Nat.sub_le _ _
        have hcols : s.nr 80 - s.nr 82 ≤ s.nr 80 := Nat.sub_le _ _
        have hprod := Nat.mul_le_mul
          (show 12 + 11 * (s.nr 80 - s.nr 82) ≤ 12 + 11 * s.nr 80 by omega) hrows
        nlinarith
    · let t := Atom.eval (⟨.realConst 82 1,trivial⟩ : Atom) input s
      refine ⟨t,4,Run.branchTrue ?_ (Run.branchFalse ?_ (Run.atom _ s)),?_,?_,?_⟩
      · simpa [Guard.eval,natTest] using hi
      · simp [Guard.eval,natTest,hj]
      · nlinarith
      · simp [t,expectedResult,show s.nr 80 ≤ s.nr 82 by omega,
          Atom.eval,ramStep,Store.at,Store.ofRAM]
      · constructor
        · intro r ha hb; rfl
        · intro r hr
          have h82 : r ≠ 82 := by omega
          simp [t,Atom.eval,ramStep,Store.at,Store.ofRAM,h82]
        · rfl
        · rfl
  · let t := Atom.eval (⟨.realConst 82 1,trivial⟩ : Atom) input s
    refine ⟨t,2,Run.branchFalse ?_ (Run.atom _ s),?_,?_,?_⟩
    · simp [Guard.eval,natTest,hi]
    · nlinarith
    · simp [t,expectedResult,show s.nr 80 ≤ s.nr 81 by omega,
        Atom.eval,ramStep,Store.at,Store.ofRAM]
    · constructor
      · intro r ha hb; rfl
      · intro r hr
        have h82 : r ≠ 82 := by omega
        simp [t,Atom.eval,ramStep,Store.at,Store.ofRAM,h82]
      · rfl
      · rfl

private theorem expectedResult_eq_edgeExpectation (A : InnerInput) (T : Table)
    (u v i j : ℕ) (s : Store)
    (hq : s.nr 80 = tickLimit A) (hi : s.nr 81 = i) (hj : s.nr 82 = j)
    (hμ : s.rr 80 = lengthRate A * A.I.length u v)
    (hν : s.rr 81 = costRate A * A.I.cost u v)
    (hmem : ∀ a < tickLimit A - i, ∀ b < tickLimit A - j,
      s.rm (s.nr 84 + s.nr 85 * ((i + a) * tickLimit A + (j + b)) + 4 * s.nr 83) =
        1 - (T u (i + a) (j + b)).value) :
    expectedResult s = edgeExpectation A T u v i j := by
  unfold expectedResult edgeExpectation
  rw [hq,hi,hj,hμ,hν]
  split
  · rfl
  · rename_i hn
    have hsum : (∑ a ∈ Finset.range (tickLimit A - i),
        ∑ b ∈ Finset.range (tickLimit A - j),
          mass (lengthRate A * A.I.length u v) a * mass (costRate A * A.I.cost u v) b *
            s.rm (s.nr 84 + s.nr 85 * ((i + a) * tickLimit A + (j + b)) + 4 * s.nr 83)) =
        (∑ a ∈ Finset.range (tickLimit A - i),
          ∑ b ∈ Finset.range (tickLimit A - j), edgeMass A u v a b) -
        ∑ a ∈ Finset.range (tickLimit A - i),
          ∑ b ∈ Finset.range (tickLimit A - j),
            edgeMass A u v a b * dpValue A T u (i + a) (j + b) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b hb
      have hai : a < tickLimit A - i := Finset.mem_range.mp ha
      have hbj : b < tickLimit A - j := Finset.mem_range.mp hb
      have hiq : i + a < tickLimit A := by omega
      have hjq : j + b < tickLimit A := by omega
      rw [hmem a hai b hbj]
      simp only [dpValue, Nat.not_le.mpr hiq, Nat.not_le.mpr hjq,
        or_self, if_false, edgeMass]
      ring
    rw [hsum]
    ring

private theorem edgeExpectation_run (input : RAMInput) (A : InnerInput) (T : Table)
    (u v i j : ℕ) (s : Store)
    (hq : s.nr 80 = tickLimit A) (hi : s.nr 81 = i) (hj : s.nr 82 = j)
    (hμ : s.rr 80 = lengthRate A * A.I.length u v)
    (hν : s.rr 81 = costRate A * A.I.cost u v)
    (hmem : ∀ a < tickLimit A - i, ∀ b < tickLimit A - j,
      s.rm (s.nr 84 + s.nr 85 * ((i + a) * tickLimit A + (j + b)) + 4 * s.nr 83) =
        1 - (T u (i + a) (j + b)).value) :
    ∃ (t : Store) (steps : ℕ), Run input expectationCmd s t steps ∧
      steps ≤ 100 * (tickLimit A + 1) ^ 2 ∧
      t.rr 82 = edgeExpectation A T u v i j ∧ FullFrame s t := by
  obtain ⟨t,n,hrun,hcost,hval,hframe⟩ := expectationCmd_run input s
  refine ⟨t,n,hrun,by simpa only [hq] using hcost,?_,hframe⟩
  exact hval.trans (expectedResult_eq_edgeExpectation A T u v i j s hq hi hj hμ hν hmem)

end NearLinearRSP.TwoResources.Mission.Expectation
end

theorem solution :
(((((((((NearLinearRSP.TwoResources.ramStep_of_halted_contract_statement ∧
(NearLinearRSP.TwoResources.execute_add_contract_statement ∧
NearLinearRSP.TwoResources.execute_of_halted_contract_statement)) ∧
(NearLinearRSP.TwoResources.Execution.steps_pos_contract_statement ∧
(NearLinearRSP.TwoResources.Execution.steps_unique_contract_statement ∧
NearLinearRSP.TwoResources.Execution.deterministic_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.countdown_prefix_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.countdown_iteration_contract_statement ∧
NearLinearRSP.TwoResources.Mission.countdown_iterations_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.countdown_exit_contract_statement ∧
NearLinearRSP.TwoResources.Mission.countdown_evaluation_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.execution_of_bounded_halt_contract_statement ∧
NearLinearRSP.TwoResources.Mission.countdownProgram_correct_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.countdownProgram_cost_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Structured.initialStore_at_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.queryStore_at_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Structured.Cmd.compile_length_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Structured.run_countdown_loop_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.loopCost_le_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Structured.CodeAt.left_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Structured.CodeAt.right_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.CodeAt.head_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Structured.codeAt_prefix_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.atom_step_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Structured.guard_step_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.jump_step_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Structured.compile_correct_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Structured.compiled_execution_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.compiled_preprocessing_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Structured.compiled_query_contract_statement ∧
(NearLinearRSP.TwoResources.standalone_RSP_FirstMin__fold_choice_le_seed_contract_statement ∧
NearLinearRSP.TwoResources.standalone_RSP_FirstMin__fold_choice_le_member_contract_statement))) ∧
((NearLinearRSP.TwoResources.firstMin_le_of_mem_contract_statement ∧
(NearLinearRSP.TwoResources.standalone_RSP_FirstMin__fold_choice_pred_contract_statement ∧
NearLinearRSP.TwoResources.firstMin_mem_contract_statement)) ∧
((NearLinearRSP.TwoResources.dp_faithfulness_saturated_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.choose_none_left_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.choose_none_right_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.choose_assoc_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Queue.fold_choose_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.winner_append_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.winner_nil_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Queue.winner_singleton_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.fold_some_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.winner_eq_firstMin_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.Tree.champion_eq_winner_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.Tree.champion_eq_firstMin_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.Path.index_lt_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.store_ext_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.run_atoms_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.merge_decode_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.loadChildren_eval_contract_statement)))))) ∧
(((((NearLinearRSP.TwoResources.Mission.Queue.storeLeft_eval_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.storeRight_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.selectChild_run_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Queue.refreshNode_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.refreshed_record_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.refreshed_other_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.refreshed_header_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.parentHop_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.repairBody_run_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.hops_zero_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.hops_pos_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.hops_le_of_lt_pow_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.hops_le_clog_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Queue.repairStep_header_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.repairStep_parent_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.repairStep_layout_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_logarithmic_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.ancestors_zero_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.ancestors_pos_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.le_of_mem_ancestors_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.repairStep_record_other_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.repairStep_ready_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_correct_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.writeLeaf_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.leafWritten_header_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Queue.updateStart_header_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.leafWritten_other_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.updateStart_parent_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Queue.updateStart_layout_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.updateStart_ready_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.updateLeaf_correct_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.run_final_unique_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.WinnerFrame.refl_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.WinnerFrame.trans_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.repairStep_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_run_frame_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.updateStart_frame_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Queue.updateLeaf_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Structured.run_atoms_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.Cmd.atoms_size_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Structured.Store.ext_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.run_atoms_append_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Structured.run_bounded_loop_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeLeafAtoms_eval_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeLeafPrepare_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeLeafReady_values_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeLeafReady_queue_header_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeInitializeLeaf_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedBody_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_counter_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_fixed_contract_statement))))))) ∧
((((((NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_memory_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedLoop_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_run_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_nr_fixed_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_top_fixed_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeSeedInv.step_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.TreeSeedInv.steps_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_correct_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.Atom.nat_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Structured.Atom.real_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.Atom.natMemory_frame_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Structured.Atom.realMemory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.Run.nat_frame_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Structured.Run.real_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Structured.Run.natMemory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.Run.realMemory_frame_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.TreeSeedInv.step_memory_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.TreeSeedInv.steps_memory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_register_frame_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_real_register_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStart_inv_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_framed_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.heapTruth_internal_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.heapTruth_leaf_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.heapTruth_coherent_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.merge_self_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Queue.heapTruth_const_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.mem_ancestors_self_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.parent_mem_ancestors_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Queue.child_not_mem_ancestors_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.heapTruth_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.leafRecords_add_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.heapTruth_decode_subtree_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.heapTruth_root_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.choose_map_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.winner_map_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.heapTruth_firstMin_contract_statement) ∧
(RSP.Tails.mass_nonneg_contract_statement ∧
RSP.Tails.mass_succ_mul_contract_statement)))) ∧
(((RSP.Tails.mass_hasSum_contract_statement ∧
(RSP.Tails.poisson_pgf_hasSum_contract_statement ∧
RSP.Tails.poisson_pgf_contract_statement)) ∧
(RSP.Tails.firstMoment_hasSum_contract_statement ∧
(RSP.Tails.factorialMoment_two_hasSum_contract_statement ∧
RSP.Tails.secondMoment_hasSum_contract_statement))) ∧
((RSP.Tails.poisson_integrable_sq_contract_statement ∧
(RSP.Tails.poisson_memLp_two_contract_statement ∧
RSP.Tails.poisson_mean_contract_statement)) ∧
((RSP.Tails.poisson_secondMoment_contract_statement ∧
RSP.Tails.poisson_variance_contract_statement) ∧
(RSP.Tails.poisson_upper_tail_contract_statement ∧
RSP.Tails.poisson_lower_tail_contract_statement)))))) ∧
(((((RSP.Tails.completeness_ratio_contract_statement ∧
(RSP.Tails.soundness_ratio_contract_statement ∧
RSP.Tails.completeness_ratio_le_contract_statement)) ∧
(RSP.Tails.soundness_ratio_le_contract_statement ∧
(RSP.Tails.poisson_completeness_tail_contract_statement ∧
RSP.Tails.poisson_completeness_tail_of_le_contract_statement))) ∧
((RSP.Tails.poisson_soundness_tail_contract_statement ∧
(RSP.Tails.resource_union_bound_contract_statement.{u_1} ∧
RSP.Tails.poisson_completeness_union_contract_statement.{u_1})) ∧
((RSP.Tails.poisson_completeness_union_of_le_contract_statement.{u_1} ∧
RSP.Tails.countdown_pos_contract_statement) ∧
(RSP.Tails.countdown_sufficient_contract_statement ∧
RSP.Tails.poisson_soundness_union_contract_statement.{u_1})))) ∧
(((RSP.PoissonBridge.lengthRate_nonneg_contract_statement ∧
(RSP.PoissonBridge.costRate_nonneg_contract_statement ∧
RSP.PoissonBridge.poissonCountMass_nonneg_contract_statement)) ∧
(RSP.PoissonBridge.poissonCountMass_hasSum_contract_statement ∧
(RSP.PoissonBridge.poissonCountMass_sum_le_one_contract_statement ∧
RSP.PoissonBridge.edgeMass_nonneg_contract_statement))) ∧
((RSP.PoissonBridge.edgeMass_rectangle_eq_contract_statement ∧
(RSP.PoissonBridge.edgeMass_rectangle_nonneg_contract_statement ∧
RSP.PoissonBridge.edgeMass_rectangle_le_one_contract_statement)) ∧
((RSP.PoissonBridge.edgeMass_sum_le_one_contract_statement ∧
NearLinearRSP.TwoResources.standalone_RSP_TableBounds__foldl_invariant_contract_statement.{u_1}) ∧
(NearLinearRSP.TwoResources.putCell_range_contract_statement ∧
NearLinearRSP.TwoResources.dpValue_range_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.edgeExpectation_range_contract_statement ∧
(NearLinearRSP.TwoResources.initLayer_range_contract_statement ∧
NearLinearRSP.TwoResources.relaxEdge_range_contract_statement)) ∧
(NearLinearRSP.TwoResources.popLayer_range_contract_statement ∧
(NearLinearRSP.TwoResources.buildLayer_range_contract_statement ∧
NearLinearRSP.TwoResources.buildTable_range_contract_statement))) ∧
((NearLinearRSP.TwoResources.dpValue_buildTable_nonneg_contract_statement ∧
(NearLinearRSP.TwoResources.dpValue_buildTable_le_one_contract_statement ∧
NearLinearRSP.TwoResources.activeVertices_edge_left_contract_statement)) ∧
((NearLinearRSP.TwoResources.activeVertices_edge_right_contract_statement ∧
NearLinearRSP.TwoResources.putCell_same_contract_statement) ∧
(NearLinearRSP.TwoResources.putCell_other_vertex_contract_statement ∧
NearLinearRSP.TwoResources.putCell_other_layer_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.relaxEdge_table_contract_statement ∧
(NearLinearRSP.TwoResources.relaxEdge_queue_contract_statement ∧
NearLinearRSP.TwoResources.relaxEdge_nextRank_contract_statement)) ∧
((NearLinearRSP.TwoResources.relaxEdge_keys_outside_contract_statement ∧
NearLinearRSP.TwoResources.relaxEdge_parents_outside_contract_statement) ∧
(NearLinearRSP.TwoResources.relaxEdge_keys_le_contract_statement ∧
NearLinearRSP.TwoResources.standalone_Mission_QueueStructure__fold_preserves_contract_statement.{u_1}))) ∧
((NearLinearRSP.TwoResources.relaxAll_table_contract_statement ∧
(NearLinearRSP.TwoResources.relaxAll_queue_contract_statement ∧
NearLinearRSP.TwoResources.relaxAll_nextRank_contract_statement)) ∧
((NearLinearRSP.TwoResources.relaxAll_keys_outside_contract_statement ∧
NearLinearRSP.TwoResources.relaxAll_parents_outside_contract_statement) ∧
(NearLinearRSP.TwoResources.popLayer_queue_length_contract_statement ∧
NearLinearRSP.TwoResources.popLayer_queue_subset_contract_statement)))))))) ∧
(((((((NearLinearRSP.TwoResources.popLayer_other_layer_contract_statement ∧
(NearLinearRSP.TwoResources.queueRun_zero_contract_statement ∧
NearLinearRSP.TwoResources.queueRun_succ_contract_statement)) ∧
(NearLinearRSP.TwoResources.queueRun_queue_length_contract_statement ∧
(NearLinearRSP.TwoResources.queueRun_queue_subset_contract_statement ∧
NearLinearRSP.TwoResources.queueRun_other_layer_contract_statement))) ∧
((NearLinearRSP.TwoResources.buildLayer_other_layer_contract_statement ∧
(NearLinearRSP.TwoResources.buildLayer_queue_exhausted_contract_statement ∧
NearLinearRSP.TwoResources.popLayer_queue_nodup_contract_statement)) ∧
((NearLinearRSP.TwoResources.queueRun_queue_nodup_contract_statement ∧
NearLinearRSP.TwoResources.popLayer_sync_contract_statement) ∧
(NearLinearRSP.TwoResources.queueRun_sync_contract_statement ∧
NearLinearRSP.TwoResources.relaxEdge_zero_key_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.relaxAll_zero_key_contract_statement ∧
(NearLinearRSP.TwoResources.popLayer_zero_key_contract_statement ∧
NearLinearRSP.TwoResources.queueRun_range_contract_statement)) ∧
(NearLinearRSP.TwoResources.queueRun_zero_key_contract_statement ∧
(NearLinearRSP.TwoResources.buildLayer_source_zero_contract_statement ∧
NearLinearRSP.TwoResources.edgeExpectation_congr_contract_statement))) ∧
((NearLinearRSP.TwoResources.edgeExpectation_mono_contract_statement ∧
(NearLinearRSP.TwoResources.edgeExpectation_extensive_contract_statement ∧
NearLinearRSP.TwoResources.dpValue_congr_at_contract_statement)) ∧
((NearLinearRSP.TwoResources.relaxEdge_futureBound_contract_statement ∧
NearLinearRSP.TwoResources.relaxAll_keys_le_contract_statement) ∧
(NearLinearRSP.TwoResources.relaxAll_futureBound_contract_statement ∧
NearLinearRSP.TwoResources.popLayer_keys_le_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.popLayer_future_dpValue_contract_statement ∧
(NearLinearRSP.TwoResources.popLayer_futureBound_contract_statement ∧
NearLinearRSP.TwoResources.queueRun_futureBound_contract_statement)) ∧
(NearLinearRSP.TwoResources.settleState_expectation_ge_contract_statement ∧
(NearLinearRSP.TwoResources.relaxEdge_keys_ge_contract_statement ∧
NearLinearRSP.TwoResources.relaxAll_keys_ge_contract_statement))) ∧
((NearLinearRSP.TwoResources.pickedVertex_mem_contract_statement ∧
(NearLinearRSP.TwoResources.pickedVertex_le_contract_statement ∧
NearLinearRSP.TwoResources.popLayer_eq_relaxAll_contract_statement)) ∧
((NearLinearRSP.TwoResources.popLayer_keys_ge_picked_contract_statement ∧
NearLinearRSP.TwoResources.popLayer_picked_key_mono_contract_statement) ∧
(NearLinearRSP.TwoResources.pathWeight_cons_cons_contract_statement ∧
NearLinearRSP.TwoResources.pathWeight_nonneg_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.pathWeight_tail_le_contract_statement ∧
(NearLinearRSP.TwoResources.pathWeight_suffix_le_contract_statement ∧
NearLinearRSP.TwoResources.exists_pathReduction_contract_statement)) ∧
(NearLinearRSP.TwoResources.isChain_vertices_lt_contract_statement ∧
(NearLinearRSP.TwoResources.IsPath.vertices_lt_contract_statement ∧
NearLinearRSP.TwoResources.IsPath.length_le_of_nodup_contract_statement))) ∧
((NearLinearRSP.TwoResources.IsPath.exists_simple_contract_statement ∧
(NearLinearRSP.TwoResources.Feasible.exists_simple_contract_statement ∧
NearLinearRSP.TwoResources.pathWeight_le_length_mul_contract_statement)) ∧
((NearLinearRSP.TwoResources.IsPath.weight_le_n_mul_contract_statement ∧
NearLinearRSP.TwoResources.distanceLess_iff_contract_statement) ∧
(NearLinearRSP.TwoResources.standalone_Mission_ShortestTreeStructure__treeFold_mem_contract_statement ∧
NearLinearRSP.TwoResources.treePick_mem_contract_statement)))))) ∧
(((((NearLinearRSP.TwoResources.standalone_Mission_ShortestTreeStructure__treeFold_le_seed_contract_statement ∧
(NearLinearRSP.TwoResources.standalone_Mission_ShortestTreeStructure__treeFold_le_mem_contract_statement ∧
NearLinearRSP.TwoResources.treePick_le_contract_statement)) ∧
(NearLinearRSP.TwoResources.treeRelax_queue_contract_statement ∧
(NearLinearRSP.TwoResources.treeRelax_rank_contract_statement ∧
NearLinearRSP.TwoResources.treeRelax_outside_contract_statement))) ∧
((NearLinearRSP.TwoResources.treeRelax_dist_le_contract_statement ∧
(NearLinearRSP.TwoResources.standalone_Mission_ShortestTreeStructure__treeFold_preserves_contract_statement.{u_1} ∧
NearLinearRSP.TwoResources.treeRelaxAll_queue_contract_statement)) ∧
((NearLinearRSP.TwoResources.treeRelaxAll_rank_contract_statement ∧
NearLinearRSP.TwoResources.treeRelaxFold_outside_contract_statement) ∧
(NearLinearRSP.TwoResources.treeRelaxAll_outside_contract_statement ∧
NearLinearRSP.TwoResources.treeRelaxFold_dist_le_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.treeRelaxAll_dist_le_contract_statement ∧
(NearLinearRSP.TwoResources.treeSettle_dist_contract_statement ∧
NearLinearRSP.TwoResources.treePop_eq_relaxAll_contract_statement)) ∧
(NearLinearRSP.TwoResources.treePop_queue_length_contract_statement ∧
(NearLinearRSP.TwoResources.treePop_queue_subset_contract_statement ∧
NearLinearRSP.TwoResources.treePop_queue_nodup_contract_statement))) ∧
((NearLinearRSP.TwoResources.treeRun_zero_contract_statement ∧
(NearLinearRSP.TwoResources.treeRun_succ_contract_statement ∧
NearLinearRSP.TwoResources.treeRun_queue_length_contract_statement)) ∧
((NearLinearRSP.TwoResources.treeRun_queue_nodup_contract_statement ∧
NearLinearRSP.TwoResources.shortestTree_eq_treeRun_contract_statement) ∧
(NearLinearRSP.TwoResources.shortestTree_queue_exhausted_contract_statement ∧
NearLinearRSP.TwoResources.treeInitial_policy_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.treeSettle_policy_contract_statement ∧
(NearLinearRSP.TwoResources.treeRelax_policy_contract_statement ∧
NearLinearRSP.TwoResources.treeRelaxFold_policy_contract_statement)) ∧
(NearLinearRSP.TwoResources.treePop_policy_contract_statement ∧
(NearLinearRSP.TwoResources.treeRun_policy_contract_statement ∧
NearLinearRSP.TwoResources.shortestTree_finite_rank_contract_statement))) ∧
((NearLinearRSP.TwoResources.shortestTree_finite_parent_contract_statement ∧
(NearLinearRSP.TwoResources.treePop_dist_le_contract_statement ∧
NearLinearRSP.TwoResources.treePop_outside_contract_statement)) ∧
((NearLinearRSP.TwoResources.treePop_dist_picked_contract_statement ∧
NearLinearRSP.TwoResources.treeRelax_dist_ge_contract_statement) ∧
(NearLinearRSP.TwoResources.treeRelaxFold_dist_ge_contract_statement ∧
NearLinearRSP.TwoResources.treePop_dist_ge_picked_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.treeRelax_edge_bound_contract_statement ∧
(NearLinearRSP.TwoResources.treeRelaxAll_edge_bound_contract_statement ∧
NearLinearRSP.TwoResources.treePop_separation_contract_statement)) ∧
((NearLinearRSP.TwoResources.treePop_bellman_contract_statement ∧
NearLinearRSP.TwoResources.treeRun_bellman_separation_contract_statement) ∧
(NearLinearRSP.TwoResources.shortestTree_bellman_contract_statement ∧
NearLinearRSP.TwoResources.treeRelax_dist_nonneg_contract_statement))) ∧
((NearLinearRSP.TwoResources.treeRelaxAll_dist_nonneg_contract_statement ∧
(NearLinearRSP.TwoResources.treePop_dist_nonneg_contract_statement ∧
NearLinearRSP.TwoResources.treeRun_dist_nonneg_contract_statement)) ∧
((NearLinearRSP.TwoResources.treeRun_dist_le_contract_statement ∧
NearLinearRSP.TwoResources.shortestTree_dist_nonneg_contract_statement) ∧
(NearLinearRSP.TwoResources.shortestTree_source_zero_contract_statement ∧
NearLinearRSP.TwoResources.shortestTree_distance_nonneg_contract_statement))))))) ∧
((((((NearLinearRSP.TwoResources.treeDist_chain_bound_contract_statement ∧
(NearLinearRSP.TwoResources.shortestTree_path_bound_contract_statement ∧
NearLinearRSP.TwoResources.pathWeight_zero_chain_contract_statement)) ∧
(NearLinearRSP.TwoResources.zeroLengthTree_path_bound_contract_statement ∧
(NearLinearRSP.TwoResources.zeroBudgetTree_path_bound_contract_statement ∧
NearLinearRSP.TwoResources.activeVertices_length_le_edges_contract_statement))) ∧
((NearLinearRSP.TwoResources.edgeWeightSum_nonneg_contract_statement ∧
(NearLinearRSP.TwoResources.weight_le_edgeWeightSum_contract_statement ∧
NearLinearRSP.TwoResources.treePolicy_distance_bound_contract_statement)) ∧
((NearLinearRSP.TwoResources.treeRun_source_zero_contract_statement ∧
NearLinearRSP.TwoResources.treeRun_sentinel_bound_contract_statement) ∧
(NearLinearRSP.TwoResources.distanceLess_eq_sentinel_contract_statement ∧
NearLinearRSP.TwoResources.treePick_eq_sentinel_firstMin_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.treeRun_pick_sentinel_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_at_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_outside_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Queue.slotVertex_injective_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.slotVertex_idxOf_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_single_change_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_delete_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_update_key_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.slotVertex_idxOf_eq_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_delete_vertex_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_update_vertex_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.standalone_Mission_QueueLeaves__getD_map_range_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.standalone_Mission_QueueLeaves__filterMap_live_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Queue.filter_sublist_members_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_records_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_firstMin_contract_statement)) ∧
(NearLinearRSP.TwoResources.popLayer_queue_sublist_contract_statement ∧
(NearLinearRSP.TwoResources.queueRun_queue_sublist_contract_statement ∧
NearLinearRSP.TwoResources.treePop_queue_sublist_contract_statement))) ∧
((NearLinearRSP.TwoResources.treeRun_queue_sublist_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.initPrefix_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.initPair_eval_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.empty_coherent_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.prefixed_inv_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.paired_inv_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.initLoop_run_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Queue.initializeEmpty_correct_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.InitFrame.refl_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.InitFrame.trans_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.prefixed_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.paired_frame_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.initLoop_run_framed_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.initializeEmpty_framed_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.updateLeaf_refines_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.initializeEmpty_represents_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.represented_root_firstMin_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Queue.prefixLeaf_zero_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.prefixLeaf_succ_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Queue.buildSetup_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.prepareInsert_eval_contract_statement)))))) ∧
(((((NearLinearRSP.TwoResources.Mission.Queue.insertIncrement_eval_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.initializeEmpty_high_register_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.updateLeaf_high_register_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Queue.WinnerFrame.initFrame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.insertBody_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.buildQueue_run_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_initial_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.prefixLeaf_records_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.seed_prefixLeaf_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeInitializeQueue_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeProbe_eval_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.activeAppend_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeInsert_run_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_frame_register_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_frame_memory_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_frame_reals_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_present_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_absent_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.active_regions_disjoint_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.stableInsert_mem_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.stableInsert_nodup_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMActiveList__stableFold_loop_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.stableFold_eq_eraseDups_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeVertices_eq_stableFold_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.flag_zero_iff_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.empty_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.insert_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.indexOf_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.index_bounds_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.inverse_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.vertex_at_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.length_le_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.congr_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.weight_nonneg_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.top_pos_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.offset_lt_four_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.capacity_pos_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.target_lt_map_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.map_le_array_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.array_end_le_winner_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.target_lt_winner_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeRegisters.transfer_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.TreeRegisters.after_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeInitializeQueue_rep_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeExtractAtoms_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeExtractPrepared_values_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeExtractPrepared_header_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeExtract__updateLeaf_nat_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeExtract__updateLeaf_real_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeExtract_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeRecordDistance_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeRecordedDistance_value_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeRecordedDistance_frame_contract_statement))))))))) ∧
((((((((NearLinearRSP.TwoResources.encodeInput_edge_left_contract_statement ∧
(NearLinearRSP.TwoResources.encodeInput_edge_right_contract_statement ∧
NearLinearRSP.TwoResources.encodeInput_length_contract_statement)) ∧
(NearLinearRSP.TwoResources.encodeInput_cost_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeEdgeAtoms_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeEdgeLoaded_values_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeTargetAtoms_eval_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeDecreaseAtoms_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeDecreased_header_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeApplyDecrease_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyAtoms_eval_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyInsert_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_head_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_link_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_memory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_register_frame_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_real_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.AdjacencyChain.frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyInsert_chain_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeAdjacencyPrepared_scratch_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeAdjacencyAdvanced_scratch_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeAdjacencyPrepared_values_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeAdjacencyLoop_run_of_edge_contract_contract_statement.{u_1} ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeCheckTarget_run_contract_statement) ∧
(NearLinearRSP.TwoResources.treePolicy_candidate_sentinel_contract_statement ∧
NearLinearRSP.TwoResources.sentinelKey_le_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.sentinel_source_none_no_decrease_contract_statement ∧
(NearLinearRSP.TwoResources.sentinel_finite_candidate_comparison_contract_statement ∧
NearLinearRSP.TwoResources.treeRelax_eq_real_test_contract_statement)) ∧
(NearLinearRSP.TwoResources.sentinelKey_update_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.TreeMemoryRep.congr_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeMemoryRep.after_readonly_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeTarget_values_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeTarget_correct_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.sentinel_bounds_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeEdge__edgeGuard_value_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeEdge__candidate_value_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeEdge__modeBody_correct_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeEdge_correct_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.treeRelax_source_zero_contract_statement ∧
(NearLinearRSP.TwoResources.TreeScanMath.step_contract_statement ∧
NearLinearRSP.TwoResources.TreeScanMath.start_contract_statement)) ∧
(NearLinearRSP.TwoResources.relaxEdge_nonoutgoing_contract_statement ∧
(NearLinearRSP.TwoResources.relaxFold_filter_outgoing_contract_statement ∧
NearLinearRSP.TwoResources.relaxAll_eq_outgoingFold_contract_statement))) ∧
((NearLinearRSP.TwoResources.treeRelax_nonoutgoing_contract_statement ∧
(NearLinearRSP.TwoResources.treeRelaxFold_filter_outgoing_contract_statement ∧
NearLinearRSP.TwoResources.treeRelaxAll_eq_outgoingFold_contract_statement)) ∧
((NearLinearRSP.TwoResources.relaxEdge_disabled_contract_statement ∧
NearLinearRSP.TwoResources.treeRelax_disabled_contract_statement) ∧
(NearLinearRSP.TwoResources.relaxEdge_comm_contract_statement ∧
NearLinearRSP.TwoResources.relaxFold_perm_contract_statement)))))) ∧
(((((NearLinearRSP.TwoResources.relaxAll_eq_reversedOutgoingFold_contract_statement ∧
(NearLinearRSP.TwoResources.treeRelax_comm_contract_statement ∧
NearLinearRSP.TwoResources.treeRelaxFold_perm_contract_statement)) ∧
(NearLinearRSP.TwoResources.treeRelaxAll_eq_reversedOutgoingFold_contract_statement ∧
(NearLinearRSP.TwoResources.popLayer_reversed_refinement_contract_statement ∧
NearLinearRSP.TwoResources.treePop_reversed_refinement_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_index_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_inputPointer_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_register_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanBody_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanLoop_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.outgoingIndices_lt_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Preprocess.outgoingIndices_succ_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyPrefix_zero_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.edgeAt_valid_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_prefix_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanResult_register_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanResult_reals_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanResult_prefix_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_memory_outside_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanResult_memory_outside_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanCmd_correct_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMAdjacencyScan__map_filter_compat_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.edgeAt_map_range_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.outgoingIndices_edges_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Preprocess.TreeScanInvariant.transfer_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.link_protected_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.graph_protected_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.AdjacencyPrefix.protected_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.outgoingIndices_valid_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeScan_run_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeExtractRefinement__queue_update_nat_high_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeExtractRefinement__queue_update_real_high_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeExtract_refines_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.treeExtract_high_register_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.sentinelKey_treeSettle_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeSettle_parent_unchanged_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeExtract_registers_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Preprocess.treeSettle_registers_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeSettle_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeSettle_counter277_contract_statement)) ∧
((NearLinearRSP.TwoResources.outgoingWork_erase_contract_statement ∧
NearLinearRSP.TwoResources.standalone_Mission_OutgoingWork__indicator_sum_contract_statement) ∧
(NearLinearRSP.TwoResources.standalone_Mission_OutgoingWork__outgoing_filter_count_contract_statement ∧
NearLinearRSP.TwoResources.outgoingWork_active_contract_statement))) ∧
((NearLinearRSP.TwoResources.outgoingWork_settle_contract_statement ∧
(NearLinearRSP.TwoResources.queueRun_succ_front_contract_statement ∧
NearLinearRSP.TwoResources.popLayer_nextRank_of_ne_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreePop__seq_attach_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeHeadStore_token_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treePopCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treePop_outgoingWork_contract_statement))))))) ∧
((((((NearLinearRSP.TwoResources.Mission.Preprocess.treeLoop_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeRun__seq_attach_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeCmd_run_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeState_final_tree_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeState_final_queue_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeMemoryRep.final_distances_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.TreeMemoryRep.final_parents_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.zeroTreeSetup_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeRegisters.prepare_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.length_field_protected_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.zeroLength_tree_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.zeroBudget_tree_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.zeroTreesCmd_run_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.standalone_Mission_Guesses__min_fold_le_seed_contract_statement ∧
(NearLinearRSP.TwoResources.standalone_Mission_Guesses__min_fold_le_member_contract_statement ∧
NearLinearRSP.TwoResources.standalone_Mission_Guesses__seed_le_max_fold_contract_statement)) ∧
(NearLinearRSP.TwoResources.standalone_Mission_Guesses__member_le_max_fold_contract_statement ∧
(NearLinearRSP.TwoResources.firstPositiveLength_le_member_contract_statement ∧
NearLinearRSP.TwoResources.member_le_largestLength_contract_statement))) ∧
((NearLinearRSP.TwoResources.largestLength_nonneg_contract_statement ∧
(NearLinearRSP.TwoResources.firstPositiveLength_le_largestLength_contract_statement ∧
NearLinearRSP.TwoResources.largestLength_pos_contract_statement)) ∧
((NearLinearRSP.TwoResources.one_le_aspectRatio_contract_statement ∧
NearLinearRSP.TwoResources.crossing_exists_contract_statement) ∧
(NearLinearRSP.TwoResources.firstCrossing_spec_contract_statement ∧
NearLinearRSP.TwoResources.firstCrossing_minimal_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.firstCrossing_le_contract_statement ∧
(NearLinearRSP.TwoResources.firstCrossing_mono_top_contract_statement ∧
NearLinearRSP.TwoResources.firstCrossing_approx_contract_statement)) ∧
(NearLinearRSP.TwoResources.geometricGuesses_cover_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.GuessLoop.step_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.GuessLoop.loop_run_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.GuessLoop.crossingCmd_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.GuessLoop.crossing_result_contract_statement ∧
NearLinearRSP.TwoResources.Mission.GuessLoop.crossing_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.acceptedIndex_spec_contract_statement ∧
NearLinearRSP.TwoResources.acceptedIndex_le_contract_statement) ∧
(NearLinearRSP.TwoResources.acceptedIndex_exists_contract_statement ∧
NearLinearRSP.TwoResources.answerBranch_inner_iff_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.answerBranch_inner_input_contract_statement ∧
(NearLinearRSP.TwoResources.answerBranch_zeroLength_spec_contract_statement ∧
NearLinearRSP.TwoResources.answerBranch_zeroBudget_spec_contract_statement)) ∧
(NearLinearRSP.TwoResources.outerInputs_mem_fields_contract_statement ∧
(NearLinearRSP.TwoResources.geometricGuesses_ordered_contract_statement ∧
NearLinearRSP.TwoResources.outerInputs_ordered_contract_statement))) ∧
((NearLinearRSP.TwoResources.outerInputs_get_length_le_contract_statement ∧
(NearLinearRSP.TwoResources.answerDistance_eq_none_iff_contract_statement ∧
NearLinearRSP.TwoResources.EncodesOutput.readDistance_eq_contract_statement)) ∧
((NearLinearRSP.TwoResources.outerInputs_length_exact_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.countCmd_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.countCmd_nat_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.countCmd_real_frame_contract_statement)))))) ∧
(((((NearLinearRSP.TwoResources.Mission.Preprocess.countCmd_memory_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.headerPrepared_values_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.headerLoopStore_zero_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.headerBody_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.headerLoop_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.headerCmd_run_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.headerResult_header_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.headerResult_memory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.NatToReal.run_atoms_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.NatToReal.powerBody_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.NatToReal.powerLoop_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.NatToReal.convertBody_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.NatToReal.Frame.refl_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.NatToReal.Frame.trans_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.NatToReal.bodyResult_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.NatToReal.convertLoop_run_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.NatToReal.convertCmd_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Scan.positives_append_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Scan.minimum_append_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Scan.addSample_summarize_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Scan.prefixSummary_succ_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Scan.encoded_samples_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Scan.max_fold_filter_positive_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Scan.summarize_edgeSamples_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Scan.minCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Scan.maxCmd_run_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Scan.positiveCmd_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Scan.scanBody_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Scan.scanBody_values_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Scan.scan_init_rep_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Scan.scan_step_rep_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Scan.scanCmd_run_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Scan.scan_encoded_correct_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Scan.scan_nat_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Scan.scan_real_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.CoreRegs.transfer_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.headerResult_core_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.scalarCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Address.standalone_Mission_RAMAddress__store_eq_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Address.standalone_Mission_RAMAddress__body_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Address.loop_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Address.addressCmd_run_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Address.addressResult_value_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Address.addressResult_frame_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Address.addressResult_memory_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Address.rectangle_index_lt_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Address.address_cost_le_rectangle_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Address.tableAddress_stride_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Address.tableAddress_next_cost_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Address.tableAddress_next_length_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Address.tableAddress_change_vertex_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.layoutFirst_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.layoutSecond_eval_contract_statement)))))))) ∧
(((((((NearLinearRSP.TwoResources.Mission.Preprocess.layoutThird_eval_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.layoutFinish_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.layout_counts_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.layoutCmd_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_values_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_headers_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_memory_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.powerCacheBody_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.powerCacheBody_run_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.powerCacheLoop_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.powerCacheCmd_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.powerCache_values_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.powerCache_frame_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Preprocess.powerCache_natMemory_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Query.prepend_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Query.storesList_cons_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Query.storesList_map_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Query.prepend_stores_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Query.prepend_memory_frame_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Query.score_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Query.score_value_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Query.score_nat_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Query.score_real_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Query.score_memory_frame_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Query.choose_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Query.choose_cost_le_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Query.header_lt_outputEnd_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Query.target_lt_outputEnd_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Query.table_lt_outputEnd_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.ScalarReady.numeric_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.NumericRegs.transfer_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_numeric_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_layout_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.layoutCacheCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeStep_register_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.activeStep_pointer_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeScanBody_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.activeScan_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.loaded_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.step_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.activeScan_rep_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.scannedVertices_pairs_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.encoded_scannedVertices_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.activeInitAtoms_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_run_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_rep_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.insert_memory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeScan_memory_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_memory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_register_frame_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_real_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.LayoutRegs.transfer_contract_statement)))))) ∧
(((((NearLinearRSP.TwoResources.Mission.Preprocess.OutputHeaders.transfer_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.graphCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.capacityStart_eval_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Queue.capacityDouble_eval_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Queue.chooseCapacity_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Queue.chooseCapacity_bounds_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Queue.chooseCapacity_exact_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.GraphReady.transfer_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.heapCmd_run_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.setupCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.capacity_bounds_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.GraphReady.runtime_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.runtime_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Preprocess.RuntimeReady.transfer_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.costSentinel_mode_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.lengthSentinel_mode_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.RuntimeReady.treeActive_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.RuntimeReady.treeAdjacency_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Structured.run_acyclic_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Structured.Cmd.atoms_evalAcyclic_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Structured.Cmd.atoms_acyclic_contract_statement ∧
NearLinearRSP.TwoResources.markAccepted_fold_contract_statement)) ∧
((NearLinearRSP.TwoResources.acceptedIndex_zero_budget_contract_statement ∧
NearLinearRSP.TwoResources.acceptedIndex_zero_accuracy_contract_statement) ∧
(NearLinearRSP.TwoResources.answerBranch_seed_find_contract_statement ∧
NearLinearRSP.TwoResources.answerBranch_incremental_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.TargetRecords.seedCmd_run_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.seedResult_values_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.markCmd_run_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.markResult_values_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.markResult_unchanged_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.LabelRep.finite_iff_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.seedTag_correct_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.seedResult_correct_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.mark_acceptance_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.selectedDistance_answer_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.selectedDistance_seed_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.seed_record_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.mark_record_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.TargetRecords.branchesAfter_zero_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.branchesAfter_succ_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.branchesAfter_end_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_correct_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_memory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_run_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_correct_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_memory_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.RecordRep.memory_congr_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.target_record_separate_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_nat_frame_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_real_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_nat_frame_contract_statement))))))) ∧
((((((NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_real_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.ActiveIterator.setup_eval_contract_statement ∧
NearLinearRSP.TwoResources.Mission.ActiveIterator.prepared_eval_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.ActiveIterator.advanced_eval_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.ActiveIterator.setup_state_contract_statement ∧
NearLinearRSP.TwoResources.Mission.ActiveIterator.prepared_state_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.ActiveIterator.prepared_values_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.ActiveIterator.advanced_state_contract_statement ∧
NearLinearRSP.TwoResources.Mission.ActiveIterator.command_run_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.ActiveIterator.prefixFold_succ_contract_statement ∧
NearLinearRSP.TwoResources.Mission.ActiveIterator.command_fold_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.ActiveIterator.command_nat_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.ActiveIterator.command_real_frame_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.standalone_Mission_QueueSource__fold_keeps_contract_statement.{u_1} ∧
(NearLinearRSP.TwoResources.standalone_Mission_QueueSource__fold_sets_contract_statement.{u_1} ∧
NearLinearRSP.TwoResources.buildRow_range_contract_statement)) ∧
(NearLinearRSP.TwoResources.buildRow_other_row_contract_statement ∧
(NearLinearRSP.TwoResources.buildRow_source_zero_contract_statement ∧
NearLinearRSP.TwoResources.buildTable_source_value_contract_statement))) ∧
((NearLinearRSP.TwoResources.dpValue_buildTable_source_contract_statement ∧
(NearLinearRSP.TwoResources.popLayer_inactive_frame_contract_statement ∧
NearLinearRSP.TwoResources.queueRun_inactive_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.buildLayer_inactive_frame_contract_statement ∧
NearLinearRSP.TwoResources.standalone_Mission_QueueInactive__fold_const_contract_statement.{u_1}) ∧
(NearLinearRSP.TwoResources.buildRow_inactive_frame_contract_statement ∧
NearLinearRSP.TwoResources.buildTable_inactive_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.dpValue_buildTable_inactive_contract_statement ∧
(NearLinearRSP.TwoResources.accepted_active_contract_statement ∧
NearLinearRSP.TwoResources.shortestTree_finite_active_contract_statement)) ∧
(NearLinearRSP.TwoResources.shortestTree_inactive_distance_contract_statement ∧
(NearLinearRSP.TwoResources.answerBranch_active_contract_statement ∧
NearLinearRSP.TwoResources.answerBranch_inactive_contract_statement))) ∧
((NearLinearRSP.TwoResources.answerDistance_inactive_contract_statement ∧
(NearLinearRSP.TwoResources.answerPath_inactive_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.TargetFrame.refl_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.TargetFrame.trans_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.TargetFrame.outside_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.TargetFrame.treeParents_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_targetFrame_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_targetFrame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.setAnswer_fold_apply_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.updateAnswer_fold_apply_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.RecordMap.initial_absent_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.RecordMap.seed_step_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.RecordMap.mark_step_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.seed_fold_exact_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.mark_fold_exact_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_world_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_iteratorFrame_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.TargetRecords.seedRecords_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.runtime_outputs_queryReady_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.treeStart_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.protected_before_winner_contract_statement)))))) ∧
(((((NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_protected_before_map_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_header_protected_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_graph_protected_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_post_targets_protected_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_cache_protected_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_tag_protected_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.zeroTrees_nat_scalar_frame_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Preprocess.zeroTrees_real_scalar_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Preprocess.ZeroTreeMemory.seedWorld_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Preprocess.zeroTrees_ready_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_world_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_iteratorFrame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.TargetRecords.markRecords_run_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Outer.prepared_values_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Outer.markPrepared_values_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Outer.advanced_values_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.poissonCountMass_recurrence_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.poisson_prefix_contract_statement ∧
NearLinearRSP.TwoResources.Mission.poisson_iteration_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.poisson_iterations_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.poisson_exit_contract_statement ∧
NearLinearRSP.TwoResources.Mission.poisson_evaluation_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.poissonProgram_correct_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.run_atoms_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Expectation.Frame.refl_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.Frame.trans_contract_statement))))) ∧
((((NearLinearRSP.TwoResources.Mission.Expectation.ColumnFrame.refl_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Expectation.ColumnFrame.trans_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.ColumnFrame.frame_contract_statement)) ∧
(NearLinearRSP.TwoResources.Mission.Expectation.columnBody_inv_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Expectation.columnBody_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.columnLoop_run_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Expectation.rowPrepare_inv_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Expectation.rowPrepare_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.RowInv.afterColumn_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Expectation.rowFinish_inv_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.rowFinish_frame_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Expectation.rowBody_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.rowLoop_run_contract_statement)))) ∧
(((NearLinearRSP.TwoResources.Mission.Expectation.corePrepare_inv_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Expectation.corePrepare_frame_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.coreFinish_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Expectation.coreCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.setupCmd_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Expectation.setupResult_values_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.FullFrame.refl_contract_statement))) ∧
((NearLinearRSP.TwoResources.Mission.Expectation.FullFrame.trans_contract_statement ∧
(NearLinearRSP.TwoResources.Mission.Expectation.Frame.full_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.setupResult_frame_contract_statement)) ∧
((NearLinearRSP.TwoResources.Mission.Expectation.nonsaturatedCmd_run_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.expectationCmd_run_contract_statement) ∧
(NearLinearRSP.TwoResources.Mission.Expectation.expectedResult_eq_edgeExpectation_contract_statement ∧
NearLinearRSP.TwoResources.Mission.Expectation.edgeExpectation_run_contract_statement)))))))))) :=
⟨⟨⟨⟨⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.ramStep_of_halted,
⟨@NearLinearRSP.TwoResources.execute_add,
@NearLinearRSP.TwoResources.execute_of_halted⟩⟩,
⟨@NearLinearRSP.TwoResources.Execution.steps_pos,
⟨@NearLinearRSP.TwoResources.Execution.steps_unique,
@NearLinearRSP.TwoResources.Execution.deterministic⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.countdown_prefix,
⟨@NearLinearRSP.TwoResources.Mission.countdown_iteration,
@NearLinearRSP.TwoResources.Mission.countdown_iterations⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.countdown_exit,
@NearLinearRSP.TwoResources.Mission.countdown_evaluation⟩,
⟨@NearLinearRSP.TwoResources.Mission.execution_of_bounded_halt,
@NearLinearRSP.TwoResources.Mission.countdownProgram_correct⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.countdownProgram_cost,
⟨@NearLinearRSP.TwoResources.Mission.Structured.initialStore_at,
@NearLinearRSP.TwoResources.Mission.Structured.queryStore_at⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Structured.Cmd.compile_length,
⟨@NearLinearRSP.TwoResources.Mission.Structured.run_countdown_loop,
@NearLinearRSP.TwoResources.Mission.Structured.loopCost_le⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Structured.CodeAt.left,
⟨@NearLinearRSP.TwoResources.Mission.Structured.CodeAt.right,
@NearLinearRSP.TwoResources.Mission.Structured.CodeAt.head⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Structured.codeAt_prefix,
@NearLinearRSP.TwoResources.Mission.Structured.atom_step⟩,
⟨@NearLinearRSP.TwoResources.Mission.Structured.guard_step,
@NearLinearRSP.TwoResources.Mission.Structured.jump_step⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Structured.compile_correct,
⟨@NearLinearRSP.TwoResources.Mission.Structured.compiled_execution,
@NearLinearRSP.TwoResources.Mission.Structured.compiled_preprocessing⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Structured.compiled_query,
⟨@NearLinearRSP.TwoResources.standalone_RSP_FirstMin__fold_choice_le_seed,
@NearLinearRSP.TwoResources.standalone_RSP_FirstMin__fold_choice_le_member⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.firstMin_le_of_mem,
⟨@NearLinearRSP.TwoResources.standalone_RSP_FirstMin__fold_choice_pred,
@NearLinearRSP.TwoResources.firstMin_mem⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.dp_faithfulness_saturated,
@NearLinearRSP.TwoResources.Mission.Queue.choose_none_left⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.choose_none_right,
@NearLinearRSP.TwoResources.Mission.Queue.choose_assoc⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.fold_choose,
⟨@NearLinearRSP.TwoResources.Mission.Queue.winner_append,
@NearLinearRSP.TwoResources.Mission.Queue.winner_nil⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.winner_singleton,
⟨@NearLinearRSP.TwoResources.Mission.Queue.fold_some,
@NearLinearRSP.TwoResources.Mission.Queue.winner_eq_firstMin⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.Tree.champion_eq_winner,
⟨@NearLinearRSP.TwoResources.Mission.Queue.Tree.champion_eq_firstMin,
@NearLinearRSP.TwoResources.Mission.Queue.Path.index_lt⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.store_ext,
@NearLinearRSP.TwoResources.Mission.Queue.run_atoms⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.merge_decode,
@NearLinearRSP.TwoResources.Mission.Queue.loadChildren_eval⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.storeLeft_eval,
⟨@NearLinearRSP.TwoResources.Mission.Queue.storeRight_eval,
@NearLinearRSP.TwoResources.Mission.Queue.selectChild_run⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.refreshNode_run,
⟨@NearLinearRSP.TwoResources.Mission.Queue.refreshed_record,
@NearLinearRSP.TwoResources.Mission.Queue.refreshed_other⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.refreshed_header,
⟨@NearLinearRSP.TwoResources.Mission.Queue.parentHop_eval,
@NearLinearRSP.TwoResources.Mission.Queue.repairBody_run⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.hops_zero,
@NearLinearRSP.TwoResources.Mission.Queue.hops_pos⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.hops_le_of_lt_pow,
@NearLinearRSP.TwoResources.Mission.Queue.hops_le_clog⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.repairStep_header,
⟨@NearLinearRSP.TwoResources.Mission.Queue.repairStep_parent,
@NearLinearRSP.TwoResources.Mission.Queue.repairStep_layout⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_run,
⟨@NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_logarithmic,
@NearLinearRSP.TwoResources.Mission.Queue.ancestors_zero⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.ancestors_pos,
⟨@NearLinearRSP.TwoResources.Mission.Queue.le_of_mem_ancestors,
@NearLinearRSP.TwoResources.Mission.Queue.repairStep_record_other⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.repairStep_ready,
@NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_correct⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.writeLeaf_eval,
@NearLinearRSP.TwoResources.Mission.Queue.leafWritten_header⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.updateStart_header,
⟨@NearLinearRSP.TwoResources.Mission.Queue.leafWritten_other,
@NearLinearRSP.TwoResources.Mission.Queue.updateStart_parent⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.updateStart_layout,
⟨@NearLinearRSP.TwoResources.Mission.Queue.updateStart_ready,
@NearLinearRSP.TwoResources.Mission.Queue.updateLeaf_correct⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.run_final_unique,
⟨@NearLinearRSP.TwoResources.Mission.Queue.WinnerFrame.refl,
@NearLinearRSP.TwoResources.Mission.Queue.WinnerFrame.trans⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.repairStep_frame,
@NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_run_frame⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.repairAncestors_frame,
@NearLinearRSP.TwoResources.Mission.Queue.updateStart_frame⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.updateLeaf_frame,
⟨@NearLinearRSP.TwoResources.Mission.Structured.run_atoms,
@NearLinearRSP.TwoResources.Mission.Structured.Cmd.atoms_size⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Structured.Store.ext,
@NearLinearRSP.TwoResources.Mission.Structured.run_atoms_append⟩,
⟨@NearLinearRSP.TwoResources.Mission.Structured.run_bounded_loop,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeLeafAtoms_eval⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeLeafPrepare_run,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeLeafReady_values,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeLeafReady_queue_header⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeInitializeLeaf_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedBody_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_counter,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_fixed⟩⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_memory,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedLoop_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_run⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_nr_fixed,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStep_top_fixed,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeSeedInv.step⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeSeedInv.steps,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_correct,
@NearLinearRSP.TwoResources.Mission.Structured.Atom.nat_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Structured.Atom.real_frame,
@NearLinearRSP.TwoResources.Mission.Structured.Atom.natMemory_frame⟩,
⟨@NearLinearRSP.TwoResources.Mission.Structured.Atom.realMemory_frame,
@NearLinearRSP.TwoResources.Mission.Structured.Run.nat_frame⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Structured.Run.real_frame,
⟨@NearLinearRSP.TwoResources.Mission.Structured.Run.natMemory_frame,
@NearLinearRSP.TwoResources.Mission.Structured.Run.realMemory_frame⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeSeedInv.step_memory_frame,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeSeedInv.steps_memory_frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_register_frame⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_real_register_frame,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeedStart_inv,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeSeed_framed⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.heapTruth_internal,
@NearLinearRSP.TwoResources.Mission.Queue.heapTruth_leaf⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.heapTruth_coherent,
@NearLinearRSP.TwoResources.Mission.Queue.merge_self⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.heapTruth_const,
⟨@NearLinearRSP.TwoResources.Mission.Queue.mem_ancestors_self,
@NearLinearRSP.TwoResources.Mission.Queue.parent_mem_ancestors⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.child_not_mem_ancestors,
⟨@NearLinearRSP.TwoResources.Mission.Queue.heapTruth_frame,
@NearLinearRSP.TwoResources.Mission.Queue.leafRecords_add⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.heapTruth_decode_subtree,
⟨@NearLinearRSP.TwoResources.Mission.Queue.heapTruth_root,
@NearLinearRSP.TwoResources.Mission.Queue.choose_map⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.winner_map,
@NearLinearRSP.TwoResources.Mission.Queue.heapTruth_firstMin⟩,
⟨@RSP.Tails.mass_nonneg,
@RSP.Tails.mass_succ_mul⟩⟩⟩⟩,
⟨⟨⟨@RSP.Tails.mass_hasSum,
⟨@RSP.Tails.poisson_pgf_hasSum,
@RSP.Tails.poisson_pgf⟩⟩,
⟨@RSP.Tails.firstMoment_hasSum,
⟨@RSP.Tails.factorialMoment_two_hasSum,
@RSP.Tails.secondMoment_hasSum⟩⟩⟩,
⟨⟨@RSP.Tails.poisson_integrable_sq,
⟨@RSP.Tails.poisson_memLp_two,
@RSP.Tails.poisson_mean⟩⟩,
⟨⟨@RSP.Tails.poisson_secondMoment,
@RSP.Tails.poisson_variance⟩,
⟨@RSP.Tails.poisson_upper_tail,
@RSP.Tails.poisson_lower_tail⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨@RSP.Tails.completeness_ratio,
⟨@RSP.Tails.soundness_ratio,
@RSP.Tails.completeness_ratio_le⟩⟩,
⟨@RSP.Tails.soundness_ratio_le,
⟨@RSP.Tails.poisson_completeness_tail,
@RSP.Tails.poisson_completeness_tail_of_le⟩⟩⟩,
⟨⟨@RSP.Tails.poisson_soundness_tail,
⟨@RSP.Tails.resource_union_bound,
@RSP.Tails.poisson_completeness_union⟩⟩,
⟨⟨@RSP.Tails.poisson_completeness_union_of_le,
@RSP.Tails.countdown_pos⟩,
⟨@RSP.Tails.countdown_sufficient,
@RSP.Tails.poisson_soundness_union⟩⟩⟩⟩,
⟨⟨⟨@RSP.PoissonBridge.lengthRate_nonneg,
⟨@RSP.PoissonBridge.costRate_nonneg,
@RSP.PoissonBridge.poissonCountMass_nonneg⟩⟩,
⟨@RSP.PoissonBridge.poissonCountMass_hasSum,
⟨@RSP.PoissonBridge.poissonCountMass_sum_le_one,
@RSP.PoissonBridge.edgeMass_nonneg⟩⟩⟩,
⟨⟨@RSP.PoissonBridge.edgeMass_rectangle_eq,
⟨@RSP.PoissonBridge.edgeMass_rectangle_nonneg,
@RSP.PoissonBridge.edgeMass_rectangle_le_one⟩⟩,
⟨⟨@RSP.PoissonBridge.edgeMass_sum_le_one,
@NearLinearRSP.TwoResources.standalone_RSP_TableBounds__foldl_invariant⟩,
⟨@NearLinearRSP.TwoResources.putCell_range,
@NearLinearRSP.TwoResources.dpValue_range⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.edgeExpectation_range,
⟨@NearLinearRSP.TwoResources.initLayer_range,
@NearLinearRSP.TwoResources.relaxEdge_range⟩⟩,
⟨@NearLinearRSP.TwoResources.popLayer_range,
⟨@NearLinearRSP.TwoResources.buildLayer_range,
@NearLinearRSP.TwoResources.buildTable_range⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.dpValue_buildTable_nonneg,
⟨@NearLinearRSP.TwoResources.dpValue_buildTable_le_one,
@NearLinearRSP.TwoResources.activeVertices_edge_left⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.activeVertices_edge_right,
@NearLinearRSP.TwoResources.putCell_same⟩,
⟨@NearLinearRSP.TwoResources.putCell_other_vertex,
@NearLinearRSP.TwoResources.putCell_other_layer⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.relaxEdge_table,
⟨@NearLinearRSP.TwoResources.relaxEdge_queue,
@NearLinearRSP.TwoResources.relaxEdge_nextRank⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.relaxEdge_keys_outside,
@NearLinearRSP.TwoResources.relaxEdge_parents_outside⟩,
⟨@NearLinearRSP.TwoResources.relaxEdge_keys_le,
@NearLinearRSP.TwoResources.standalone_Mission_QueueStructure__fold_preserves⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.relaxAll_table,
⟨@NearLinearRSP.TwoResources.relaxAll_queue,
@NearLinearRSP.TwoResources.relaxAll_nextRank⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.relaxAll_keys_outside,
@NearLinearRSP.TwoResources.relaxAll_parents_outside⟩,
⟨@NearLinearRSP.TwoResources.popLayer_queue_length,
@NearLinearRSP.TwoResources.popLayer_queue_subset⟩⟩⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.popLayer_other_layer,
⟨@NearLinearRSP.TwoResources.queueRun_zero,
@NearLinearRSP.TwoResources.queueRun_succ⟩⟩,
⟨@NearLinearRSP.TwoResources.queueRun_queue_length,
⟨@NearLinearRSP.TwoResources.queueRun_queue_subset,
@NearLinearRSP.TwoResources.queueRun_other_layer⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.buildLayer_other_layer,
⟨@NearLinearRSP.TwoResources.buildLayer_queue_exhausted,
@NearLinearRSP.TwoResources.popLayer_queue_nodup⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.queueRun_queue_nodup,
@NearLinearRSP.TwoResources.popLayer_sync⟩,
⟨@NearLinearRSP.TwoResources.queueRun_sync,
@NearLinearRSP.TwoResources.relaxEdge_zero_key⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.relaxAll_zero_key,
⟨@NearLinearRSP.TwoResources.popLayer_zero_key,
@NearLinearRSP.TwoResources.queueRun_range⟩⟩,
⟨@NearLinearRSP.TwoResources.queueRun_zero_key,
⟨@NearLinearRSP.TwoResources.buildLayer_source_zero,
@NearLinearRSP.TwoResources.edgeExpectation_congr⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.edgeExpectation_mono,
⟨@NearLinearRSP.TwoResources.edgeExpectation_extensive,
@NearLinearRSP.TwoResources.dpValue_congr_at⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.relaxEdge_futureBound,
@NearLinearRSP.TwoResources.relaxAll_keys_le⟩,
⟨@NearLinearRSP.TwoResources.relaxAll_futureBound,
@NearLinearRSP.TwoResources.popLayer_keys_le⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.popLayer_future_dpValue,
⟨@NearLinearRSP.TwoResources.popLayer_futureBound,
@NearLinearRSP.TwoResources.queueRun_futureBound⟩⟩,
⟨@NearLinearRSP.TwoResources.settleState_expectation_ge,
⟨@NearLinearRSP.TwoResources.relaxEdge_keys_ge,
@NearLinearRSP.TwoResources.relaxAll_keys_ge⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.pickedVertex_mem,
⟨@NearLinearRSP.TwoResources.pickedVertex_le,
@NearLinearRSP.TwoResources.popLayer_eq_relaxAll⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.popLayer_keys_ge_picked,
@NearLinearRSP.TwoResources.popLayer_picked_key_mono⟩,
⟨@NearLinearRSP.TwoResources.pathWeight_cons_cons,
@NearLinearRSP.TwoResources.pathWeight_nonneg⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.pathWeight_tail_le,
⟨@NearLinearRSP.TwoResources.pathWeight_suffix_le,
@NearLinearRSP.TwoResources.exists_pathReduction⟩⟩,
⟨@NearLinearRSP.TwoResources.isChain_vertices_lt,
⟨@NearLinearRSP.TwoResources.IsPath.vertices_lt,
@NearLinearRSP.TwoResources.IsPath.length_le_of_nodup⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.IsPath.exists_simple,
⟨@NearLinearRSP.TwoResources.Feasible.exists_simple,
@NearLinearRSP.TwoResources.pathWeight_le_length_mul⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.IsPath.weight_le_n_mul,
@NearLinearRSP.TwoResources.distanceLess_iff⟩,
⟨@NearLinearRSP.TwoResources.standalone_Mission_ShortestTreeStructure__treeFold_mem,
@NearLinearRSP.TwoResources.treePick_mem⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.standalone_Mission_ShortestTreeStructure__treeFold_le_seed,
⟨@NearLinearRSP.TwoResources.standalone_Mission_ShortestTreeStructure__treeFold_le_mem,
@NearLinearRSP.TwoResources.treePick_le⟩⟩,
⟨@NearLinearRSP.TwoResources.treeRelax_queue,
⟨@NearLinearRSP.TwoResources.treeRelax_rank,
@NearLinearRSP.TwoResources.treeRelax_outside⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRelax_dist_le,
⟨@NearLinearRSP.TwoResources.standalone_Mission_ShortestTreeStructure__treeFold_preserves,
@NearLinearRSP.TwoResources.treeRelaxAll_queue⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRelaxAll_rank,
@NearLinearRSP.TwoResources.treeRelaxFold_outside⟩,
⟨@NearLinearRSP.TwoResources.treeRelaxAll_outside,
@NearLinearRSP.TwoResources.treeRelaxFold_dist_le⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.treeRelaxAll_dist_le,
⟨@NearLinearRSP.TwoResources.treeSettle_dist,
@NearLinearRSP.TwoResources.treePop_eq_relaxAll⟩⟩,
⟨@NearLinearRSP.TwoResources.treePop_queue_length,
⟨@NearLinearRSP.TwoResources.treePop_queue_subset,
@NearLinearRSP.TwoResources.treePop_queue_nodup⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRun_zero,
⟨@NearLinearRSP.TwoResources.treeRun_succ,
@NearLinearRSP.TwoResources.treeRun_queue_length⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRun_queue_nodup,
@NearLinearRSP.TwoResources.shortestTree_eq_treeRun⟩,
⟨@NearLinearRSP.TwoResources.shortestTree_queue_exhausted,
@NearLinearRSP.TwoResources.treeInitial_policy⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.treeSettle_policy,
⟨@NearLinearRSP.TwoResources.treeRelax_policy,
@NearLinearRSP.TwoResources.treeRelaxFold_policy⟩⟩,
⟨@NearLinearRSP.TwoResources.treePop_policy,
⟨@NearLinearRSP.TwoResources.treeRun_policy,
@NearLinearRSP.TwoResources.shortestTree_finite_rank⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.shortestTree_finite_parent,
⟨@NearLinearRSP.TwoResources.treePop_dist_le,
@NearLinearRSP.TwoResources.treePop_outside⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treePop_dist_picked,
@NearLinearRSP.TwoResources.treeRelax_dist_ge⟩,
⟨@NearLinearRSP.TwoResources.treeRelaxFold_dist_ge,
@NearLinearRSP.TwoResources.treePop_dist_ge_picked⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.treeRelax_edge_bound,
⟨@NearLinearRSP.TwoResources.treeRelaxAll_edge_bound,
@NearLinearRSP.TwoResources.treePop_separation⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treePop_bellman,
@NearLinearRSP.TwoResources.treeRun_bellman_separation⟩,
⟨@NearLinearRSP.TwoResources.shortestTree_bellman,
@NearLinearRSP.TwoResources.treeRelax_dist_nonneg⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRelaxAll_dist_nonneg,
⟨@NearLinearRSP.TwoResources.treePop_dist_nonneg,
@NearLinearRSP.TwoResources.treeRun_dist_nonneg⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRun_dist_le,
@NearLinearRSP.TwoResources.shortestTree_dist_nonneg⟩,
⟨@NearLinearRSP.TwoResources.shortestTree_source_zero,
@NearLinearRSP.TwoResources.shortestTree_distance_nonneg⟩⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.treeDist_chain_bound,
⟨@NearLinearRSP.TwoResources.shortestTree_path_bound,
@NearLinearRSP.TwoResources.pathWeight_zero_chain⟩⟩,
⟨@NearLinearRSP.TwoResources.zeroLengthTree_path_bound,
⟨@NearLinearRSP.TwoResources.zeroBudgetTree_path_bound,
@NearLinearRSP.TwoResources.activeVertices_length_le_edges⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.edgeWeightSum_nonneg,
⟨@NearLinearRSP.TwoResources.weight_le_edgeWeightSum,
@NearLinearRSP.TwoResources.treePolicy_distance_bound⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRun_source_zero,
@NearLinearRSP.TwoResources.treeRun_sentinel_bound⟩,
⟨@NearLinearRSP.TwoResources.distanceLess_eq_sentinel,
@NearLinearRSP.TwoResources.treePick_eq_sentinel_firstMin⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.treeRun_pick_sentinel,
⟨@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_at,
@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_outside⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.slotVertex_injective,
⟨@NearLinearRSP.TwoResources.Mission.Queue.slotVertex_idxOf,
@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_single_change⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_delete,
⟨@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_update_key,
@NearLinearRSP.TwoResources.Mission.Queue.slotVertex_idxOf_eq⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_delete_vertex,
@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_update_vertex⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.standalone_Mission_QueueLeaves__getD_map_range,
@NearLinearRSP.TwoResources.Mission.Queue.standalone_Mission_QueueLeaves__filterMap_live⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.filter_sublist_members,
⟨@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_records,
@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_firstMin⟩⟩,
⟨@NearLinearRSP.TwoResources.popLayer_queue_sublist,
⟨@NearLinearRSP.TwoResources.queueRun_queue_sublist,
@NearLinearRSP.TwoResources.treePop_queue_sublist⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRun_queue_sublist,
⟨@NearLinearRSP.TwoResources.Mission.Queue.initPrefix_eval,
@NearLinearRSP.TwoResources.Mission.Queue.initPair_eval⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.empty_coherent,
@NearLinearRSP.TwoResources.Mission.Queue.prefixed_inv⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.paired_inv,
@NearLinearRSP.TwoResources.Mission.Queue.initLoop_run⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.initializeEmpty_correct,
⟨@NearLinearRSP.TwoResources.Mission.Queue.InitFrame.refl,
@NearLinearRSP.TwoResources.Mission.Queue.InitFrame.trans⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.prefixed_frame,
@NearLinearRSP.TwoResources.Mission.Queue.paired_frame⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.initLoop_run_framed,
@NearLinearRSP.TwoResources.Mission.Queue.initializeEmpty_framed⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.updateLeaf_refines,
⟨@NearLinearRSP.TwoResources.Mission.Queue.initializeEmpty_represents,
@NearLinearRSP.TwoResources.Mission.Queue.represented_root_firstMin⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.prefixLeaf_zero,
@NearLinearRSP.TwoResources.Mission.Queue.prefixLeaf_succ⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.buildSetup_eval,
@NearLinearRSP.TwoResources.Mission.Queue.prepareInsert_eval⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.insertIncrement_eval,
⟨@NearLinearRSP.TwoResources.Mission.Queue.initializeEmpty_high_register,
@NearLinearRSP.TwoResources.Mission.Queue.updateLeaf_high_register⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.WinnerFrame.initFrame,
⟨@NearLinearRSP.TwoResources.Mission.Queue.insertBody_run,
@NearLinearRSP.TwoResources.Mission.Queue.buildQueue_run⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.activeLeaf_initial,
⟨@NearLinearRSP.TwoResources.Mission.Queue.prefixLeaf_records,
@NearLinearRSP.TwoResources.Mission.Preprocess.seed_prefixLeaf⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeInitializeQueue_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeProbe_eval⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeAppend_eval,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeInsert_run⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_frame_register,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_frame_memory,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_frame_reals⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_present,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeResult_absent,
@NearLinearRSP.TwoResources.Mission.Preprocess.active_regions_disjoint⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.stableInsert_mem,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.stableInsert_nodup,
@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMActiveList__stableFold_loop⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.stableFold_eq_eraseDups,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeVertices_eq_stableFold⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.flag_zero_iff,
@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.empty⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.insert,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.indexOf,
@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.index_bounds⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.inverse,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.vertex_at,
@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.length_le⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.congr,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.weight_nonneg,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.top_pos⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.offset_lt_four,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.capacity_pos⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.target_lt_map,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.map_le_array⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.array_end_le_winner,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.target_lt_winner,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeRegisters.transfer⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeRegisters.after_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeInitializeQueue_rep⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeExtractAtoms_eval,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeExtractPrepared_values⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeExtractPrepared_header,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeExtract__updateLeaf_nat_frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeExtract__updateLeaf_real_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeExtract_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeRecordDistance_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeRecordedDistance_value,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeRecordedDistance_frame⟩⟩⟩⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.encodeInput_edge_left,
⟨@NearLinearRSP.TwoResources.encodeInput_edge_right,
@NearLinearRSP.TwoResources.encodeInput_length⟩⟩,
⟨@NearLinearRSP.TwoResources.encodeInput_cost,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeEdgeAtoms_eval,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeEdgeLoaded_values⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeTargetAtoms_eval,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeDecreaseAtoms_eval,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeDecreased_header⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeApplyDecrease_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyAtoms_eval⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyInsert_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_head⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_link,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_memory_frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_register_frame⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyResult_real_frame,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.AdjacencyChain.frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyInsert_chain⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeAdjacencyPrepared_scratch,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeAdjacencyAdvanced_scratch,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeAdjacencyPrepared_values⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeAdjacencyLoop_run_of_edge_contract,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeCheckTarget_run⟩,
⟨@NearLinearRSP.TwoResources.treePolicy_candidate_sentinel,
@NearLinearRSP.TwoResources.sentinelKey_le⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.sentinel_source_none_no_decrease,
⟨@NearLinearRSP.TwoResources.sentinel_finite_candidate_comparison,
@NearLinearRSP.TwoResources.treeRelax_eq_real_test⟩⟩,
⟨@NearLinearRSP.TwoResources.sentinelKey_update,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMemoryRep.congr,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMemoryRep.after_readonly⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeTarget_values,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeTarget_correct,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.sentinel_bounds⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeEdge__edgeGuard_value,
@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeEdge__candidate_value⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeEdge__modeBody_correct,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeEdge_correct⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.treeRelax_source_zero,
⟨@NearLinearRSP.TwoResources.TreeScanMath.step,
@NearLinearRSP.TwoResources.TreeScanMath.start⟩⟩,
⟨@NearLinearRSP.TwoResources.relaxEdge_nonoutgoing,
⟨@NearLinearRSP.TwoResources.relaxFold_filter_outgoing,
@NearLinearRSP.TwoResources.relaxAll_eq_outgoingFold⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.treeRelax_nonoutgoing,
⟨@NearLinearRSP.TwoResources.treeRelaxFold_filter_outgoing,
@NearLinearRSP.TwoResources.treeRelaxAll_eq_outgoingFold⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.relaxEdge_disabled,
@NearLinearRSP.TwoResources.treeRelax_disabled⟩,
⟨@NearLinearRSP.TwoResources.relaxEdge_comm,
@NearLinearRSP.TwoResources.relaxFold_perm⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.relaxAll_eq_reversedOutgoingFold,
⟨@NearLinearRSP.TwoResources.treeRelax_comm,
@NearLinearRSP.TwoResources.treeRelaxFold_perm⟩⟩,
⟨@NearLinearRSP.TwoResources.treeRelaxAll_eq_reversedOutgoingFold,
⟨@NearLinearRSP.TwoResources.popLayer_reversed_refinement,
@NearLinearRSP.TwoResources.treePop_reversed_refinement⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_index,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_inputPointer,
@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_register⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanBody_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanLoop_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanCmd_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.outgoingIndices_lt⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.outgoingIndices_succ,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyPrefix_zero,
@NearLinearRSP.TwoResources.Mission.Preprocess.edgeAt_valid⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_prefix,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanResult_register,
@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanResult_reals⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanResult_prefix,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyStep_memory_outside,
@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanResult_memory_outside⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.adjacencyScanCmd_correct,
@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMAdjacencyScan__map_filter_compat⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.edgeAt_map_range,
@NearLinearRSP.TwoResources.Mission.Preprocess.outgoingIndices_edges⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeScanInvariant.transfer,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.link_protected,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.graph_protected⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.AdjacencyPrefix.protected_frame,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.outgoingIndices_valid,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeScan_run⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeExtractRefinement__queue_update_nat_high,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeExtractRefinement__queue_update_real_high,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeExtract_refines⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeExtract_high_register,
@NearLinearRSP.TwoResources.Mission.Preprocess.sentinelKey_treeSettle⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSettle_parent_unchanged,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeExtract_registers⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSettle_registers,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeSettle_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeSettle_counter277⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.outgoingWork_erase,
@NearLinearRSP.TwoResources.standalone_Mission_OutgoingWork__indicator_sum⟩,
⟨@NearLinearRSP.TwoResources.standalone_Mission_OutgoingWork__outgoing_filter_count,
@NearLinearRSP.TwoResources.outgoingWork_active⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.outgoingWork_settle,
⟨@NearLinearRSP.TwoResources.queueRun_succ_front,
@NearLinearRSP.TwoResources.popLayer_nextRank_of_ne⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreePop__seq_attach,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeHeadStore_token⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treePopCmd_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.treePop_outgoingWork⟩⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeLoop_run,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.standalone_Mission_RAMTreeRun__seq_attach,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeCmd_run⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeState_final_tree,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeState_final_queue,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMemoryRep.final_distances⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMemoryRep.final_parents,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.zeroTreeSetup_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeRegisters.prepare⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.length_field_protected,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.zeroLength_tree⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.TreeMode.zeroBudget_tree,
@NearLinearRSP.TwoResources.Mission.Preprocess.zeroTreesCmd_run⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.standalone_Mission_Guesses__min_fold_le_seed,
⟨@NearLinearRSP.TwoResources.standalone_Mission_Guesses__min_fold_le_member,
@NearLinearRSP.TwoResources.standalone_Mission_Guesses__seed_le_max_fold⟩⟩,
⟨@NearLinearRSP.TwoResources.standalone_Mission_Guesses__member_le_max_fold,
⟨@NearLinearRSP.TwoResources.firstPositiveLength_le_member,
@NearLinearRSP.TwoResources.member_le_largestLength⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.largestLength_nonneg,
⟨@NearLinearRSP.TwoResources.firstPositiveLength_le_largestLength,
@NearLinearRSP.TwoResources.largestLength_pos⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.one_le_aspectRatio,
@NearLinearRSP.TwoResources.crossing_exists⟩,
⟨@NearLinearRSP.TwoResources.firstCrossing_spec,
@NearLinearRSP.TwoResources.firstCrossing_minimal⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.firstCrossing_le,
⟨@NearLinearRSP.TwoResources.firstCrossing_mono_top,
@NearLinearRSP.TwoResources.firstCrossing_approx⟩⟩,
⟨@NearLinearRSP.TwoResources.geometricGuesses_cover,
⟨@NearLinearRSP.TwoResources.Mission.GuessLoop.step_run,
@NearLinearRSP.TwoResources.Mission.GuessLoop.loop_run⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.GuessLoop.crossingCmd_run,
⟨@NearLinearRSP.TwoResources.Mission.GuessLoop.crossing_result,
@NearLinearRSP.TwoResources.Mission.GuessLoop.crossing_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.acceptedIndex_spec,
@NearLinearRSP.TwoResources.acceptedIndex_le⟩,
⟨@NearLinearRSP.TwoResources.acceptedIndex_exists,
@NearLinearRSP.TwoResources.answerBranch_inner_iff⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.answerBranch_inner_input,
⟨@NearLinearRSP.TwoResources.answerBranch_zeroLength_spec,
@NearLinearRSP.TwoResources.answerBranch_zeroBudget_spec⟩⟩,
⟨@NearLinearRSP.TwoResources.outerInputs_mem_fields,
⟨@NearLinearRSP.TwoResources.geometricGuesses_ordered,
@NearLinearRSP.TwoResources.outerInputs_ordered⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.outerInputs_get_length_le,
⟨@NearLinearRSP.TwoResources.answerDistance_eq_none_iff,
@NearLinearRSP.TwoResources.EncodesOutput.readDistance_eq⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.outerInputs_length_exact,
@NearLinearRSP.TwoResources.Mission.Preprocess.countCmd_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.countCmd_nat_frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.countCmd_real_frame⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.countCmd_memory_frame,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.headerPrepared_values,
@NearLinearRSP.TwoResources.Mission.Preprocess.headerLoopStore_zero⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.headerBody_run,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.headerLoop_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.headerCmd_run⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.headerResult_header,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.headerResult_memory_frame,
@NearLinearRSP.TwoResources.Mission.NatToReal.run_atoms⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.NatToReal.powerBody_run,
@NearLinearRSP.TwoResources.Mission.NatToReal.powerLoop_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.NatToReal.convertBody_run,
@NearLinearRSP.TwoResources.Mission.NatToReal.Frame.refl⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.NatToReal.Frame.trans,
⟨@NearLinearRSP.TwoResources.Mission.NatToReal.bodyResult_frame,
@NearLinearRSP.TwoResources.Mission.NatToReal.convertLoop_run⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.NatToReal.convertCmd_run,
⟨@NearLinearRSP.TwoResources.Mission.Scan.positives_append,
@NearLinearRSP.TwoResources.Mission.Scan.minimum_append⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Scan.addSample_summarize,
⟨@NearLinearRSP.TwoResources.Mission.Scan.prefixSummary_succ,
@NearLinearRSP.TwoResources.Mission.Scan.encoded_samples⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Scan.max_fold_filter_positive,
@NearLinearRSP.TwoResources.Mission.Scan.summarize_edgeSamples⟩,
⟨@NearLinearRSP.TwoResources.Mission.Scan.minCmd_run,
@NearLinearRSP.TwoResources.Mission.Scan.maxCmd_run⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Scan.positiveCmd_run,
⟨@NearLinearRSP.TwoResources.Mission.Scan.scanBody_run,
@NearLinearRSP.TwoResources.Mission.Scan.scanBody_values⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Scan.scan_init_rep,
⟨@NearLinearRSP.TwoResources.Mission.Scan.scan_step_rep,
@NearLinearRSP.TwoResources.Mission.Scan.scanCmd_run⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Scan.scan_encoded_correct,
⟨@NearLinearRSP.TwoResources.Mission.Scan.scan_nat_frame,
@NearLinearRSP.TwoResources.Mission.Scan.scan_real_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.CoreRegs.transfer,
@NearLinearRSP.TwoResources.Mission.Preprocess.headerResult_core⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.scalarCmd_run,
@NearLinearRSP.TwoResources.Mission.Address.standalone_Mission_RAMAddress__store_eq⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Address.standalone_Mission_RAMAddress__body_run,
⟨@NearLinearRSP.TwoResources.Mission.Address.loop_run,
@NearLinearRSP.TwoResources.Mission.Address.addressCmd_run⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Address.addressResult_value,
@NearLinearRSP.TwoResources.Mission.Address.addressResult_frame⟩,
⟨@NearLinearRSP.TwoResources.Mission.Address.addressResult_memory,
@NearLinearRSP.TwoResources.Mission.Address.rectangle_index_lt⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Address.address_cost_le_rectangle,
⟨@NearLinearRSP.TwoResources.Mission.Address.tableAddress_stride,
@NearLinearRSP.TwoResources.Mission.Address.tableAddress_next_cost⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Address.tableAddress_next_length,
@NearLinearRSP.TwoResources.Mission.Address.tableAddress_change_vertex⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.layoutFirst_eval,
@NearLinearRSP.TwoResources.Mission.Preprocess.layoutSecond_eval⟩⟩⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.layoutThird_eval,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.layoutFinish_eval,
@NearLinearRSP.TwoResources.Mission.Preprocess.layout_counts⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.layoutCmd_run,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_values,
@NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_headers⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_memory_frame,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.powerCacheBody_eval,
@NearLinearRSP.TwoResources.Mission.Preprocess.powerCacheBody_run⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.powerCacheLoop_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.powerCacheCmd_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.powerCache_values,
@NearLinearRSP.TwoResources.Mission.Preprocess.powerCache_frame⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.powerCache_natMemory,
⟨@NearLinearRSP.TwoResources.Mission.Query.prepend_run,
@NearLinearRSP.TwoResources.Mission.Query.storesList_cons⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Query.storesList_map,
⟨@NearLinearRSP.TwoResources.Mission.Query.prepend_stores,
@NearLinearRSP.TwoResources.Mission.Query.prepend_memory_frame⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Query.score_run,
⟨@NearLinearRSP.TwoResources.Mission.Query.score_value,
@NearLinearRSP.TwoResources.Mission.Query.score_nat_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Query.score_real_frame,
@NearLinearRSP.TwoResources.Mission.Query.score_memory_frame⟩,
⟨@NearLinearRSP.TwoResources.Mission.Query.choose_run,
@NearLinearRSP.TwoResources.Mission.Query.choose_cost_le⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Query.header_lt_outputEnd,
⟨@NearLinearRSP.TwoResources.Mission.Query.target_lt_outputEnd,
@NearLinearRSP.TwoResources.Mission.Query.table_lt_outputEnd⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ScalarReady.numeric,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.NumericRegs.transfer,
@NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_numeric⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.layoutResult_layout,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.layoutCacheCmd_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeStep_register⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeStep_pointer,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeScanBody_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeScan_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.loaded⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.step,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeScan_rep,
@NearLinearRSP.TwoResources.Mission.Preprocess.scannedVertices_pairs⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.encoded_scannedVertices,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeInitAtoms_eval,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_run⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_rep,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.ActiveRep.insert_memory_frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeScan_memory_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_memory_frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_register_frame⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.activeInit_real_frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.LayoutRegs.transfer⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.OutputHeaders.transfer,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.graphCmd_run,
@NearLinearRSP.TwoResources.Mission.Queue.capacityStart_eval⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Queue.capacityDouble_eval,
⟨@NearLinearRSP.TwoResources.Mission.Queue.chooseCapacity_run,
@NearLinearRSP.TwoResources.Mission.Queue.chooseCapacity_bounds⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Queue.chooseCapacity_exact,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.GraphReady.transfer,
@NearLinearRSP.TwoResources.Mission.Preprocess.heapCmd_run⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.setupCmd_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.capacity_bounds⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.GraphReady.runtime,
@NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.runtime⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.RuntimeReady.transfer,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.costSentinel_mode,
@NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.lengthSentinel_mode⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.RuntimeReady.treeActive,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.RuntimeReady.treeAdjacency,
@NearLinearRSP.TwoResources.Mission.Structured.run_acyclic⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Structured.Cmd.atoms_evalAcyclic,
⟨@NearLinearRSP.TwoResources.Mission.Structured.Cmd.atoms_acyclic,
@NearLinearRSP.TwoResources.markAccepted_fold⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.acceptedIndex_zero_budget,
@NearLinearRSP.TwoResources.acceptedIndex_zero_accuracy⟩,
⟨@NearLinearRSP.TwoResources.answerBranch_seed_find,
@NearLinearRSP.TwoResources.answerBranch_incremental⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedCmd_run,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedResult_values,
@NearLinearRSP.TwoResources.Mission.TargetRecords.markCmd_run⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.markResult_values,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.markResult_unchanged,
@NearLinearRSP.TwoResources.Mission.TargetRecords.LabelRep.finite_iff⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedTag_correct,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedResult_correct,
@NearLinearRSP.TwoResources.Mission.TargetRecords.mark_acceptance⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.selectedDistance_answer,
@NearLinearRSP.TwoResources.Mission.TargetRecords.selectedDistance_seed⟩,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seed_record,
@NearLinearRSP.TwoResources.Mission.TargetRecords.mark_record⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.branchesAfter_zero,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.branchesAfter_succ,
@NearLinearRSP.TwoResources.Mission.TargetRecords.branchesAfter_end⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_run,
@NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_correct⟩,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_memory_frame,
@NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_run⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_correct,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_memory_frame,
@NearLinearRSP.TwoResources.Mission.TargetRecords.RecordRep.memory_congr⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.target_record_separate,
@NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_nat_frame⟩,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_real_frame,
@NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_nat_frame⟩⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_real_frame,
⟨@NearLinearRSP.TwoResources.Mission.ActiveIterator.setup_eval,
@NearLinearRSP.TwoResources.Mission.ActiveIterator.prepared_eval⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.ActiveIterator.advanced_eval,
⟨@NearLinearRSP.TwoResources.Mission.ActiveIterator.setup_state,
@NearLinearRSP.TwoResources.Mission.ActiveIterator.prepared_state⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.ActiveIterator.prepared_values,
⟨@NearLinearRSP.TwoResources.Mission.ActiveIterator.advanced_state,
@NearLinearRSP.TwoResources.Mission.ActiveIterator.command_run⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.ActiveIterator.prefixFold_succ,
@NearLinearRSP.TwoResources.Mission.ActiveIterator.command_fold⟩,
⟨@NearLinearRSP.TwoResources.Mission.ActiveIterator.command_nat_frame,
@NearLinearRSP.TwoResources.Mission.ActiveIterator.command_real_frame⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.standalone_Mission_QueueSource__fold_keeps,
⟨@NearLinearRSP.TwoResources.standalone_Mission_QueueSource__fold_sets,
@NearLinearRSP.TwoResources.buildRow_range⟩⟩,
⟨@NearLinearRSP.TwoResources.buildRow_other_row,
⟨@NearLinearRSP.TwoResources.buildRow_source_zero,
@NearLinearRSP.TwoResources.buildTable_source_value⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.dpValue_buildTable_source,
⟨@NearLinearRSP.TwoResources.popLayer_inactive_frame,
@NearLinearRSP.TwoResources.queueRun_inactive_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.buildLayer_inactive_frame,
@NearLinearRSP.TwoResources.standalone_Mission_QueueInactive__fold_const⟩,
⟨@NearLinearRSP.TwoResources.buildRow_inactive_frame,
@NearLinearRSP.TwoResources.buildTable_inactive⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.dpValue_buildTable_inactive,
⟨@NearLinearRSP.TwoResources.accepted_active,
@NearLinearRSP.TwoResources.shortestTree_finite_active⟩⟩,
⟨@NearLinearRSP.TwoResources.shortestTree_inactive_distance,
⟨@NearLinearRSP.TwoResources.answerBranch_active,
@NearLinearRSP.TwoResources.answerBranch_inactive⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.answerDistance_inactive,
⟨@NearLinearRSP.TwoResources.answerPath_inactive,
@NearLinearRSP.TwoResources.Mission.TargetRecords.TargetFrame.refl⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.TargetFrame.trans,
@NearLinearRSP.TwoResources.Mission.TargetRecords.TargetFrame.outside⟩,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.TargetFrame.treeParents,
@NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_targetFrame⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_targetFrame,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.setAnswer_fold_apply,
@NearLinearRSP.TwoResources.Mission.TargetRecords.updateAnswer_fold_apply⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.RecordMap.initial_absent,
@NearLinearRSP.TwoResources.Mission.TargetRecords.RecordMap.seed_step⟩,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.RecordMap.mark_step,
@NearLinearRSP.TwoResources.Mission.TargetRecords.seed_fold_exact⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.mark_fold_exact,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_world,
@NearLinearRSP.TwoResources.Mission.TargetRecords.seedVisitor_iteratorFrame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.seedRecords_run,
@NearLinearRSP.TwoResources.Mission.Preprocess.runtime_outputs_queryReady⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.SetupReady.treeStart,
@NearLinearRSP.TwoResources.Mission.Preprocess.TreeAllocation.protected_before_winner⟩⟩⟩⟩⟩⟩,
⟨⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_protected_before_map,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_header_protected,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_graph_protected⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_post_targets_protected,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_cache_protected,
@NearLinearRSP.TwoResources.Mission.Preprocess.treeAllocation_tag_protected⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.zeroTrees_nat_scalar_frame,
⟨@NearLinearRSP.TwoResources.Mission.Preprocess.zeroTrees_real_scalar_frame,
@NearLinearRSP.TwoResources.Mission.Preprocess.ZeroTreeMemory.seedWorld⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Preprocess.zeroTrees_ready,
@NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_world⟩,
⟨@NearLinearRSP.TwoResources.Mission.TargetRecords.markVisitor_iteratorFrame,
@NearLinearRSP.TwoResources.Mission.TargetRecords.markRecords_run⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Outer.prepared_values,
⟨@NearLinearRSP.TwoResources.Mission.Outer.markPrepared_values,
@NearLinearRSP.TwoResources.Mission.Outer.advanced_values⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.poissonCountMass_recurrence,
⟨@NearLinearRSP.TwoResources.Mission.poisson_prefix,
@NearLinearRSP.TwoResources.Mission.poisson_iteration⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.poisson_iterations,
⟨@NearLinearRSP.TwoResources.Mission.poisson_exit,
@NearLinearRSP.TwoResources.Mission.poisson_evaluation⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.poissonProgram_correct,
@NearLinearRSP.TwoResources.Mission.Expectation.run_atoms⟩,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.Frame.refl,
@NearLinearRSP.TwoResources.Mission.Expectation.Frame.trans⟩⟩⟩⟩⟩,
⟨⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Expectation.ColumnFrame.refl,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.ColumnFrame.trans,
@NearLinearRSP.TwoResources.Mission.Expectation.ColumnFrame.frame⟩⟩,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.columnBody_inv,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.columnBody_frame,
@NearLinearRSP.TwoResources.Mission.Expectation.columnLoop_run⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Expectation.rowPrepare_inv,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.rowPrepare_frame,
@NearLinearRSP.TwoResources.Mission.Expectation.RowInv.afterColumn⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Expectation.rowFinish_inv,
@NearLinearRSP.TwoResources.Mission.Expectation.rowFinish_frame⟩,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.rowBody_run,
@NearLinearRSP.TwoResources.Mission.Expectation.rowLoop_run⟩⟩⟩⟩,
⟨⟨⟨@NearLinearRSP.TwoResources.Mission.Expectation.corePrepare_inv,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.corePrepare_frame,
@NearLinearRSP.TwoResources.Mission.Expectation.coreFinish_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Expectation.coreCmd_run,
@NearLinearRSP.TwoResources.Mission.Expectation.setupCmd_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.setupResult_values,
@NearLinearRSP.TwoResources.Mission.Expectation.FullFrame.refl⟩⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Expectation.FullFrame.trans,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.Frame.full,
@NearLinearRSP.TwoResources.Mission.Expectation.setupResult_frame⟩⟩,
⟨⟨@NearLinearRSP.TwoResources.Mission.Expectation.nonsaturatedCmd_run,
@NearLinearRSP.TwoResources.Mission.Expectation.expectationCmd_run⟩,
⟨@NearLinearRSP.TwoResources.Mission.Expectation.expectedResult_eq_edgeExpectation,
@NearLinearRSP.TwoResources.Mission.Expectation.edgeExpectation_run⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
