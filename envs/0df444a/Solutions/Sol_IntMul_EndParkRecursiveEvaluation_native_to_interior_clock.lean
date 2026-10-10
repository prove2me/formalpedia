-- Prove2me | solution 1 for IntMul.EndParkRecursiveEvaluation.native_to_interior_clock
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T07:56:37.219637+00:00
-- url     : https://prove2.me/submissions/104f05b9-b369-4cd6-8b90-afb28ea4b96a

import Definitions.Def_IntMul_EndParkRecursiveRelocation
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_evaluates_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_prefix_clock
import Theorems.Thm_IntMul_EndParkRecursiveRelocation_native_to_interior_execution
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.EndParkRecursiveSchedulerNativeInvariants

open IntMul.TrackedBankedSimulation (extents nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem owned_native_child_clock_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem owned_native_child_clock_word_payload_ne_start (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (inputWord M x y).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (inputWord M x y).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hl := owned_native_child_clock_word_letter M x y (inputWord M x y)[p] (List.getElem_mem hp)
    aesop
  · rw [List.getD_eq_default _ _ (by omega)]
    aesop

private theorem initial_unique_markers (M : MultitapeTM) (x y : List Bool) :
    ∀ j p, (M.initCfg x y).cells j p = M.startSym ↔ p = 0 := by
  intro j p
  cases p with
  | zero =>
      simp only [MultitapeTM.initCfg]
      split <;> simp [MultitapeTM.tapeOf]
  | succ p =>
      simp only [MultitapeTM.initCfg]
      by_cases hj : j = M.inTape
      · simp only [if_pos hj]
        change (inputWord M x y).getD p M.blank = M.startSym ↔ p + 1 = 0
        have h := owned_native_child_clock_word_payload_ne_start M x y p
        simp only [h,Nat.succ_ne_zero]
      · simp only [if_neg hj,MultitapeTM.tapeOf,List.getD_nil]
        have hd := M.syms_distinct
        simp only [List.nodup_cons,List.mem_cons,not_or] at hd
        aesop

private theorem initial_blank_tails (M : MultitapeTM) (x y : List Bool) :
    ∀ j p, initialExtent M x y j < p → (M.initCfg x y).cells j p = M.blank := by
  intro j p hp
  by_cases hj : j = M.inTape
  · simp only [initialExtent,if_pos hj] at hp
    simp only [MultitapeTM.initCfg,if_pos hj]
    cases p with
    | zero => omega
    | succ p =>
        change (inputWord M x y).getD p M.blank = _
        exact List.getD_eq_default _ _ (by omega)
  · simp only [initialExtent,if_neg hj] at hp
    simp only [MultitapeTM.initCfg,if_neg hj]
    cases p with
    | zero => omega
    | succ p => rfl

private theorem initial_heads_near (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).head j ≤ initialExtent M x y j + 1 := by
  intro j
  simp [MultitapeTM.initCfg]


end IntMul.EndParkRecursiveSchedulerNativeInvariants


namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem owned_native_child_clock_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem owned_native_child_clock_halted_step (N : MultitapeTM) (c : N.Cfg)
    (halt : c.state=N.qHalt) : N.step c=c := by
  apply owned_native_child_clock_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

private theorem owned_native_child_clock_halted_iterate (N : MultitapeTM) (c : N.Cfg)
    (halt : c.state=N.qHalt) (t : ℕ) : N.step^[t] c=c := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,owned_native_child_clock_halted_step N c halt]

private theorem owned_native_child_clock_live_before_halt (N : MultitapeTM) (c : N.Cfg) (p H : ℕ)
    (live : (N.step^[p] c).state≠N.qHalt)
    (halt : (N.step^[H] c).state=N.qHalt) : p< H := by
  by_contra hp
  have hHp : H≤ p := by omega
  have heq : N.step^[p] c=N.step^[H] c := by
    rw [show p=(p-H)+H by omega,Function.iterate_add_apply,owned_native_child_clock_halted_iterate N _ halt]
  exact live (by rw [heq]; exact halt)


end IntMul.EndParkRecursiveEvaluation


namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveReturn
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- A finite native child evaluation is replayed in arbitrary positive caller
windows with a body/cleanup clock strictly below any actual native halt clock.
All noninput trajectory conditions are proved, rather than assumed. -/
private theorem native_to_interior_clock (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset : Fin M.k → ℕ) (x y w : List Bool) (budget H : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (root_blank : base.cells (machine M n request resume).inTape
      (base.head (machine M n request resume).inTape)=(machine M n request resume).blank)
    (evaluation : Evaluates M n request resume (initialExtent M x y)
      (M.initCfg x y) [] w budget)
    (halt : ((machine M n request resume).step^[H]
      ((machine M n request resume).initCfg x y)).state=(machine M n request resume).qHalt) :
    ∃ q, q ≤ budget ∧ q < H ∧
      (machine M n request resume).step^[q]
        (bodyFrame M n request resume base rho sigma offset
          (initialExtent M x y) (M.initCfg x y) [])=
        inspectionFrame M n request resume base rho sigma offset w := by
  obtain ⟨b,z,hb,hz,hbz,hboot,hzrun⟩ := native_prefix_clock M n request resume x y w budget H evaluation halt
  obtain ⟨q,hq,hRun,hInside⟩ := evaluates_protected_prefix M n request resume (initialExtent M x y)
    (M.initCfg x y) [] w budget evaluation
    (nativeBase M n request resume x y) 1 1 (fun _ => 1)
    (by intro j; omega) (by omega) (by omega)
    (EndParkRecursiveSchedulerNativeInvariants.initial_unique_markers M x y)
    (EndParkRecursiveSchedulerNativeInvariants.initial_blank_tails M x y)
    (EndParkRecursiveSchedulerNativeInvariants.initial_heads_near M x y)
  have hprefix : (machine M n request resume).step^[b+q]
      ((machine M n request resume).initCfg x y)=
      inspectionFrame M n request resume (nativeBase M n request resume x y)
        1 1 (fun _ => 1) w := by
    rw [Nat.add_comm b q,Function.iterate_add_apply,hboot,hRun]
  have hlive : ((machine M n request resume).step^[b+q]
      ((machine M n request resume).initCfg x y)).state≠(machine M n request resume).qHalt := by
    rw [hprefix]
    change FlatRecursiveScheduler.State.inspectStack≠FlatRecursiveScheduler.State.halt
    simp
  have hclock := owned_native_child_clock_live_before_halt (machine M n request resume) _ (b+q) H hlive halt
  refine ⟨q,hq,by omega,?_⟩
  exact EndParkRecursiveRelocation.native_to_interior_execution M n request resume base rho sigma offset
    x y w q hrho hsigma hoffset root_blank hInside hRun

end IntMul.EndParkRecursiveEvaluation


open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveReturn IntMul.EndParkRecursiveEvaluation IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset : Fin M.k → ℕ) (x y w : List Bool) (budget H : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (root_blank : base.cells (machine M n request resume).inTape
      (base.head (machine M n request resume).inTape)=(machine M n request resume).blank)
    (evaluation : Evaluates M n request resume (initialExtent M x y)
      (M.initCfg x y) [] w budget)
    (halt : ((machine M n request resume).step^[H]
      ((machine M n request resume).initCfg x y)).state=(machine M n request resume).qHalt) :
    ∃ q, q ≤ budget ∧ q < H ∧
      (machine M n request resume).step^[q]
        (bodyFrame M n request resume base rho sigma offset
          (initialExtent M x y) (M.initCfg x y) [])=
        inspectionFrame M n request resume base rho sigma offset w :=
  IntMul.EndParkRecursiveEvaluation.native_to_interior_clock M n request resume base rho sigma offset x y w budget H hrho hsigma hoffset root_blank evaluation halt

#print axioms solution
