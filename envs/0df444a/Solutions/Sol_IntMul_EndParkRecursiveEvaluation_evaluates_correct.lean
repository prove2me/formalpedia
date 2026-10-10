-- Prove2me | solution 1 for IntMul.EndParkRecursiveEvaluation.evaluates_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T04:14:26.301947+00:00
-- url     : https://prove2.me/submissions/f486f0da-d09b-43bc-9ddb-f03ff1a45df9

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_EndParkRecursiveScheduler_resume_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
import Theorems.Thm_IntMul_TrackedReturnReplacement_return_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem optimized_recursive_internal_blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_blank_tail_step M _ _ ih

private theorem optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step c).cells j p = M.startSym ↔ p = 0 := by
  classical
  intro j p
  change Function.update (c.cells j) (c.head j)
    ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = M.startSym ↔ p = 0
  by_cases hp : p = c.head j
  · rw [hp,Function.update_self]
    by_cases hz : c.head j = 0
    · have hs := (M.start_preserved c.state (fun j => c.cells j (c.head j)) j ((unique j _).mpr hz)).1
      simp only [hs,hz,iff_true]
    · have hn := M.start_only_at_start c.state (fun j => c.cells j (c.head j)) j
        (mt (unique j _).mp hz)
      simp only [hn,hz,iff_false]
  · rw [Function.update_of_ne hp]
    exact unique j p

/-- Local markers stay unique in every actual child run, so a physical
rewind cannot stop at an interior payload cell. -/
private theorem optimized_recursive_internal_unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_unique_marker_step M _ ih

private theorem optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem optimized_recursive_internal_heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact optimized_recursive_internal_solutions_intmultrackedbankedspaceinvariants_near_step M _ _ ih


end IntMul.TrackedBankedSpace




namespace IntMul.EndParkRecursiveSchedulerNativeInvariants

open IntMul.TrackedBankedSimulation (extents nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulernativeinvariants_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulernativeinvariants_word_payload_ne_start (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (inputWord M x y).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (inputWord M x y).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hl := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulernativeinvariants_word_letter M x y (inputWord M x y)[p] (List.getElem_mem hp)
    aesop
  · rw [List.getD_eq_default _ _ (by omega)]
    aesop

private theorem optimized_recursive_internal_initial_unique_markers (M : MultitapeTM) (x y : List Bool) :
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
        have h := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulernativeinvariants_word_payload_ne_start M x y p
        simp only [h,Nat.succ_ne_zero]
      · simp only [if_neg hj,MultitapeTM.tapeOf,List.getD_nil]
        have hd := M.syms_distinct
        simp only [List.nodup_cons,List.mem_cons,not_or] at hd
        aesop

private theorem optimized_recursive_internal_initial_blank_tails (M : MultitapeTM) (x y : List Bool) :
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

private theorem optimized_recursive_internal_initial_heads_near (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).head j ≤ initialExtent M x y j + 1 := by
  intro j
  simp [MultitapeTM.initCfg]


end IntMul.EndParkRecursiveSchedulerNativeInvariants



namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveevaluationinvariants_bits_payload_ne_start (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    (w.map M.bitSym).getD p M.blank≠M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (w.map M.bitSym).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hm := List.getElem_mem hp
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hm
    rw [←hb]
    cases b <;> simp only [MultitapeTM.bitSym] <;> aesop
  · rw [List.getD_eq_default _ _ (by omega)]
    aesop

private theorem optimized_recursive_internal_resumed_unique (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0) :
    ∀ j p, (resumedParent M n resume label extent c w).cells j p=M.startSym ↔ p=0 := by
  intro j p
  simp only [resumedParent]
  by_cases hj : j=M.outTape
  · simp only [if_pos hj]
    cases p with
    | zero => simp [MultitapeTM.tapeOf]
    | succ p =>
      change (w.map M.bitSym).getD p M.blank=M.startSym ↔ p+1=0
      simp only [optimized_recursive_internal_solutions_intmulendparkrecursiveevaluationinvariants_bits_payload_ne_start M w p,Nat.succ_ne_zero]
  · simp only [if_neg hj]
    exact unique j p

private theorem optimized_recursive_internal_resumed_tail (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∀ j p, parentAfterChildExtent M extent w j < p →
      (resumedParent M n resume label extent c w).cells j p=M.blank := by
  intro j p hp
  simp only [parentAfterChildExtent] at hp
  simp only [resumedParent]
  by_cases hj : j=M.outTape
  · simp only [if_pos hj] at hp ⊢
    cases p with
    | zero => omega
    | succ p =>
      change (w.map M.bitSym).getD p M.blank=M.blank
      exact List.getD_eq_default _ _ (by simp only [List.length_map]; omega)
  · simp only [if_neg hj] at hp ⊢
    exact tail j p hp

private theorem optimized_recursive_internal_resumed_near (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    ∀ j, (resumedParent M n resume label extent c w).head j≤ parentAfterChildExtent M extent w j+1 := by
  intro j
  by_cases hj : j=M.outTape <;> simp [resumedParent,parentAfterChildExtent,hj]

private theorem optimized_recursive_internal_step_unique (M : MultitapeTM) (c : M.Cfg)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0) :
    ∀ j p, (M.step c).cells j p=M.startSym ↔ p=0 := by
  have h := TrackedBankedSpace.optimized_recursive_internal_unique_marker_run M c 1 unique
  simpa only [Function.iterate_one] using h

private theorem optimized_recursive_internal_step_tail (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p=M.blank := by
  have h := TrackedBankedSpace.optimized_recursive_internal_blank_tail_run M c extent 1 tail
  simpa only [Function.iterate_one,extents,Function.iterate_zero,Function.id_def] using h

private theorem optimized_recursive_internal_step_near (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j≤ extent j+1) :
    ∀ j, (M.step c).head j≤ nextExtent M c extent j+1 := by
  have h := TrackedBankedSpace.optimized_recursive_internal_heads_near_run M c extent 1 near
  simpa only [Function.iterate_one,extents,Function.iterate_zero,Function.id_def] using h

end IntMul.EndParkRecursiveEvaluation



namespace IntMul.EndParkRecursiveScheduler

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem optimized_recursive_internal_boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem optimized_recursive_internal_boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_boot_iterate M n request resume c s hlive,he]

private theorem optimized_recursive_internal_preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem optimized_recursive_internal_preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_preparation_iterate M n request resume c s hlive,he]

private theorem optimized_recursive_internal_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,no_request]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem optimized_recursive_internal_body_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bodyMachine M).step^[s] c).state≠(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    (machine M n request resume).step^[T] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)) (by intro s hs; exact no_request s (by omega)),
      optimized_recursive_internal_body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem optimized_recursive_internal_input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem optimized_recursive_internal_input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_input_iterate M n request resume label c s hlive,he]

private theorem optimized_recursive_internal_reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem optimized_recursive_internal_reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_reservation_iterate M n request resume c s hlive,he]

private theorem optimized_recursive_internal_return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem optimized_recursive_internal_return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_return_iterate M n request resume c s hlive,he]

private theorem optimized_recursive_internal_cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem optimized_recursive_internal_cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_cleanup_iterate M n request resume c s hlive,he]

private theorem optimized_recursive_internal_output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem optimized_recursive_internal_output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_output_iterate M n request resume label c s hlive,he]

private theorem optimized_recursive_internal_finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem optimized_recursive_internal_finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_finish_iterate M n request resume c s hlive,he]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankedSimulation (nextExtent extents)

private noncomputable def optimized_recursive_internal_evalBodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)

private theorem optimized_recursive_internal_ordinary_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1≤ offset j)
    (c : M.Cfg) (v : List Bool)
    (marker : ∀ j, c.cells j 0=M.startSym) (near : ∀ j, c.head j≤ extent j+1)
    (live : c.state≠M.qHalt) (ordinary : request c.state=none) :
    (machine M n request resume).step (bodyFrame M n request resume base rho sigma offset extent c v)=
      bodyFrame M n request resume base rho sigma offset (nextExtent M c extent) (M.step c) v := by
  have h := (FixedTapeExtension.simulate_run (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c) 1).1
  rw [(TrackedBankedSimulation.simulate_run M (parentBase M n request resume base sigma v)
    offset extent positive c 1 marker near).1] at h
  simp only [Function.iterate_one,extents,Function.iterate_zero,Function.id_def] at h
  change (machine M n request resume).step (liftBody M n request resume
    (optimized_recursive_internal_evalBodyView M n request resume base rho sigma offset extent c v))=_
  rw [optimized_recursive_internal_body_step M n request resume _ live ordinary]
  exact congrArg (liftBody M n request resume) h

end IntMul.EndParkRecursiveEvaluation



namespace IntMul.EndParkRecursiveScheduler

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerpadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem optimized_recursive_internal_extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem optimized_recursive_internal_extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem optimized_recursive_internal_extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem optimized_recursive_internal_extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.cells (FixedTapeExtension.oldTape N j)=c.cells j) :
    (FixedTapeExtension.embed N base c).cells=base.cells := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem optimized_recursive_internal_extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.head (FixedTapeExtension.oldTape N j)=c.head j) :
    (FixedTapeExtension.embed N base c).head=base.head := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem optimized_recursive_internal_padded_init (N : MultitapeTM) (x y : List Bool) :
    (FixedTapeExtension.machine N).initCfg x y =
      FixedTapeExtension.embed N ((FixedTapeExtension.machine N).initCfg x y) (N.initCfg x y) := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerpadding_cfg_ext
  · rfl
  · apply (optimized_recursive_internal_extension_cells_ready N _ _ ?_).symm
    intro j
    have hzero : FixedTapeExtension.oldTape N j=(FixedTapeExtension.machine N).inTape ↔ j=N.inTape := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg (fun i : Fin (N.k+1) => i.val) h
        exact hv
      · intro h; subst j; rfl
    simp only [MultitapeTM.initCfg,hzero]
    split <;> rfl
  · apply (optimized_recursive_internal_extension_heads_ready N _ _ ?_).symm
    intro j
    rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem optimized_recursive_internal_work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem optimized_recursive_internal_work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedChildInputBridge.bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [workTape,TrackedChildInputBridge.bufferTape] at h
  omega

private theorem optimized_recursive_internal_embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem optimized_recursive_internal_embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem optimized_recursive_internal_embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (canonical : ∀ j p, base.cells (workTape M j) (offset j+p)=some (c.cells j p,decide (p≤ extent j))) :
    (TrackedBankedSimulation.embed M base offset extent c).cells=base.cells := by
  funext i p
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    let j := innerTape M i hi
    by_cases hp : p< offset j
    · dsimp only [j] at hp
      simp only [if_pos hp]
    · have hle : offset j≤ p := Nat.le_of_not_gt hp
      dsimp only [j] at hp
      rw [if_neg hp]
      have h := canonical j (p-offset j)
      have hw : workTape M j=i := optimized_recursive_internal_work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem optimized_recursive_internal_embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [optimized_recursive_internal_work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (extents)

private noncomputable def optimized_recursive_internal_bodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)

private theorem optimized_recursive_internal_body_service_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v : List Bool) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym) (near : ∀ j, c.head j ≤ extent j+1) :
    (bodyMachine M).step^[T] (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v)=
      optimized_recursive_internal_bodyView M n request resume base rho sigma offset (extents M c extent T) (M.step^[T] c) v := by
  have hr := (FixedTapeExtension.simulate_run (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c) T).1
  rw [(TrackedBankedSimulation.simulate_run M (parentBase M n request resume base sigma v)
    offset extent positive c T marker near).1] at hr
  exact hr

/-- The actual flat scheduler executes an ordinary body segment and reaches
its complete tracked terminal frame without consuming a request state. -/
private theorem optimized_recursive_internal_body_segment_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v : List Bool) (T : ℕ)
    (marker : ∀ j, c.cells j 0=M.startSym) (near : ∀ j, c.head j ≤ extent j+1)
    (halt : (M.step^[T] c).state=M.qHalt)
    (no_request : ∀ s, s < T → request (M.step^[s] c).state=none) :
    ∃ t, t ≤ T ∧ (machine M n request resume).step^[t]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      bodyFrame M n request resume base rho sigma offset (extents M c extent T) (M.step^[T] c) v := by
  have hr := optimized_recursive_internal_body_service_run M n request resume base rho sigma offset extent positive c v T marker near
  have hh : ((bodyMachine M).step^[T] (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v)).state=
      (bodyMachine M).qHalt := by
    rw [hr]
    exact halt
  obtain ⟨t,ht,htrun⟩ := optimized_recursive_internal_body_to_halt M n request resume
    (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v) T hh (by
      intro s hs
      rw [optimized_recursive_internal_body_service_run M n request resume base rho sigma offset extent positive c v s marker near]
      exact no_request s hs)
  rw [hr] at htrun
  exact ⟨t,ht,htrun⟩

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallinputframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_recursive_internal_inputParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) : (TrackedChildInputBridge.machine M).Cfg where
  state := (TrackedChildInputBridge.machine M).qStart
  cells := fun i => base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)
  head := fun i => base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)

private noncomputable def optimized_recursive_internal_inputPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (inputMachine M).Cfg where
  state := (inputMachine M).qStart
  cells := (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v).cells
  head := (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v).head

private noncomputable def optimized_recursive_internal_inputStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (inputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedChildInputBridge.machine M)
    (optimized_recursive_internal_inputPadBase M n request resume base rho sigma offset extent c v)
    (TrackedChildInputBridge.initialFrame M (optimized_recursive_internal_inputParent M n request resume base) sigma offset extent c v)

private noncomputable def optimized_recursive_internal_inputFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) : (inputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedChildInputBridge.machine M)
    (optimized_recursive_internal_inputPadBase M n request resume base rho sigma offset extent c v)
    (TrackedChildInputBridge.finalFrame M (optimized_recursive_internal_inputParent M n request resume base) sigma offset extent c v x y)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallinputframes_word_before_heads (M : MultitapeTM) (base : (TrackedChildInputBridge.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    (TrackedChildInputBridge.beforeFrame M base sigma offset extent c v 0).head=
      TrackedChildInputBridge.initialHeads M base sigma offset extent c v := by
  funext i
  simp only [TrackedChildInputBridge.beforeFrame,Nat.sub_zero]
  by_cases hb : i=TrackedChildInputBridge.bufferTape M
  · subst i
    simp only [if_true,TrackedChildInputBridge.initialHeads,TrackedBankedSimulation.embed,
      TrackedChildInputBridge.bufferTape,dif_neg (by omega : ¬2 ≤ (1 : ℕ)),
      TrackedChildInputBridge.parentBase,if_true]
    omega
  · simp only [if_neg hb]
    by_cases hp : i=TrackedChildInputBridge.packetTape M
    · subst i
      simp only [if_true]
      exact (optimized_recursive_internal_embed_work_head M (TrackedChildInputBridge.parentBase M base sigma v)
        offset extent c M.outTape).symm
    · simp only [if_neg hp]

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallinputframes_word_parent_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ) (v : List Bool) :
    TrackedChildInputBridge.parentBase M
      (optimized_recursive_internal_inputParent M n request resume base) sigma v=
      parentBase M n request resume base sigma v := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursivecallinputframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedChildInputBridge.parentBase,optimized_recursive_internal_inputParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedChildInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedChildInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]
  · funext i
    simp only [TrackedChildInputBridge.parentBase,optimized_recursive_internal_inputParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedChildInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedChildInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]

private theorem optimized_recursive_internal_body_input_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    relabel M n request resume (.input label .before)
      (bodyFrame M n request resume base rho sigma offset extent c v)=
    liftInput M n request resume label (optimized_recursive_internal_inputStart M n request resume base rho sigma offset extent c v) := by
  have hc : (TrackedChildInputBridge.initialFrame M (optimized_recursive_internal_inputParent M n request resume base)
      sigma offset extent c v).cells=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).cells := by
    simp only [TrackedChildInputBridge.initialFrame,
      TrackedChildInputBridge.initialFrame,TrackedChildInputBridge.beforeFrame,
      TrackedChildInputBridge.initialCells,optimized_recursive_internal_solutions_intmulendparkrecursivecallinputframes_word_parent_ready]
  have hh : (TrackedChildInputBridge.initialFrame M (optimized_recursive_internal_inputParent M n request resume base)
      sigma offset extent c v).head=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).head := by
    simp only [TrackedChildInputBridge.initialFrame,
      TrackedChildInputBridge.initialFrame,optimized_recursive_internal_solutions_intmulendparkrecursivecallinputframes_word_before_heads,
      TrackedChildInputBridge.initialHeads,optimized_recursive_internal_solutions_intmulendparkrecursivecallinputframes_word_parent_ready]
  apply optimized_recursive_internal_solutions_intmulendparkrecursivecallinputframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftInput,optimized_recursive_internal_inputStart,optimized_recursive_internal_inputPadBase,optimized_recursive_internal_bodyView,
      FixedTapeExtension.embed,hc]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftInput,optimized_recursive_internal_inputStart,optimized_recursive_internal_inputPadBase,optimized_recursive_internal_bodyView,
      FixedTapeExtension.embed,hh]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallstackframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_recursive_internal_pushParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (FiniteContinuationStack.machine M n).Cfg where
  state := .popStart
  cells := (optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y).cells
  head := (optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y).head

private theorem optimized_recursive_internal_input_stack_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M) := by
    apply Fin.ext; rfl
  simp only [optimized_recursive_internal_inputFinal,he,optimized_recursive_internal_extension_extra_cells,optimized_recursive_internal_inputPadBase,optimized_recursive_internal_bodyView,optimized_recursive_internal_extension_extra_cells]
  rw [show FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M)=
    FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl]
  simp only [optimized_recursive_internal_extension_extra_cells,optimized_recursive_internal_extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
  simp only [stackBase,eq_self,if_true]

private theorem optimized_recursive_internal_input_stack_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y).head (stackTape M)=rho := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M) := by
    apply Fin.ext; rfl
  simp only [optimized_recursive_internal_inputFinal,he,optimized_recursive_internal_extension_extra_heads,optimized_recursive_internal_inputPadBase,optimized_recursive_internal_bodyView,optimized_recursive_internal_extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedChildInputBridge.machine M)=
    FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl]
  simp only [optimized_recursive_internal_extension_extra_cells,optimized_recursive_internal_extension_extra_heads]
  rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
  simp only [stackBase,eq_self,if_true]

private theorem optimized_recursive_internal_input_push_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    relabel M n request resume (.push (.pushStart label))
      (liftInput M n request resume label (optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y))=
    liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n
      (optimized_recursive_internal_pushParent M n request resume base rho sigma offset extent c v x y) rho label) := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursivecallstackframes_cfg_ext
  · rfl
  · funext i p
    simp only [relabel,liftInput,liftPush,FiniteContinuationStack.pushStartFrame,optimized_recursive_internal_pushParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,optimized_recursive_internal_input_stack_cells,FiniteContinuationStack.freshTape]
      by_cases hp : p < rho <;> simp only [hp,if_true,if_false]
    · simp only [if_neg hi]
  · funext i
    simp only [relabel,liftInput,liftPush,FiniteContinuationStack.pushStartFrame,optimized_recursive_internal_pushParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,optimized_recursive_internal_input_stack_head]
    · simp only [if_neg hi]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallreservationframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_recursive_internal_pushed (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (FiniteContinuationStack.machine M n).Cfg :=
  FiniteContinuationStack.pushFrame M n
    (optimized_recursive_internal_pushParent M n request resume base rho sigma offset extent c v x y) rho label n

private noncomputable def optimized_recursive_internal_reserveParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (TrackedBankReservation.machine M).Cfg where
  state := .seek
  cells := fun i => (optimized_recursive_internal_pushed M n request resume label base rho sigma offset extent c v x y).cells
    (FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i)
  head := fun i => (optimized_recursive_internal_pushed M n request resume label base rho sigma offset extent c v x y).head
    (FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i)

private noncomputable def optimized_recursive_internal_reservePadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg where
  state := .seek
  cells := (optimized_recursive_internal_pushed M n request resume label base rho sigma offset extent c v x y).cells
  head := (optimized_recursive_internal_pushed M n request resume label base rho sigma offset extent c v x y).head

private noncomputable def optimized_recursive_internal_reserveStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankReservation.machine M)
    (optimized_recursive_internal_reservePadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankReservation.initialFrame M
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c))

private noncomputable def optimized_recursive_internal_reserveFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (reservationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankReservation.machine M)
    (optimized_recursive_internal_reservePadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankReservation.finalFrame M
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c))

private theorem optimized_recursive_internal_stack_ne_old (M : MultitapeTM) (i : Fin (M.k+2)) :
    FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i≠stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,stackTape,FiniteContinuationStack.stackTape] at h
  have := i.isLt
  omega

private theorem optimized_recursive_internal_reserve_parent_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (j : Fin M.k) (p : ℕ) :
    (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).cells
      (workTape M j) (offset j+p)=some ((parentAfterInput M c).cells j p,decide (p≤ extent j)) := by
  simp only [optimized_recursive_internal_reserveParent,optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame,if_neg (optimized_recursive_internal_stack_ne_old M _),optimized_recursive_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) (workTape M j)=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j) by rfl]
  simp only [optimized_recursive_internal_inputFinal,optimized_recursive_internal_extension_old_cells,TrackedChildInputBridge.finalFrame,
    if_neg (optimized_recursive_internal_work_ne_buffer M j),TrackedChildInputBridge.initialCells,parentAfterInput]
  exact optimized_recursive_internal_embed_work M _ offset extent c j p

private theorem optimized_recursive_internal_reserve_parent_heads (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (j : Fin M.k) :
    (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).head
      (workTape M j)=offset j+(parentAfterInput M c).head j := by
  simp only [optimized_recursive_internal_reserveParent,optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame,if_neg (optimized_recursive_internal_stack_ne_old M _),optimized_recursive_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) (workTape M j)=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) (workTape M j) by rfl]
  simp only [optimized_recursive_internal_inputFinal,optimized_recursive_internal_extension_old_heads,TrackedChildInputBridge.finalFrame,
    if_neg (optimized_recursive_internal_work_ne_buffer M j),parentAfterInput]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedChildInputBridge.packetTape,eq_self,if_true,Nat.add_zero]
  · have hn : workTape M j≠TrackedChildInputBridge.packetTape M := by
      intro h; exact hj (optimized_recursive_internal_work_injective M h)
    rw [if_neg hn]
    simp only [if_neg hj,TrackedChildInputBridge.initialHeads]
    exact optimized_recursive_internal_embed_work_head M _ offset extent c j

private theorem optimized_recursive_internal_push_reserve_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    relabel M n request resume (.reservation .seek)
      (liftPush M n request resume (optimized_recursive_internal_pushed M n request resume label base rho sigma offset extent c v x y))=
    liftReservation M n request resume (optimized_recursive_internal_reserveStart M n request resume label base rho sigma offset extent c v x y) := by
  have hc : (TrackedBankReservation.initialFrame M
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).cells=
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).cells := by
    exact optimized_recursive_internal_embed_cells_ready M _ offset extent _ (optimized_recursive_internal_reserve_parent_cells M n request resume label base rho sigma offset extent c v x y)
  have hh : (TrackedBankReservation.initialFrame M
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).head=
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).head := by
    simp only [TrackedBankReservation.initialFrame,TrackedBankReservation.seekFrame,Nat.zero_min,Nat.add_zero]
    exact optimized_recursive_internal_embed_heads_ready M
      (TrackedBankReservation.parentBase M (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y))
      offset extent (parentAfterInput M c) (optimized_recursive_internal_reserve_parent_heads M n request resume label base rho sigma offset extent c v x y)
  apply optimized_recursive_internal_solutions_intmulendparkrecursivecallreservationframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,liftPush,liftReservation,optimized_recursive_internal_reserveStart,FixedTapeExtension.embed]
    rw [hc]
    simp only [optimized_recursive_internal_reserveParent,optimized_recursive_internal_reservePadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,liftPush,liftReservation,optimized_recursive_internal_reserveStart,FixedTapeExtension.embed]
    rw [hh]
    simp only [optimized_recursive_internal_reserveParent,optimized_recursive_internal_reservePadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallpreparationframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_recursive_internal_preparationParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (TrackedBankPreparation.machine M).Cfg where
  state := .mark
  cells := (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).cells
  head := (TrackedBankReservation.finalFrame M
    (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
    offset extent (parentAfterInput M c)).head

private noncomputable def optimized_recursive_internal_preparationPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg where
  state := .mark
  cells := (optimized_recursive_internal_reserveFinal M n request resume label base rho sigma offset extent c v x y).cells
  head := (optimized_recursive_internal_reserveFinal M n request resume label base rho sigma offset extent c v x y).head

private noncomputable def optimized_recursive_internal_preparationStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M)
    (optimized_recursive_internal_preparationPadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankPreparation.initialFrame M
      (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y)

private noncomputable def optimized_recursive_internal_preparationFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M)
    (optimized_recursive_internal_preparationPadBase M n request resume label base rho sigma offset extent c v x y)
    (TrackedBankPreparation.readyFrame M
      (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y)

private theorem optimized_recursive_internal_preparation_fresh (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    TrackedBankPreparation.freshTape M
      ((optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells (workTape M j))
      (newOffsets M offset extent j)=
    (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells (workTape M j) := by
  funext p
  by_cases hp : p < newOffsets M offset extent j
  · simp only [TrackedBankPreparation.freshTape,if_pos hp]
  · simp only [TrackedBankPreparation.freshTape,if_neg hp]
    have ho : offset j≤ p := by unfold newOffsets at hp; omega
    have he : extent j < p-offset j := by unfold newOffsets at hp; omega
    have h := optimized_recursive_internal_reserve_parent_cells M n request resume label base rho sigma offset extent c v x y j (p-offset j)
    rw [show offset j+(p-offset j)=p by omega] at h
    simp only [parentAfterInput] at h
    rw [show (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      (workTape M j) p=some (c.cells j (p-offset j),decide (p-offset j≤ extent j)) from h]
    rw [tail j (p-offset j) he]
    simp only [decide_eq_false_iff_not.mpr (by omega : ¬p-offset j≤ extent j)]

private theorem optimized_recursive_internal_preparation_source (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      ⟨1,by change 1 < M.k+2; omega⟩=
      TrackedBankPreparation.sourceTape M
        ((optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells
          ⟨1,by change 1 < M.k+2; omega⟩) sigma (TrackedBankPreparation.inputWord M x y) := by
  have he : FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩≠FiniteContinuationStack.stackTape M :=
    optimized_recursive_internal_stack_ne_old M _
  simp only [optimized_recursive_internal_preparationParent,optimized_recursive_internal_reserveParent,optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame,if_neg he,optimized_recursive_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [optimized_recursive_internal_inputFinal,optimized_recursive_internal_extension_old_cells,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,if_true]
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedBankPreparation.sourceTape,hp,if_true,if_false]

private theorem optimized_recursive_internal_preparation_source_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).head
      ⟨1,by change 1 < M.k+2; omega⟩=sigma := by
  simp only [optimized_recursive_internal_preparationParent,TrackedBankReservation.finalFrame,dif_neg (by omega : ¬2≤ (1:ℕ)),
    optimized_recursive_internal_reserveParent,optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame,if_neg (optimized_recursive_internal_stack_ne_old M _),optimized_recursive_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [optimized_recursive_internal_inputFinal,optimized_recursive_internal_extension_old_heads,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,if_true]

private theorem optimized_recursive_internal_reserve_preparation_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    relabel M n request resume (.preparation .mark)
      (liftReservation M n request resume (optimized_recursive_internal_reserveFinal M n request resume label base rho sigma offset extent c v x y))=
    liftPreparation M n request resume (optimized_recursive_internal_preparationStart M n request resume label base rho sigma offset extent c v x y) := by
  have hc : (TrackedBankReservation.finalFrame M
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c)).cells=
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y).cells := by
    exact optimized_recursive_internal_embed_cells_ready M _ offset extent _ (optimized_recursive_internal_reserve_parent_cells M n request resume label base rho sigma offset extent c v x y)
  have hpc : (TrackedBankPreparation.initialFrame M
      (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y).cells=
      (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells := by
    funext i
    simp only [TrackedBankPreparation.initialFrame]
    by_cases hw : 2≤ i.val
    · simp only [dif_pos hw]
      have h := optimized_recursive_internal_preparation_fresh M n request resume label base rho sigma offset extent c v x y tail (innerTape M i hw)
      rw [optimized_recursive_internal_work_inner M i hw] at h
      exact h
    · simp only [dif_neg hw]
      by_cases hb : i.val=1
      · simp only [if_pos hb]
        have hi : i=⟨1,by change 1 < M.k+2; omega⟩ := Fin.ext hb
        rw [hi]
        exact (optimized_recursive_internal_preparation_source M n request resume label base rho sigma offset extent c v x y).symm
      · simp only [if_neg hb]
  have hph : (TrackedBankPreparation.initialFrame M
      (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
      sigma (newOffsets M offset extent) x y).head=
      (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).head := by
    funext i
    simp only [TrackedBankPreparation.initialFrame]
    by_cases hw : 2≤ i.val
    · simp only [dif_pos hw,optimized_recursive_internal_preparationParent,TrackedBankReservation.finalFrame]
    · simp only [dif_neg hw]
      by_cases hb : i.val=1
      · simp only [if_pos hb]
        have hi : i=⟨1,by change 1 < M.k+2; omega⟩ := Fin.ext hb
        rw [hi]
        exact (optimized_recursive_internal_preparation_source_head M n request resume label base rho sigma offset extent c v x y).symm
      · simp only [if_neg hb]
  apply optimized_recursive_internal_solutions_intmulendparkrecursivecallpreparationframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,liftReservation,liftPreparation,optimized_recursive_internal_preparationStart,FixedTapeExtension.embed]
    rw [hpc]
    simp only [optimized_recursive_internal_reserveFinal,optimized_recursive_internal_preparationPadBase,optimized_recursive_internal_preparationParent,FixedTapeExtension.embed]
    rw [hc]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,liftReservation,liftPreparation,optimized_recursive_internal_preparationStart,FixedTapeExtension.embed]
    rw [hph]
    simp only [optimized_recursive_internal_reserveFinal,optimized_recursive_internal_preparationPadBase,optimized_recursive_internal_preparationParent,FixedTapeExtension.embed]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallchildframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallchildframes_bank_empty_buffer (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) :
    TrackedBankPreparation.bankTape M base sigma []=TrackedOutputReturn.bufferTape M base sigma [] := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,if_pos hp]
  · by_cases he : p=sigma
    · subst p
      simp [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,MultitapeTM.tapeOf]
    · simp only [TrackedBankPreparation.bankTape,TrackedOutputReturn.bufferTape,if_neg hp,if_neg he]
      cases hq : p-sigma with
      | zero => omega
      | succ q =>
        simp only [MultitapeTM.tapeOf,List.map_nil,List.getD_nil,List.length_nil]
        simp

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivecallchildframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem optimized_recursive_internal_preparation_buffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)=
      TrackedOutputReturn.bufferTape M
        ((optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)) sigma [] ∧
    (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).head (bufferTape M)=
      sigma+(TrackedBankPreparation.inputWord M x y).length+1 := by
  have hc : (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (bufferTape M)=
      TrackedBankPreparation.bankTape M
        ((optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells ⟨1,by change 1 < M.k+2; omega⟩) sigma [] := by
    change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) _
      (TrackedBankPreparation.readyFrame M _ sigma (newOffsets M offset extent) x y)).cells
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [optimized_recursive_internal_extension_old_cells]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]
  constructor
  · rw [hc,optimized_recursive_internal_solutions_intmulendparkrecursivecallchildframes_bank_empty_buffer]
    exact (optimized_recursive_internal_solutions_intmulendparkrecursivecallchildframes_return_idem M _ sigma []).symm
  · change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) _
      (TrackedBankPreparation.readyFrame M _ sigma (newOffsets M offset extent) x y)).head
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [optimized_recursive_internal_extension_old_heads]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]

private theorem optimized_recursive_internal_preparation_parent_nonbuffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (i : Fin (M.k+2)) (hi : i.val≠1) :
    (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells i=
      (childBase M n request resume base rho sigma offset extent c label).cells
        (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i) := by
  have hb : i≠TrackedChildInputBridge.bufferTape M := by
    intro h; exact hi (congrArg Fin.val h)
  simp only [optimized_recursive_internal_preparationParent,optimized_recursive_internal_reserveParent,optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame,
    if_neg (optimized_recursive_internal_stack_ne_old M i),optimized_recursive_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) i by rfl]
  simp only [optimized_recursive_internal_inputFinal,optimized_recursive_internal_extension_old_cells]
  simp only [TrackedChildInputBridge.finalFrame,if_neg hb,TrackedChildInputBridge.initialCells]
  simp only [childBase,if_neg (optimized_recursive_internal_stack_ne_old M i),FixedTapeExtension.oldTape,if_neg hi,bodyFrame,liftBody]
  have hs : (⟨i.val,by have := i.isLt; omega⟩ : Fin (M.k+3))≠stackTape M := optimized_recursive_internal_stack_ne_old M i
  simp only [if_neg hs,FixedTapeExtension.embed,dif_pos i.isLt,FixedTapeExtension.innerTape]
  funext p
  simp only [TrackedBankedSimulation.embed]
  by_cases hw : 2 ≤ i.val
  · simp only [dif_pos hw]
    by_cases hp : p < offset (innerTape M i hw)
    · simp only [if_pos hp,TrackedChildInputBridge.parentBase,if_neg hb,optimized_recursive_internal_inputParent,parentBase,if_neg hi]
    · simp only [if_neg hp]
  · simp only [dif_neg hw,TrackedChildInputBridge.parentBase,if_neg hb,optimized_recursive_internal_inputParent,parentBase,if_neg hi]

private theorem optimized_recursive_internal_preparation_parent_buffer_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) (p : ℕ) (hp : p < sigma) :
    (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).cells
      ⟨1,by change 1 < M.k+2; omega⟩ p=base.cells (bufferTape M) p := by
  simp only [optimized_recursive_internal_preparationParent,optimized_recursive_internal_reserveParent,optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame,
    if_neg (optimized_recursive_internal_stack_ne_old M _),optimized_recursive_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) ⟨1,by change 1 < M.k+2; omega⟩=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩ by rfl]
  simp only [optimized_recursive_internal_inputFinal,optimized_recursive_internal_extension_old_cells,TrackedChildInputBridge.finalFrame,
    show (⟨1,by change 1 < M.k+2; omega⟩ : Fin (M.k+2))=TrackedChildInputBridge.bufferTape M by rfl,
    if_true,TrackedBankPreparation.sourceTape,if_pos hp,optimized_recursive_internal_inputParent]
  rfl

private theorem optimized_recursive_internal_preparation_stack_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedBankPreparation.machine M) := by apply Fin.ext; rfl
  simp only [optimized_recursive_internal_preparationFinal,he,optimized_recursive_internal_extension_extra_cells,optimized_recursive_internal_preparationPadBase,optimized_recursive_internal_reserveFinal]
  rw [show FixedTapeExtension.extraTape (TrackedBankPreparation.machine M)=
    FixedTapeExtension.extraTape (TrackedBankReservation.machine M) by rfl]
  simp only [optimized_recursive_internal_extension_extra_cells,optimized_recursive_internal_reservePadBase,optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame]
  rw [show FixedTapeExtension.extraTape (TrackedBankReservation.machine M)=stackTape M by rfl]
  simp only [eq_self,if_true,optimized_recursive_internal_pushParent,optimized_recursive_internal_input_stack_cells]
  funext p
  by_cases hp : p < rho <;> simp only [FiniteContinuationStack.recordTape,FiniteContinuationStack.freshTape,hp,if_true,if_false]

private theorem optimized_recursive_internal_preparation_stack_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).head (stackTape M)=rho+n+1 := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedBankPreparation.machine M) := by apply Fin.ext; rfl
  simp only [optimized_recursive_internal_preparationFinal,he,optimized_recursive_internal_extension_extra_heads,optimized_recursive_internal_preparationPadBase,optimized_recursive_internal_reserveFinal]
  rw [show FixedTapeExtension.extraTape (TrackedBankPreparation.machine M)=
    FixedTapeExtension.extraTape (TrackedBankReservation.machine M) by rfl]
  simp only [optimized_recursive_internal_extension_extra_heads,optimized_recursive_internal_reservePadBase,optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame]
  rw [show FixedTapeExtension.extraTape (TrackedBankReservation.machine M)=stackTape M by rfl]
  simp only [eq_self,if_true]


private theorem optimized_recursive_internal_preparation_parent_root_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (i : Fin (M.k+2)) (hi : i.val=0) :
    (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y).head i=
      base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i) := by
  have hb : i≠TrackedChildInputBridge.bufferTape M := by intro h; have := congrArg Fin.val h; simp [hi,TrackedChildInputBridge.bufferTape] at this
  have hp : i≠TrackedChildInputBridge.packetTape M := by intro h; have := congrArg Fin.val h; simp [hi,TrackedChildInputBridge.packetTape,workTape] at this
  have hw : ¬2 ≤ i.val := by omega
  simp only [optimized_recursive_internal_preparationParent,TrackedBankReservation.finalFrame,dif_neg hw,optimized_recursive_internal_reserveParent,optimized_recursive_internal_pushed,
    FiniteContinuationStack.pushFrame,if_neg (optimized_recursive_internal_stack_ne_old M _),optimized_recursive_internal_pushParent]
  rw [show FixedTapeExtension.oldTape (TrackedBankReservation.machine M) i=
    FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) i by rfl]
  simp only [optimized_recursive_internal_inputFinal,optimized_recursive_internal_extension_old_heads,TrackedChildInputBridge.finalFrame,if_neg hb,if_neg hp,
    TrackedChildInputBridge.initialHeads,TrackedBankedSimulation.embed,dif_neg hw,
    TrackedChildInputBridge.parentBase,if_neg hb,optimized_recursive_internal_inputParent]

private theorem optimized_recursive_internal_preparation_child_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool) :
    headFrame M n request resume (.body M.qStart)
      (relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y)))
      (bufferTape M) (sigma+1)=
    childFrame M n request resume base rho sigma offset extent c label x y := by
  classical
  apply optimized_recursive_internal_solutions_intmulendparkrecursivecallchildframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · simp only [headFrame,relabel,liftPreparation,optimized_recursive_internal_preparationFinal,childFrame,bodyFrame,liftBody,
        FixedTapeExtension.embed,dif_pos hi]
      simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
        TrackedBankPreparation.callerBase,parentBase,FixedTapeExtension.innerTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
        by_cases hp : p < newOffsets M offset extent (innerTape M ⟨i.val,hi⟩ hw)
        · simp only [if_pos hp,if_neg (by omega : i.val≠1)]
          exact congrFun (optimized_recursive_internal_preparation_parent_nonbuffer M n request resume label base rho sigma offset extent c v x y
            ⟨i.val,hi⟩ (by change i.val≠1; omega)) p
        · simp only [if_neg hp]
      · simp only [dif_neg hw]
        by_cases hb : i.val=1
        · simp only [if_pos hb]
          rw [optimized_recursive_internal_solutions_intmulendparkrecursivecallchildframes_bank_empty_buffer]
          by_cases hp : p < sigma
          · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
            have hi1 : (⟨i.val,hi⟩ : Fin (M.k+2))=⟨1,by omega⟩ := Fin.ext hb
            rw [hi1,optimized_recursive_internal_preparation_parent_buffer_prefix M n request resume label base rho sigma offset extent c v x y p hp]
            change base.cells (bufferTape M) p=
              (childBase M n request resume base rho sigma offset extent c label).cells (bufferTape M) p
            simp [childBase,bufferTape,stackTape,FiniteContinuationStack.stackTape,
              TrackedOutputReturn.bufferTape,hp]
          · simp only [TrackedOutputReturn.bufferTape,if_neg hp]
        · simp only [if_neg hb]
          exact congrFun (optimized_recursive_internal_preparation_parent_nonbuffer M n request resume label base rho sigma offset extent c v x y
            ⟨i.val,hi⟩ hb) p
    · have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      change (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y).cells (stackTape M) p=
        (FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
          (stackBase M n request resume (childBase M n request resume base rho sigma offset extent c label) (rho+n+1))
          (TrackedBankedSimulation.embed M _ _ _ _)).cells (stackTape M) p
      rw [optimized_recursive_internal_preparation_stack_cells]
      rw [show stackTape M=FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl,
        optimized_recursive_internal_extension_extra_cells]
      rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
      simp only [stackBase,if_true,childBase,if_true,FiniteContinuationStack.freshTape]
      by_cases hp : p < rho+n+1
      · simp only [if_pos hp]
      · simp only [if_neg hp,FiniteContinuationStack.recordTape,
          if_neg (by omega : ¬p < rho),if_neg (by omega : p≠rho),if_neg hp]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hb : i=bufferTape M
    · subst i
      simp [headFrame,childFrame,bodyFrame,liftBody,FixedTapeExtension.embed,
        TrackedBankedSimulation.embed,parentBase,bufferTape,FixedTapeExtension.innerTape]
    · simp only [headFrame,Function.update_of_ne hb,relabel,liftPreparation]
      by_cases hi : i.val < M.k+2
      · simp only [optimized_recursive_internal_preparationFinal,childFrame,bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
          TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,FixedTapeExtension.innerTape]
        by_cases hw : 2 ≤ i.val
        · simp [dif_pos hw,MultitapeTM.initCfg]
        · have hn : i.val≠1 := by intro h; exact hb (Fin.ext h)
          have hz : i.val=0 := by omega
          simp only [dif_neg hw,TrackedBankPreparation.callerBase,parentBase,if_neg hn]
          rw [optimized_recursive_internal_preparation_parent_root_head M n request resume label base rho sigma offset extent c v x y ⟨i.val,hi⟩ hz]
          simp only [childBase,FixedTapeExtension.oldTape]
          have hs : (⟨i.val,by omega⟩ : Fin (M.k+3))≠stackTape M := by intro h; have := congrArg Fin.val h; simp [stackTape,FiniteContinuationStack.stackTape] at this; omega
          simp only [if_neg hs,if_neg hn,dif_pos hi,dif_neg hw]
      · have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
        subst i
        rw [optimized_recursive_internal_preparation_stack_head]
        simp only [childFrame,bodyFrame,liftBody]
        rw [show stackTape M=FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M) by rfl,
          optimized_recursive_internal_extension_extra_heads]
        rw [show FixedTapeExtension.extraTape (TrackedBankedSimulation.machine M)=stackTape M by rfl]
        simp only [stackBase,if_true]

end IntMul.EndParkRecursiveCall




namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulfinitecontinuationstacktape_zero_ne_one (M : MultitapeTM) : M.zero ≠ M.one := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem optimized_recursive_internal_decode_onehot (M : MultitapeTM) (n : ℕ) (q : Fin n) (j : ℕ) :
    TrackedBankedSimulation.decode M (some (M.bitSym (decide (j = q.val)),true)) = M.one ↔ j = q.val := by
  by_cases hj : j = q.val
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode]
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode,optimized_recursive_internal_solutions_intmulfinitecontinuationstacktape_zero_ne_one M]

private theorem optimized_recursive_internal_record_bit (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (r : ℕ) (hr : r < j) :
    recordTape M n base rho q j (rho + r + 1) = some (M.bitSym (decide (r = q.val)),true) := by
  simp [recordTape,show ¬rho + r + 1 < rho by omega,
    show rho + r + 1 ≠ rho by omega,show rho + r + 1 < rho + j + 1 by omega,
    show rho + r + 1 - rho - 1 = r by omega]

private theorem optimized_recursive_internal_record_marker (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    recordTape M n base rho q j rho = some (M.sep,true) := by simp [recordTape]

private theorem optimized_recursive_internal_fresh_at (M : MultitapeTM) (base : ℕ → Sym M) (rho p : ℕ) (hp : rho ≤ p) :
    freshTape M base rho p = some (M.blank,false) := by simp [freshTape,show ¬p < rho by omega]

private theorem optimized_recursive_internal_marker_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (freshTape M base rho) rho (some (M.sep,true)) = recordTape M n base rho q 0 := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [recordTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [freshTape,recordTape,hp]
    · simp [freshTape,recordTape,hp,he,show ¬p < rho + 0 + 1 by omega]

private theorem optimized_recursive_internal_bit_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    Function.update (recordTape M n base rho q j) (rho + j + 1)
      (some (M.bitSym (decide (j = q.val)),true)) = recordTape M n base rho q (j + 1) := by
  funext p
  by_cases he : p = rho + j + 1
  · subst p
    simp [recordTape,show ¬rho + j + 1 < rho by omega,show rho + j + 1 ≠ rho by omega,show rho + j + 1 - rho - 1 = j by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,hp]
    · by_cases hm : p = rho
      · simp [recordTape,hp,hm]
      · by_cases hj : p < rho + j + 1
        · simp [recordTape,hp,hm,hj,show p < rho + (j + 1) + 1 by omega]
        · simp [recordTape,hp,hm,hj,show ¬p < rho + (j + 1) + 1 by omega]

private theorem optimized_recursive_internal_bit_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (hj : j < n) :
    Function.update (recordTape M n base rho q (n - j)) (rho + (n - j)) (some (M.blank,false)) =
      recordTape M n base rho q (n - (j + 1)) := by
  funext p
  by_cases he : p = rho + (n - j)
  · subst p
    simp [recordTape,show ¬rho + (n - j) < rho by omega,show rho + (n - j) ≠ rho by omega,
      show ¬rho + (n - j) < rho + (n - (j + 1)) + 1 by omega,show n - j ≠ 0 by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,hp]
    · by_cases hm : p = rho
      · simp [recordTape,hp,hm]
      · by_cases hbit : p < rho + (n - (j + 1)) + 1
        · simp [recordTape,hp,hm,hbit,show p < rho + (n - j) + 1 by omega]
        · simp [recordTape,hp,hm,hbit,show ¬p < rho + (n - j) + 1 by omega]

private theorem optimized_recursive_internal_marker_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (recordTape M n base rho q 0) rho (some (M.blank,false)) = freshTape M base rho := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [freshTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [recordTape,freshTape,hp]
    · simp [recordTape,freshTape,hp,he,show ¬p < rho + 0 + 1 by omega]

/-- A correctly read one-hot bit updates a finite control register only.
No host memory stores the continuation. -/
private theorem optimized_recursive_internal_recovered_step (n : ℕ) (q : Fin n) (j : ℕ) (hj : j < n) :
    (if n - 1 - j = q.val then some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) =
      recovered n q (j + 1) := by
  unfold recovered
  by_cases he : n - 1 - j = q.val
  · rw [if_pos he,if_pos (by have := q.isLt; omega : n - q.val ≤ j + 1)]
    congr 1
    exact Fin.ext he
  · rw [if_neg he]
    by_cases hp : n - q.val ≤ j
    · rw [if_pos hp,if_pos (by omega : n - q.val ≤ j + 1)]
    · rw [if_neg hp,if_neg (by have := q.isLt; omega : ¬n - q.val ≤ j + 1)]

private theorem optimized_recursive_internal_pop_scan (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (popFrame M n base rho q j).cells (stackTape M) ((popFrame M n base rho q j).head (stackTape M)) =
      some (M.bitSym (decide (n - 1 - j = q.val)),true) := by
  simp only [popFrame,ite_true]
  have he : rho + (n - j) = rho + (n - 1 - j) + 1 := by omega
  rw [he,optimized_recursive_internal_record_bit M n _ rho q (n - j) (n - 1 - j) (by omega)]

end IntMul.FiniteContinuationStack



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_raw_other (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (i : Fin (M.k + 3)) (hi : i ≠ stackTape M) :
    (rawTransition M n q a).2 i = (a i,.stay) := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;> simp_all

private theorem optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

/-- A tagged scan and tagged write make the physical protection wrapper
transparent; every non-stack tape remains exact and its head stays. -/
private theorem optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_physical_transition (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (target : State n) (old write : M.Sym × Bool) (d : Move)
    (hs : a (stackTape M) = some old) (hstate : (rawTransition M n q a).1 = target)
    (hstack : (rawTransition M n q a).2 (stackTape M) = (some write,d)) :
    transition M n q a = (target,fun i => if i = stackTape M then (some write,d) else (a i,.stay)) := by
  classical
  apply Prod.ext
  · exact hstate
  · funext i
    change TrackedBankCleanup.protect M (a i) ((rawTransition M n q a).2 i).1
      ((rawTransition M n q a).2 i).2 = _
    by_cases hi : i = stackTape M
    · subst i
      rw [hstack,hs]
      simp only [TrackedBankCleanup.protect,ite_true]
    · rw [optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_raw_other M n q a i hi,optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_protect_same_stay]
      simp only [if_neg hi]

private theorem optimized_recursive_internal_push_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushStartFrame M n base rho q) = pushFrame M n base rho q 0 := by
  let a := fun i => (pushStartFrame M n base rho q).cells i ((pushStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushStartFrame,freshTape]
  have ht := optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_physical_transition M n (.pushStart q) a (pushFrame M n base rho q 0).state
    (M.blank,false) (M.sep,true) .right hs
    (by simp [rawTransition,pushFrame,show 0 < n by have := q.isLt; omega]) (by simp [rawTransition])
  dsimp only [a] at ht
  change transition M n (pushStartFrame M n base rho q).state _ = _ at ht
  apply optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true]
      exact optimized_recursive_internal_marker_write M n _ rho q
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true,Nat.add_zero]
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]

private theorem optimized_recursive_internal_push_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (pushFrame M n base rho q j) = pushFrame M n base rho q (j + 1) := by
  let a := fun i => (pushFrame M n base rho q j).cells i ((pushFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushFrame,recordTape,show ¬rho + j + 1 < rho by omega,show rho + j + 1 ≠ rho by omega]
  have ht := optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_physical_transition M n (pushFrame M n base rho q j).state a
    (pushFrame M n base rho q (j + 1)).state (M.blank,false) (M.bitSym (decide (j = q.val)),true) .right hs
    (by simp only [pushFrame,dif_pos hj,rawTransition])
    (by simp only [pushFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushFrame,ite_true]
      exact optimized_recursive_internal_bit_write M n _ rho q j
    · simp only [if_neg hi,pushFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushFrame,ite_true]
      omega
    · simp only [if_neg hi,pushFrame,if_neg hi]

/-- One real transition switches from completed push to the pop routine.
A caller compiler can instead intercept pushDone to run its child. -/
private theorem optimized_recursive_internal_push_dispatch (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushFrame M n base rho q n) = popStartFrame M n base rho q := by
  have ht : transition M n (pushFrame M n base rho q n).state
      (fun i => (pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i)) =
      (.popStart,fun i => ((pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i),.stay)) := by
    simp only [pushFrame,dif_neg (by omega : ¬n < n),transition,rawTransition,optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_protect_same_stay]
  apply optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

private theorem optimized_recursive_internal_pop_start_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popStartFrame M n base rho q) = popFrame M n base rho q 0 := by
  let a := fun i => (popStartFrame M n base rho q).cells i ((popStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,popStartFrame,pushFrame,recordTape,show ¬rho + n + 1 < rho by omega,
      show rho + n + 1 ≠ rho by omega]
  have hf : recovered n q 0 = none := by
    simp [recovered,show ¬n - q.val ≤ 0 by have := q.isLt; omega]
  have ht := optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_physical_transition M n .popStart a (popFrame M n base rho q 0).state
    (M.blank,false) (M.blank,false) .left hs
    (by simp only [rawTransition,if_pos (by have := q.isLt; omega : 0 < n),popFrame,
      dif_pos (by have := q.isLt; omega : 0 < n),hf])
    (by simp [rawTransition,show 0 < n by have := q.isLt; omega,hs])
  dsimp only [a] at ht
  change transition M n (popStartFrame M n base rho q).state _ = _ at ht
  apply optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popStartFrame,pushFrame,popFrame,ite_true,Nat.sub_zero]
      have hscan : recordTape M n (base.cells (stackTape M)) rho q n (rho + n + 1) = some (M.blank,false) := by
        simpa only [a,popStartFrame,pushFrame,ite_true] using hs
      rw [←hscan,Function.update_eq_self]
    · simp only [if_neg hi,popStartFrame,pushFrame,popFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popStartFrame,pushFrame,popFrame,ite_true,Nat.sub_zero]
      omega
    · simp only [if_neg hi,popStartFrame,pushFrame,popFrame,if_neg hi]

private theorem optimized_recursive_internal_pop_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (popFrame M n base rho q j) = popFrame M n base rho q (j + 1) := by
  classical
  let a := fun i => (popFrame M n base rho q j).cells i ((popFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.bitSym (decide (n - 1 - j = q.val)),true) :=
    optimized_recursive_internal_pop_scan M n base rho q j hj
  have hpred : TrackedBankedSimulation.decode M (a (stackTape M)) = M.one ↔ n - 1 - j = q.val := by
    rw [hs]
    exact optimized_recursive_internal_decode_onehot M n q (n - 1 - j)
  have hf : (if TrackedBankedSimulation.decode M (a (stackTape M)) = M.one then
      some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) = recovered n q (j + 1) := by
    simpa only [hpred] using optimized_recursive_internal_recovered_step n q j hj
  have ht := optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q j).state a
    (popFrame M n base rho q (j + 1)).state
    (M.bitSym (decide (n - 1 - j = q.val)),true) (M.blank,false) .left hs
    (by simp only [popFrame,dif_pos hj,rawTransition]; rw [hf])
    (by simp only [popFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      exact optimized_recursive_internal_bit_erase M n _ rho q j hj
    · simp only [if_neg hi,popFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      omega
    · simp only [if_neg hi,popFrame,if_neg hi]

/-- The last physical pop transition erases the separator and enters the
finite resume state containing the recovered label, retaining older records. -/
private theorem optimized_recursive_internal_pop_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popFrame M n base rho q n) = finalFrame M n base rho q := by
  let a := fun i => (popFrame M n base rho q n).cells i ((popFrame M n base rho q n).head i)
  have hs : a (stackTape M) = some (M.sep,true) := by
    simp [a,popFrame,recordTape]
  have hf : recovered n q n = some q := by simp [recovered]
  have ht := optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q n).state a (.resume q)
    (M.sep,true) (M.blank,false) .stay hs
    (by simp only [popFrame,dif_neg (by omega : ¬n < n),hf,rawTransition,if_pos hs])
    (by simp [popFrame,hf,rawTransition])
  dsimp only [a] at ht
  apply optimized_recursive_internal_solutions_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
      exact optimized_recursive_internal_marker_erase M n _ rho q
    · simp only [if_neg hi,popFrame,finalFrame,pushStartFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
    · simp only [if_neg hi,popFrame,finalFrame,pushStartFrame,if_neg hi]

end IntMul.FiniteContinuationStack




namespace IntMul.FiniteContinuationStack

/-- Every write is an actual right-moving transition. The finite counter
has the caller's fixed control size; it never depends on recursion depth. -/
private theorem optimized_recursive_internal_push_run (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n).step^[j] (pushFrame M n base rho q 0) = pushFrame M n base rho q j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),optimized_recursive_internal_push_bit_step M n base rho q j (by omega)]

private theorem optimized_recursive_internal_push_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[n + 1] (pushStartFrame M n base rho q) = pushFrame M n base rho q n := by
  rw [Function.iterate_add_apply,Function.iterate_one,optimized_recursive_internal_push_marker_step,optimized_recursive_internal_push_run M n base rho q n le_rfl]

/-- Every read/erase is an actual left-moving transition, updating only a
finite recovered-label register while retaining all older prefix records. -/
private theorem optimized_recursive_internal_pop_run (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n).step^[j] (popFrame M n base rho q 0) = popFrame M n base rho q j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),optimized_recursive_internal_pop_bit_step M n base rho q j (by omega)]

private theorem optimized_recursive_internal_pop_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[n + 2] (popStartFrame M n base rho q) = finalFrame M n base rho q := by
  have h : (machine M n).step^[n + 1] (popStartFrame M n base rho q) = popFrame M n base rho q n := by
    rw [Function.iterate_add_apply,Function.iterate_one,optimized_recursive_internal_pop_start_step,optimized_recursive_internal_pop_run M n base rho q n le_rfl]
  rw [show n + 2 = (n + 1) + 1 by omega,Function.iterate_succ_apply',h,optimized_recursive_internal_pop_marker_step]

/-- One physical push-to-pop dispatch is included in the exact round trip.
The returned finite control state contains the recovered continuation q.
All tape cells and head positions equal the complete initial frame. -/
private theorem optimized_recursive_internal_round_trip_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q) = finalFrame M n base rho q ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).state = .resume q ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).cells =
      (pushStartFrame M n base rho q).cells ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).head =
      (pushStartFrame M n base rho q).head := by
  have h : (machine M n).step^[n + 2] (pushStartFrame M n base rho q) = popStartFrame M n base rho q := by
    rw [show n + 2 = (n + 1) + 1 by omega,Function.iterate_succ_apply',optimized_recursive_internal_push_correct,optimized_recursive_internal_push_dispatch]
  have hr : (machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q) = finalFrame M n base rho q := by
    rw [show 2 * n + 4 = (n + 2) + (n + 2) by omega,Function.iterate_add_apply,h,optimized_recursive_internal_pop_correct]
  refine ⟨hr,?_,?_,?_⟩ <;> rw [hr] <;> rfl

end IntMul.FiniteContinuationStack



namespace IntMul.EndParkRecursiveStack

open IntMul.EndParkRecursiveScheduler

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivestack_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_push_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : c.state≠.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      liftPush M n request resume ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n request resume (.push c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.push r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkrecursivestack_cfg_ext
  · simp only [MultitapeTM.step,liftPush,ht]
  · simp only [MultitapeTM.step,liftPush,ht]
  · simp only [MultitapeTM.step,liftPush,ht]

private theorem optimized_recursive_internal_push_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n request resume).step^[j]
      (liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label 0))=
      liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlive : (FiniteContinuationStack.pushFrame M n base rho label j).state≠.pushDone := by
      simp only [FiniteContinuationStack.pushFrame,dif_pos (by omega : j < n)]
      simp
    rw [Function.iterate_succ_apply',ih (by omega),optimized_recursive_internal_push_step M n request resume _ hlive,
      FiniteContinuationStack.optimized_recursive_internal_push_bit_step M n base rho label j (by omega)]

private theorem optimized_recursive_internal_push_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) :
    (machine M n request resume).step^[n+1]
      (liftPush M n request resume (FiniteContinuationStack.pushStartFrame M n base rho label))=
      liftPush M n request resume (FiniteContinuationStack.pushFrame M n base rho label n) := by
  have hlive : (FiniteContinuationStack.pushStartFrame M n base rho label).state≠.pushDone := by simp [FiniteContinuationStack.pushStartFrame]
  rw [Function.iterate_add_apply,Function.iterate_one,optimized_recursive_internal_push_step M n request resume _ hlive,
    FiniteContinuationStack.optimized_recursive_internal_push_marker_step,optimized_recursive_internal_push_run M n request resume base rho label n le_rfl]

private theorem optimized_recursive_internal_pop_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : ∀ label, c.state≠.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      liftPop M n request resume ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n request resume (.pop c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.pop r.1,r.2)) := by
    cases hs : c.state <;> first | (simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false]; try rfl) | skip
    rename_i label
    exact False.elim (live label hs)
  apply optimized_recursive_internal_solutions_intmulendparkrecursivestack_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]

private theorem optimized_recursive_internal_pop_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n request resume).step^[j]
      (liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label 0))=
      liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlive : ∀ q, (FiniteContinuationStack.popFrame M n base rho label j).state≠.resume q := by
      intro q
      simp only [FiniteContinuationStack.popFrame,dif_pos (by omega : j < n)]
      simp
    rw [Function.iterate_succ_apply',ih (by omega),optimized_recursive_internal_pop_step M n request resume _ hlive,
      FiniteContinuationStack.optimized_recursive_internal_pop_bit_step M n base rho label j (by omega)]

private theorem optimized_recursive_internal_pop_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) :
    (machine M n request resume).step^[n+2]
      (liftPop M n request resume (FiniteContinuationStack.popStartFrame M n base rho label))=
      liftPop M n request resume (FiniteContinuationStack.finalFrame M n base rho label) := by
  have hlive : ∀ q, (FiniteContinuationStack.popStartFrame M n base rho label).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popStartFrame]
  have hr : (machine M n request resume).step^[n+1]
      (liftPop M n request resume (FiniteContinuationStack.popStartFrame M n base rho label))=
      liftPop M n request resume (FiniteContinuationStack.popFrame M n base rho label n) := by
    rw [Function.iterate_add_apply,Function.iterate_one,optimized_recursive_internal_pop_step M n request resume _ hlive,
      FiniteContinuationStack.optimized_recursive_internal_pop_start_step,optimized_recursive_internal_pop_run M n request resume base rho label n le_rfl]
  have hm : ∀ q, (FiniteContinuationStack.popFrame M n base rho label n).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popFrame]
  rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply',hr,optimized_recursive_internal_pop_step M n request resume _ hm,
    FiniteContinuationStack.optimized_recursive_internal_pop_marker_step]

end IntMul.EndParkRecursiveStack



namespace IntMul.EndParkRecursiveScheduler

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerdispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerdispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerdispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) (present : a tape≠none) : moveActions M a tape .left=
      fun i => (a i,if i=tape then .left else .stay) := by
  classical
  funext i
  simp only [moveActions]
  by_cases hi : i=tape
  · subst i
    simp only [eq_self,if_true]
    cases h : a tape with
    | none => exact False.elim (present h)
    | some s => rfl
  · simp only [if_neg hi]
    cases a i <;> rfl

private theorem optimized_recursive_internal_stay_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,fun i => (c.cells i (c.head i),.stay))) :
    (machine M n request resume).step c=relabel M n request resume q c := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,relabel]
  · simp only [MultitapeTM.step,ht,relabel]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,relabel]

private theorem optimized_recursive_internal_right_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .right)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape+1) := by
  classical
  rw [optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerdispatch_right_actions] at ht
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,headFrame]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    by_cases hi : i=tape
    · subst i
      simp
    · simp [hi]

private theorem optimized_recursive_internal_left_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (present : c.cells tape (c.head tape)≠none)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .left)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape-1) := by
  classical
  rw [optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerdispatch_left_actions M _ tape present] at ht
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,headFrame]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,headFrame]
    funext i
    by_cases hi : i=tape
    · subst i
      simp
    · simp [hi]

private theorem optimized_recursive_internal_boot_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (exit : c.state=(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=headFrame M n request resume (.preparation .mark) (liftBoot M n request resume c) (stackTape M) (c.head (stackTape M)+1) := by
  apply optimized_recursive_internal_right_step
  change transition M n request resume (.boot c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply optimized_recursive_internal_left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,call]
  all_goals try rfl

private theorem optimized_recursive_internal_push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_recursive_internal_pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,exit]
  all_goals try rfl

private theorem optimized_recursive_internal_inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply optimized_recursive_internal_stay_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,FlatRecursiveScheduler.stackTape,reduceCtorEq,if_false,if_pos root]
  all_goals try rfl

private theorem optimized_recursive_internal_inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply optimized_recursive_internal_right_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,FlatRecursiveScheduler.stackTape,reduceCtorEq,if_false,if_neg parent]
  all_goals try rfl

private theorem optimized_recursive_internal_reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  have hm : c.cells (FlatRecursiveScheduler.bufferTape M) (c.head (FlatRecursiveScheduler.bufferTape M))=some (M.startSym,true) := marker
  apply optimized_recursive_internal_right_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos hm]
  rfl

private theorem optimized_recursive_internal_reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  have hm : c.cells (FlatRecursiveScheduler.bufferTape M) (c.head (FlatRecursiveScheduler.bufferTape M))≠some (M.startSym,true) := marker
  apply optimized_recursive_internal_left_step M n request resume _ _ _ present
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg hm]
  rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerreset_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_recursive_internal_resetFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ) : (machine M n request resume).Cfg where
  state := .resetBuffer
  cells := c.cells
  head := Function.update c.head (bufferTape M) (sigma+(a-r))

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerreset_empty_return_scan (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (sigma p : ℕ) : TrackedOutputReturn.bufferTape M base sigma [] (sigma+p)=
      if p=0 then some (M.startSym,true) else some (M.blank,false) := by
  cases p with
  | zero => simp [TrackedOutputReturn.bufferTape]
  | succ p => simp [TrackedOutputReturn.bufferTape,show ¬sigma+(p+1) < sigma by omega,
      show sigma+(p+1)≠sigma by omega]

private theorem optimized_recursive_internal_reset_scan (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (optimized_recursive_internal_resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((optimized_recursive_internal_resetFrame M n request resume c sigma a r).head (bufferTape M))=
        if a ≤ r then some (M.startSym,true) else some (M.blank,false) := by
  simp only [optimized_recursive_internal_resetFrame,Function.update_self]
  rw [empty,optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerreset_empty_return_scan]
  split_ifs <;> first | rfl | omega

private theorem optimized_recursive_internal_reset_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r < a) :
    (machine M n request resume).step (optimized_recursive_internal_resetFrame M n request resume c sigma a r)=
      optimized_recursive_internal_resetFrame M n request resume c sigma a (r+1) := by
  have hscan := optimized_recursive_internal_reset_scan M n request resume c sigma a r empty
  rw [if_neg (by omega : ¬a ≤ r)] at hscan
  have hm : (optimized_recursive_internal_resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((optimized_recursive_internal_resetFrame M n request resume c sigma a r).head (bufferTape M))≠some (M.startSym,true) := by
    rw [hscan]
    intro h
    have h := congrArg Prod.snd (Option.some.inj h)
    cases h
  rw [optimized_recursive_internal_reset_live_step M n request resume _ rfl hm (by rw [hscan]; exact Option.some_ne_none _)]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,optimized_recursive_internal_resetFrame,Function.update_self,Function.update_idem]
    congr 1
    omega

private theorem optimized_recursive_internal_reset_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r ≤ a) :
    (machine M n request resume).step^[r] (optimized_recursive_internal_resetFrame M n request resume c sigma a 0)=
      optimized_recursive_internal_resetFrame M n request resume c sigma a r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),optimized_recursive_internal_reset_step M n request resume c sigma a r empty (by omega)]

private theorem optimized_recursive_internal_reset_complete (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a : ℕ)
    (phase : c.state=.resetBuffer) (head : c.head (bufferTape M)=sigma+a)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (machine M n request resume).step^[a+1] c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (sigma+1) := by
  have hstart : c=optimized_recursive_internal_resetFrame M n request resume c sigma a 0 := by
    apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerreset_cfg_ext
    · exact phase
    · rfl
    · simp only [optimized_recursive_internal_resetFrame,Nat.sub_zero,←head]
      exact (Function.update_eq_self _ _).symm
  rw [hstart,Function.iterate_succ_apply',optimized_recursive_internal_reset_run M n request resume _ sigma a a empty le_rfl]
  have hm := optimized_recursive_internal_reset_scan M n request resume c sigma a a empty
  rw [if_pos le_rfl] at hm
  rw [optimized_recursive_internal_reset_marker_dispatch M n request resume _ rfl hm]
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,optimized_recursive_internal_resetFrame,Nat.sub_self,Nat.add_zero,Function.update_self,Function.update_idem]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord)
open IntMul.TrackedBankCleanup (span)

/-- One real recursive call entry in the single flat transition table. -/
private theorem optimized_recursive_internal_call_entry_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (live : c.state≠M.qHalt) (call : request c.state=some label)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (near : ∀ j, c.head j≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        3*(inputWord M x y).length+
        span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        childFrame M n request resume base rho sigma offset extent c label x y := by
  have hbody : (machine M n request resume).step
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftInput M n request resume label (optimized_recursive_internal_inputStart M n request resume base rho sigma offset extent c v) := by
    change (machine M n request resume).step
      (liftBody M n request resume (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v))=_
    rw [optimized_recursive_internal_body_request_dispatch M n request resume _ label live call]
    exact optimized_recursive_internal_body_input_ready M n request resume label base rho sigma offset extent c v
  let I := max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+4
  have hir : (inputMachine M).step^[I] (optimized_recursive_internal_inputStart M n request resume base rho sigma offset extent c v)=
      optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedChildInputBridge.machine M)
      (optimized_recursive_internal_inputPadBase M n request resume base rho sigma offset extent c v)
      (TrackedChildInputBridge.initialFrame M (optimized_recursive_internal_inputParent M n request resume base) sigma offset extent c v) I).1
    rw [(TrackedChildInputBridge.input_correct M (optimized_recursive_internal_inputParent M n request resume base)
      sigma offset extent c v x y packet).1] at h
    exact h
  have hih : ((inputMachine M).step^[I] (optimized_recursive_internal_inputStart M n request resume base rho sigma offset extent c v)).state=
      (inputMachine M).qHalt := by rw [hir]; rfl
  obtain ⟨s,hsc,hsr⟩ := optimized_recursive_internal_input_to_halt M n request resume label
    (optimized_recursive_internal_inputStart M n request resume base rho sigma offset extent c v) I hih
  rw [hir] at hsr
  have hdown1 : (machine M n request resume).step^[s+1]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftInput M n request resume label (optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y) := by
    rw [Function.iterate_succ_apply,hbody,hsr]
  have hstack : (machine M n request resume).step^[n+2]
      (liftInput M n request resume label (optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y))=
      liftPush M n request resume (optimized_recursive_internal_pushed M n request resume label base rho sigma offset extent c v x y) := by
    rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply,optimized_recursive_internal_input_dispatch M n request resume label _ rfl,
      optimized_recursive_internal_input_push_ready M n request resume label base rho sigma offset extent c v x y]
    exact EndParkRecursiveStack.optimized_recursive_internal_push_correct M n request resume _ rho label
  have hdown2 : (machine M n request resume).step^[n+3]
      (liftInput M n request resume label (optimized_recursive_internal_inputFinal M n request resume base rho sigma offset extent c v x y))=
      liftReservation M n request resume (optimized_recursive_internal_reserveStart M n request resume label base rho sigma offset extent c v x y) := by
    rw [show n+3=(n+2)+1 by omega,Function.iterate_succ_apply',hstack,
      optimized_recursive_internal_push_dispatch M n request resume _ (by simp [optimized_recursive_internal_pushed,FiniteContinuationStack.pushFrame])]
    exact optimized_recursive_internal_push_reserve_ready M n request resume label base rho sigma offset extent c v x y
  have hnear : ∀ j, (parentAfterInput M c).head j≤ extent j+1 := by
    intro j
    simp only [parentAfterInput]
    split
    · omega
    · exact near j
  have htail : ∀ j p, extent j < p → (parentAfterInput M c).cells j p=M.blank := tail
  let R := span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+1
  have hrr : (reservationMachine M).step^[R]
      (optimized_recursive_internal_reserveStart M n request resume label base rho sigma offset extent c v x y)=
      optimized_recursive_internal_reserveFinal M n request resume label base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedBankReservation.machine M)
      (optimized_recursive_internal_reservePadBase M n request resume label base rho sigma offset extent c v x y)
      (TrackedBankReservation.initialFrame M
        (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
        offset extent (parentAfterInput M c)) R).1
    rw [(TrackedBankReservation.reserve_correct M
      (optimized_recursive_internal_reserveParent M n request resume label base rho sigma offset extent c v x y)
      offset extent (parentAfterInput M c) hnear htail).1] at h
    exact h
  have hrh : ((reservationMachine M).step^[R]
      (optimized_recursive_internal_reserveStart M n request resume label base rho sigma offset extent c v x y)).state=(reservationMachine M).qHalt := by
    rw [hrr]; rfl
  obtain ⟨q,hqc,hqr⟩ := optimized_recursive_internal_reservation_to_halt M n request resume
    (optimized_recursive_internal_reserveStart M n request resume label base rho sigma offset extent c v x y) R hrh
  rw [hrr] at hqr
  have hdown3 : (machine M n request resume).step^[q+1]
      (liftReservation M n request resume (optimized_recursive_internal_reserveStart M n request resume label base rho sigma offset extent c v x y))=
      liftPreparation M n request resume (optimized_recursive_internal_preparationStart M n request resume label base rho sigma offset extent c v x y) := by
    rw [Function.iterate_succ_apply',hqr,optimized_recursive_internal_reservation_dispatch M n request resume _ rfl]
    exact optimized_recursive_internal_reserve_preparation_ready M n request resume label base rho sigma offset extent c v x y tail
  let P := 2*(inputWord M x y).length+3
  have hpr : (preparationMachine M).step^[P]
      (optimized_recursive_internal_preparationStart M n request resume label base rho sigma offset extent c v x y)=
      optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y := by
    have h := (FixedTapeExtension.simulate_run (TrackedBankPreparation.machine M)
      (optimized_recursive_internal_preparationPadBase M n request resume label base rho sigma offset extent c v x y)
      (TrackedBankPreparation.initialFrame M
        (optimized_recursive_internal_preparationParent M n request resume label base rho sigma offset extent c v x y)
        sigma (TrackedBankReservation.newOffsets M offset extent) x y) P).1
    rw [TrackedBankPreparation.setup_correct] at h
    exact h
  have hph : ((preparationMachine M).step^[P]
      (optimized_recursive_internal_preparationStart M n request resume label base rho sigma offset extent c v x y)).state=(preparationMachine M).qHalt := by
    rw [hpr]; rfl
  obtain ⟨p,hpc,hprun⟩ := optimized_recursive_internal_preparation_to_halt M n request resume
    (optimized_recursive_internal_preparationStart M n request resume label base rho sigma offset extent c v x y) P hph
  rw [hpr] at hprun
  have hdown4 : (machine M n request resume).step^[p+1]
      (liftPreparation M n request resume (optimized_recursive_internal_preparationStart M n request resume label base rho sigma offset extent c v x y))=
      relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y)) := by
    rw [Function.iterate_succ_apply',hprun,optimized_recursive_internal_preparation_dispatch M n request resume _ rfl]
  have hbuf := optimized_recursive_internal_preparation_buffer M n request resume label base rho sigma offset extent c v x y
  have hdown5 : (machine M n request resume).step^[(inputWord M x y).length+2]
      (relabel M n request resume .resetBuffer
        (liftPreparation M n request resume (optimized_recursive_internal_preparationFinal M n request resume label base rho sigma offset extent c v x y)))=
      childFrame M n request resume base rho sigma offset extent c label x y := by
    rw [show (inputWord M x y).length+2=((inputWord M x y).length+1)+1 by omega,
      optimized_recursive_internal_reset_complete M n request resume _ sigma ((inputWord M x y).length+1) rfl hbuf.2 hbuf.1]
    exact optimized_recursive_internal_preparation_child_ready M n request resume label base rho sigma offset extent c v x y
  let a := s+1
  let b := n+3
  let d := q+1
  let e := p+1
  let f := (inputWord M x y).length+2
  refine ⟨f+(e+(d+(b+a))),by dsimp only [a,b,d,e,f,I,R,P] at *; omega,?_⟩
  rw [Function.iterate_add_apply (machine M n request resume).step f (e+(d+(b+a))),
    Function.iterate_add_apply (machine M n request resume).step e (d+(b+a)),
    Function.iterate_add_apply (machine M n request resume).step d (b+a),
    Function.iterate_add_apply (machine M n request resume).step b a,
    hdown1,hdown2,hdown3,hdown4,hdown5]

end IntMul.EndParkRecursiveCall



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private noncomputable def optimized_recursive_internal_physicalWork (M : MultitapeTM) (j : Fin M.k) : Fin (M.k+3) :=
  FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j)

private theorem optimized_recursive_internal_work_not_stack (M : MultitapeTM) (j : Fin M.k) : optimized_recursive_internal_physicalWork M j≠stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [optimized_recursive_internal_physicalWork,FixedTapeExtension.oldTape,workTape,stackTape,FiniteContinuationStack.stackTape] at h
  have := j.isLt
  omega

private theorem optimized_recursive_internal_child_work (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (j : Fin M.k) :
    (childBase M n request resume base rho sigma offset extent c label).cells (optimized_recursive_internal_physicalWork M j)=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma []) offset extent c).cells
        (workTape M j) := by
  simp only [childBase,if_neg (optimized_recursive_internal_work_not_stack M j)]
  have hn : (optimized_recursive_internal_physicalWork M j).val≠1 := by simp only [optimized_recursive_internal_physicalWork,FixedTapeExtension.oldTape,workTape]; omega
  simp only [if_neg hn,bodyFrame,liftBody]
  simp only [optimized_recursive_internal_physicalWork,optimized_recursive_internal_extension_old_cells]

private theorem optimized_recursive_internal_child_work_fresh (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    TrackedBankCleanup.freshTape M
      ((childBase M n request resume base rho sigma offset extent c label).cells (optimized_recursive_internal_physicalWork M j))
      (newOffsets M offset extent j)=
      (childBase M n request resume base rho sigma offset extent c label).cells (optimized_recursive_internal_physicalWork M j) := by
  funext p
  by_cases hp : p < newOffsets M offset extent j
  · simp only [TrackedBankCleanup.freshTape,if_pos hp]
  · simp only [TrackedBankCleanup.freshTape,if_neg hp]
    have ho : offset j≤ p := by unfold newOffsets at hp; omega
    have he : extent j < p-offset j := by unfold newOffsets at hp; omega
    rw [optimized_recursive_internal_child_work]
    have h := optimized_recursive_internal_embed_work M (parentBase M n request resume base sigma []) offset extent c j (p-offset j)
    rw [show offset j+(p-offset j)=p by omega] at h
    rw [h,tail j (p-offset j) he]
    simp only [decide_eq_false_iff_not.mpr (by omega : ¬p-offset j≤ extent j)]

private theorem optimized_recursive_internal_inspection_work (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (optimized_recursive_internal_physicalWork M j)=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma []) offset extent c).cells
        (workTape M j) := by
  simp only [childInspection,EndParkRecursiveReturn.inspectionFrame,optimized_recursive_internal_physicalWork,FixedTapeExtension.oldTape,workTape]
  rw [dif_pos (by have := j.isLt; omega),dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by have := j.isLt; omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext; simp [innerTape]
  rw [hi]
  change TrackedBankCleanup.freshTape M
    ((childBase M n request resume base rho sigma offset extent c label).cells (optimized_recursive_internal_physicalWork M j))
    (newOffsets M offset extent j)=_
  rw [optimized_recursive_internal_child_work_fresh M n request resume base rho sigma offset extent c label tail j,optimized_recursive_internal_child_work]
  rfl

private theorem optimized_recursive_internal_inspection_work_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (childInspection M n request resume base rho sigma offset extent c label w).head (optimized_recursive_internal_physicalWork M j)=
      newOffsets M offset extent j := by
  simp only [childInspection,EndParkRecursiveReturn.inspectionFrame,optimized_recursive_internal_physicalWork,FixedTapeExtension.oldTape,workTape]
  rw [dif_pos (by have := j.isLt; omega),dif_pos (by omega)]
  congr 1

private theorem optimized_recursive_internal_inspection_stack (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n ∧
    (childInspection M n request resume base rho sigma offset extent c label w).head (stackTape M)=rho+n := by
  have hi : ¬(stackTape M).val < M.k+2 := by simp [stackTape,FiniteContinuationStack.stackTape]
  have hn : 0 < n := by have := label.isLt; omega
  constructor
  · simp only [childInspection,EndParkRecursiveReturn.inspectionFrame,dif_neg hi,childBase,if_true]
    funext p
    by_cases hp : p < rho+n+1
    · simp only [FiniteContinuationStack.freshTape,if_pos hp]
    · simp only [FiniteContinuationStack.freshTape,if_neg hp,FiniteContinuationStack.recordTape,
        if_neg (by omega : ¬p < rho),if_neg (by omega : p≠rho),if_neg hp]
  · simp only [childInspection,EndParkRecursiveReturn.inspectionFrame,dif_neg hi]
    omega

private theorem optimized_recursive_internal_inspection_nonroot (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (stackTape M)
      ((childInspection M n request resume base rho sigma offset extent c label w).head (stackTape M))≠none := by
  have h := optimized_recursive_internal_inspection_stack M n request resume base rho sigma offset extent c label w
  rw [h.1,h.2]
  have hn : 0 < n := by have := label.isLt; omega
  simp [FiniteContinuationStack.recordTape,hn.ne',show ¬rho+n < rho by omega,show rho+n≠rho by omega]

end IntMul.EndParkRecursiveResume



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveresumelowframes_buffer_replace (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (v w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma v) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem optimized_recursive_internal_inspection_buffer (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (bufferTape M)=
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
    (childInspection M n request resume base rho sigma offset extent c label w).head (bufferTape M)=sigma+w.length+1 := by
  have hs : bufferTape M≠stackTape M := by
    intro h; have := congrArg Fin.val h; simp [bufferTape,stackTape,FiniteContinuationStack.stackTape] at this
  constructor
  · simp only [childInspection,EndParkRecursiveReturn.inspectionFrame,bufferTape]
    rw [dif_pos (by omega),dif_neg (by omega)]
    simp only [if_true,childBase]
    change (⟨1,by omega⟩ : Fin (M.k+3))≠stackTape M at hs
    rw [if_neg hs]
    exact optimized_recursive_internal_solutions_intmulendparkrecursiveresumelowframes_buffer_replace M _ sigma [] w
  · simp [childInspection,EndParkRecursiveReturn.inspectionFrame,bufferTape]

private theorem optimized_recursive_internal_inspection_root (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells ⟨0,by change 0 < M.k+3; omega⟩=
      base.cells ⟨0,by change 0 < M.k+3; omega⟩ ∧
    (childInspection M n request resume base rho sigma offset extent c label w).head ⟨0,by change 0 < M.k+3; omega⟩=
      base.head ⟨0,by change 0 < M.k+3; omega⟩ := by
  have hs : (⟨0,by omega⟩ : Fin (M.k+3))≠stackTape M := by
    intro h; have := congrArg Fin.val h; simp [stackTape,FiniteContinuationStack.stackTape] at this
  constructor
  · simp only [childInspection,EndParkRecursiveReturn.inspectionFrame]
    rw [dif_pos (by omega),dif_neg (by omega)]
    simp only [if_false,childBase,if_neg hs,bodyFrame,liftBody,FixedTapeExtension.embed]
    rw [dif_pos (by omega)]
    simp [TrackedBankedSimulation.embed,parentBase,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
  · simp only [childInspection,EndParkRecursiveReturn.inspectionFrame]
    rw [dif_pos (by omega),dif_neg (by omega)]
    simp only [if_false,childBase,if_neg hs]
    rw [dif_pos (by omega),dif_neg (by omega)]
    simp

end IntMul.EndParkRecursiveResume



namespace IntMul.EndParkResume

private theorem optimized_recursive_internal_solutions_intmulendparkresumepadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem optimized_recursive_internal_extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem optimized_recursive_internal_extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem optimized_recursive_internal_extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem optimized_recursive_internal_extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.cells (FixedTapeExtension.oldTape N j)=c.cells j) :
    (FixedTapeExtension.embed N base c).cells=base.cells := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]

private theorem optimized_recursive_internal_extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
    (old : ∀ j, base.head (FixedTapeExtension.oldTape N j)=c.head j) :
    (FixedTapeExtension.embed N base c).head=base.head := by
  funext i
  by_cases hi : i.val < N.k
  · simp only [FixedTapeExtension.embed,dif_pos hi]
    have h := old (FixedTapeExtension.innerTape N i hi)
    have he : FixedTapeExtension.oldTape N (FixedTapeExtension.innerTape N i hi)=i := by apply Fin.ext; rfl
    rw [he] at h
    exact h.symm
  · simp only [FixedTapeExtension.embed,dif_neg hi]


end IntMul.EndParkResume



namespace IntMul.EndParkResume

private theorem optimized_recursive_internal_solutions_intmulendparkresumeprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_solutions_intmulendparkresumeprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem optimized_recursive_internal_solutions_intmulendparkresumeprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply optimized_recursive_internal_solutions_intmulendparkresumeprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem optimized_recursive_internal_solutions_intmulendparkresumeprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,optimized_recursive_internal_solutions_intmulendparkresumeprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem optimized_recursive_internal_restore_step (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n).step (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step c) := by
  have ht : transition M n (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem optimized_recursive_internal_restore_iterate (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n).step^[T] (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_restore_step M n _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_restore_to_halt (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n).step^[s] (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkresumeprograms_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkresumeprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_restore_iterate M n c s hlive,he]

private theorem optimized_recursive_internal_output_step (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n).step (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step c) := by
  have ht : transition M n (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply optimized_recursive_internal_solutions_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem optimized_recursive_internal_output_iterate (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n).step^[T] (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_recursive_internal_output_step M n label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_recursive_internal_output_to_halt (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n).step^[s] (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_recursive_internal_solutions_intmulendparkresumeprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact optimized_recursive_internal_solutions_intmulendparkresumeprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_recursive_internal_output_iterate M n label c s hlive,he]

private theorem optimized_recursive_internal_pop_step (M : MultitapeTM) (n : ℕ)
    
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : ∀ label, c.state≠.resume label) :
    (machine M n).step (liftPop M n c)=
      liftPop M n ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n (.pop c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.pop r.1,r.2)) := by
    cases hs : c.state <;> first | rfl | skip
    rename_i label
    exact False.elim (live label hs)
  apply optimized_recursive_internal_solutions_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]

private theorem optimized_recursive_internal_pop_run (M : MultitapeTM) (n : ℕ)
    
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n).step^[j]
      (liftPop M n (FiniteContinuationStack.popFrame M n base rho label 0))=
      liftPop M n (FiniteContinuationStack.popFrame M n base rho label j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlive : ∀ q, (FiniteContinuationStack.popFrame M n base rho label j).state≠.resume q := by
      intro q
      simp only [FiniteContinuationStack.popFrame,dif_pos (by omega : j < n)]
      simp
    rw [Function.iterate_succ_apply',ih (by omega),optimized_recursive_internal_pop_step M n _ hlive,
      FiniteContinuationStack.optimized_recursive_internal_pop_bit_step M n base rho label j (by omega)]

private theorem optimized_recursive_internal_pop_correct (M : MultitapeTM) (n : ℕ)
    
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n) :
    (machine M n).step^[n+2]
      (liftPop M n (FiniteContinuationStack.popStartFrame M n base rho label))=
      liftPop M n (FiniteContinuationStack.finalFrame M n base rho label) := by
  have hlive : ∀ q, (FiniteContinuationStack.popStartFrame M n base rho label).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popStartFrame]
  have hr : (machine M n).step^[n+1]
      (liftPop M n (FiniteContinuationStack.popStartFrame M n base rho label))=
      liftPop M n (FiniteContinuationStack.popFrame M n base rho label n) := by
    rw [Function.iterate_add_apply,Function.iterate_one,optimized_recursive_internal_pop_step M n _ hlive,
      FiniteContinuationStack.optimized_recursive_internal_pop_start_step,optimized_recursive_internal_pop_run M n base rho label n le_rfl]
  have hm : ∀ q, (FiniteContinuationStack.popFrame M n base rho label n).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popFrame]
  rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply',hr,optimized_recursive_internal_pop_step M n _ hm,
    FiniteContinuationStack.optimized_recursive_internal_pop_marker_step]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.FiniteContinuationStack (stackTape)
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkresumestackframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_restore_stack (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (restoreFinal M n base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n ∧
    (restoreFinal M n base rho sigma offset extent c label w).head (stackTape M)=rho+n+1 := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedSelectiveParentRestore.machine M (active M)) := by apply Fin.ext; rfl
  constructor
  · simp only [restoreFinal,he,optimized_recursive_internal_extension_extra_cells,restorePadBase]
    rw [he.symm]
    simp only [if_true]
  · simp only [restoreFinal,he,optimized_recursive_internal_extension_extra_heads,restorePadBase]
    rw [he.symm]
    simp only [if_true]

private theorem optimized_recursive_internal_restore_pop_ready (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    relabel M n (.pop .popStart)
      (liftRestore M n (restoreFinal M n base rho sigma offset extent c label w))=
    liftPop M n (FiniteContinuationStack.popStartFrame M n
      (popParent M n base rho sigma offset extent c label w) rho label) := by
  have hs := optimized_recursive_internal_restore_stack M n base rho sigma offset extent c label w
  apply optimized_recursive_internal_solutions_intmulendparkresumestackframes_cfg_ext
  · rfl
  · funext i p
    simp only [relabel,liftRestore,liftPop,FiniteContinuationStack.popStartFrame,
      FiniteContinuationStack.pushFrame,popParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,hs.1]
      by_cases hp : p < rho <;> simp only [FiniteContinuationStack.recordTape,hp,if_true,if_false]
    · simp only [if_neg hi]
  · funext i
    simp only [relabel,liftRestore,liftPop,FiniteContinuationStack.popStartFrame,
      FiniteContinuationStack.pushFrame,popParent]
    by_cases hi : i=stackTape M
    · subst i
      simp only [if_true,hs.2]
    · simp only [if_neg hi]

private theorem optimized_recursive_internal_popped_stack (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (popped M n base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
    (popped M n base rho sigma offset extent c label w).head (stackTape M)=rho := by
  constructor
  · simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true,popParent,
      (optimized_recursive_internal_restore_stack M n base rho sigma offset extent c label w).1]
    funext p
    by_cases hp : p < rho <;> simp only [FiniteContinuationStack.freshTape,FiniteContinuationStack.recordTape,hp,if_true,if_false]
  · simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.FiniteContinuationStack (stackTape)

private theorem optimized_recursive_internal_solutions_intmulendparkresumeworkframes_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (workTape M j).val := by simp [workTape]

private theorem optimized_recursive_internal_solutions_intmulendparkresumeworkframes_inner_work (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (workTape M j).val) : innerTape M (workTape M j) h=j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem optimized_recursive_internal_solutions_intmulendparkresumeworkframes_old_work_ne_stack (M : MultitapeTM) (j : Fin M.k) :
    FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)≠stackTape M := by
  intro h
  have hv := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,workTape,stackTape] at hv
  have := j.isLt
  omega

private theorem optimized_recursive_internal_popped_other_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+3)) (hi : i≠stackTape M) :
    (popped M n base rho sigma offset extent c label w).cells i=
      (restoreFinal M n base rho sigma offset extent c label w).cells i := by
  simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg hi,popParent]

private theorem optimized_recursive_internal_popped_other_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+3)) (hi : i≠stackTape M) :
    (popped M n base rho sigma offset extent c label w).head i=
      (restoreFinal M n base rho sigma offset extent c label w).head i := by
  simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg hi,popParent]

private theorem optimized_recursive_internal_restore_work_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (restoreFinal M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)) p=
      if p < offset j then
        base.cells (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)) p
      else some (c.cells j (p-offset j),decide (p-offset j ≤ extent j)) := by
  simp only [restoreFinal,optimized_recursive_internal_extension_old_cells,TrackedSelectiveParentRestore.finalFrame,
    TrackedBankedSimulation.embed,dif_pos (optimized_recursive_internal_solutions_intmulendparkresumeworkframes_work_ge M j),optimized_recursive_internal_solutions_intmulendparkresumeworkframes_inner_work,
    TrackedSelectiveParentRestore.parentBase,restorePlainBase]
  simp only [if_neg (by simp [workTape] : ¬(workTape M j).val=1)]

private theorem optimized_recursive_internal_restore_work_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) :
    (restoreFinal M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j))=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  simp only [restoreFinal,optimized_recursive_internal_extension_old_heads]
  simp only [TrackedSelectiveParentRestore.finalFrame,dif_pos (optimized_recursive_internal_solutions_intmulendparkresumeworkframes_work_ge M j),optimized_recursive_internal_solutions_intmulendparkresumeworkframes_inner_work,
    active,decide_eq_true_eq]

private theorem optimized_recursive_internal_output_parent_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (outputPlainBase M n base rho sigma offset extent c label w).cells (workTape M j) p=
      if p < offset j then
        base.cells (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j)) p
      else some (c.cells j (p-offset j),decide (p-offset j ≤ extent j)) := by
  simp only [outputPlainBase]
  change (popped M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)) p=
    if p < offset j then
      base.cells (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)) p
    else some (c.cells j (p-offset j),decide (p-offset j ≤ extent j))
  rw [optimized_recursive_internal_popped_other_cells M n base rho sigma offset extent c label w _ (optimized_recursive_internal_solutions_intmulendparkresumeworkframes_old_work_ne_stack M j)]
  exact optimized_recursive_internal_restore_work_cells M n base rho sigma offset extent c label w j p

private theorem optimized_recursive_internal_output_parent_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) :
    (outputPlainBase M n base rho sigma offset extent c label w).head (workTape M j)=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  simp only [outputPlainBase]
  change (popped M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j))=
    offset j+(if j=M.outTape then 0 else extent j+1)
  rw [optimized_recursive_internal_popped_other_heads M n base rho sigma offset extent c label w _ (optimized_recursive_internal_solutions_intmulendparkresumeworkframes_old_work_ne_stack M j)]
  exact optimized_recursive_internal_restore_work_heads M n base rho sigma offset extent c label w j

private theorem optimized_recursive_internal_restore_low (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+2)) (hi : i.val < 2) :
    (restoreFinal M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)=
      (restorePlainBase M n base sigma w).cells i ∧
    (restoreFinal M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)=
      (restorePlainBase M n base sigma w).head i := by
  constructor
  · simp only [restoreFinal,optimized_recursive_internal_extension_old_cells,TrackedSelectiveParentRestore.finalFrame,
      TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),TrackedSelectiveParentRestore.parentBase]
  · simp only [restoreFinal,optimized_recursive_internal_extension_old_heads,TrackedSelectiveParentRestore.finalFrame,
      dif_neg (by omega : ¬2 ≤ i.val)]

private theorem optimized_recursive_internal_output_low (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+2)) (hi : i.val < 2) :
    (outputPlainBase M n base rho sigma offset extent c label w).cells i=
      (restorePlainBase M n base sigma w).cells i ∧
    (outputPlainBase M n base rho sigma offset extent c label w).head i=
      (restorePlainBase M n base sigma w).head i := by
  have hs : FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i≠stackTape M := by
    intro h
    have hv := congrArg Fin.val h
    simp only [FixedTapeExtension.oldTape,stackTape] at hv
    have := M.two_le_k
    omega
  constructor
  · simp only [outputPlainBase,optimized_recursive_internal_popped_other_cells M n base rho sigma offset extent c label w _ hs]
    exact (optimized_recursive_internal_restore_low M n base rho sigma offset extent c label w i hi).1
  · simp only [outputPlainBase,optimized_recursive_internal_popped_other_heads M n base rho sigma offset extent c label w _ hs]
    exact (optimized_recursive_internal_restore_low M n base rho sigma offset extent c label w i hi).2

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem optimized_recursive_internal_work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem optimized_recursive_internal_embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem optimized_recursive_internal_embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem optimized_recursive_internal_embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (canonical : ∀ j p, base.cells (workTape M j) (offset j+p)=some (c.cells j p,decide (p≤ extent j))) :
    (TrackedBankedSimulation.embed M base offset extent c).cells=base.cells := by
  funext i p
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    let j := innerTape M i hi
    by_cases hp : p< offset j
    · dsimp only [j] at hp
      simp only [if_pos hp]
    · have hle : offset j≤ p := Nat.le_of_not_gt hp
      dsimp only [j] at hp
      rw [if_neg hp]
      have h := canonical j (p-offset j)
      have hw : workTape M j=i := optimized_recursive_internal_work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem optimized_recursive_internal_embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [optimized_recursive_internal_work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkresumeoutputframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_output_parent_work (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (outputPlainBase M n base rho sigma offset extent c label w).cells (workTape M j) (offset j+p)=
      some ((parentAtEnds M extent c).cells j p,decide (p≤ extent j)) := by
  rw [optimized_recursive_internal_output_parent_cells]
  simp only [if_neg (by omega : ¬offset j+p < offset j),Nat.add_sub_cancel_left,parentAtEnds]

private theorem optimized_recursive_internal_output_parent_work_head (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (outputPlainBase M n base rho sigma offset extent c label w).head (workTape M j)=
      offset j+(parentAtEnds M extent c).head j := by
  exact optimized_recursive_internal_output_parent_heads M n base rho sigma offset extent c label w j

private theorem optimized_recursive_internal_output_parent_buffer (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (outputPlainBase M n base rho sigma offset extent c label w).cells (TrackedParentOutputBridge.bufferTape M)=
      TrackedOutputReturn.bufferTape M
        (base.cells (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M)
          (TrackedParentOutputBridge.bufferTape M))) sigma w ∧
    (outputPlainBase M n base rho sigma offset extent c label w).head (TrackedParentOutputBridge.bufferTape M)=
      sigma+w.length+1 := by
  have h := optimized_recursive_internal_output_low M n base rho sigma offset extent c label w
    (TrackedParentOutputBridge.bufferTape M) (by simp [TrackedParentOutputBridge.bufferTape])
  constructor
  · rw [h.1]
    simp only [restorePlainBase,TrackedParentOutputBridge.bufferTape,if_true]
    rfl
  · rw [h.2]
    simp only [restorePlainBase,TrackedParentOutputBridge.bufferTape,if_true]

private theorem optimized_recursive_internal_solutions_intmulendparkresumeoutputframes_buffer_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem optimized_recursive_internal_output_initial_ready (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (TrackedParentOutputBridge.initialFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w).cells=
      (outputPlainBase M n base rho sigma offset extent c label w).cells ∧
    (TrackedParentOutputBridge.initialFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w).head=
      (outputPlainBase M n base rho sigma offset extent c label w).head := by
  let B := outputPlainBase M n base rho sigma offset extent c label w
  have hbuf := optimized_recursive_internal_output_parent_buffer M n base rho sigma offset extent c label w
  have hbc : (TrackedParentOutputBridge.parentBase M B sigma w).cells=B.cells := by
    funext i
    simp only [TrackedParentOutputBridge.parentBase]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp only [if_true]
      rw [hbuf.1]
      exact optimized_recursive_internal_solutions_intmulendparkresumeoutputframes_buffer_idem M _ sigma w
    · simp only [if_neg hb]
  have hbh : (TrackedParentOutputBridge.parentBase M B sigma w).head=B.head := by
    funext i
    simp only [TrackedParentOutputBridge.parentBase]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp only [if_true]
      exact hbuf.2.symm
    · simp only [if_neg hb]
  have hc : (TrackedBankedSimulation.embed M (TrackedParentOutputBridge.parentBase M B sigma w)
      offset extent (parentAtEnds M extent c)).cells=B.cells := by
    have h := optimized_recursive_internal_embed_cells_ready M (TrackedParentOutputBridge.parentBase M B sigma w) offset extent (parentAtEnds M extent c)
      (by rw [hbc]; exact optimized_recursive_internal_output_parent_work M n base rho sigma offset extent c label w)
    rw [hbc] at h
    exact h
  have hh : (TrackedBankedSimulation.embed M (TrackedParentOutputBridge.parentBase M B sigma w)
      offset extent (parentAtEnds M extent c)).head=B.head := by
    have h := optimized_recursive_internal_embed_heads_ready M (TrackedParentOutputBridge.parentBase M B sigma w) offset extent (parentAtEnds M extent c)
      (by intro j; rw [hbh,optimized_recursive_internal_output_parent_work_head])
    rw [hbh] at h
    exact h
  constructor
  · exact hc
  · funext i
    simp only [TrackedParentOutputBridge.initialFrame,TrackedParentOutputBridge.beforeFrame,Nat.sub_zero,
      TrackedParentOutputBridge.initialHeads,hh]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp only [if_true]
      exact hbuf.2.symm
    · simp only [if_neg hb]
      by_cases ht : i=TrackedParentOutputBridge.targetTape M
      · subst i
        simp only [if_true]
        simpa only [parentAtEnds,if_true,Nat.add_zero,TrackedParentOutputBridge.targetTape] using (optimized_recursive_internal_output_parent_work_head M n base rho sigma offset extent c label w M.outTape).symm
      · simp only [if_neg ht]
        exact congrFun hh i

private theorem optimized_recursive_internal_pop_output_ready (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    relabel M n (.output label .before)
      (liftPop M n (popped M n base rho sigma offset extent c label w))=
    liftOutput M n label (outputStart M n base rho sigma offset extent c label w) := by
  have h := optimized_recursive_internal_output_initial_ready M n base rho sigma offset extent c label w
  apply optimized_recursive_internal_solutions_intmulendparkresumeoutputframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,liftPop,liftOutput,outputStart,FixedTapeExtension.embed]
    rw [h.1]
    simp only [outputPlainBase,outputPadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,liftPop,liftOutput,outputStart,FixedTapeExtension.embed]
    rw [h.2]
    simp only [outputPlainBase,outputPadBase]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · simp only [dif_neg hi]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.FiniteContinuationStack (stackTape)

private theorem optimized_recursive_internal_final_work_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (finalFrame M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  change (outputFinal M n base rho sigma offset extent c label w).head _=_
  simp only [outputFinal,optimized_recursive_internal_extension_old_heads,TrackedParentOutputBridge.finalFrame]
  have hb : workTape M j≠TrackedParentOutputBridge.bufferTape M := by
    intro h
    have hv := congrArg Fin.val h
    simp only [workTape,TrackedParentOutputBridge.bufferTape] at hv
    omega
  rw [if_neg hb]
  by_cases hj : j=M.outTape
  · subst j
    rw [if_pos (show workTape M M.outTape=TrackedParentOutputBridge.targetTape M by rfl)]
    simp only [if_true,Nat.add_zero]
  · have ht : workTape M j≠TrackedParentOutputBridge.targetTape M := by
      intro h
      apply hj
      exact optimized_recursive_internal_work_injective M h
    rw [if_neg ht]
    have hh := congrFun
      (optimized_recursive_internal_output_initial_ready M n base rho sigma offset extent c label w).2 (workTape M j)
    simpa only [TrackedParentOutputBridge.initialFrame,TrackedParentOutputBridge.beforeFrame,
      if_neg hb,Nat.sub_zero] using hh.trans
        (optimized_recursive_internal_output_parent_heads M n base rho sigma offset extent c label w j)

private theorem optimized_recursive_internal_final_output_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) (p : ℕ) :
    (finalFrame M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))
      (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length)) := by
  change (outputFinal M n base rho sigma offset extent c label w).cells _ _=_
  simp only [outputFinal,optimized_recursive_internal_extension_old_cells,TrackedParentOutputBridge.finalFrame,
    if_pos (show workTape M M.outTape=TrackedParentOutputBridge.targetTape M by rfl)]
  simp only [TrackedBankPreparation.bankTape,
    if_neg (by omega : ¬offset M.outTape+p < offset M.outTape),Nat.add_sub_cancel_left,List.length_map]

private theorem optimized_recursive_internal_final_stack (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) :
    (finalFrame M n base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
    (finalFrame M n base rho sigma offset extent c label w).head (stackTape M)=rho := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedParentOutputBridge.machine M) := by
    apply Fin.ext
    rfl
  constructor
  · change (outputFinal M n base rho sigma offset extent c label w).cells _=_
    simp only [outputFinal,he,optimized_recursive_internal_extension_extra_cells,outputPadBase]
    rw [he.symm]
    exact (optimized_recursive_internal_popped_stack M n base rho sigma offset extent c label w).1
  · change (outputFinal M n base rho sigma offset extent c label w).head _=_
    simp only [outputFinal,he,optimized_recursive_internal_extension_extra_heads,outputPadBase]
    rw [he.symm]
    exact (optimized_recursive_internal_popped_stack M n base rho sigma offset extent c label w).2

end IntMul.EndParkResume



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveresumestartframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_inspection_resume_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    headFrame M n request resume (.restore .rewind)
      (childInspection M n request resume base rho sigma offset extent c label w)
      (stackTape M) (rho+n+1)=
    initialFrame M n request resume (serviceBase M n request resume base)
      rho sigma offset extent c label w := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveresumestartframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : optimized_recursive_internal_physicalWork M j=i := by
          apply Fin.ext
          simp only [optimized_recursive_internal_physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he]
        change (childInspection M n request resume base rho sigma offset extent c label w).cells
          (optimized_recursive_internal_physicalWork M j) p =
          (EndParkResume.restoreFinal M n (serviceBase M n request resume base)
            rho sigma offset extent c label w).cells
            (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (EndParkResume.active M)) (workTape M j)) p
        rw [optimized_recursive_internal_inspection_work M n request resume base rho sigma offset extent c label w tail j,
          EndParkResume.optimized_recursive_internal_restore_work_cells]
        simp only [TrackedBankedSimulation.embed,workTape]
        rw [dif_pos (by omega)]
        have hj : innerTape M ⟨j.val+2,by have := j.isLt; omega⟩ (by change 2 ≤ j.val+2; omega)=j := by
          apply Fin.ext
          simp [innerTape]
        simp only [hj,parentBase,if_neg (by omega : j.val+2≠1),serviceBase]
        rfl
      · by_cases hb : i.val=1
        · have he : i=bufferTape M := Fin.ext hb
          rw [he]
          change (childInspection M n request resume base rho sigma offset extent c label w).cells (bufferTape M) p=_
          rw [(optimized_recursive_internal_inspection_buffer M n request resume base rho sigma offset extent c label w).1]
          simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
            EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.optimized_recursive_internal_extension_old_cells,
            TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,TrackedBankedSimulation.embed,
            TrackedSelectiveParentRestore.parentBase,EndParkResume.restorePlainBase,
            serviceBase,bufferTape,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        · have hz : i.val=0 := by omega
          have he : i=⟨0,by omega⟩ := Fin.ext hz
          rw [he]
          change (childInspection M n request resume base rho sigma offset extent c label w).cells ⟨0,by omega⟩ p=_
          rw [(optimized_recursive_internal_inspection_root M n request resume base rho sigma offset extent c label w).1]
          simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
            EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.optimized_recursive_internal_extension_old_cells,
            TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,TrackedBankedSimulation.embed,
            TrackedSelectiveParentRestore.parentBase,EndParkResume.restorePlainBase,
            serviceBase,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · have he : i=stackTape M := by
        apply Fin.ext
        simp only [stackTape,FiniteContinuationStack.stackTape]
        omega
      subst i
      change (childInspection M n request resume base rho sigma offset extent c label w).cells (stackTape M) p=_
      rw [(optimized_recursive_internal_inspection_stack M n request resume base rho sigma offset extent c label w).1]
      simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
        EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.optimized_recursive_internal_extension_extra_cells,
        EndParkResume.restorePadBase,serviceBase,stackTape,FiniteContinuationStack.stackTape,
        FixedTapeExtension.extraTape,FixedTapeExtension.oldTape]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · have hs : i≠stackTape M := by
        intro h
        have hv := congrArg Fin.val h
        simp only [stackTape,FiniteContinuationStack.stackTape] at hv
        omega
      simp only [headFrame,Function.update_of_ne hs]
      by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : optimized_recursive_internal_physicalWork M j=i := by
          apply Fin.ext
          simp only [optimized_recursive_internal_physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he,optimized_recursive_internal_inspection_work_head]
        simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
          EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.optimized_recursive_internal_extension_old_heads,
          TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,
          optimized_recursive_internal_physicalWork,workTape,innerTape,j,FixedTapeExtension.oldTape,FixedTapeExtension.innerTape,
          TrackedBankReservation.newOffsets,Nat.add_assoc,hi,hw]
      · by_cases hb : i.val=1
        · have he : i=bufferTape M := Fin.ext hb
          subst i
          rw [(optimized_recursive_internal_inspection_buffer M n request resume base rho sigma offset extent c label w).2]
          simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
            EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.optimized_recursive_internal_extension_old_heads,
            TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,
            EndParkResume.restorePlainBase,serviceBase,bufferTape,
            FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        · have hz : i.val=0 := by omega
          have he : i=⟨0,by omega⟩ := Fin.ext hz
          rw [he]
          rw [(optimized_recursive_internal_inspection_root M n request resume base rho sigma offset extent c label w).2]
          simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
            EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.optimized_recursive_internal_extension_old_heads,
            TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,
            EndParkResume.restorePlainBase,serviceBase,
            FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · have he : i=stackTape M := by
        apply Fin.ext
        simp only [stackTape,FiniteContinuationStack.stackTape]
        omega
      subst i
      simp [headFrame,initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
        EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.optimized_recursive_internal_extension_extra_heads,
        EndParkResume.restorePadBase,serviceBase,stackTape,FiniteContinuationStack.stackTape,
        FixedTapeExtension.extraTape,FixedTapeExtension.oldTape]

end IntMul.EndParkRecursiveResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)

private theorem optimized_recursive_internal_final_work_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (finalFrame M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j)) p=
      if p < offset j then
        base.cells (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j)) p
      else if j=M.outTape then
        some (M.tapeOf (w.map M.bitSym) (p-offset j),decide (p-offset j ≤ w.length))
      else some (c.cells j (p-offset j),decide (p-offset j ≤ extent j)) := by
  change (outputFinal M n base rho sigma offset extent c label w).cells _ _=_
  simp only [outputFinal,optimized_recursive_internal_extension_old_cells]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedParentOutputBridge.finalFrame,
      if_pos (show workTape M M.outTape=TrackedParentOutputBridge.targetTape M by rfl),
      TrackedBankPreparation.bankTape,List.length_map,if_true]
    by_cases hp : p < offset M.outTape
    · simp only [if_pos hp]
      rw [optimized_recursive_internal_output_parent_cells,if_pos hp]
    · simp only [if_neg hp]
  · have ht : workTape M j≠TrackedParentOutputBridge.targetTape M := by
      intro h
      exact hj (optimized_recursive_internal_work_injective M h)
    simp only [TrackedParentOutputBridge.finalFrame,if_neg ht,if_neg hj]
    change (TrackedParentOutputBridge.initialFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w).cells (workTape M j) p=_
    rw [(optimized_recursive_internal_output_initial_ready M n base rho sigma offset extent c label w).1,
      optimized_recursive_internal_output_parent_cells]

private theorem optimized_recursive_internal_final_low (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) (i : Fin (M.k+2)) (hi : i.val < 2) :
    (finalFrame M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i)=
      (restorePlainBase M n base sigma w).cells i ∧
    (finalFrame M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) i)=
      (restorePlainBase M n base sigma w).head i := by
  have ht : i≠TrackedParentOutputBridge.targetTape M := by
    intro h
    have hv := congrArg Fin.val h
    simp only [TrackedParentOutputBridge.targetTape,workTape] at hv
    omega
  constructor
  · change (outputFinal M n base rho sigma offset extent c label w).cells _=_
    simp only [outputFinal,optimized_recursive_internal_extension_old_cells,TrackedParentOutputBridge.finalFrame,if_neg ht]
    change (TrackedParentOutputBridge.initialFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w).cells i=_
    rw [(optimized_recursive_internal_output_initial_ready M n base rho sigma offset extent c label w).1]
    exact (optimized_recursive_internal_output_low M n base rho sigma offset extent c label w i hi).1
  · change (outputFinal M n base rho sigma offset extent c label w).head _=_
    simp only [outputFinal,optimized_recursive_internal_extension_old_heads,TrackedParentOutputBridge.finalFrame,if_neg ht]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp [restorePlainBase,TrackedParentOutputBridge.bufferTape]
    · rw [if_neg hb]
      have hh := congrFun (optimized_recursive_internal_output_initial_ready M n base rho sigma offset extent c label w).2 i
      have hl := (optimized_recursive_internal_output_low M n base rho sigma offset extent c label w i hi).2
      simpa only [TrackedParentOutputBridge.initialFrame,TrackedParentOutputBridge.beforeFrame,
        if_neg hb,Nat.sub_zero] using hh.trans hl


end IntMul.EndParkResume



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursiveresumefinalframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_resumed_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    finalFrame M n request resume (serviceBase M n request resume base)
      rho sigma offset extent c label w =
    resumedFrame M n request resume base rho sigma offset extent c label w := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursiveresumefinalframes_cfg_ext
  · rfl
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : optimized_recursive_internal_physicalWork M j=i := by
          apply Fin.ext
          simp only [optimized_recursive_internal_physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he]
        change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
          rho sigma offset extent c label w).cells
            (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
          (FixedTapeExtension.embed (TrackedBankedSimulation.machine M) _
            (TrackedBankedSimulation.embed M _ _ _ _)).cells
            (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j))
        rw [optimized_recursive_internal_extension_old_cells]
        funext p
        rw [EndParkResume.optimized_recursive_internal_final_work_cells]
        simp only [TrackedBankedSimulation.embed,workTape]
        rw [dif_pos (by change 2 ≤ j.val+2; omega)]
        have hj : innerTape M ⟨j.val+2,by have := j.isLt; omega⟩ (by change 2 ≤ j.val+2; omega)=j := by
          apply Fin.ext
          simp [innerTape]
        simp only [hj,parentBase,if_neg (by omega : j.val+2≠1),serviceBase,
          parentAfterChildExtent,resumedParent]
        by_cases hp : p < offset j <;> by_cases ho : j=M.outTape <;>
          simp only [hp,ho,if_true,if_false]
        all_goals rfl
      · by_cases hb : i.val=1
        · have he : i=bufferTape M := Fin.ext hb
          subst i
          change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
            rho sigma offset extent c label w).cells
              (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
          rw [(EndParkResume.optimized_recursive_internal_final_low M n (serviceBase M n request resume base)
            rho sigma offset extent c label w ⟨1,by change 1 < M.k+2; omega⟩ (by simp)).1]
          simp [EndParkResume.restorePlainBase,serviceBase,resumedFrame,bodyFrame,liftBody,
            FixedTapeExtension.embed,TrackedBankedSimulation.embed,parentBase,bufferTape,
            FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        · have hz : i.val=0 := by omega
          have he : i=⟨0,by omega⟩ := Fin.ext hz
          rw [he]
          change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
            rho sigma offset extent c label w).cells
              (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) ⟨0,by change 0 < M.k+2; omega⟩)=_
          rw [(EndParkResume.optimized_recursive_internal_final_low M n (serviceBase M n request resume base)
            rho sigma offset extent c label w ⟨0,by change 0 < M.k+2; omega⟩ (by simp)).1]
          simp [EndParkResume.restorePlainBase,serviceBase,resumedFrame,bodyFrame,liftBody,
            FixedTapeExtension.embed,TrackedBankedSimulation.embed,parentBase,
            FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · have he : i=stackTape M := by
        apply Fin.ext
        simp only [stackTape,FiniteContinuationStack.stackTape]
        omega
      subst i
      change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
        rho sigma offset extent c label w).cells (stackTape M)=_
      rw [(EndParkResume.optimized_recursive_internal_final_stack M n (serviceBase M n request resume base)
        rho sigma offset extent c label w).1]
      simp [resumedFrame,bodyFrame,liftBody,FixedTapeExtension.embed,stackBase,serviceBase,
        stackTape,FiniteContinuationStack.stackTape]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : optimized_recursive_internal_physicalWork M j=i := by
          apply Fin.ext
          simp only [optimized_recursive_internal_physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he]
        change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
          rho sigma offset extent c label w).head
            (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
          (FixedTapeExtension.embed (TrackedBankedSimulation.machine M) _
            (TrackedBankedSimulation.embed M _ _ _ _)).head
            (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j))
        rw [EndParkResume.optimized_recursive_internal_final_work_heads,optimized_recursive_internal_extension_old_heads,optimized_recursive_internal_embed_work_head]
        rfl
      · by_cases hb : i.val=1
        · have he : i=bufferTape M := Fin.ext hb
          subst i
          change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
            rho sigma offset extent c label w).head
              (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
          rw [(EndParkResume.optimized_recursive_internal_final_low M n (serviceBase M n request resume base)
            rho sigma offset extent c label w ⟨1,by change 1 < M.k+2; omega⟩ (by simp)).2]
          simp [EndParkResume.restorePlainBase,serviceBase,resumedFrame,bodyFrame,liftBody,
            FixedTapeExtension.embed,TrackedBankedSimulation.embed,parentBase,bufferTape,
            FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        · have hz : i.val=0 := by omega
          have he : i=⟨0,by omega⟩ := Fin.ext hz
          rw [he]
          change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
            rho sigma offset extent c label w).head
              (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) ⟨0,by change 0 < M.k+2; omega⟩)=_
          rw [(EndParkResume.optimized_recursive_internal_final_low M n (serviceBase M n request resume base)
            rho sigma offset extent c label w ⟨0,by change 0 < M.k+2; omega⟩ (by simp)).2]
          simp [EndParkResume.restorePlainBase,serviceBase,resumedFrame,bodyFrame,liftBody,
            FixedTapeExtension.embed,TrackedBankedSimulation.embed,parentBase,
            FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · have he : i=stackTape M := by
        apply Fin.ext
        simp only [stackTape,FiniteContinuationStack.stackTape]
        omega
      subst i
      change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
        rho sigma offset extent c label w).head (stackTape M)=_
      rw [(EndParkResume.optimized_recursive_internal_final_stack M n (serviceBase M n request resume base)
        rho sigma offset extent c label w).2]
      simp [resumedFrame,bodyFrame,liftBody,FixedTapeExtension.embed,stackBase,serviceBase,
        stackTape,FiniteContinuationStack.stackTape]

end IntMul.EndParkRecursiveResume



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall

private theorem optimized_recursive_internal_resume_parent_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+13 ∧
      (machine M n request resume).step^[t]
        (childInspection M n request resume base rho sigma offset extent c label w)=
        resumedFrame M n request resume base rho sigma offset extent c label w := by
  have hinspect : (machine M n request resume).step
      (childInspection M n request resume base rho sigma offset extent c label w)=
      initialFrame M n request resume (serviceBase M n request resume base)
        rho sigma offset extent c label w := by
    rw [optimized_recursive_internal_inspect_parent_dispatch M n request resume _ rfl
      (optimized_recursive_internal_inspection_nonroot M n request resume base rho sigma offset extent c label w)]
    rw [(optimized_recursive_internal_inspection_stack M n request resume base rho sigma offset extent c label w).2]
    exact optimized_recursive_internal_inspection_resume_ready M n request resume base rho sigma offset extent c label w tail
  obtain ⟨t,ht,hrun,_⟩ := EndParkRecursiveScheduler.resume_correct M n request resume
    (serviceBase M n request resume base) rho sigma offset extent c label w unique (tail M.outTape)
  refine ⟨t+1,by omega,?_⟩
  rw [Function.iterate_succ_apply,hinspect,hrun,optimized_recursive_internal_resumed_ready]

end IntMul.EndParkRecursiveResume



namespace IntMul.EndParkRecursiveReturn

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivereturnframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_recursive_internal_returnParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) : (TrackedReturnReplacement.machine M).Cfg where
  state := (TrackedReturnReplacement.machine M).qStart
  cells := fun i => base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)
  head := fun i => base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)

private noncomputable def optimized_recursive_internal_returnPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (returnMachine M).Cfg where
  state := (returnMachine M).qStart
  cells := (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v).cells
  head := (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v).head

private noncomputable def optimized_recursive_internal_returnStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (returnMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedReturnReplacement.machine M)
    (optimized_recursive_internal_returnPadBase M n request resume base rho sigma offset extent c v)
    (TrackedReturnReplacement.initialFrame M (optimized_recursive_internal_returnParent M n request resume base) sigma offset extent c v)

private noncomputable def optimized_recursive_internal_returnFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (returnMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedReturnReplacement.machine M)
    (optimized_recursive_internal_returnPadBase M n request resume base rho sigma offset extent c v)
    (TrackedReturnReplacement.finalFrame M (optimized_recursive_internal_returnParent M n request resume base) sigma offset extent c v w)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivereturnframes_word_before_heads (M : MultitapeTM) (base : (TrackedWordInputBridge.machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    (TrackedWordInputBridge.beforeFrame M base sigma offset extent c v 0).head=
      TrackedWordInputBridge.initialHeads M base sigma offset extent c v := by
  funext i
  simp only [TrackedWordInputBridge.beforeFrame,Nat.sub_zero]
  by_cases hb : i=TrackedWordInputBridge.bufferTape M
  · subst i
    simp only [if_true,TrackedWordInputBridge.initialHeads,TrackedBankedSimulation.embed,
      TrackedWordInputBridge.bufferTape,dif_neg (by omega : ¬2 ≤ (1 : ℕ)),
      TrackedWordInputBridge.parentBase,if_true]
    omega
  · simp only [if_neg hb]
    by_cases hp : i=TrackedWordInputBridge.packetTape M
    · subst i
      simp only [if_true]
      exact (optimized_recursive_internal_embed_work_head M (TrackedWordInputBridge.parentBase M base sigma v)
        offset extent c M.outTape).symm
    · simp only [if_neg hp]

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivereturnframes_word_parent_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ) (v : List Bool) :
    TrackedWordInputBridge.parentBase M
      (TrackedReturnReplacement.inputBase M (optimized_recursive_internal_returnParent M n request resume base)) sigma v=
      parentBase M n request resume base sigma v := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursivereturnframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedWordInputBridge.parentBase,TrackedReturnReplacement.inputBase,optimized_recursive_internal_returnParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedWordInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedWordInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]
  · funext i
    simp only [TrackedWordInputBridge.parentBase,TrackedReturnReplacement.inputBase,optimized_recursive_internal_returnParent,parentBase]
    by_cases hb : i.val=1
    · have he : i=TrackedWordInputBridge.bufferTape M := Fin.ext hb
      simp only [if_pos he,if_pos hb]
    · have he : i≠TrackedWordInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
      simp only [if_neg he,if_neg hb]

private theorem optimized_recursive_internal_body_return_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    relabel M n request resume (.returning (returnMachine M).qStart)
      (bodyFrame M n request resume base rho sigma offset extent c v)=
    liftReturn M n request resume (optimized_recursive_internal_returnStart M n request resume base rho sigma offset extent c v) := by
  have hc : (TrackedReturnReplacement.initialFrame M (optimized_recursive_internal_returnParent M n request resume base)
      sigma offset extent c v).cells=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).cells := by
    simp only [TrackedReturnReplacement.initialFrame,TrackedReturnReplacement.liftInput,
      TrackedWordInputBridge.initialFrame,TrackedWordInputBridge.beforeFrame,
      TrackedWordInputBridge.initialCells,optimized_recursive_internal_solutions_intmulendparkrecursivereturnframes_word_parent_ready]
  have hh : (TrackedReturnReplacement.initialFrame M (optimized_recursive_internal_returnParent M n request resume base)
      sigma offset extent c v).head=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c).head := by
    simp only [TrackedReturnReplacement.initialFrame,TrackedReturnReplacement.liftInput,
      TrackedWordInputBridge.initialFrame,optimized_recursive_internal_solutions_intmulendparkrecursivereturnframes_word_before_heads,
      TrackedWordInputBridge.initialHeads,optimized_recursive_internal_solutions_intmulendparkrecursivereturnframes_word_parent_ready]
  apply optimized_recursive_internal_solutions_intmulendparkrecursivereturnframes_cfg_ext
  · rfl
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftReturn,optimized_recursive_internal_returnStart,optimized_recursive_internal_returnPadBase,optimized_recursive_internal_bodyView,
      FixedTapeExtension.embed,hc]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]
  · funext i
    simp only [relabel,bodyFrame,liftBody,liftReturn,optimized_recursive_internal_returnStart,optimized_recursive_internal_returnPadBase,optimized_recursive_internal_bodyView,
      FixedTapeExtension.embed,hh]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,FixedTapeExtension.innerTape]
    · simp only [dif_neg hi]

end IntMul.EndParkRecursiveReturn



namespace IntMul.EndParkRecursiveReturn

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivereturncleanupframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_recursive_internal_cleanupParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (TrackedBankCleanup.machine M).Cfg where
  state := .rewind
  cells := (TrackedReturnReplacement.finalFrame M (optimized_recursive_internal_returnParent M n request resume base)
    sigma offset extent c v w).cells
  head := (TrackedReturnReplacement.finalFrame M (optimized_recursive_internal_returnParent M n request resume base)
    sigma offset extent c v w).head

private noncomputable def optimized_recursive_internal_cleanupPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (cleanupMachine M).Cfg where
  state := .rewind
  cells := (optimized_recursive_internal_returnFinal M n request resume base rho sigma offset extent c v w).cells
  head := (optimized_recursive_internal_returnFinal M n request resume base rho sigma offset extent c v w).head

private noncomputable def optimized_recursive_internal_cleanupStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (cleanupMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankCleanup.machine M)
    (optimized_recursive_internal_cleanupPadBase M n request resume base rho sigma offset extent c v w)
    (TrackedBankCleanup.rewindFrame M (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w)
      offset extent c (returnedHeads M c))

private noncomputable def optimized_recursive_internal_cleanupFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) : (cleanupMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankCleanup.machine M)
    (optimized_recursive_internal_cleanupPadBase M n request resume base rho sigma offset extent c v w)
    (TrackedBankCleanup.finalFrame M (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w) offset)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivereturncleanupframes_work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedWordInputBridge.bufferTape M := by
  intro h
  have hv := congrArg Fin.val h
  simp only [workTape,TrackedWordInputBridge.bufferTape] at hv
  omega

private theorem optimized_recursive_internal_return_work_canonical (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (j : Fin M.k) (p : ℕ) :
    (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [optimized_recursive_internal_cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
    TrackedReturnReplacement.bufferTape,if_neg (optimized_recursive_internal_solutions_intmulendparkrecursivereturncleanupframes_work_ne_buffer M j),TrackedWordInputBridge.finalFrame,
    TrackedReturnReplacement.inputBase,TrackedWordInputBridge.initialCells]
  exact optimized_recursive_internal_embed_work M _ offset extent c j p

private theorem optimized_recursive_internal_return_work_heads (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (j : Fin M.k) :
    (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w).head (workTape M j)=
      offset j+returnedHeads M c j := by
  simp only [optimized_recursive_internal_cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
    TrackedReturnReplacement.bufferTape,if_neg (optimized_recursive_internal_solutions_intmulendparkrecursivereturncleanupframes_work_ne_buffer M j),TrackedWordInputBridge.finalFrame,
    TrackedReturnReplacement.inputBase]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedWordInputBridge.packetTape,if_true,returnedHeads,Nat.add_zero]
  · have hp : workTape M j≠TrackedWordInputBridge.packetTape M := by
      intro h; exact hj (optimized_recursive_internal_work_injective M h)
    simp only [if_neg hp,returnedHeads,if_neg hj,TrackedWordInputBridge.initialHeads]
    exact optimized_recursive_internal_embed_work_head M _ offset extent c j

private theorem optimized_recursive_internal_return_cleanup_old_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    TrackedBankCleanup.rewindFrame M (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w)
      offset extent c (returnedHeads M c)=
      optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursivereturncleanupframes_cfg_ext
  · rfl
  · apply optimized_recursive_internal_embed_cells_ready
    intro j p
    exact optimized_recursive_internal_return_work_canonical M n request resume base sigma offset extent c v w j p
  · funext i
    simp only [TrackedBankCleanup.rewindFrame]
    by_cases hi : 2 ≤ i.val
    · simp only [dif_pos hi]
      have h := optimized_recursive_internal_return_work_heads M n request resume base sigma offset extent c v w (innerTape M i hi)
      rw [optimized_recursive_internal_work_inner M i hi] at h
      exact h.symm
    · simp only [dif_neg hi]

private theorem optimized_recursive_internal_return_cleanup_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    relabel M n request resume (.cleanup .rewind)
      (liftReturn M n request resume (optimized_recursive_internal_returnFinal M n request resume base rho sigma offset extent c v w))=
      liftCleanup M n request resume (optimized_recursive_internal_cleanupStart M n request resume base rho sigma offset extent c v w) := by
  rw [optimized_recursive_internal_cleanupStart,optimized_recursive_internal_return_cleanup_old_ready]
  have hp : FixedTapeExtension.embed (TrackedBankCleanup.machine M)
      (optimized_recursive_internal_cleanupPadBase M n request resume base rho sigma offset extent c v w)
      (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w)=
      optimized_recursive_internal_cleanupPadBase M n request resume base rho sigma offset extent c v w := by
    apply optimized_recursive_internal_solutions_intmulendparkrecursivereturncleanupframes_cfg_ext
    · rfl
    · apply optimized_recursive_internal_extension_cells_ready
      intro j
      change (FixedTapeExtension.embed (TrackedReturnReplacement.machine M) _ _).cells
        (FixedTapeExtension.oldTape (TrackedReturnReplacement.machine M) j)=_
      rw [optimized_recursive_internal_extension_old_cells]
      rfl
    · apply optimized_recursive_internal_extension_heads_ready
      intro j
      change (FixedTapeExtension.embed (TrackedReturnReplacement.machine M) _ _).head
        (FixedTapeExtension.oldTape (TrackedReturnReplacement.machine M) j)=_
      rw [optimized_recursive_internal_extension_old_heads]
      rfl
  rw [hp]
  rfl

end IntMul.EndParkRecursiveReturn



namespace IntMul.EndParkRecursiveReturn

open IntMul.EndParkRecursiveScheduler
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivereturninspection_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_recursive_internal_solutions_intmulendparkrecursivereturninspection_work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedWordInputBridge.bufferTape M := by
  intro h
  have hv := congrArg Fin.val h
  simp only [workTape,TrackedWordInputBridge.bufferTape] at hv
  omega

private theorem optimized_recursive_internal_return_work_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (j : Fin M.k) (p : ℕ)
    (hp : p < offset j) :
    (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w).cells (workTape M j) p=
      base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j)) p := by
  simp only [optimized_recursive_internal_cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
    TrackedReturnReplacement.bufferTape,if_neg (optimized_recursive_internal_solutions_intmulendparkrecursivereturninspection_work_ne_buffer M j),TrackedWordInputBridge.finalFrame,
    TrackedReturnReplacement.inputBase,TrackedWordInputBridge.initialCells]
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2 ≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp only [innerTape]
    omega
  rw [hi,if_pos hp]
  change (TrackedWordInputBridge.parentBase M
    (TrackedReturnReplacement.inputBase M (optimized_recursive_internal_returnParent M n request resume base)) sigma v).cells (workTape M j) p=_
  simp only [TrackedWordInputBridge.parentBase,if_neg (optimized_recursive_internal_solutions_intmulendparkrecursivereturninspection_work_ne_buffer M j),
    TrackedReturnReplacement.inputBase,optimized_recursive_internal_returnParent]
  rfl

private theorem optimized_recursive_internal_return_low (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (i : Fin (M.k+2))
    (hi : i.val < 2) :
    (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w).cells i=
      (if i.val=1 then TrackedOutputReturn.bufferTape M
        (base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)) sigma w
        else base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)) ∧
    (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w).head i=
      (if i.val=1 then sigma+w.length+1
        else base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)) := by
  by_cases hb : i.val=1
  · have he : i=TrackedWordInputBridge.bufferTape M := Fin.ext hb
    constructor
    · simp only [optimized_recursive_internal_cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
        TrackedReturnReplacement.bufferTape,if_pos he,if_pos hb,optimized_recursive_internal_returnParent]
    · simp only [optimized_recursive_internal_cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
        TrackedReturnReplacement.bufferTape,if_pos he,if_pos hb]
  · have he : i≠TrackedWordInputBridge.bufferTape M := by intro h; exact hb (congrArg Fin.val h)
    have hp : i≠TrackedWordInputBridge.packetTape M := by
      intro h; have hv := congrArg Fin.val h
      simp only [TrackedWordInputBridge.packetTape,workTape,MultitapeTM.outTape] at hv
      omega
    constructor
    · simp only [optimized_recursive_internal_cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
        TrackedReturnReplacement.bufferTape,if_neg he,TrackedWordInputBridge.finalFrame,
        TrackedReturnReplacement.inputBase,TrackedWordInputBridge.initialCells,
        TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),
        TrackedWordInputBridge.parentBase,if_neg he,optimized_recursive_internal_returnParent,if_neg hb]
    · simp only [optimized_recursive_internal_cleanupParent,TrackedReturnReplacement.finalFrame,TrackedReturnReplacement.seekFrame,
        TrackedReturnReplacement.bufferTape,if_neg he,TrackedWordInputBridge.finalFrame,
        TrackedReturnReplacement.inputBase,if_neg hp,TrackedWordInputBridge.initialHeads,
        TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),
        TrackedWordInputBridge.parentBase,if_neg he,optimized_recursive_internal_returnParent,if_neg hb]

private theorem optimized_recursive_internal_cleanup_stack (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    (optimized_recursive_internal_cleanupFinal M n request resume base rho sigma offset extent c v w).head (stackTape M)=rho ∧
    (optimized_recursive_internal_cleanupFinal M n request resume base rho sigma offset extent c v w).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho := by
  have hi : ¬(stackTape M).val < M.k+2 := by change ¬M.k+2 < M.k+2; omega
  constructor
  · simp only [optimized_recursive_internal_cleanupFinal,FixedTapeExtension.embed,dif_neg hi,optimized_recursive_internal_cleanupPadBase,optimized_recursive_internal_returnFinal,
      optimized_recursive_internal_returnPadBase,optimized_recursive_internal_bodyView,stackBase,if_true]
  · simp only [optimized_recursive_internal_cleanupFinal,FixedTapeExtension.embed,dif_neg hi,optimized_recursive_internal_cleanupPadBase,optimized_recursive_internal_returnFinal,
      optimized_recursive_internal_returnPadBase,optimized_recursive_internal_bodyView,stackBase,if_true]

private theorem optimized_recursive_internal_cleanup_inspection_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) :
    headFrame M n request resume .inspectStack
      (liftCleanup M n request resume (optimized_recursive_internal_cleanupFinal M n request resume base rho sigma offset extent c v w))
      (stackTape M) (rho-1)=inspectionFrame M n request resume base rho sigma offset w := by
  apply optimized_recursive_internal_solutions_intmulendparkrecursivereturninspection_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    simp only [headFrame,liftCleanup,optimized_recursive_internal_cleanupFinal,FixedTapeExtension.embed,inspectionFrame]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi,TrackedBankCleanup.finalFrame,FixedTapeExtension.innerTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
        let j := innerTape M ⟨i.val,hi⟩ hw
        change (if p < offset j then
          (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w).cells ⟨i.val,hi⟩ p
          else some (M.blank,false))=(if p < offset j then base.cells i p else some (M.blank,false))
        by_cases hp : p < offset j
        · simp only [TrackedBankCleanup.freshTape,if_pos hp]
          have h := optimized_recursive_internal_return_work_prefix M n request resume base sigma offset extent c v w j p hp
          have he : workTape M j=⟨i.val,hi⟩ := optimized_recursive_internal_work_inner M _ hw
          rw [he] at h
          exact h
        · simp only [TrackedBankCleanup.freshTape,if_neg hp]
      · simp only [dif_neg hw]
        have h := (optimized_recursive_internal_return_low M n request resume base sigma offset extent c v w ⟨i.val,hi⟩ (by change i.val < 2; omega)).1
        exact congrFun h p
    · simp only [dif_neg hi]
      have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      have h := (optimized_recursive_internal_cleanup_stack M n request resume base rho sigma offset extent c v w).2
      simpa only [optimized_recursive_internal_cleanupFinal,FixedTapeExtension.embed,dif_neg hi] using congrFun h p
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    simp only [headFrame,liftCleanup,inspectionFrame]
    by_cases hi : i.val < M.k+2
    · have hs : i≠stackTape M := by
        intro h; have hv := congrArg Fin.val h
        simp only [stackTape,FiniteContinuationStack.stackTape] at hv
        omega
      rw [Function.update_of_ne hs]
      simp only [optimized_recursive_internal_cleanupFinal,FixedTapeExtension.embed,dif_pos hi,TrackedBankCleanup.finalFrame,
        FixedTapeExtension.innerTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
      · simp only [dif_neg hw]
        exact (optimized_recursive_internal_return_low M n request resume base sigma offset extent c v w ⟨i.val,hi⟩ (by change i.val < 2; omega)).2
    · simp only [dif_neg hi]
      have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      simp only [Function.update_self]

end IntMul.EndParkRecursiveReturn



namespace IntMul.EndParkRecursiveReturn

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankCleanup (span)

/-- The actual flat scheduler returns from one finished body, replaces an
arbitrary older result, clears every current work bank and physically probes
the continuation stack. All three dispatches and every head move are charged. -/
private theorem optimized_recursive_internal_return_cleanup_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (v w : List Bool) (halt : c.state=M.qHalt)
    (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym))
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+
        span M (returnedHeads M c)+2*span M extent+12 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w := by
  have hbody : (machine M n request resume).step
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftReturn M n request resume (optimized_recursive_internal_returnStart M n request resume base rho sigma offset extent c v) := by
    change (machine M n request resume).step
      (liftBody M n request resume (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v))=_
    rw [optimized_recursive_internal_body_dispatch M n request resume (optimized_recursive_internal_bodyView M n request resume base rho sigma offset extent c v) halt]
    exact optimized_recursive_internal_body_return_ready M n request resume base rho sigma offset extent c v
  obtain ⟨r,hrclock,hrrun,hrhalt,hrbuffer,hrbufferhead,hrbanks,hrheads⟩ :=
    TrackedReturnReplacement.return_correct M (optimized_recursive_internal_returnParent M n request resume base)
      sigma offset extent c v w out
  have hr : (returnMachine M).step^[r] (optimized_recursive_internal_returnStart M n request resume base rho sigma offset extent c v)=
      optimized_recursive_internal_returnFinal M n request resume base rho sigma offset extent c v w := by
    have h := (FixedTapeExtension.simulate_run (TrackedReturnReplacement.machine M)
      (optimized_recursive_internal_returnPadBase M n request resume base rho sigma offset extent c v)
      (TrackedReturnReplacement.initialFrame M (optimized_recursive_internal_returnParent M n request resume base) sigma offset extent c v) r).1
    rw [hrrun] at h
    exact h
  have hre : ((returnMachine M).step^[r]
      (optimized_recursive_internal_returnStart M n request resume base rho sigma offset extent c v)).state=(returnMachine M).qHalt := by
    rw [hr]
    exact hrhalt
  obtain ⟨s,hsclock,hsrun⟩ := optimized_recursive_internal_return_to_halt M n request resume
    (optimized_recursive_internal_returnStart M n request resume base rho sigma offset extent c v) r hre
  rw [hr] at hsrun
  have hreturn : (machine M n request resume).step^[s+1]
      (liftReturn M n request resume (optimized_recursive_internal_returnStart M n request resume base rho sigma offset extent c v))=
      liftCleanup M n request resume (optimized_recursive_internal_cleanupStart M n request resume base rho sigma offset extent c v w) := by
    rw [Function.iterate_succ_apply',hsrun,optimized_recursive_internal_return_dispatch M n request resume _ hrhalt]
    exact optimized_recursive_internal_return_cleanup_ready M n request resume base rho sigma offset extent c v w
  let C := span M (returnedHeads M c)+2*span M extent+3
  have hclean : (cleanupMachine M).step^[C] (optimized_recursive_internal_cleanupStart M n request resume base rho sigma offset extent c v w)=
      optimized_recursive_internal_cleanupFinal M n request resume base rho sigma offset extent c v w := by
    have h := (FixedTapeExtension.simulate_run (TrackedBankCleanup.machine M)
      (optimized_recursive_internal_cleanupPadBase M n request resume base rho sigma offset extent c v w)
      (TrackedBankCleanup.rewindFrame M (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w)
        offset extent c (returnedHeads M c)) C).1
    rw [(TrackedBankCleanup.cleanup_correct M (optimized_recursive_internal_cleanupParent M n request resume base sigma offset extent c v w)
      offset extent positive c (returnedHeads M c) unique tail).1] at h
    exact h
  have hce : ((cleanupMachine M).step^[C]
      (optimized_recursive_internal_cleanupStart M n request resume base rho sigma offset extent c v w)).state=(cleanupMachine M).qHalt := by
    rw [hclean]
    rfl
  obtain ⟨q,hqclock,hqrun⟩ := optimized_recursive_internal_cleanup_to_halt M n request resume
    (optimized_recursive_internal_cleanupStart M n request resume base rho sigma offset extent c v w) C hce
  rw [hclean] at hqrun
  have hstack := optimized_recursive_internal_cleanup_stack M n request resume base rho sigma offset extent c v w
  have hpresent : (optimized_recursive_internal_cleanupFinal M n request resume base rho sigma offset extent c v w).cells (stackTape M)
      ((optimized_recursive_internal_cleanupFinal M n request resume base rho sigma offset extent c v w).head (stackTape M))≠none := by
    rw [hstack.1,hstack.2]
    simp [FiniteContinuationStack.freshTape]
  have hcleanup : (machine M n request resume).step^[q+1]
      (liftCleanup M n request resume (optimized_recursive_internal_cleanupStart M n request resume base rho sigma offset extent c v w))=
      inspectionFrame M n request resume base rho sigma offset w := by
    rw [Function.iterate_succ_apply',hqrun,optimized_recursive_internal_cleanup_dispatch M n request resume _ rfl hpresent,hstack.1]
    exact optimized_recursive_internal_cleanup_inspection_ready M n request resume base rho sigma offset extent c v w
  have hstaged : (machine M n request resume).step^[(s+1)+1]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      liftCleanup M n request resume (optimized_recursive_internal_cleanupStart M n request resume base rho sigma offset extent c v w) := by
    rw [Function.iterate_succ_apply,hbody,hreturn]
  refine ⟨(q+1)+((s+1)+1),by dsimp only [C] at *; omega,?_⟩
  rw [Function.iterate_add_apply,hstaged,hcleanup]

end IntMul.EndParkRecursiveReturn



namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveReturn
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankedSimulation (nextExtent)
open IntMul.TrackedBankPreparation (initialExtent)

/-- A finite recursive derivation is executed by the actual single scheduler.
The conclusion is exact equality of the WHOLE physical returned frame. -/
private theorem evaluates_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (budget : ℕ)
    (evaluation : Evaluates M n request resume extent c v w budget) :
    ∀ (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
      (offset : Fin M.k → ℕ), (∀ j, 1 ≤ offset j) →
      (∀ j p, c.cells j p=M.startSym ↔ p=0) →
      (∀ j p, extent j < p → c.cells j p=M.blank) →
      (∀ j, c.head j≤ extent j+1) →
      ∃ t, t≤ budget ∧ (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w := by
  induction evaluation with
  | halt extent c v w halt out =>
    intro base rho sigma offset positive unique tail near
    exact optimized_recursive_internal_return_cleanup_correct M n request resume base rho sigma offset extent positive c v w halt out unique tail
  | step extent c v w budget live ordinary rest ih =>
    intro base rho sigma offset positive unique tail near
    obtain ⟨t,ht,hrun⟩ := ih base rho sigma offset positive
      (optimized_recursive_internal_step_unique M c unique) (optimized_recursive_internal_step_tail M extent c tail) (optimized_recursive_internal_step_near M extent c near)
    refine ⟨t+1,by omega,?_⟩
    rw [Function.iterate_succ_apply,
      optimized_recursive_internal_ordinary_body_step M n request resume base rho sigma offset extent positive c v
        (fun j => (unique j 0).2 rfl) near live ordinary,hrun]
  | call extent c v x y childWord w label childBudget parentBudget live request_label packet child parent ihchild ihparent =>
    intro base rho sigma offset positive unique tail near
    obtain ⟨d,hd,hdown⟩ := optimized_recursive_internal_call_entry_correct M n request resume label base rho sigma offset extent c v x y
      live request_label packet near tail
    have hpositive : ∀ j, 1≤ TrackedBankReservation.newOffsets M offset extent j := by
      intro j
      unfold TrackedBankReservation.newOffsets
      omega
    obtain ⟨q,hq,hchild⟩ := ihchild
      (childBase M n request resume base rho sigma offset extent c label) (rho+n+1) sigma
      (TrackedBankReservation.newOffsets M offset extent) hpositive
      (EndParkRecursiveSchedulerNativeInvariants.optimized_recursive_internal_initial_unique_markers M x y)
      (EndParkRecursiveSchedulerNativeInvariants.optimized_recursive_internal_initial_blank_tails M x y)
      (EndParkRecursiveSchedulerNativeInvariants.optimized_recursive_internal_initial_heads_near M x y)
    change (machine M n request resume).step^[q]
      (childFrame M n request resume base rho sigma offset extent c label x y)=
      childInspection M n request resume base rho sigma offset extent c label childWord at hchild
    obtain ⟨r,hr,hresume⟩ := optimized_recursive_internal_resume_parent_correct M n request resume base rho sigma offset extent c label childWord unique tail
    obtain ⟨p,hp,hparent⟩ := ihparent base rho sigma offset positive
      (optimized_recursive_internal_resumed_unique M n resume extent c label childWord unique)
      (optimized_recursive_internal_resumed_tail M n resume extent c label childWord tail)
      (optimized_recursive_internal_resumed_near M n resume extent c label childWord)
    change (machine M n request resume).step^[p]
      (resumedFrame M n request resume base rho sigma offset extent c label childWord)=
      inspectionFrame M n request resume base rho sigma offset w at hparent
    refine ⟨p+(r+(q+d)),by dsimp only [callCost,resumeCost] at *; omega,?_⟩
    rw [Function.iterate_add_apply (machine M n request resume).step p (r+(q+d)),
      Function.iterate_add_apply (machine M n request resume).step r (q+d),
      Function.iterate_add_apply (machine M n request resume).step q d,
      hdown,hchild,hresume,hparent]

end IntMul.EndParkRecursiveEvaluation


open IntMul IntMul.EndParkRecursiveEvaluation IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveCall IntMul.EndParkRecursiveReturn IntMul.EndParkRecursiveResume

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (budget : ℕ)
    (evaluation : Evaluates M n request resume extent c v w budget) :
    ∀ (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
      (offset : Fin M.k → ℕ), (∀ j, 1 ≤ offset j) →
      (∀ j p, c.cells j p=M.startSym ↔ p=0) →
      (∀ j p, extent j < p → c.cells j p=M.blank) →
      (∀ j, c.head j≤ extent j+1) →
      ∃ t, t≤ budget ∧ (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        inspectionFrame M n request resume base rho sigma offset w :=
  IntMul.EndParkRecursiveEvaluation.evaluates_correct M n request resume extent c v w budget evaluation

#print axioms solution
