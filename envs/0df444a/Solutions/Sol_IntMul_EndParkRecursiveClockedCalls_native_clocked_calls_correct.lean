-- Prove2me | solution 1 for IntMul.EndParkRecursiveClockedCalls.native_clocked_calls_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T08:09:10.165462+00:00
-- url     : https://prove2.me/submissions/76580a72-dd54-4aaf-858d-137ee25a4777

import Definitions.Def_IntMul_EndParkRecursiveClockedCalls
import Theorems.Thm_IntMul_EndParkRecursiveReturn_return_cleanup_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveCall_call_entry_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveResume_resume_parent_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_to_interior_clock
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem owned_intmultrackedbankedspaceinvariants_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmultrackedbankedspaceinvariants_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply owned_intmultrackedbankedspaceinvariants_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem owned_intmultrackedbankedspaceinvariants_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [owned_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact owned_intmultrackedbankedspaceinvariants_blank_tail_step M _ _ ih

private theorem owned_intmultrackedbankedspaceinvariants_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
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
private theorem unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact owned_intmultrackedbankedspaceinvariants_unique_marker_step M _ ih

private theorem owned_intmultrackedbankedspaceinvariants_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem owned_intmultrackedbankedspaceinvariants_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [owned_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := owned_intmultrackedbankedspaceinvariants_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact owned_intmultrackedbankedspaceinvariants_near_step M _ _ ih


end IntMul.TrackedBankedSpace




namespace IntMul.EndParkRecursiveSchedulerNativeInvariants

open IntMul.TrackedBankedSimulation (extents nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem owned_intmulendparkrecursiveschedulernativeinvariants_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem owned_intmulendparkrecursiveschedulernativeinvariants_word_payload_ne_start (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (inputWord M x y).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (inputWord M x y).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hl := owned_intmulendparkrecursiveschedulernativeinvariants_word_letter M x y (inputWord M x y)[p] (List.getElem_mem hp)
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
        have h := owned_intmulendparkrecursiveschedulernativeinvariants_word_payload_ne_start M x y p
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

open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem owned_intmulendparkrecursiveevaluationinvariants_bits_payload_ne_start (M : MultitapeTM) (w : List Bool) (p : ℕ) :
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

private theorem resumed_unique (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
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
      simp only [owned_intmulendparkrecursiveevaluationinvariants_bits_payload_ne_start M w p,Nat.succ_ne_zero]
  · simp only [if_neg hj]
    exact unique j p

private theorem resumed_tail (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
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

private theorem resumed_near (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    ∀ j, (resumedParent M n resume label extent c w).head j≤ parentAfterChildExtent M extent w j+1 := by
  intro j
  by_cases hj : j=M.outTape <;> simp [resumedParent,parentAfterChildExtent,hj]

private theorem step_unique (M : MultitapeTM) (c : M.Cfg)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0) :
    ∀ j p, (M.step c).cells j p=M.startSym ↔ p=0 := by
  have h := TrackedBankedSpace.unique_marker_run M c 1 unique
  simpa only [Function.iterate_one] using h

private theorem step_tail (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p=M.blank := by
  have h := TrackedBankedSpace.blank_tail_run M c extent 1 tail
  simpa only [Function.iterate_one,extents,Function.iterate_zero,Function.id_def] using h

private theorem step_near (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j≤ extent j+1) :
    ∀ j, (M.step c).head j≤ nextExtent M c extent j+1 := by
  have h := TrackedBankedSpace.heads_near_run M c extent 1 near
  simpa only [Function.iterate_one,extents,Function.iterate_zero,Function.id_def] using h

end IntMul.EndParkRecursiveEvaluation



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulendparkrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem owned_intmulendparkrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem owned_intmulendparkrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,owned_intmulendparkrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [boot_iterate M n request resume c s hlive,he]

private theorem preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [preparation_iterate M n request resume c s hlive,he]

private theorem body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,no_request]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem body_iterate (M : MultitapeTM) (n : ℕ)
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
      body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [input_iterate M n request resume label c s hlive,he]

private theorem reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [reservation_iterate M n request resume c s hlive,he]

private theorem return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [return_iterate M n request resume c s hlive,he]

private theorem cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [cleanup_iterate M n request resume c s hlive,he]

private theorem output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [output_iterate M n request resume label c s hlive,he]

private theorem finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply owned_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact owned_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [finish_iterate M n request resume c s hlive,he]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankedSimulation (nextExtent extents)

private noncomputable def evalBodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)

private theorem ordinary_body_step (M : MultitapeTM) (n : ℕ)
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
    (evalBodyView M n request resume base rho sigma offset extent c v))=_
  rw [body_step M n request resume _ live ordinary]
  exact congrArg (liftBody M n request resume) h

end IntMul.EndParkRecursiveEvaluation



namespace IntMul.EndParkRecursiveTraffic

open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveReturn
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem owned_intmulendparkrecursivetrafficcosts_component_le_span (M : MultitapeTM) (extent : Fin M.k → ℕ) (j : Fin M.k) :
    extent j ≤ span M extent := Finset.le_sup (f:=extent) (Finset.mem_univ j)

private theorem owned_intmulendparkrecursivetrafficcosts_span_le (M : MultitapeTM) (f : Fin M.k → ℕ) (B : ℕ) (bound : ∀ j, f j ≤ B) :
    span M f ≤ B := by
  apply Finset.sup_le
  intro j _
  exact bound j

private theorem return_cost_le_traffic (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
    (near : ∀ j, c.head j ≤ extent j+1) :
    returnCost M extent c v w ≤ 14*returnTraffic M extent v w := by
  have hhead : c.head M.outTape ≤ span M extent+1 := by
    have := near M.outTape
    have := owned_intmulendparkrecursivetrafficcosts_component_le_span M extent M.outTape
    omega
  have hscan : span M (returnedHeads M c) ≤ span M extent+1 := by
    apply owned_intmulendparkrecursivetrafficcosts_span_le
    intro j
    have := near j
    have := owned_intmulendparkrecursivetrafficcosts_component_le_span M extent j
    simp only [returnedHeads]
    split <;> omega
  have hfirst : max (c.head M.outTape) (v.length+1) ≤ span M extent+v.length+1 := by
    apply max_le <;> omega
  have hwords : max w.length v.length ≤ w.length+v.length := by
    apply max_le <;> omega
  unfold returnCost returnTraffic
  omega

private theorem result_extent_le_distance (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg) :
    extent M.outTape+1 ≤ reservationDistance M extent c := by
  have h := Finset.le_sup (s:=Finset.univ)
    (f:=TrackedBankReservation.distance M extent (parentAfterInput M c).head)
    (Finset.mem_univ M.outTape)
  simpa only [reservationDistance,span,TrackedBankReservation.distance,parentAfterInput,
    if_true,Nat.sub_zero] using h

private theorem call_resume_cost_le_traffic (M : MultitapeTM) (labels : ℕ) (extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y childWord : List Bool) :
    callCost M labels extent c v x y+resumeCost M labels extent childWord ≤
      32*callTraffic M labels extent c v x y childWord := by
  have hout := result_extent_le_distance M extent c
  have hfirst : max (c.head M.outTape) (v.length+1) ≤ c.head M.outTape+v.length+1 := by
    apply max_le <;> omega
  have hwords : max (inputWord M x y).length v.length ≤ (inputWord M x y).length+v.length := by
    apply max_le <;> omega
  have hresult : max childWord.length (extent M.outTape) ≤ childWord.length+reservationDistance M extent c := by
    apply max_le <;> omega
  unfold callCost resumeCost callTraffic
  change max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
    3*(inputWord M x y).length+reservationDistance M extent c+labels+16+
    (extent M.outTape+labels+childWord.length+2*max childWord.length (extent M.outTape)+13) ≤ _
  omega

/-- Parked untouched heads incur no reservation distance at the next call. -/
private theorem parked_reservation_distance (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (parked : ∀ j, j≠M.outTape → c.head j=extent j+1) :
    reservationDistance M extent c=extent M.outTape+1 := by
  apply Nat.le_antisymm
  · apply owned_intmulendparkrecursivetrafficcosts_span_le
    intro j
    by_cases hj : j=M.outTape
    · subst j
      simp [TrackedBankReservation.distance,parentAfterInput]
    · simp [TrackedBankReservation.distance,parentAfterInput,hj,parked j hj]
  · exact result_extent_le_distance M extent c

/-- Repeated calls after a child return pay only the preceding child word,
new packet and new result, with no retained unrelated parent space charge. -/
private theorem call_traffic_after_resume (M : MultitapeTM) (labels : ℕ) (resume : Fin labels → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin labels)
    (previousWord x y childWord : List Bool) :
    callTraffic M labels (parentAfterChildExtent M extent previousWord)
      (resumedParent M labels resume label extent c previousWord) previousWord x y childWord=
      2*previousWord.length+(inputWord M x y).length+childWord.length+labels+2 := by
  have hd := parked_reservation_distance M (parentAfterChildExtent M extent previousWord)
    (resumedParent M labels resume label extent c previousWord) (by
      intro j hj
      simp [parentAfterChildExtent,resumedParent,hj])
  unfold callTraffic
  rw [hd]
  simp only [resumedParent,parentAfterChildExtent,if_true]
  omega

/-- Linear physical overhead in an additive recursive word/space workload.
The counted ordinary body transitions are actual transitions of M. -/
private theorem budget_of_traffic (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps mass : ℕ)
    (workload : HasTraffic M labels request resume extent c v w steps mass) :
    (∀ j, c.head j ≤ extent j+1) →
      ∃ budget, budget ≤ steps+32*mass ∧ Evaluates M labels request resume extent c v w budget := by
  induction workload with
  | halt extent c v w halt out =>
    intro near
    refine ⟨returnCost M extent c v w,?_,Evaluates.halt extent c v w halt out⟩
    have h := return_cost_le_traffic M extent c v w near
    omega
  | step extent c v w steps mass live ordinary rest ih =>
    intro near
    have hnear := TrackedBankedSpace.heads_near_run M c extent 1 near
    simp only [Function.iterate_one,TrackedBankedSimulation.extents,Function.iterate_zero,Function.id_def] at hnear
    obtain ⟨budget,hbudget,heval⟩ := ih hnear
    exact ⟨budget+1,by omega,Evaluates.step extent c v w budget live ordinary heval⟩
  | call extent c v x y childWord w label childSteps childMass parentSteps parentMass live request_label packet child parent ihchild ihparent =>
    intro near
    obtain ⟨childBudget,hchildBudget,hchild⟩ := ihchild (by intro j; simp [MultitapeTM.initCfg])
    have hpnear : ∀ j, (resumedParent M labels resume label extent c childWord).head j ≤
        parentAfterChildExtent M extent childWord j+1 := by
      intro j
      by_cases hj : j=M.outTape <;> simp [resumedParent,parentAfterChildExtent,hj]
    obtain ⟨parentBudget,hparentBudget,hparent⟩ := ihparent hpnear
    refine ⟨callCost M labels extent c v x y+childBudget+resumeCost M labels extent childWord+parentBudget,
      ?_,Evaluates.call extent c v x y childWord w label childBudget parentBudget live request_label packet hchild hparent⟩
    have h := call_resume_cost_le_traffic M labels extent c v x y childWord
    omega

end IntMul.EndParkRecursiveTraffic



namespace IntMul.EndParkRecursiveAmortizedWork

open IntMul.EndParkRecursiveTraffic
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankPreparation (inputWord initialExtent)
open IntMul.TrackedBankedSimulation (nextExtent)

private theorem owned_intmulendparkrecursiveamortizedcosts_space_le (M : MultitapeTM) (E : Fin M.k → ℕ) (B : ℕ)
    (h : ∀ j, E j≤ B) : span M E≤ B := by
  apply Finset.sup_le
  intro j _
  exact h j

private theorem owned_intmulendparkrecursiveamortizedcosts_space_component (M : MultitapeTM) (E : Fin M.k → ℕ) (j : Fin M.k) :
    E j≤ span M E := Finset.le_sup (f:=E) (Finset.mem_univ j)

private theorem owned_intmulendparkrecursiveamortizedcosts_slack_le_sum (M : MultitapeTM) (E : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    headSlack M E c j≤∑ i, headSlack M E c i :=
  Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)

/-- One body transition replenishes the potential by at most a fixed amount. -/
private theorem potential_step (M : MultitapeTM) (E : Fin M.k → ℕ) (c : M.Cfg)
    (live : c.state≠M.qHalt) (near : ∀ j, c.head j≤ E j+1) :
    potential M (nextExtent M c E) (M.step c)≤ potential M E c+(2*M.k+3) := by
  have hs : span M (nextExtent M c E)≤ span M E+1 := by
    apply owned_intmulendparkrecursiveamortizedcosts_space_le
    intro j
    have := near j
    have := owned_intmulendparkrecursiveamortizedcosts_space_component M E j
    simp only [nextExtent,if_neg live]
    omega
  have ho : nextExtent M c E M.outTape≤ E M.outTape+1 := by
    have := near M.outTape
    simp only [nextExtent,if_neg live]
    omega
  have hslack : ∀ j, headSlack M (nextExtent M c E) (M.step c) j≤ headSlack M E c j+2 := by
    intro j
    by_cases hj : j=M.outTape
    · simp [headSlack,hj]
    · have hh : c.head j≤ (M.step c).head j+1 := by
        simp only [MultitapeTM.step]
        split <;> omega
      simp only [headSlack,if_neg hj,nextExtent,if_neg live]
      omega
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hslack j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  unfold potential
  omega

/-- Resumption releases all nonresult head-distance potential. -/
private theorem potential_resume (M : MultitapeTM) (labels : ℕ) (resume : Fin labels → M.K)
    (E : Fin M.k → ℕ) (c : M.Cfg) (label : Fin labels) (w : List Bool) :
    potential M (parentAfterChildExtent M E w) (resumedParent M labels resume label E c w)≤
      span M E+3*w.length := by
  have hs : span M (parentAfterChildExtent M E w)≤ span M E+w.length := by
    apply owned_intmulendparkrecursiveamortizedcosts_space_le
    intro j
    have := owned_intmulendparkrecursiveamortizedcosts_space_component M E j
    simp only [parentAfterChildExtent]
    split <;> omega
  have hz : ∀ j, headSlack M (parentAfterChildExtent M E w)
      (resumedParent M labels resume label E c w) j=0 := by
    intro j
    by_cases hj : j=M.outTape <;> simp [headSlack,parentAfterChildExtent,resumedParent,hj]
  unfold potential
  simp only [parentAfterChildExtent,if_true]
  simp_rw [hz]
  simp only [Finset.sum_const_zero]
  omega

/-- Native child initialization has potential linear in its input packet. -/
private theorem potential_initial (M : MultitapeTM) (x y : List Bool) :
    potential M (initialExtent M x y) (M.initCfg x y)≤
      (M.k+1)*(inputWord M x y).length+M.k := by
  have hs : span M (initialExtent M x y)≤ (inputWord M x y).length := by
    apply owned_intmulendparkrecursiveamortizedcosts_space_le
    intro j
    simp only [initialExtent]
    split <;> omega
  have hio : M.outTape≠M.inTape := by
    simp [MultitapeTM.outTape,MultitapeTM.inTape,Fin.ext_iff]
  have ho : initialExtent M x y M.outTape=0 := by simp [initialExtent,hio]
  have hslack : ∀ j, headSlack M (initialExtent M x y) (M.initCfg x y) j≤ (inputWord M x y).length+1 := by
    intro j
    simp only [headSlack,MultitapeTM.initCfg,Nat.sub_zero,initialExtent]
    split
    · omega
    · split <;> omega
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hslack j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hsum
  unfold potential
  rw [ho]
  nlinarith

private theorem owned_intmulendparkrecursiveamortizedcosts_reservation_le_slack (M : MultitapeTM) (E : Fin M.k → ℕ) (c : M.Cfg) :
    reservationDistance M E c≤ E M.outTape+1+∑ j, headSlack M E c j := by
  apply owned_intmulendparkrecursiveamortizedcosts_space_le
  intro j
  by_cases hj : j=M.outTape
  · subst j
    simp [TrackedBankReservation.distance,parentAfterInput]
  · have h := owned_intmulendparkrecursiveamortizedcosts_slack_le_sum M E c j
    rw [show headSlack M E c j=E j+1-c.head j by simp [headSlack,hj]] at h
    simp only [TrackedBankReservation.distance,parentAfterInput,if_neg hj]
    omega

/-- Call traffic, remaining parent potential and initial child potential
are paid by the old potential plus simple argument/result word lengths. -/
private theorem call_balance (M : MultitapeTM) (labels : ℕ) (resume : Fin labels → M.K)
    (E : Fin M.k → ℕ) (c : M.Cfg) (label : Fin labels) (v x y childWord : List Bool)
    (near : ∀ j, c.head j≤ E j+1) :
    callTraffic M labels E c v x y childWord+
      potential M (parentAfterChildExtent M E childWord)
        (resumedParent M labels resume label E c childWord)+
      potential M (initialExtent M x y) (M.initCfg x y)≤
      potential M E c+callWordWork M labels v x y childWord := by
  have hr := owned_intmulendparkrecursiveamortizedcosts_reservation_le_slack M E c
  have hp := potential_resume M labels resume E c label childWord
  have hi := potential_initial M x y
  have hh := near M.outTape
  unfold callTraffic potential callWordWork at *
  nlinarith

end IntMul.EndParkRecursiveAmortizedWork



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveschedulerpadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem padded_init (N : MultitapeTM) (x y : List Bool) :
    (FixedTapeExtension.machine N).initCfg x y =
      FixedTapeExtension.embed N ((FixedTapeExtension.machine N).initCfg x y) (N.initCfg x y) := by
  apply owned_intmulendparkrecursiveschedulerpadding_cfg_ext
  · rfl
  · apply (extension_cells_ready N _ _ ?_).symm
    intro j
    have hzero : FixedTapeExtension.oldTape N j=(FixedTapeExtension.machine N).inTape ↔ j=N.inTape := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg (fun i : Fin (N.k+1) => i.val) h
        exact hv
      · intro h; subst j; rfl
    simp only [MultitapeTM.initCfg,hzero]
    split <;> rfl
  · apply (extension_heads_ready N _ _ ?_).symm
    intro j
    rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkrecursiveschedulerleafframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def leafInspection (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (machine M n request resume).Cfg :=
  EndParkRecursiveReturn.inspectionFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1) w

private noncomputable def leafShiftParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (TrackedOutputShift.machine M).Cfg where
  state := .rewind
  cells := fun i => (leafInspection M n request resume x y w).cells
    (FixedTapeExtension.oldTape (TrackedOutputShift.machine M) i)
  head := fun i => (leafInspection M n request resume x y w).head
    (FixedTapeExtension.oldTape (TrackedOutputShift.machine M) i)

private noncomputable def leafShiftPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg where
  state := .rewind
  cells := (leafInspection M n request resume x y w).cells
  head := (leafInspection M n request resume x y w).head

private noncomputable def leafShiftStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedOutputShift.machine M) (leafShiftPadBase M n request resume x y w)
    (TrackedOutputShift.rewindFrame M (leafShiftParent M n request resume x y w) w (w.length+2))

private noncomputable def leafShiftFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedOutputShift.machine M) (leafShiftPadBase M n request resume x y w)
    (TrackedOutputShift.finalFrame M (leafShiftParent M n request resume x y w) w)

private theorem owned_intmulendparkrecursiveschedulerleafframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
  · simp only [TrackedOutputReturn.bufferTape,if_neg hp]

private theorem leaf_shift_old_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    TrackedOutputShift.rewindFrame M (leafShiftParent M n request resume x y w) w (w.length+2)=
      leafShiftParent M n request resume x y w := by
  apply owned_intmulendparkrecursiveschedulerleafframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedOutputShift.rewindFrame]
    by_cases hi : i.val=1
    · simp only [if_pos hi,leafShiftParent,leafInspection,EndParkRecursiveReturn.inspectionFrame,
        FixedTapeExtension.oldTape,dif_pos i.isLt,dif_neg (by omega : ¬2 ≤ i.val),if_pos hi]
      exact owned_intmulendparkrecursiveschedulerleafframes_return_idem M _ 1 w
    · simp only [if_neg hi]
  · funext i
    simp only [TrackedOutputShift.rewindFrame]
    by_cases hi : i.val=1
    · simp only [if_pos hi,leafShiftParent,leafInspection,EndParkRecursiveReturn.inspectionFrame,
        FixedTapeExtension.oldTape,dif_pos i.isLt,dif_neg (by omega : ¬2 ≤ i.val),if_pos hi]
      omega
    · simp only [if_neg hi]

private theorem leaf_shift_start_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    relabel M n request resume (.finish .rewind) (leafInspection M n request resume x y w)=
      liftFinish M n request resume (leafShiftStart M n request resume x y w) := by
  rw [leafShiftStart,leaf_shift_old_ready]
  have hp : FixedTapeExtension.embed (TrackedOutputShift.machine M)
      (leafShiftPadBase M n request resume x y w) (leafShiftParent M n request resume x y w)=
      leafShiftPadBase M n request resume x y w := by
    apply owned_intmulendparkrecursiveschedulerleafframes_cfg_ext
    · rfl
    · apply extension_cells_ready
      intro j
      rfl
    · apply extension_heads_ready
      intro j
      rfl
  rw [hp]
  rfl

private theorem owned_intmulendparkrecursiveschedulerleafframes_initial_zero (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) :
    (N.initCfg x y).cells i 0=N.startSym := by
  simp only [MultitapeTM.initCfg]
  split <;> rfl

private theorem owned_intmulendparkrecursiveschedulerleafframes_initial_empty (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) (hi : i.val ≠ 0) :
    (N.initCfg x y).cells i=N.tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem leaf_stack_root (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (leafInspection M n request resume x y w).cells (stackTape M)
      ((leafInspection M n request resume x y w).head (stackTape M))=none := by
  have hi : ¬(stackTape M).val < M.k+2 := by change ¬M.k+2 < M.k+2; omega
  simp only [leafInspection,EndParkRecursiveReturn.inspectionFrame,dif_neg hi,Nat.sub_self,
    FiniteContinuationStack.freshTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
  exact owned_intmulendparkrecursiveschedulerleafframes_initial_zero _ _ _ _

private theorem owned_intmulendparkrecursiveschedulerleafframes_output_base_eq (M : MultitapeTM) (a b : ℕ → Sym M) (w : List Bool) (h : a 0=b 0) :
    TrackedOutputShift.outputTape M a w=TrackedOutputShift.outputTape M b w := by
  funext p
  by_cases hp : p=0
  · subst p
    simp only [TrackedOutputShift.outputTape,if_true,h]
  · simp only [TrackedOutputShift.outputTape,if_neg hp]

private theorem owned_intmulendparkrecursiveschedulerleafframes_fresh_native (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y : List Bool) (i : Fin (M.k+3)) (hi : i.val ≠ 0) :
    TrackedBankCleanup.freshTape M (((machine M n request resume).initCfg x y).cells i) 1=
      ((machine M n request resume).initCfg x y).cells i := by
  rw [owned_intmulendparkrecursiveschedulerleafframes_initial_empty (machine M n request resume) x y i hi]
  funext p
  cases p with
  | zero => rfl
  | succ p => simp [TrackedBankCleanup.freshTape,MultitapeTM.tapeOf]

private theorem leaf_final_native (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    relabel M n request resume .halt (liftFinish M n request resume (leafShiftFinal M n request resume x y w))=
      nativeFinalFrame M n request resume x y w := by
  apply owned_intmulendparkrecursiveschedulerleafframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    simp only [relabel,liftFinish,leafShiftFinal,FixedTapeExtension.embed,nativeFinalFrame]
    by_cases hb : i.val=1
    · have hi : i.val < M.k+2 := by have := M.two_le_k; omega
      simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_pos hb]
      have hzero : (leafShiftParent M n request resume x y w).cells ⟨i.val,hi⟩ 0=
          ((machine M n request resume).initCfg x y).cells i 0 := by
        simp only [leafShiftParent,leafInspection,EndParkRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi,dif_neg (by omega : ¬2 ≤ i.val),if_pos hb,
          TrackedOutputReturn.bufferTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
      exact congrFun (owned_intmulendparkrecursiveschedulerleafframes_output_base_eq M _ _ w hzero) p
    · simp only [if_neg hb]
      by_cases hi : i.val < M.k+2
      · simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_neg hb,
          leafShiftParent,leafInspection,EndParkRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi]
        by_cases hw : 2 ≤ i.val
        · simp only [dif_pos hw,nativeBase]
          exact congrFun (owned_intmulendparkrecursiveschedulerleafframes_fresh_native M n request resume x y i (by omega)) p
        · simp only [dif_neg hw,if_neg hb,nativeBase]
      · simp only [dif_neg hi,leafShiftPadBase,leafInspection,EndParkRecursiveReturn.inspectionFrame,
          dif_neg hi,nativeBase]
        change TrackedBankCleanup.freshTape M (((machine M n request resume).initCfg x y).cells i) 1 p=_
        exact congrFun (owned_intmulendparkrecursiveschedulerleafframes_fresh_native M n request resume x y i (by omega)) p
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    simp only [relabel,liftFinish,leafShiftFinal,FixedTapeExtension.embed,nativeFinalFrame]
    by_cases hi : i.val < M.k+2
    · have hs : i≠stackTape M := by
        intro h; have hv := congrArg Fin.val h
        simp only [stackTape,FiniteContinuationStack.stackTape] at hv
        omega
      simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_neg hs]
      by_cases hb : i.val=1
      · simp only [if_pos hb,if_neg (by omega : i.val ≠ 0)]
      · simp only [if_neg hb,leafShiftParent,leafInspection,EndParkRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi]
        by_cases hw : 2 ≤ i.val
        · simp only [dif_pos hw,if_neg (by omega : i.val ≠ 0)]
        · have hz : i.val=0 := by omega
          simp only [dif_neg hw,if_neg hb,nativeBase,if_pos hz]
    · have hs : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      simp only [dif_neg hi,leafShiftPadBase,leafInspection,EndParkRecursiveReturn.inspectionFrame,
        dif_neg hi,Nat.sub_self,if_neg (by omega : i.val ≠ 0),if_neg (by omega : i.val ≠ 1),if_pos hs]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveschedulerdispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulendparkrecursiveschedulerdispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem owned_intmulendparkrecursiveschedulerdispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
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

private theorem stay_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,fun i => (c.cells i (c.head i),.stay))) :
    (machine M n request resume).step c=relabel M n request resume q c := by
  apply owned_intmulendparkrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,relabel]
  · simp only [MultitapeTM.step,ht,relabel]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,relabel]

private theorem right_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .right)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape+1) := by
  classical
  rw [owned_intmulendparkrecursiveschedulerdispatch_right_actions] at ht
  apply owned_intmulendparkrecursiveschedulerdispatch_cfg_ext
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

private theorem left_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (present : c.cells tape (c.head tape)≠none)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .left)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape-1) := by
  classical
  rw [owned_intmulendparkrecursiveschedulerdispatch_left_actions M _ tape present] at ht
  apply owned_intmulendparkrecursiveschedulerdispatch_cfg_ext
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

private theorem boot_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (exit : c.state=(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=headFrame M n request resume (.preparation .mark) (liftBoot M n request resume c) (stackTape M) (c.head (stackTape M)+1) := by
  apply right_step
  change transition M n request resume (.boot c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,call]
  all_goals try rfl

private theorem push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,exit]
  all_goals try rfl

private theorem inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply stay_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,FlatRecursiveScheduler.stackTape,reduceCtorEq,if_false,if_pos root]
  all_goals try rfl

private theorem inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply right_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,FlatRecursiveScheduler.stackTape,reduceCtorEq,if_false,if_neg parent]
  all_goals try rfl

private theorem reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  have hm : c.cells (FlatRecursiveScheduler.bufferTape M) (c.head (FlatRecursiveScheduler.bufferTape M))=some (M.startSym,true) := marker
  apply right_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos hm]
  rfl

private theorem reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  have hm : c.cells (FlatRecursiveScheduler.bufferTape M) (c.head (FlatRecursiveScheduler.bufferTape M))≠some (M.startSym,true) := marker
  apply left_step M n request resume _ _ _ present
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg hm]
  rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler

private theorem eval_native_finish_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    ∃ t, t ≤ 4*w.length+5 ∧
      (machine M n request resume).step^[t]
        (liftFinish M n request resume (leafShiftStart M n request resume x y w))=
        nativeFinalFrame M n request resume x y w := by
  have hr : (finishMachine M).step^[4*w.length+4] (leafShiftStart M n request resume x y w)=
      leafShiftFinal M n request resume x y w := by
    have h := (FixedTapeExtension.simulate_run (TrackedOutputShift.machine M)
      (leafShiftPadBase M n request resume x y w)
      (TrackedOutputShift.rewindFrame M (leafShiftParent M n request resume x y w) w (w.length+2))
      (4*w.length+4)).1
    rw [TrackedOutputShift.shift_correct] at h
    exact h
  have he : ((finishMachine M).step^[4*w.length+4]
      (leafShiftStart M n request resume x y w)).state=(finishMachine M).qHalt := by
    rw [hr]
    rfl
  obtain ⟨s,hsclock,hsrun⟩ := finish_to_halt M n request resume
    (leafShiftStart M n request resume x y w) (4*w.length+4) he
  rw [hr] at hsrun
  refine ⟨s+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',hsrun,finish_dispatch M n request resume _ rfl,leaf_final_native]

private theorem eval_native_root_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    ∃ t, t ≤ 4*w.length+6 ∧
      (machine M n request resume).step^[t] (leafInspection M n request resume x y w)=
        nativeFinalFrame M n request resume x y w := by
  obtain ⟨s,hs,hr⟩ := eval_native_finish_correct M n request resume x y w
  refine ⟨s+1,by omega,?_⟩
  rw [Function.iterate_succ_apply,inspect_root_dispatch M n request resume _ rfl
    (leaf_stack_root M n request resume x y w),leaf_shift_start_ready,hr]

private theorem eval_native_final_output (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (nativeFinalFrame M n request resume x y w).cells (machine M n request resume).outTape=
      (machine M n request resume).tapeOf (w.map (machine M n request resume).bitSym) := by
  funext p
  simp only [nativeFinalFrame,MultitapeTM.outTape,if_true]
  cases p with
  | zero =>
    simp only [TrackedOutputShift.outputTape,if_true,MultitapeTM.initCfg]
    split <;> rfl
  | succ p =>
    simp only [TrackedOutputShift.outputTape,Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,MultitapeTM.tapeOf]
    by_cases hp : p < w.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getD_eq_getElem _ _ (by simpa using hp)]
      simp only [List.getElem_map,hp,decide_true]
      cases h : w[p] <;> rfl
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
      simp only [hp,decide_false]


end IntMul.EndParkRecursiveEvaluation



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkrecursiveschedulerbootstrapframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def bootFinal (M : MultitapeTM) (x y : List Bool) : (bootMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedRootInputCopy.machine M)
    ((bootMachine M).initCfg x y) (TrackedRootInputCopy.finalFrame M x y)

private noncomputable def rootPreparationBase (M : MultitapeTM) (x y : List Bool) :
    (TrackedBankPreparation.machine M).Cfg where
  state := .mark
  cells := (TrackedRootInputCopy.finalFrame M x y).cells
  head := (TrackedRootInputCopy.finalFrame M x y).head

private noncomputable def rootPreparationPadBase (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg where
  state := .mark
  cells := (bootFinal M x y).cells
  head := Function.update (bootFinal M x y).head (stackTape M) 1

private noncomputable def rootPreparationStart (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M) (rootPreparationPadBase M x y)
    (TrackedBankPreparation.initialFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y)

private noncomputable def rootPreparationFinal (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M) (rootPreparationPadBase M x y)
    (TrackedBankPreparation.readyFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y)

private theorem owned_intmulendparkrecursiveschedulerbootstrapframes_source_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) :
    TrackedBankPreparation.sourceTape M (TrackedBankPreparation.sourceTape M base sigma w) sigma w =
      TrackedBankPreparation.sourceTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedBankPreparation.sourceTape,if_pos hp]
  · simp only [TrackedBankPreparation.sourceTape,if_neg hp]

private theorem owned_intmulendparkrecursiveschedulerbootstrapframes_fresh_native (M : MultitapeTM) :
    TrackedBankPreparation.freshTape M ((TrackedRootInputCopy.machine M).tapeOf []) 1 =
      (TrackedRootInputCopy.machine M).tapeOf [] := by
  funext p
  cases p with
  | zero => rfl
  | succ p => simp [TrackedBankPreparation.freshTape,MultitapeTM.tapeOf]

private theorem owned_intmulendparkrecursiveschedulerbootstrapframes_root_initial_empty (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k+2)) (hi : i.val ≠ 0) :
    ((TrackedRootInputCopy.machine M).initCfg x y).cells i = (TrackedRootInputCopy.machine M).tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem root_preparation_ready (M : MultitapeTM) (x y : List Bool) :
    TrackedBankPreparation.initialFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y=
      rootPreparationBase M x y := by
  apply owned_intmulendparkrecursiveschedulerbootstrapframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedBankPreparation.initialFrame,rootPreparationBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,
        if_neg (by omega : i.val ≠ 1)]
      rw [owned_intmulendparkrecursiveschedulerbootstrapframes_root_initial_empty M x y i (by omega)]
      exact owned_intmulendparkrecursiveschedulerbootstrapframes_fresh_native M
    · simp only [dif_neg hw]
      by_cases hi : i.val=1
      · simp only [if_pos hi,TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,
          if_pos hi,List.take_length]
        exact owned_intmulendparkrecursiveschedulerbootstrapframes_source_idem M _ 1 _
      · simp only [if_neg hi]
  · funext i
    simp only [TrackedBankPreparation.initialFrame,rootPreparationBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedRootInputCopy.finalFrame,if_neg (by omega : i.val ≠ 0)]
    · simp only [dif_neg hw]
      by_cases hi : i.val=1
      · simp only [if_pos hi,TrackedRootInputCopy.finalFrame,if_neg (by omega : i.val ≠ 0)]
      · simp only [if_neg hi]

private theorem owned_intmulendparkrecursiveschedulerbootstrapframes_old_ne_stack (M : MultitapeTM) (j : Fin (M.k+2)) :
    FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) j ≠ stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,stackTape,FiniteContinuationStack.stackTape] at h
  omega

private theorem root_preparation_start_ready (M : MultitapeTM) (x y : List Bool) :
    rootPreparationStart M x y=rootPreparationPadBase M x y := by
  rw [rootPreparationStart,root_preparation_ready]
  apply owned_intmulendparkrecursiveschedulerbootstrapframes_cfg_ext
  · rfl
  · apply extension_cells_ready
    intro j
    change (FixedTapeExtension.embed (TrackedRootInputCopy.machine M)
      ((bootMachine M).initCfg x y) (TrackedRootInputCopy.finalFrame M x y)).cells
      (FixedTapeExtension.oldTape (TrackedRootInputCopy.machine M) j)=_
    rw [extension_old_cells]
    rfl
  · apply extension_heads_ready
    intro j
    simp only [rootPreparationPadBase,Function.update_of_ne (owned_intmulendparkrecursiveschedulerbootstrapframes_old_ne_stack M j),bootFinal]
    change (FixedTapeExtension.embed (TrackedRootInputCopy.machine M)
      ((bootMachine M).initCfg x y) (TrackedRootInputCopy.finalFrame M x y)).head
      (FixedTapeExtension.oldTape (TrackedRootInputCopy.machine M) j)=_
    rw [extension_old_heads]
    rfl

private theorem boot_final_stack_head (M : MultitapeTM) (x y : List Bool) :
    (bootFinal M x y).head (stackTape M)=0 := by
  change (bootFinal M x y).head (FixedTapeExtension.extraTape (TrackedRootInputCopy.machine M))=0
  rw [bootFinal,extension_extra_heads]
  rfl

private theorem boot_dispatch_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    headFrame M n request resume (.preparation .mark) (liftBoot M n request resume (bootFinal M x y))
      (stackTape M) ((bootFinal M x y).head (stackTape M)+1)=
        liftPreparation M n request resume (rootPreparationStart M x y) := by
  rw [boot_final_stack_head,root_preparation_start_ready]
  rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkrecursiveschedulernativeframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulendparkrecursiveschedulernativeframes_bank_empty_buffer (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) :
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

private theorem owned_intmulendparkrecursiveschedulernativeframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
  · simp only [TrackedOutputReturn.bufferTape,if_neg hp]

private theorem owned_intmulendparkrecursiveschedulernativeframes_initial_zero (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) :
    (N.initCfg x y).cells i 0=N.startSym := by
  simp only [MultitapeTM.initCfg]
  split <;> rfl

private theorem owned_intmulendparkrecursiveschedulernativeframes_initial_empty (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) (hi : i.val ≠ 0) :
    (N.initCfg x y).cells i=N.tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem owned_intmulendparkrecursiveschedulernativeframes_root_final_zero (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k+2)) :
    (TrackedRootInputCopy.finalFrame M x y).cells i 0=none := by
  simp only [TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame]
  by_cases hi : i.val=1
  · simp only [if_pos hi,TrackedBankPreparation.sourceTape,if_pos (by omega : (0 : ℕ) < 1)]
    exact owned_intmulendparkrecursiveschedulernativeframes_initial_zero _ _ _ _
  · simp only [if_neg hi]
    exact owned_intmulendparkrecursiveschedulernativeframes_initial_zero _ _ _ _

private theorem owned_intmulendparkrecursiveschedulernativeframes_native_old_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) (j : Fin (M.k+2)) :
    ((TrackedRootInputCopy.machine M).initCfg x y).cells j=
      ((machine M n request resume).initCfg x y).cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) j) := by
  have hz : FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) j=(machine M n request resume).inTape ↔
      j=(TrackedRootInputCopy.machine M).inTape := by
    constructor
    · intro h; apply Fin.ext
      exact congrArg (fun i : Fin (M.k+3) => i.val) h
    · intro h; subst j; rfl
  simp only [MultitapeTM.initCfg,hz]
  split <;> rfl

private theorem root_preparation_buffer (M : MultitapeTM) (x y : List Bool) :
    (rootPreparationFinal M x y).cells (bufferTape M)=
      TrackedOutputReturn.bufferTape M ((rootPreparationFinal M x y).cells (bufferTape M)) 1 [] ∧
    (rootPreparationFinal M x y).head (bufferTape M)=1+(TrackedBankPreparation.inputWord M x y).length+1 := by
  have hc : (rootPreparationFinal M x y).cells (bufferTape M)=
      TrackedBankPreparation.bankTape M
        ((rootPreparationBase M x y).cells ⟨1,by change 1 < M.k+2; omega⟩) 1 [] := by
    change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) (rootPreparationPadBase M x y)
      (TrackedBankPreparation.readyFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y)).cells
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [extension_old_cells]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]
  constructor
  · rw [hc,owned_intmulendparkrecursiveschedulernativeframes_bank_empty_buffer]
    exact (owned_intmulendparkrecursiveschedulernativeframes_return_idem M _ 1 []).symm
  · change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) (rootPreparationPadBase M x y)
      (TrackedBankPreparation.readyFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y)).head
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [extension_old_heads]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]

private theorem root_body_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    headFrame M n request resume (.body M.qStart)
      (relabel M n request resume .resetBuffer (liftPreparation M n request resume (rootPreparationFinal M x y)))
      (bufferTape M) 2 =
    bodyFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1)
      (TrackedBankPreparation.initialExtent M x y) (M.initCfg x y) [] := by
  classical
  apply owned_intmulendparkrecursiveschedulernativeframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    simp only [headFrame,relabel,liftPreparation,rootPreparationFinal,bodyFrame,liftBody,
      FixedTapeExtension.embed]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi]
      simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
        TrackedBankPreparation.callerBase,parentBase,rootPreparationBase,
        FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
        by_cases hp : p < 1
        · have hp0 : p=0 := by omega
          subst p
          simp only [if_pos (by omega : (0 : ℕ) < 1),if_neg (by omega : i.val ≠ 1),nativeBase]
          rw [owned_intmulendparkrecursiveschedulernativeframes_root_final_zero,owned_intmulendparkrecursiveschedulernativeframes_initial_zero]
        · simp only [if_neg hp]
      · simp only [dif_neg hw]
        by_cases hb : i.val=1
        · simp only [if_pos hb]
          rw [owned_intmulendparkrecursiveschedulernativeframes_bank_empty_buffer]
          by_cases hp : p < 1
          · have hp0 : p=0 := by omega
            subst p
            simp only [TrackedOutputReturn.bufferTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
            rw [owned_intmulendparkrecursiveschedulernativeframes_root_final_zero,owned_intmulendparkrecursiveschedulernativeframes_initial_zero]
          · simp only [TrackedOutputReturn.bufferTape,if_neg hp]
        · simp only [if_neg hb]
          simp only [TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,if_neg hb,nativeBase]
          exact congrFun (owned_intmulendparkrecursiveschedulernativeframes_native_old_cells M n request resume x y ⟨i.val,hi⟩) p
    · simp only [dif_neg hi]
      have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      simp only [rootPreparationPadBase,bootFinal,FixedTapeExtension.embed,
        dif_neg hi,stackBase,if_true,nativeBase]
      cases p with
      | zero =>
        simp only [FiniteContinuationStack.freshTape,if_pos (by omega : (0 : ℕ) < 1)]
        rw [owned_intmulendparkrecursiveschedulernativeframes_initial_zero,owned_intmulendparkrecursiveschedulernativeframes_initial_zero]
      | succ p =>
        rw [owned_intmulendparkrecursiveschedulernativeframes_initial_empty (bootMachine M) x y (stackTape M) (by change M.k+2 ≠ 0; omega)]
        simp only [MultitapeTM.tapeOf,List.getD_nil,FiniteContinuationStack.freshTape,
          if_neg (by omega : ¬p+1 < 1)]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    simp only [headFrame,relabel,liftPreparation,rootPreparationFinal,bodyFrame,liftBody,
      FixedTapeExtension.embed]
    by_cases hb : i=bufferTape M
    · subst i
      simp [bufferTape,TrackedBankedSimulation.embed,parentBase,FixedTapeExtension.innerTape]
    · rw [Function.update_of_ne hb]
      by_cases hi : i.val < M.k+2
      · simp only [dif_pos hi]
        simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
          TrackedBankPreparation.callerBase,parentBase,rootPreparationBase,
          FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        by_cases hw : 2 ≤ i.val
        · simp [dif_pos hw,MultitapeTM.initCfg]
        · have hn : i.val ≠ 1 := by intro h; exact hb (Fin.ext h)
          have hz : i.val=0 := by omega
          simp only [dif_neg hw,if_neg hn,TrackedRootInputCopy.finalFrame,nativeBase,if_pos hz]
      · simp only [dif_neg hi]
        have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
        subst i
        simp [rootPreparationPadBase,stackBase]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveschedulerreset_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def resetFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ) : (machine M n request resume).Cfg where
  state := .resetBuffer
  cells := c.cells
  head := Function.update c.head (bufferTape M) (sigma+(a-r))

private theorem owned_intmulendparkrecursiveschedulerreset_empty_return_scan (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (sigma p : ℕ) : TrackedOutputReturn.bufferTape M base sigma [] (sigma+p)=
      if p=0 then some (M.startSym,true) else some (M.blank,false) := by
  cases p with
  | zero => simp [TrackedOutputReturn.bufferTape]
  | succ p => simp [TrackedOutputReturn.bufferTape,show ¬sigma+(p+1) < sigma by omega,
      show sigma+(p+1)≠sigma by omega]

private theorem reset_scan (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((resetFrame M n request resume c sigma a r).head (bufferTape M))=
        if a ≤ r then some (M.startSym,true) else some (M.blank,false) := by
  simp only [resetFrame,Function.update_self]
  rw [empty,owned_intmulendparkrecursiveschedulerreset_empty_return_scan]
  split_ifs <;> first | rfl | omega

private theorem reset_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r < a) :
    (machine M n request resume).step (resetFrame M n request resume c sigma a r)=
      resetFrame M n request resume c sigma a (r+1) := by
  have hscan := reset_scan M n request resume c sigma a r empty
  rw [if_neg (by omega : ¬a ≤ r)] at hscan
  have hm : (resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((resetFrame M n request resume c sigma a r).head (bufferTape M))≠some (M.startSym,true) := by
    rw [hscan]
    intro h
    have h := congrArg Prod.snd (Option.some.inj h)
    cases h
  rw [reset_live_step M n request resume _ rfl hm (by rw [hscan]; exact Option.some_ne_none _)]
  apply owned_intmulendparkrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,resetFrame,Function.update_self,Function.update_idem]
    congr 1
    omega

private theorem reset_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r ≤ a) :
    (machine M n request resume).step^[r] (resetFrame M n request resume c sigma a 0)=
      resetFrame M n request resume c sigma a r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),reset_step M n request resume c sigma a r empty (by omega)]

private theorem reset_complete (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a : ℕ)
    (phase : c.state=.resetBuffer) (head : c.head (bufferTape M)=sigma+a)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (machine M n request resume).step^[a+1] c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (sigma+1) := by
  have hstart : c=resetFrame M n request resume c sigma a 0 := by
    apply owned_intmulendparkrecursiveschedulerreset_cfg_ext
    · exact phase
    · rfl
    · simp only [resetFrame,Nat.sub_zero,←head]
      exact (Function.update_eq_self _ _).symm
  rw [hstart,Function.iterate_succ_apply',reset_run M n request resume _ sigma a a empty le_rfl]
  have hm := reset_scan M n request resume c sigma a a empty
  rw [if_pos le_rfl] at hm
  rw [reset_marker_dispatch M n request resume _ rfl hm]
  apply owned_intmulendparkrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,resetFrame,Nat.sub_self,Nat.add_zero,Function.update_self,Function.update_idem]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem bootstrap_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    ∃ t, t ≤ 5*(inputWord M x y).length+12 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        bodyFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1)
          (initialExtent M x y) (M.initCfg x y) [] := by
  let L := (inputWord M x y).length
  have hboot : (bootMachine M).step^[2*L+5] ((bootMachine M).initCfg x y)=bootFinal M x y := by
    have hr := (FixedTapeExtension.simulate_run (TrackedRootInputCopy.machine M)
      ((bootMachine M).initCfg x y) ((TrackedRootInputCopy.machine M).initCfg x y) (2*L+5)).1
    rw [←padded_init,TrackedRootInputCopy.copy_correct] at hr
    exact hr
  have hb : ((bootMachine M).step^[2*L+5] ((bootMachine M).initCfg x y)).state=(bootMachine M).qHalt := by
    rw [hboot]
    rfl
  obtain ⟨b,hbclock,hbrun⟩ := boot_to_halt M n request resume ((bootMachine M).initCfg x y) (2*L+5) hb
  rw [hboot] at hbrun
  have hbstart : liftBoot M n request resume ((bootMachine M).initCfg x y)=
      (machine M n request resume).initCfg x y := rfl
  rw [hbstart] at hbrun
  have hdispatch : (machine M n request resume).step^[b+1] ((machine M n request resume).initCfg x y)=
      liftPreparation M n request resume (rootPreparationStart M x y) := by
    rw [Function.iterate_succ_apply',hbrun,boot_dispatch M n request resume _ rfl,boot_dispatch_ready]
  have hprep : (preparationMachine M).step^[2*L+3] (rootPreparationStart M x y)=
      rootPreparationFinal M x y := by
    have hr := (FixedTapeExtension.simulate_run (TrackedBankPreparation.machine M)
      (rootPreparationPadBase M x y)
      (TrackedBankPreparation.initialFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y)
      (2*L+3)).1
    rw [TrackedBankPreparation.setup_correct] at hr
    exact hr
  have hp : ((preparationMachine M).step^[2*L+3] (rootPreparationStart M x y)).state=(preparationMachine M).qHalt := by
    rw [hprep]
    rfl
  obtain ⟨p,hpclock,hprun⟩ := preparation_to_halt M n request resume (rootPreparationStart M x y) (2*L+3) hp
  rw [hprep] at hprun
  let c := relabel M n request resume .resetBuffer
    (liftPreparation M n request resume (rootPreparationFinal M x y))
  have hreset : (machine M n request resume).step^[p+1+(b+1)] ((machine M n request resume).initCfg x y)=c := by
    rw [Function.iterate_add_apply,hdispatch,Function.iterate_succ_apply',hprun,
      preparation_dispatch M n request resume _ rfl]
  have hc : c.head (bufferTape M)=1+(L+1) := by
    change (rootPreparationFinal M x y).head (bufferTape M)=1+(L+1)
    have h := (root_preparation_buffer M x y).2
    dsimp only [L]
    omega
  have he : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) 1 [] :=
    (root_preparation_buffer M x y).1
  have hr := reset_complete M n request resume c 1 (L+1) rfl hc he
  have hready := root_body_ready M n request resume x y
  refine ⟨(L+2)+(p+1+(b+1)),by dsimp only [L] at *; omega,?_⟩
  rw [Function.iterate_add_apply,hreset,hr]
  exact hready

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveRelocation

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord)

/-- Native body entry scans the same blank outer-input symbol at every
input size, although its physical input-head position depends on that size. -/
private theorem native_root_blank (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    (nativeBase M n request resume x y).cells (machine M n request resume).inTape
      ((nativeBase M n request resume x y).head (machine M n request resume).inTape)=
      (machine M n request resume).blank := by
  have hhead : (nativeBase M n request resume x y).head (machine M n request resume).inTape=
      (inputWord M x y).length+1 := by
    simp only [nativeBase,MultitapeTM.inTape,if_true]
  rw [hhead]
  change ((machine M n request resume).initCfg x y).cells
    (machine M n request resume).inTape ((inputWord M x y).length+1)=_
  simp only [MultitapeTM.initCfg,if_pos rfl]
  rw [if_pos (by trivial)]
  simp only [MultitapeTM.tapeOf]
  apply List.getD_eq_default
  simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,inputWord]
  simp

end IntMul.EndParkRecursiveRelocation



namespace IntMul.EndParkRecursiveClockedCalls

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveEvaluation
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveResume
open IntMul.EndParkRecursiveReturn
open IntMul.EndParkRecursiveAmortizedWork
open IntMul.EndParkRecursiveTraffic
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem child_scans_blank (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (base : (machine M labels request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin labels)
    (root_blank : base.cells (machine M labels request resume).inTape
      (base.head (machine M labels request resume).inTape)=(machine M labels request resume).blank) :
    let b := childBase M labels request resume base rho sigma offset extent c label
    b.cells (machine M labels request resume).inTape (b.head (machine M labels request resume).inTape)=
      (machine M labels request resume).blank := by
  have hk : 0 < M.k+2 := by omega
  have hs : (⟨0,by omega⟩ : Fin (M.k+3))≠stackTape M := by
    intro h
    have hv := congrArg Fin.val h
    simp only [stackTape,FiniteContinuationStack.stackTape] at hv
    omega
  simpa only [childBase,MultitapeTM.inTape,if_neg hs,show (0:ℕ)≠1 by omega,if_false,
    dif_pos hk,dif_neg (by omega : ¬2 ≤ (0:ℕ)),bodyFrame,liftBody,FixedTapeExtension.embed,
    FixedTapeExtension.innerTape,FixedTapeExtension.oldTape,TrackedBankedSimulation.embed,parentBase] using root_blank

private theorem executes_clocked_calls (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (steps clocks work : ℕ)
    (certificate : HasClockedCalls M labels request resume extent c v w steps clocks work) :
    ∀ (base : (machine M labels request resume).Cfg) (rho sigma : ℕ) (offset : Fin M.k → ℕ),
      (∀ j, 1 ≤ offset j) → 1 ≤ rho → 1 ≤ sigma →
      base.cells (machine M labels request resume).inTape
        (base.head (machine M labels request resume).inTape)=(machine M labels request resume).blank →
      (∀ j p, c.cells j p=M.startSym ↔ p=0) →
      (∀ j p, extent j < p → c.cells j p=M.blank) →
      (∀ j, c.head j ≤ extent j+1) →
      ∃ t, t ≤ clocks+steps+32*(work+potential M extent c+(2*M.k+3)*steps) ∧
        (machine M labels request resume).step^[t]
          (bodyFrame M labels request resume base rho sigma offset extent c v)=
          inspectionFrame M labels request resume base rho sigma offset w := by
  induction certificate with
  | halt extent c v w halt out =>
    intro base rho sigma offset positive hrho hsigma root_blank unique tail near
    obtain ⟨t,ht,hrun,hsafe⟩ := return_cleanup_protected_prefix M labels request resume base rho sigma offset extent
      positive hrho hsigma c v w halt out unique tail
    have hcost := return_cost_le_traffic M extent c v w near
    have hpay : returnTraffic M extent v w ≤ v.length+w.length+1+potential M extent c := by
      unfold returnTraffic potential
      omega
    refine ⟨t,?_,hrun⟩
    simp only [Nat.zero_add,Nat.mul_zero,Nat.add_zero]
    change t ≤ returnCost M extent c v w at ht
    omega
  | step extent c v w steps clocks work live ordinary rest ih =>
    intro base rho sigma offset positive hrho hsigma root_blank unique tail near
    obtain ⟨t,ht,hrun⟩ := ih base rho sigma offset positive hrho hsigma root_blank
      (step_unique M c unique) (step_tail M extent c tail) (step_near M extent c near)
    have hp := potential_step M extent c live near
    refine ⟨t+1,by nlinarith,?_⟩
    rw [Function.iterate_succ_apply,
      ordinary_body_step M labels request resume base rho sigma offset extent positive c v
        (fun j => (unique j 0).2 rfl) near live ordinary,hrun]
  | call extent c v x y childWord w label childBudget H parentSteps parentClocks parentWork live request_label packet child child_halt parent ih =>
    intro base rho sigma offset positive hrho hsigma root_blank unique tail near
    obtain ⟨d,hd,hdown,_⟩ := call_entry_protected_prefix M labels request resume label base rho sigma offset extent c v x y
      positive hrho hsigma live request_label packet near tail
    have hpositive : ∀ j, 1 ≤ TrackedBankReservation.newOffsets M offset extent j := by
      intro j
      unfold TrackedBankReservation.newOffsets
      omega
    obtain ⟨q,hqbudget,hqclock,hchild⟩ := native_to_interior_clock M labels request resume
      (childBase M labels request resume base rho sigma offset extent c label) (rho+labels+1) sigma
      (TrackedBankReservation.newOffsets M offset extent) x y childWord childBudget H
      (by omega) hsigma hpositive
      (child_scans_blank M labels request resume base rho sigma offset extent c label root_blank)
      child child_halt
    change (machine M labels request resume).step^[q]
      (childFrame M labels request resume base rho sigma offset extent c label x y)=
      childInspection M labels request resume base rho sigma offset extent c label childWord at hchild
    obtain ⟨r,hr,hresume,_⟩ := resume_parent_protected_prefix M labels request resume
      base rho sigma offset extent c label childWord positive hrho hsigma unique tail
    obtain ⟨p,hp,hparent⟩ := ih base rho sigma offset positive hrho hsigma root_blank
      (resumed_unique M labels resume extent c label childWord unique)
      (resumed_tail M labels resume extent c label childWord tail)
      (resumed_near M labels resume extent c label childWord)
    change (machine M labels request resume).step^[p]
      (resumedFrame M labels request resume base rho sigma offset extent c label childWord)=
      inspectionFrame M labels request resume base rho sigma offset w at hparent
    have hcost := call_resume_cost_le_traffic M labels extent c v x y childWord
    have hbalance := call_balance M labels resume extent c label v x y childWord near
    change d ≤ callCost M labels extent c v x y at hd
    change r ≤ resumeCost M labels extent childWord at hr
    refine ⟨p+(r+(q+d)),by nlinarith,?_⟩
    rw [Function.iterate_add_apply (machine M labels request resume).step p (r+(q+d)),
      Function.iterate_add_apply (machine M labels request resume).step r (q+d),
      Function.iterate_add_apply (machine M labels request resume).step q d,
      hdown,hchild,hresume,hparent]

/-- Complete physical native execution charges ACTUAL child halt clocks with
coefficient one; all caller bank movement is paid by local word work. -/
private theorem native_clocked_calls_correct (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (x y w : List Bool) (steps clocks work : ℕ)
    (certificate : HasClockedCalls M labels request resume (initialExtent M x y)
      (M.initCfg x y) [] w steps clocks work) :
    ∃ t, t ≤ clocks+steps+32*(work+(M.k+1)*(inputWord M x y).length+M.k+(2*M.k+3)*steps)+
        5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M labels request resume).step^[t] ((machine M labels request resume).initCfg x y)=
        nativeFinalFrame M labels request resume x y w ∧
      (machine M labels request resume).HaltsWithOutput x y t w := by
  obtain ⟨b,hb,hboot⟩ := bootstrap_correct M labels request resume x y
  obtain ⟨q,hq,heval⟩ := executes_clocked_calls M labels request resume (initialExtent M x y)
    (M.initCfg x y) [] w steps clocks work certificate
    (nativeBase M labels request resume x y) 1 1 (fun _ => 1)
    (by intro j; omega) (by omega) (by omega)
    (EndParkRecursiveRelocation.native_root_blank M labels request resume x y)
    (EndParkRecursiveSchedulerNativeInvariants.initial_unique_markers M x y)
    (EndParkRecursiveSchedulerNativeInvariants.initial_blank_tails M x y)
    (EndParkRecursiveSchedulerNativeInvariants.initial_heads_near M x y)
  change (machine M labels request resume).step^[q]
    (bodyFrame M labels request resume (nativeBase M labels request resume x y) 1 1 (fun _ => 1)
      (initialExtent M x y) (M.initCfg x y) [])=leafInspection M labels request resume x y w at heval
  obtain ⟨f,hf,hfinish⟩ := eval_native_root_correct M labels request resume x y w
  have hrun : (machine M labels request resume).step^[f+(q+b)] ((machine M labels request resume).initCfg x y)=
      nativeFinalFrame M labels request resume x y w := by
    rw [Function.iterate_add_apply (machine M labels request resume).step f (q+b),
      Function.iterate_add_apply (machine M labels request resume).step q b,hboot,heval,hfinish]
  have hpotential := potential_initial M x y
  refine ⟨f+(q+b),by nlinarith,hrun,?_⟩
  unfold MultitapeTM.HaltsWithOutput
  rw [hrun]
  exact ⟨rfl,eval_native_final_output M labels request resume x y w⟩

end IntMul.EndParkRecursiveClockedCalls


open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveClockedCalls IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (x y w : List Bool) (steps clocks work : ℕ)
    (certificate : HasClockedCalls M labels request resume (initialExtent M x y)
      (M.initCfg x y) [] w steps clocks work) :
    ∃ t, t ≤ clocks+steps+32*(work+(M.k+1)*(inputWord M x y).length+M.k+(2*M.k+3)*steps)+
        5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M labels request resume).step^[t] ((machine M labels request resume).initCfg x y)=
        nativeFinalFrame M labels request resume x y w ∧
      (machine M labels request resume).HaltsWithOutput x y t w :=
  IntMul.EndParkRecursiveClockedCalls.native_clocked_calls_correct M labels request resume x y w steps clocks work certificate

#print axioms solution
