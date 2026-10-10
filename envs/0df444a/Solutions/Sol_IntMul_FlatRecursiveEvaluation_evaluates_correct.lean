-- Prove2me | solution 1 for IntMul.FlatRecursiveEvaluation.evaluates_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T03:15:37.494061+00:00
-- url     : https://prove2.me/submissions/1e01ca7b-56e8-45d6-b632-274dde0eb7c0

import Definitions.Def_IntMul_FlatRecursiveEvaluation
import Theorems.Thm_IntMul_FlatRecursiveCall_call_entry_correct
import Theorems.Thm_IntMul_FlatRecursiveResume_resume_parent_correct
import Theorems.Thm_IntMul_FlatRecursiveReturn_return_cleanup_correct
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.FlatRecursiveSchedulerNativeInvariants

open IntMul.TrackedBankedSimulation (extents nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem evaluation_internal_flatrecursiveschedulernativeinvariants_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem evaluation_internal_flatrecursiveschedulernativeinvariants_word_payload_ne_start (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (inputWord M x y).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (inputWord M x y).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hl := evaluation_internal_flatrecursiveschedulernativeinvariants_word_letter M x y (inputWord M x y)[p] (List.getElem_mem hp)
    aesop
  · rw [List.getD_eq_default _ _ (by omega)]
    aesop

private theorem evaluation_internal_initial_unique_markers (M : MultitapeTM) (x y : List Bool) :
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
        have h := evaluation_internal_flatrecursiveschedulernativeinvariants_word_payload_ne_start M x y p
        simp only [h,Nat.succ_ne_zero]
      · simp only [if_neg hj,MultitapeTM.tapeOf,List.getD_nil]
        have hd := M.syms_distinct
        simp only [List.nodup_cons,List.mem_cons,not_or] at hd
        aesop

private theorem evaluation_internal_initial_blank_tails (M : MultitapeTM) (x y : List Bool) :
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

private theorem evaluation_internal_initial_heads_near (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).head j ≤ initialExtent M x y j + 1 := by
  intro j
  simp [MultitapeTM.initCfg]


end IntMul.FlatRecursiveSchedulerNativeInvariants



namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem evaluation_internal_trackedbankedspaceinvariants_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem evaluation_internal_trackedbankedspaceinvariants_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply evaluation_internal_trackedbankedspaceinvariants_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem evaluation_internal_trackedbankedspaceinvariants_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [evaluation_internal_trackedbankedspaceinvariants_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem evaluation_internal_blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact evaluation_internal_trackedbankedspaceinvariants_blank_tail_step M _ _ ih

private theorem evaluation_internal_trackedbankedspaceinvariants_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
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
private theorem evaluation_internal_unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact evaluation_internal_trackedbankedspaceinvariants_unique_marker_step M _ ih

private theorem evaluation_internal_trackedbankedspaceinvariants_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem evaluation_internal_trackedbankedspaceinvariants_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [evaluation_internal_trackedbankedspaceinvariants_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := evaluation_internal_trackedbankedspaceinvariants_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem evaluation_internal_heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact evaluation_internal_trackedbankedspaceinvariants_near_step M _ _ ih


end IntMul.TrackedBankedSpace




namespace IntMul.FlatRecursiveScheduler

private theorem evaluation_internal_flatrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem evaluation_internal_flatrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem evaluation_internal_flatrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem evaluation_internal_flatrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,evaluation_internal_flatrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem evaluation_internal_boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem evaluation_internal_boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_boot_iterate M n request resume c s hlive,he]

private theorem evaluation_internal_preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem evaluation_internal_preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_preparation_iterate M n request resume c s hlive,he]

private theorem evaluation_internal_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,if_neg live,no_request]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem evaluation_internal_body_iterate (M : MultitapeTM) (n : ℕ)
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
      evaluation_internal_body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem evaluation_internal_input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem evaluation_internal_input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_input_iterate M n request resume label c s hlive,he]

private theorem evaluation_internal_reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem evaluation_internal_reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_reservation_iterate M n request resume c s hlive,he]

private theorem evaluation_internal_return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem evaluation_internal_return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_return_iterate M n request resume c s hlive,he]

private theorem evaluation_internal_cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem evaluation_internal_cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_cleanup_iterate M n request resume c s hlive,he]

private theorem evaluation_internal_restore_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step c) := by
  have ht : transition M n request resume (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem evaluation_internal_restore_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_restore_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_restore_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_restore_iterate M n request resume c s hlive,he]

private theorem evaluation_internal_output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem evaluation_internal_output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_output_iterate M n request resume label c s hlive,he]

private theorem evaluation_internal_finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply evaluation_internal_flatrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem evaluation_internal_finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      evaluation_internal_finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem evaluation_internal_finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := evaluation_internal_flatrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact evaluation_internal_flatrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [evaluation_internal_finish_iterate M n request resume c s hlive,he]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveEvaluation

open IntMul.FlatRecursiveCall
open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem evaluation_internal_flatrecursiveevaluationinvariants_bits_payload_ne_start (M : MultitapeTM) (w : List Bool) (p : ℕ) :
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

private theorem evaluation_internal_resumed_unique (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0) :
    ∀ j p, (parentAfterChild M n resume label c w).cells j p=M.startSym ↔ p=0 := by
  intro j p
  simp only [parentAfterChild]
  by_cases hj : j=M.outTape
  · simp only [if_pos hj]
    cases p with
    | zero => simp [MultitapeTM.tapeOf]
    | succ p =>
      change (w.map M.bitSym).getD p M.blank=M.startSym ↔ p+1=0
      simp only [evaluation_internal_flatrecursiveevaluationinvariants_bits_payload_ne_start M w p,Nat.succ_ne_zero]
  · simp only [if_neg hj]
    exact unique j p

private theorem evaluation_internal_resumed_tail (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∀ j p, parentAfterChildExtent M extent w j < p →
      (parentAfterChild M n resume label c w).cells j p=M.blank := by
  intro j p hp
  simp only [parentAfterChildExtent] at hp
  simp only [parentAfterChild]
  by_cases hj : j=M.outTape
  · simp only [if_pos hj] at hp ⊢
    cases p with
    | zero => omega
    | succ p =>
      change (w.map M.bitSym).getD p M.blank=M.blank
      exact List.getD_eq_default _ _ (by simp only [List.length_map]; omega)
  · simp only [if_neg hj] at hp ⊢
    exact tail j p hp

private theorem evaluation_internal_resumed_near (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    ∀ j, (parentAfterChild M n resume label c w).head j≤ parentAfterChildExtent M extent w j+1 := by
  intro j
  simp [parentAfterChild]

private theorem evaluation_internal_step_unique (M : MultitapeTM) (c : M.Cfg)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0) :
    ∀ j p, (M.step c).cells j p=M.startSym ↔ p=0 := by
  have h := TrackedBankedSpace.evaluation_internal_unique_marker_run M c 1 unique
  simpa only [Function.iterate_one] using h

private theorem evaluation_internal_step_tail (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p=M.blank := by
  have h := TrackedBankedSpace.evaluation_internal_blank_tail_run M c extent 1 tail
  simpa only [Function.iterate_one,extents,Function.iterate_zero,Function.id_def] using h

private theorem evaluation_internal_step_near (M : MultitapeTM) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j≤ extent j+1) :
    ∀ j, (M.step c).head j≤ nextExtent M c extent j+1 := by
  have h := TrackedBankedSpace.evaluation_internal_heads_near_run M c extent 1 near
  simpa only [Function.iterate_one,extents,Function.iterate_zero,Function.id_def] using h

end IntMul.FlatRecursiveEvaluation



namespace IntMul.FlatRecursiveEvaluation

open IntMul.FlatRecursiveScheduler
open IntMul.TrackedBankedSimulation (nextExtent extents)

private noncomputable def evaluation_internal_evalBodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)

private theorem evaluation_internal_ordinary_body_step (M : MultitapeTM) (n : ℕ)
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
    (evaluation_internal_evalBodyView M n request resume base rho sigma offset extent c v))=_
  rw [evaluation_internal_body_step M n request resume _ live ordinary]
  exact congrArg (liftBody M n request resume) h

end IntMul.FlatRecursiveEvaluation



namespace IntMul.FlatRecursiveEvaluation

open IntMul.FlatRecursiveScheduler
open IntMul.FlatRecursiveCall
open IntMul.FlatRecursiveReturn
open IntMul.FlatRecursiveResume
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
    exact return_cleanup_correct M n request resume base rho sigma offset extent positive c v w halt out unique tail
  | step extent c v w budget live ordinary rest ih =>
    intro base rho sigma offset positive unique tail near
    obtain ⟨t,ht,hrun⟩ := ih base rho sigma offset positive
      (evaluation_internal_step_unique M c unique) (evaluation_internal_step_tail M extent c tail) (evaluation_internal_step_near M extent c near)
    refine ⟨t+1,by omega,?_⟩
    rw [Function.iterate_succ_apply,
      evaluation_internal_ordinary_body_step M n request resume base rho sigma offset extent positive c v
        (fun j => (unique j 0).2 rfl) near live ordinary,hrun]
  | call extent c v x y childWord w label childBudget parentBudget live request_label packet child parent ihchild ihparent =>
    intro base rho sigma offset positive unique tail near
    obtain ⟨d,hd,hdown⟩ := call_entry_correct M n request resume label base rho sigma offset extent c v x y
      live request_label packet near tail
    have hpositive : ∀ j, 1≤ TrackedBankReservation.newOffsets M offset extent j := by
      intro j
      unfold TrackedBankReservation.newOffsets
      omega
    obtain ⟨q,hq,hchild⟩ := ihchild
      (childBase M n request resume base rho sigma offset extent c label) (rho+n+1) sigma
      (TrackedBankReservation.newOffsets M offset extent) hpositive
      (FlatRecursiveSchedulerNativeInvariants.evaluation_internal_initial_unique_markers M x y)
      (FlatRecursiveSchedulerNativeInvariants.evaluation_internal_initial_blank_tails M x y)
      (FlatRecursiveSchedulerNativeInvariants.evaluation_internal_initial_heads_near M x y)
    change (machine M n request resume).step^[q]
      (childFrame M n request resume base rho sigma offset extent c label x y)=
      childInspection M n request resume base rho sigma offset extent c label childWord at hchild
    obtain ⟨r,hr,hresume⟩ := resume_parent_correct M n request resume base rho sigma offset extent c label childWord unique tail
    obtain ⟨p,hp,hparent⟩ := ihparent base rho sigma offset positive
      (evaluation_internal_resumed_unique M n resume c label childWord unique)
      (evaluation_internal_resumed_tail M n resume extent c label childWord tail)
      (evaluation_internal_resumed_near M n resume extent c label childWord)
    change (machine M n request resume).step^[p]
      (resumedFrame M n request resume base rho sigma offset extent c label childWord)=
      inspectionFrame M n request resume base rho sigma offset w at hparent
    refine ⟨p+(r+(q+d)),by dsimp only [callCost,resumeCost] at *; omega,?_⟩
    rw [Function.iterate_add_apply (machine M n request resume).step p (r+(q+d)),
      Function.iterate_add_apply (machine M n request resume).step r (q+d),
      Function.iterate_add_apply (machine M n request resume).step q d,
      hdown,hchild,hresume,hparent]

end IntMul.FlatRecursiveEvaluation


open IntMul IntMul.FlatRecursiveEvaluation IntMul.FlatRecursiveScheduler IntMul.FlatRecursiveCall IntMul.FlatRecursiveReturn IntMul.FlatRecursiveResume

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
  IntMul.FlatRecursiveEvaluation.evaluates_correct M n request resume extent c v w budget evaluation

#print axioms solution
