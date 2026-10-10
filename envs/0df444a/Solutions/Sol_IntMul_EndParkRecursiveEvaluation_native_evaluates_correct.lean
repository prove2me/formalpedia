-- Prove2me | solution 1 for IntMul.EndParkRecursiveEvaluation.native_evaluates_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T04:30:19.975407+00:00
-- url     : https://prove2.me/submissions/2ec6de73-7c4f-45e0-8f80-9b351386130b

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_evaluates_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace IntMul.EndParkRecursiveSchedulerNativeInvariants

open IntMul.TrackedBankedSimulation (extents nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeinvariants_word_letter (M : MultitapeTM) (x y : List Bool) (a : M.Sym)
    (ha : a ∈ inputWord M x y) : a = M.zero ∨ a = M.one ∨ a = M.sep := by
  simp only [inputWord,List.mem_append,List.mem_cons,List.mem_map] at ha
  rcases ha with ⟨b,_,rfl⟩ | (ha | ⟨b,_,rfl⟩)
  · cases b <;> simp [MultitapeTM.bitSym]
  · exact Or.inr (Or.inr ha)
  · cases b <;> simp [MultitapeTM.bitSym]

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeinvariants_word_payload_ne_start (M : MultitapeTM) (x y : List Bool) (p : ℕ) :
    (inputWord M x y).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < (inputWord M x y).length
  · rw [List.getD_eq_getElem _ _ hp]
    have hl := optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeinvariants_word_letter M x y (inputWord M x y)[p] (List.getElem_mem hp)
    aesop
  · rw [List.getD_eq_default _ _ (by omega)]
    aesop

private theorem optimized_native_internal_initial_unique_markers (M : MultitapeTM) (x y : List Bool) :
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
        have h := optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeinvariants_word_payload_ne_start M x y p
        simp only [h,Nat.succ_ne_zero]
      · simp only [if_neg hj,MultitapeTM.tapeOf,List.getD_nil]
        have hd := M.syms_distinct
        simp only [List.nodup_cons,List.mem_cons,not_or] at hd
        aesop

private theorem optimized_native_internal_initial_blank_tails (M : MultitapeTM) (x y : List Bool) :
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

private theorem optimized_native_internal_initial_heads_near (M : MultitapeTM) (x y : List Bool) :
    ∀ j, (M.initCfg x y).head j ≤ initialExtent M x y j + 1 := by
  intro j
  simp [MultitapeTM.initCfg]


end IntMul.EndParkRecursiveSchedulerNativeInvariants



namespace IntMul.EndParkRecursiveScheduler

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerpadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_native_internal_extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem optimized_native_internal_extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem optimized_native_internal_extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem optimized_native_internal_extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem optimized_native_internal_extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem optimized_native_internal_extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem optimized_native_internal_padded_init (N : MultitapeTM) (x y : List Bool) :
    (FixedTapeExtension.machine N).initCfg x y =
      FixedTapeExtension.embed N ((FixedTapeExtension.machine N).initCfg x y) (N.initCfg x y) := by
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerpadding_cfg_ext
  · rfl
  · apply (optimized_native_internal_extension_cells_ready N _ _ ?_).symm
    intro j
    have hzero : FixedTapeExtension.oldTape N j=(FixedTapeExtension.machine N).inTape ↔ j=N.inTape := by
      constructor
      · intro h; apply Fin.ext
        have hv := congrArg (fun i : Fin (N.k+1) => i.val) h
        exact hv
      · intro h; subst j; rfl
    simp only [MultitapeTM.initCfg,hzero]
    split <;> rfl
  · apply (optimized_native_internal_extension_heads_ready N _ _ ?_).symm
    intro j
    rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_native_internal_leafInspection (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (machine M n request resume).Cfg :=
  EndParkRecursiveReturn.inspectionFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1) w

private noncomputable def optimized_native_internal_leafShiftParent (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (TrackedOutputShift.machine M).Cfg where
  state := .rewind
  cells := fun i => (optimized_native_internal_leafInspection M n request resume x y w).cells
    (FixedTapeExtension.oldTape (TrackedOutputShift.machine M) i)
  head := fun i => (optimized_native_internal_leafInspection M n request resume x y w).head
    (FixedTapeExtension.oldTape (TrackedOutputShift.machine M) i)

private noncomputable def optimized_native_internal_leafShiftPadBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg where
  state := .rewind
  cells := (optimized_native_internal_leafInspection M n request resume x y w).cells
  head := (optimized_native_internal_leafInspection M n request resume x y w).head

private noncomputable def optimized_native_internal_leafShiftStart (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedOutputShift.machine M) (optimized_native_internal_leafShiftPadBase M n request resume x y w)
    (TrackedOutputShift.rewindFrame M (optimized_native_internal_leafShiftParent M n request resume x y w) w (w.length+2))

private noncomputable def optimized_native_internal_leafShiftFinal (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) : (finishMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedOutputShift.machine M) (optimized_native_internal_leafShiftPadBase M n request resume x y w)
    (TrackedOutputShift.finalFrame M (optimized_native_internal_leafShiftParent M n request resume x y w) w)

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
  · simp only [TrackedOutputReturn.bufferTape,if_neg hp]

private theorem optimized_native_internal_leaf_shift_old_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    TrackedOutputShift.rewindFrame M (optimized_native_internal_leafShiftParent M n request resume x y w) w (w.length+2)=
      optimized_native_internal_leafShiftParent M n request resume x y w := by
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedOutputShift.rewindFrame]
    by_cases hi : i.val=1
    · simp only [if_pos hi,optimized_native_internal_leafShiftParent,optimized_native_internal_leafInspection,EndParkRecursiveReturn.inspectionFrame,
        FixedTapeExtension.oldTape,dif_pos i.isLt,dif_neg (by omega : ¬2 ≤ i.val),if_pos hi]
      exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_return_idem M _ 1 w
    · simp only [if_neg hi]
  · funext i
    simp only [TrackedOutputShift.rewindFrame]
    by_cases hi : i.val=1
    · simp only [if_pos hi,optimized_native_internal_leafShiftParent,optimized_native_internal_leafInspection,EndParkRecursiveReturn.inspectionFrame,
        FixedTapeExtension.oldTape,dif_pos i.isLt,dif_neg (by omega : ¬2 ≤ i.val),if_pos hi]
      omega
    · simp only [if_neg hi]

private theorem optimized_native_internal_leaf_shift_start_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    relabel M n request resume (.finish .rewind) (optimized_native_internal_leafInspection M n request resume x y w)=
      liftFinish M n request resume (optimized_native_internal_leafShiftStart M n request resume x y w) := by
  rw [optimized_native_internal_leafShiftStart,optimized_native_internal_leaf_shift_old_ready]
  have hp : FixedTapeExtension.embed (TrackedOutputShift.machine M)
      (optimized_native_internal_leafShiftPadBase M n request resume x y w) (optimized_native_internal_leafShiftParent M n request resume x y w)=
      optimized_native_internal_leafShiftPadBase M n request resume x y w := by
    apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_cfg_ext
    · rfl
    · apply optimized_native_internal_extension_cells_ready
      intro j
      rfl
    · apply optimized_native_internal_extension_heads_ready
      intro j
      rfl
  rw [hp]
  rfl

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_initial_zero (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) :
    (N.initCfg x y).cells i 0=N.startSym := by
  simp only [MultitapeTM.initCfg]
  split <;> rfl

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_initial_empty (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) (hi : i.val ≠ 0) :
    (N.initCfg x y).cells i=N.tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem optimized_native_internal_leaf_stack_root (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (optimized_native_internal_leafInspection M n request resume x y w).cells (stackTape M)
      ((optimized_native_internal_leafInspection M n request resume x y w).head (stackTape M))=none := by
  have hi : ¬(stackTape M).val < M.k+2 := by change ¬M.k+2 < M.k+2; omega
  simp only [optimized_native_internal_leafInspection,EndParkRecursiveReturn.inspectionFrame,dif_neg hi,Nat.sub_self,
    FiniteContinuationStack.freshTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
  exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_initial_zero _ _ _ _

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_output_base_eq (M : MultitapeTM) (a b : ℕ → Sym M) (w : List Bool) (h : a 0=b 0) :
    TrackedOutputShift.outputTape M a w=TrackedOutputShift.outputTape M b w := by
  funext p
  by_cases hp : p=0
  · subst p
    simp only [TrackedOutputShift.outputTape,if_true,h]
  · simp only [TrackedOutputShift.outputTape,if_neg hp]

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_fresh_native (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y : List Bool) (i : Fin (M.k+3)) (hi : i.val ≠ 0) :
    TrackedBankCleanup.freshTape M (((machine M n request resume).initCfg x y).cells i) 1=
      ((machine M n request resume).initCfg x y).cells i := by
  rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_initial_empty (machine M n request resume) x y i hi]
  funext p
  cases p with
  | zero => rfl
  | succ p => simp [TrackedBankCleanup.freshTape,MultitapeTM.tapeOf]

private theorem optimized_native_internal_leaf_final_native (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    relabel M n request resume .halt (liftFinish M n request resume (optimized_native_internal_leafShiftFinal M n request resume x y w))=
      nativeFinalFrame M n request resume x y w := by
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    simp only [relabel,liftFinish,optimized_native_internal_leafShiftFinal,FixedTapeExtension.embed,nativeFinalFrame]
    by_cases hb : i.val=1
    · have hi : i.val < M.k+2 := by have := M.two_le_k; omega
      simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_pos hb]
      have hzero : (optimized_native_internal_leafShiftParent M n request resume x y w).cells ⟨i.val,hi⟩ 0=
          ((machine M n request resume).initCfg x y).cells i 0 := by
        simp only [optimized_native_internal_leafShiftParent,optimized_native_internal_leafInspection,EndParkRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi,dif_neg (by omega : ¬2 ≤ i.val),if_pos hb,
          TrackedOutputReturn.bufferTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
      exact congrFun (optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_output_base_eq M _ _ w hzero) p
    · simp only [if_neg hb]
      by_cases hi : i.val < M.k+2
      · simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_neg hb,
          optimized_native_internal_leafShiftParent,optimized_native_internal_leafInspection,EndParkRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi]
        by_cases hw : 2 ≤ i.val
        · simp only [dif_pos hw,nativeBase]
          exact congrFun (optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_fresh_native M n request resume x y i (by omega)) p
        · simp only [dif_neg hw,if_neg hb,nativeBase]
      · simp only [dif_neg hi,optimized_native_internal_leafShiftPadBase,optimized_native_internal_leafInspection,EndParkRecursiveReturn.inspectionFrame,
          dif_neg hi,nativeBase]
        change TrackedBankCleanup.freshTape M (((machine M n request resume).initCfg x y).cells i) 1 p=_
        exact congrFun (optimized_native_internal_solutions_intmulendparkrecursiveschedulerleafframes_fresh_native M n request resume x y i (by omega)) p
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    simp only [relabel,liftFinish,optimized_native_internal_leafShiftFinal,FixedTapeExtension.embed,nativeFinalFrame]
    by_cases hi : i.val < M.k+2
    · have hs : i≠stackTape M := by
        intro h; have hv := congrArg Fin.val h
        simp only [stackTape,FiniteContinuationStack.stackTape] at hv
        omega
      simp only [dif_pos hi,TrackedOutputShift.finalFrame,FixedTapeExtension.innerTape,if_neg hs]
      by_cases hb : i.val=1
      · simp only [if_pos hb,if_neg (by omega : i.val ≠ 0)]
      · simp only [if_neg hb,optimized_native_internal_leafShiftParent,optimized_native_internal_leafInspection,EndParkRecursiveReturn.inspectionFrame,
          FixedTapeExtension.oldTape,dif_pos hi]
        by_cases hw : 2 ≤ i.val
        · simp only [dif_pos hw,if_neg (by omega : i.val ≠ 0)]
        · have hz : i.val=0 := by omega
          simp only [dif_neg hw,if_neg hb,nativeBase,if_pos hz]
    · have hs : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      simp only [dif_neg hi,optimized_native_internal_leafShiftPadBase,optimized_native_internal_leafInspection,EndParkRecursiveReturn.inspectionFrame,
        dif_neg hi,Nat.sub_self,if_neg (by omega : i.val ≠ 0),if_neg (by omega : i.val ≠ 1),if_pos hs]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem optimized_native_internal_boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]
  · simp only [MultitapeTM.step,liftBoot,ht]

private theorem optimized_native_internal_boot_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((bootMachine M).step^[s] c).state≠(bootMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_native_internal_boot_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_boot_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (T : ℕ)
    (exit : ((bootMachine M).step^[T] c).state=(bootMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_boot_iterate M n request resume c s hlive,he]

private theorem optimized_native_internal_preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]
  · simp only [MultitapeTM.step,liftPreparation,ht]

private theorem optimized_native_internal_preparation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((preparationMachine M).step^[s] c).state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_native_internal_preparation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_preparation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (T : ℕ)
    (exit : ((preparationMachine M).step^[T] c).state=(preparationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_preparation_iterate M n request resume c s hlive,he]

private theorem optimized_native_internal_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,no_request]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]

private theorem optimized_native_internal_body_iterate (M : MultitapeTM) (n : ℕ)
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
      optimized_native_internal_body_step M n request resume _ (live T (by omega)) (no_request T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_body_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (T : ℕ)
    (exit : ((bodyMachine M).step^[T] c).state=(bodyMachine M).qHalt)
    (no_request : ∀ s, s < T → request (((bodyMachine M).step^[s] c).state)=none) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem optimized_native_internal_input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]
  · simp only [MultitapeTM.step,liftInput,ht]

private theorem optimized_native_internal_input_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((inputMachine M).step^[s] c).state≠(inputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_native_internal_input_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_input_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (T : ℕ)
    (exit : ((inputMachine M).step^[T] c).state=(inputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_input_iterate M n request resume label c s hlive,he]

private theorem optimized_native_internal_reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]
  · simp only [MultitapeTM.step,liftReservation,ht]

private theorem optimized_native_internal_reservation_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((reservationMachine M).step^[s] c).state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_native_internal_reservation_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_reservation_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (T : ℕ)
    (exit : ((reservationMachine M).step^[T] c).state=(reservationMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_reservation_iterate M n request resume c s hlive,he]

private theorem optimized_native_internal_return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]
  · simp only [MultitapeTM.step,liftReturn,ht]

private theorem optimized_native_internal_return_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((returnMachine M).step^[s] c).state≠(returnMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_native_internal_return_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_return_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (T : ℕ)
    (exit : ((returnMachine M).step^[T] c).state=(returnMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_return_iterate M n request resume c s hlive,he]

private theorem optimized_native_internal_cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]
  · simp only [MultitapeTM.step,liftCleanup,ht]

private theorem optimized_native_internal_cleanup_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((cleanupMachine M).step^[s] c).state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_native_internal_cleanup_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_cleanup_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (T : ℕ)
    (exit : ((cleanupMachine M).step^[T] c).state=(cleanupMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_cleanup_iterate M n request resume c s hlive,he]

private theorem optimized_native_internal_output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem optimized_native_internal_output_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_native_internal_output_step M n request resume label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_output_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_output_iterate M n request resume label c s hlive,he]

private theorem optimized_native_internal_finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_cfg_ext
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]
  · simp only [MultitapeTM.step,liftFinish,ht]

private theorem optimized_native_internal_finish_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((finishMachine M).step^[s] c).state≠(finishMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      optimized_native_internal_finish_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem optimized_native_internal_finish_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (T : ℕ)
    (exit : ((finishMachine M).step^[T] c).state=(finishMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [optimized_native_internal_finish_iterate M n request resume c s hlive,he]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerdispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerdispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerdispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
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

private theorem optimized_native_internal_stay_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,fun i => (c.cells i (c.head i),.stay))) :
    (machine M n request resume).step c=relabel M n request resume q c := by
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerdispatch_cfg_ext
  · simp only [MultitapeTM.step,ht,relabel]
  · simp only [MultitapeTM.step,ht,relabel]
    funext i
    rw [Function.update_eq_self]
  · simp only [MultitapeTM.step,ht,relabel]

private theorem optimized_native_internal_right_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .right)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape+1) := by
  classical
  rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulerdispatch_right_actions] at ht
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerdispatch_cfg_ext
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

private theorem optimized_native_internal_left_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (q : State M n) (tape : Fin (M.k+3))
    (present : c.cells tape (c.head tape)≠none)
    (ht : transition M n request resume c.state (fun i => c.cells i (c.head i))=
      (q,moveActions M (fun i => c.cells i (c.head i)) tape .left)) :
    (machine M n request resume).step c=headFrame M n request resume q c tape (c.head tape-1) := by
  classical
  rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulerdispatch_left_actions M _ tape present] at ht
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerdispatch_cfg_ext
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

private theorem optimized_native_internal_boot_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (exit : c.state=(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=headFrame M n request resume (.preparation .mark) (liftBoot M n request resume c) (stackTape M) (c.head (stackTape M)+1) := by
  apply optimized_native_internal_right_step
  change transition M n request resume (.boot c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply optimized_native_internal_left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,call]
  all_goals try rfl

private theorem optimized_native_internal_push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos exit]
  all_goals try rfl

private theorem optimized_native_internal_pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply optimized_native_internal_stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,exit]
  all_goals try rfl

private theorem optimized_native_internal_inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply optimized_native_internal_stay_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,FlatRecursiveScheduler.stackTape,reduceCtorEq,if_false,if_pos root]
  all_goals try rfl

private theorem optimized_native_internal_inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply optimized_native_internal_right_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,FlatRecursiveScheduler.stackTape,reduceCtorEq,if_false,if_neg parent]
  all_goals try rfl

private theorem optimized_native_internal_reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  have hm : c.cells (FlatRecursiveScheduler.bufferTape M) (c.head (FlatRecursiveScheduler.bufferTape M))=some (M.startSym,true) := marker
  apply optimized_native_internal_right_step
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_pos hm]
  rfl

private theorem optimized_native_internal_reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  have hm : c.cells (FlatRecursiveScheduler.bufferTape M) (c.head (FlatRecursiveScheduler.bufferTape M))≠some (M.startSym,true) := marker
  apply optimized_native_internal_left_step M n request resume _ _ _ present
  change transition M n request resume c.state _=_
  simp only [transition,phase,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg hm]
  rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler

private theorem optimized_native_internal_eval_native_finish_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    ∃ t, t ≤ 4*w.length+5 ∧
      (machine M n request resume).step^[t]
        (liftFinish M n request resume (optimized_native_internal_leafShiftStart M n request resume x y w))=
        nativeFinalFrame M n request resume x y w := by
  have hr : (finishMachine M).step^[4*w.length+4] (optimized_native_internal_leafShiftStart M n request resume x y w)=
      optimized_native_internal_leafShiftFinal M n request resume x y w := by
    have h := (FixedTapeExtension.simulate_run (TrackedOutputShift.machine M)
      (optimized_native_internal_leafShiftPadBase M n request resume x y w)
      (TrackedOutputShift.rewindFrame M (optimized_native_internal_leafShiftParent M n request resume x y w) w (w.length+2))
      (4*w.length+4)).1
    rw [TrackedOutputShift.shift_correct] at h
    exact h
  have he : ((finishMachine M).step^[4*w.length+4]
      (optimized_native_internal_leafShiftStart M n request resume x y w)).state=(finishMachine M).qHalt := by
    rw [hr]
    rfl
  obtain ⟨s,hsclock,hsrun⟩ := optimized_native_internal_finish_to_halt M n request resume
    (optimized_native_internal_leafShiftStart M n request resume x y w) (4*w.length+4) he
  rw [hr] at hsrun
  refine ⟨s+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',hsrun,optimized_native_internal_finish_dispatch M n request resume _ rfl,optimized_native_internal_leaf_final_native]

private theorem optimized_native_internal_eval_native_root_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    ∃ t, t ≤ 4*w.length+6 ∧
      (machine M n request resume).step^[t] (optimized_native_internal_leafInspection M n request resume x y w)=
        nativeFinalFrame M n request resume x y w := by
  obtain ⟨s,hs,hr⟩ := optimized_native_internal_eval_native_finish_correct M n request resume x y w
  refine ⟨s+1,by omega,?_⟩
  rw [Function.iterate_succ_apply,optimized_native_internal_inspect_root_dispatch M n request resume _ rfl
    (optimized_native_internal_leaf_stack_root M n request resume x y w),optimized_native_internal_leaf_shift_start_ready,hr]

private theorem optimized_native_internal_eval_native_final_output (M : MultitapeTM) (n : ℕ)
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

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_native_internal_bootFinal (M : MultitapeTM) (x y : List Bool) : (bootMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedRootInputCopy.machine M)
    ((bootMachine M).initCfg x y) (TrackedRootInputCopy.finalFrame M x y)

private noncomputable def optimized_native_internal_rootPreparationBase (M : MultitapeTM) (x y : List Bool) :
    (TrackedBankPreparation.machine M).Cfg where
  state := .mark
  cells := (TrackedRootInputCopy.finalFrame M x y).cells
  head := (TrackedRootInputCopy.finalFrame M x y).head

private noncomputable def optimized_native_internal_rootPreparationPadBase (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg where
  state := .mark
  cells := (optimized_native_internal_bootFinal M x y).cells
  head := Function.update (optimized_native_internal_bootFinal M x y).head (stackTape M) 1

private noncomputable def optimized_native_internal_rootPreparationStart (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M) (optimized_native_internal_rootPreparationPadBase M x y)
    (TrackedBankPreparation.initialFrame M (optimized_native_internal_rootPreparationBase M x y) 1 (fun _ => 1) x y)

private noncomputable def optimized_native_internal_rootPreparationFinal (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M) (optimized_native_internal_rootPreparationPadBase M x y)
    (TrackedBankPreparation.readyFrame M (optimized_native_internal_rootPreparationBase M x y) 1 (fun _ => 1) x y)

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_source_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) :
    TrackedBankPreparation.sourceTape M (TrackedBankPreparation.sourceTape M base sigma w) sigma w =
      TrackedBankPreparation.sourceTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedBankPreparation.sourceTape,if_pos hp]
  · simp only [TrackedBankPreparation.sourceTape,if_neg hp]

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_fresh_native (M : MultitapeTM) :
    TrackedBankPreparation.freshTape M ((TrackedRootInputCopy.machine M).tapeOf []) 1 =
      (TrackedRootInputCopy.machine M).tapeOf [] := by
  funext p
  cases p with
  | zero => rfl
  | succ p => simp [TrackedBankPreparation.freshTape,MultitapeTM.tapeOf]

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_root_initial_empty (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k+2)) (hi : i.val ≠ 0) :
    ((TrackedRootInputCopy.machine M).initCfg x y).cells i = (TrackedRootInputCopy.machine M).tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem optimized_native_internal_root_preparation_ready (M : MultitapeTM) (x y : List Bool) :
    TrackedBankPreparation.initialFrame M (optimized_native_internal_rootPreparationBase M x y) 1 (fun _ => 1) x y=
      optimized_native_internal_rootPreparationBase M x y := by
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedBankPreparation.initialFrame,optimized_native_internal_rootPreparationBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,
        if_neg (by omega : i.val ≠ 1)]
      rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_root_initial_empty M x y i (by omega)]
      exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_fresh_native M
    · simp only [dif_neg hw]
      by_cases hi : i.val=1
      · simp only [if_pos hi,TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,
          if_pos hi,List.take_length]
        exact optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_source_idem M _ 1 _
      · simp only [if_neg hi]
  · funext i
    simp only [TrackedBankPreparation.initialFrame,optimized_native_internal_rootPreparationBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedRootInputCopy.finalFrame,if_neg (by omega : i.val ≠ 0)]
    · simp only [dif_neg hw]
      by_cases hi : i.val=1
      · simp only [if_pos hi,TrackedRootInputCopy.finalFrame,if_neg (by omega : i.val ≠ 0)]
      · simp only [if_neg hi]

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_old_ne_stack (M : MultitapeTM) (j : Fin (M.k+2)) :
    FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) j ≠ stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,stackTape,FiniteContinuationStack.stackTape] at h
  omega

private theorem optimized_native_internal_root_preparation_start_ready (M : MultitapeTM) (x y : List Bool) :
    optimized_native_internal_rootPreparationStart M x y=optimized_native_internal_rootPreparationPadBase M x y := by
  rw [optimized_native_internal_rootPreparationStart,optimized_native_internal_root_preparation_ready]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_cfg_ext
  · rfl
  · apply optimized_native_internal_extension_cells_ready
    intro j
    change (FixedTapeExtension.embed (TrackedRootInputCopy.machine M)
      ((bootMachine M).initCfg x y) (TrackedRootInputCopy.finalFrame M x y)).cells
      (FixedTapeExtension.oldTape (TrackedRootInputCopy.machine M) j)=_
    rw [optimized_native_internal_extension_old_cells]
    rfl
  · apply optimized_native_internal_extension_heads_ready
    intro j
    simp only [optimized_native_internal_rootPreparationPadBase,Function.update_of_ne (optimized_native_internal_solutions_intmulendparkrecursiveschedulerbootstrapframes_old_ne_stack M j),optimized_native_internal_bootFinal]
    change (FixedTapeExtension.embed (TrackedRootInputCopy.machine M)
      ((bootMachine M).initCfg x y) (TrackedRootInputCopy.finalFrame M x y)).head
      (FixedTapeExtension.oldTape (TrackedRootInputCopy.machine M) j)=_
    rw [optimized_native_internal_extension_old_heads]
    rfl

private theorem optimized_native_internal_boot_final_stack_head (M : MultitapeTM) (x y : List Bool) :
    (optimized_native_internal_bootFinal M x y).head (stackTape M)=0 := by
  change (optimized_native_internal_bootFinal M x y).head (FixedTapeExtension.extraTape (TrackedRootInputCopy.machine M))=0
  rw [optimized_native_internal_bootFinal,optimized_native_internal_extension_extra_heads]
  rfl

private theorem optimized_native_internal_boot_dispatch_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    headFrame M n request resume (.preparation .mark) (liftBoot M n request resume (optimized_native_internal_bootFinal M x y))
      (stackTape M) ((optimized_native_internal_bootFinal M x y).head (stackTape M)+1)=
        liftPreparation M n request resume (optimized_native_internal_rootPreparationStart M x y) := by
  rw [optimized_native_internal_boot_final_stack_head,optimized_native_internal_root_preparation_start_ready]
  rfl

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_bank_empty_buffer (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) :
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

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
  · simp only [TrackedOutputReturn.bufferTape,if_neg hp]

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_zero (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) :
    (N.initCfg x y).cells i 0=N.startSym := by
  simp only [MultitapeTM.initCfg]
  split <;> rfl

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_empty (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) (hi : i.val ≠ 0) :
    (N.initCfg x y).cells i=N.tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_root_final_zero (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k+2)) :
    (TrackedRootInputCopy.finalFrame M x y).cells i 0=none := by
  simp only [TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame]
  by_cases hi : i.val=1
  · simp only [if_pos hi,TrackedBankPreparation.sourceTape,if_pos (by omega : (0 : ℕ) < 1)]
    exact optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_zero _ _ _ _
  · simp only [if_neg hi]
    exact optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_zero _ _ _ _

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_native_old_cells (M : MultitapeTM) (n : ℕ)
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

private theorem optimized_native_internal_root_preparation_buffer (M : MultitapeTM) (x y : List Bool) :
    (optimized_native_internal_rootPreparationFinal M x y).cells (bufferTape M)=
      TrackedOutputReturn.bufferTape M ((optimized_native_internal_rootPreparationFinal M x y).cells (bufferTape M)) 1 [] ∧
    (optimized_native_internal_rootPreparationFinal M x y).head (bufferTape M)=1+(TrackedBankPreparation.inputWord M x y).length+1 := by
  have hc : (optimized_native_internal_rootPreparationFinal M x y).cells (bufferTape M)=
      TrackedBankPreparation.bankTape M
        ((optimized_native_internal_rootPreparationBase M x y).cells ⟨1,by change 1 < M.k+2; omega⟩) 1 [] := by
    change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) (optimized_native_internal_rootPreparationPadBase M x y)
      (TrackedBankPreparation.readyFrame M (optimized_native_internal_rootPreparationBase M x y) 1 (fun _ => 1) x y)).cells
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [optimized_native_internal_extension_old_cells]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]
  constructor
  · rw [hc,optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_bank_empty_buffer]
    exact (optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_return_idem M _ 1 []).symm
  · change (FixedTapeExtension.embed (TrackedBankPreparation.machine M) (optimized_native_internal_rootPreparationPadBase M x y)
      (TrackedBankPreparation.readyFrame M (optimized_native_internal_rootPreparationBase M x y) 1 (fun _ => 1) x y)).head
      (FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
    rw [optimized_native_internal_extension_old_heads]
    simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
      dif_neg (by omega : ¬2 ≤ (1 : ℕ)),TrackedBankPreparation.callerBase,if_true]

private theorem optimized_native_internal_root_body_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    headFrame M n request resume (.body M.qStart)
      (relabel M n request resume .resetBuffer (liftPreparation M n request resume (optimized_native_internal_rootPreparationFinal M x y)))
      (bufferTape M) 2 =
    bodyFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1)
      (TrackedBankPreparation.initialExtent M x y) (M.initCfg x y) [] := by
  classical
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    simp only [headFrame,relabel,liftPreparation,optimized_native_internal_rootPreparationFinal,bodyFrame,liftBody,
      FixedTapeExtension.embed]
    by_cases hi : i.val < M.k+2
    · simp only [dif_pos hi]
      simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
        TrackedBankPreparation.callerBase,parentBase,optimized_native_internal_rootPreparationBase,
        FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
      by_cases hw : 2 ≤ i.val
      · simp only [dif_pos hw]
        by_cases hp : p < 1
        · have hp0 : p=0 := by omega
          subst p
          simp only [if_pos (by omega : (0 : ℕ) < 1),if_neg (by omega : i.val ≠ 1),nativeBase]
          rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_root_final_zero,optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_zero]
        · simp only [if_neg hp]
      · simp only [dif_neg hw]
        by_cases hb : i.val=1
        · simp only [if_pos hb]
          rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_bank_empty_buffer]
          by_cases hp : p < 1
          · have hp0 : p=0 := by omega
            subst p
            simp only [TrackedOutputReturn.bufferTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
            rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_root_final_zero,optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_zero]
          · simp only [TrackedOutputReturn.bufferTape,if_neg hp]
        · simp only [if_neg hb]
          simp only [TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,if_neg hb,nativeBase]
          exact congrFun (optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_native_old_cells M n request resume x y ⟨i.val,hi⟩) p
    · simp only [dif_neg hi]
      have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      simp only [optimized_native_internal_rootPreparationPadBase,optimized_native_internal_bootFinal,FixedTapeExtension.embed,
        dif_neg hi,stackBase,if_true,nativeBase]
      cases p with
      | zero =>
        simp only [FiniteContinuationStack.freshTape,if_pos (by omega : (0 : ℕ) < 1)]
        rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_zero,optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_zero]
      | succ p =>
        rw [optimized_native_internal_solutions_intmulendparkrecursiveschedulernativeframes_initial_empty (bootMachine M) x y (stackTape M) (by change M.k+2 ≠ 0; omega)]
        simp only [MultitapeTM.tapeOf,List.getD_nil,FiniteContinuationStack.freshTape,
          if_neg (by omega : ¬p+1 < 1)]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    simp only [headFrame,relabel,liftPreparation,optimized_native_internal_rootPreparationFinal,bodyFrame,liftBody,
      FixedTapeExtension.embed]
    by_cases hb : i=bufferTape M
    · subst i
      simp [bufferTape,TrackedBankedSimulation.embed,parentBase,FixedTapeExtension.innerTape]
    · rw [Function.update_of_ne hb]
      by_cases hi : i.val < M.k+2
      · simp only [dif_pos hi]
        simp only [TrackedBankPreparation.readyFrame,TrackedBankedSimulation.embed,
          TrackedBankPreparation.callerBase,parentBase,optimized_native_internal_rootPreparationBase,
          FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        by_cases hw : 2 ≤ i.val
        · simp [dif_pos hw,MultitapeTM.initCfg]
        · have hn : i.val ≠ 1 := by intro h; exact hb (Fin.ext h)
          have hz : i.val=0 := by omega
          simp only [dif_neg hw,if_neg hn,TrackedRootInputCopy.finalFrame,nativeBase,if_pos hz]
      · simp only [dif_neg hi]
        have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
        subst i
        simp [optimized_native_internal_rootPreparationPadBase,stackBase]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerreset_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def optimized_native_internal_resetFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ) : (machine M n request resume).Cfg where
  state := .resetBuffer
  cells := c.cells
  head := Function.update c.head (bufferTape M) (sigma+(a-r))

private theorem optimized_native_internal_solutions_intmulendparkrecursiveschedulerreset_empty_return_scan (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (sigma p : ℕ) : TrackedOutputReturn.bufferTape M base sigma [] (sigma+p)=
      if p=0 then some (M.startSym,true) else some (M.blank,false) := by
  cases p with
  | zero => simp [TrackedOutputReturn.bufferTape]
  | succ p => simp [TrackedOutputReturn.bufferTape,show ¬sigma+(p+1) < sigma by omega,
      show sigma+(p+1)≠sigma by omega]

private theorem optimized_native_internal_reset_scan (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (optimized_native_internal_resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((optimized_native_internal_resetFrame M n request resume c sigma a r).head (bufferTape M))=
        if a ≤ r then some (M.startSym,true) else some (M.blank,false) := by
  simp only [optimized_native_internal_resetFrame,Function.update_self]
  rw [empty,optimized_native_internal_solutions_intmulendparkrecursiveschedulerreset_empty_return_scan]
  split_ifs <;> first | rfl | omega

private theorem optimized_native_internal_reset_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r < a) :
    (machine M n request resume).step (optimized_native_internal_resetFrame M n request resume c sigma a r)=
      optimized_native_internal_resetFrame M n request resume c sigma a (r+1) := by
  have hscan := optimized_native_internal_reset_scan M n request resume c sigma a r empty
  rw [if_neg (by omega : ¬a ≤ r)] at hscan
  have hm : (optimized_native_internal_resetFrame M n request resume c sigma a r).cells (bufferTape M)
      ((optimized_native_internal_resetFrame M n request resume c sigma a r).head (bufferTape M))≠some (M.startSym,true) := by
    rw [hscan]
    intro h
    have h := congrArg Prod.snd (Option.some.inj h)
    cases h
  rw [optimized_native_internal_reset_live_step M n request resume _ rfl hm (by rw [hscan]; exact Option.some_ne_none _)]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,optimized_native_internal_resetFrame,Function.update_self,Function.update_idem]
    congr 1
    omega

private theorem optimized_native_internal_reset_run (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma [])
    (hr : r ≤ a) :
    (machine M n request resume).step^[r] (optimized_native_internal_resetFrame M n request resume c sigma a 0)=
      optimized_native_internal_resetFrame M n request resume c sigma a r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),optimized_native_internal_reset_step M n request resume c sigma a r empty (by omega)]

private theorem optimized_native_internal_reset_complete (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a : ℕ)
    (phase : c.state=.resetBuffer) (head : c.head (bufferTape M)=sigma+a)
    (empty : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) sigma []) :
    (machine M n request resume).step^[a+1] c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (sigma+1) := by
  have hstart : c=optimized_native_internal_resetFrame M n request resume c sigma a 0 := by
    apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerreset_cfg_ext
    · exact phase
    · rfl
    · simp only [optimized_native_internal_resetFrame,Nat.sub_zero,←head]
      exact (Function.update_eq_self _ _).symm
  rw [hstart,Function.iterate_succ_apply',optimized_native_internal_reset_run M n request resume _ sigma a a empty le_rfl]
  have hm := optimized_native_internal_reset_scan M n request resume c sigma a a empty
  rw [if_pos le_rfl] at hm
  rw [optimized_native_internal_reset_marker_dispatch M n request resume _ rfl hm]
  apply optimized_native_internal_solutions_intmulendparkrecursiveschedulerreset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,optimized_native_internal_resetFrame,Nat.sub_self,Nat.add_zero,Function.update_self,Function.update_idem]

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankPreparation (inputWord initialExtent)

private theorem optimized_native_internal_bootstrap_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    ∃ t, t ≤ 5*(inputWord M x y).length+12 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        bodyFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1)
          (initialExtent M x y) (M.initCfg x y) [] := by
  let L := (inputWord M x y).length
  have hboot : (bootMachine M).step^[2*L+5] ((bootMachine M).initCfg x y)=optimized_native_internal_bootFinal M x y := by
    have hr := (FixedTapeExtension.simulate_run (TrackedRootInputCopy.machine M)
      ((bootMachine M).initCfg x y) ((TrackedRootInputCopy.machine M).initCfg x y) (2*L+5)).1
    rw [←optimized_native_internal_padded_init,TrackedRootInputCopy.copy_correct] at hr
    exact hr
  have hb : ((bootMachine M).step^[2*L+5] ((bootMachine M).initCfg x y)).state=(bootMachine M).qHalt := by
    rw [hboot]
    rfl
  obtain ⟨b,hbclock,hbrun⟩ := optimized_native_internal_boot_to_halt M n request resume ((bootMachine M).initCfg x y) (2*L+5) hb
  rw [hboot] at hbrun
  have hbstart : liftBoot M n request resume ((bootMachine M).initCfg x y)=
      (machine M n request resume).initCfg x y := rfl
  rw [hbstart] at hbrun
  have hdispatch : (machine M n request resume).step^[b+1] ((machine M n request resume).initCfg x y)=
      liftPreparation M n request resume (optimized_native_internal_rootPreparationStart M x y) := by
    rw [Function.iterate_succ_apply',hbrun,optimized_native_internal_boot_dispatch M n request resume _ rfl,optimized_native_internal_boot_dispatch_ready]
  have hprep : (preparationMachine M).step^[2*L+3] (optimized_native_internal_rootPreparationStart M x y)=
      optimized_native_internal_rootPreparationFinal M x y := by
    have hr := (FixedTapeExtension.simulate_run (TrackedBankPreparation.machine M)
      (optimized_native_internal_rootPreparationPadBase M x y)
      (TrackedBankPreparation.initialFrame M (optimized_native_internal_rootPreparationBase M x y) 1 (fun _ => 1) x y)
      (2*L+3)).1
    rw [TrackedBankPreparation.setup_correct] at hr
    exact hr
  have hp : ((preparationMachine M).step^[2*L+3] (optimized_native_internal_rootPreparationStart M x y)).state=(preparationMachine M).qHalt := by
    rw [hprep]
    rfl
  obtain ⟨p,hpclock,hprun⟩ := optimized_native_internal_preparation_to_halt M n request resume (optimized_native_internal_rootPreparationStart M x y) (2*L+3) hp
  rw [hprep] at hprun
  let c := relabel M n request resume .resetBuffer
    (liftPreparation M n request resume (optimized_native_internal_rootPreparationFinal M x y))
  have hreset : (machine M n request resume).step^[p+1+(b+1)] ((machine M n request resume).initCfg x y)=c := by
    rw [Function.iterate_add_apply,hdispatch,Function.iterate_succ_apply',hprun,
      optimized_native_internal_preparation_dispatch M n request resume _ rfl]
  have hc : c.head (bufferTape M)=1+(L+1) := by
    change (optimized_native_internal_rootPreparationFinal M x y).head (bufferTape M)=1+(L+1)
    have h := (optimized_native_internal_root_preparation_buffer M x y).2
    dsimp only [L]
    omega
  have he : c.cells (bufferTape M)=TrackedOutputReturn.bufferTape M (c.cells (bufferTape M)) 1 [] :=
    (optimized_native_internal_root_preparation_buffer M x y).1
  have hr := optimized_native_internal_reset_complete M n request resume c 1 (L+1) rfl hc he
  have hready := optimized_native_internal_root_body_ready M n request resume x y
  refine ⟨(L+2)+(p+1+(b+1)),by dsimp only [L] at *; omega,?_⟩
  rw [Function.iterate_add_apply,hreset,hr]
  exact hready

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- Complete native execution of any finite recursive evaluation through
one depth-independent finite machine with exactly M.k+3 tapes. -/
private theorem native_evaluates_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y w : List Bool) (budget : ℕ)
    (evaluation : Evaluates M n request resume (initialExtent M x y) (M.initCfg x y) [] w budget) :
    ∃ t, t≤ budget+5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        nativeFinalFrame M n request resume x y w ∧
      (machine M n request resume).HaltsWithOutput x y t w := by
  obtain ⟨b,hb,hboot⟩ := optimized_native_internal_bootstrap_correct M n request resume x y
  obtain ⟨q,hq,heval⟩ := evaluates_correct M n request resume (initialExtent M x y) (M.initCfg x y) [] w budget evaluation
    (nativeBase M n request resume x y) 1 1 (fun _ => 1) (by intro j; omega)
    (EndParkRecursiveSchedulerNativeInvariants.optimized_native_internal_initial_unique_markers M x y)
    (EndParkRecursiveSchedulerNativeInvariants.optimized_native_internal_initial_blank_tails M x y)
    (EndParkRecursiveSchedulerNativeInvariants.optimized_native_internal_initial_heads_near M x y)
  change (machine M n request resume).step^[q]
    (bodyFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1)
      (initialExtent M x y) (M.initCfg x y) [])=optimized_native_internal_leafInspection M n request resume x y w at heval
  obtain ⟨f,hf,hfinish⟩ := optimized_native_internal_eval_native_root_correct M n request resume x y w
  have hrun : (machine M n request resume).step^[f+(q+b)] ((machine M n request resume).initCfg x y)=
      nativeFinalFrame M n request resume x y w := by
    rw [Function.iterate_add_apply (machine M n request resume).step f (q+b),
      Function.iterate_add_apply (machine M n request resume).step q b,hboot,heval,hfinish]
  refine ⟨f+(q+b),by omega,hrun,?_⟩
  unfold MultitapeTM.HaltsWithOutput
  rw [hrun]
  exact ⟨rfl,optimized_native_internal_eval_native_final_output M n request resume x y w⟩

end IntMul.EndParkRecursiveEvaluation


open IntMul IntMul.EndParkRecursiveEvaluation IntMul.EndParkRecursiveScheduler IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y w : List Bool) (budget : ℕ)
    (evaluation : Evaluates M n request resume (initialExtent M x y) (M.initCfg x y) [] w budget) :
    ∃ t, t≤budget+5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        nativeFinalFrame M n request resume x y w ∧
      (machine M n request resume).HaltsWithOutput x y t w :=
  IntMul.EndParkRecursiveEvaluation.native_evaluates_correct M n request resume x y w budget evaluation

#print axioms solution
