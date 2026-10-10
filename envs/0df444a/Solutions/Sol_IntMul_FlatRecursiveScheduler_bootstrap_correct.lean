-- Prove2me | solution 1 for IntMul.FlatRecursiveScheduler.bootstrap_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T02:01:40.604724+00:00
-- url     : https://prove2.me/submissions/d98c9b3b-6aea-4d58-85c7-b7a1cbadf416

import Definitions.Def_IntMul_FlatRecursiveScheduler
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic


namespace IntMul.FlatRecursiveScheduler

private theorem padding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
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
  apply padding_cfg_ext
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

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

private theorem bootstrapframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

noncomputable def bootFinal (M : MultitapeTM) (x y : List Bool) : (bootMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedRootInputCopy.machine M)
    ((bootMachine M).initCfg x y) (TrackedRootInputCopy.finalFrame M x y)

noncomputable def rootPreparationBase (M : MultitapeTM) (x y : List Bool) :
    (TrackedBankPreparation.machine M).Cfg where
  state := .mark
  cells := (TrackedRootInputCopy.finalFrame M x y).cells
  head := (TrackedRootInputCopy.finalFrame M x y).head

noncomputable def rootPreparationPadBase (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg where
  state := .mark
  cells := (bootFinal M x y).cells
  head := Function.update (bootFinal M x y).head (stackTape M) 1

noncomputable def rootPreparationStart (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M) (rootPreparationPadBase M x y)
    (TrackedBankPreparation.initialFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y)

noncomputable def rootPreparationFinal (M : MultitapeTM) (x y : List Bool) : (preparationMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankPreparation.machine M) (rootPreparationPadBase M x y)
    (TrackedBankPreparation.readyFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y)

private theorem bootstrapframes_source_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) :
    TrackedBankPreparation.sourceTape M (TrackedBankPreparation.sourceTape M base sigma w) sigma w =
      TrackedBankPreparation.sourceTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedBankPreparation.sourceTape,if_pos hp]
  · simp only [TrackedBankPreparation.sourceTape,if_neg hp]

private theorem bootstrapframes_fresh_native (M : MultitapeTM) :
    TrackedBankPreparation.freshTape M ((TrackedRootInputCopy.machine M).tapeOf []) 1 =
      (TrackedRootInputCopy.machine M).tapeOf [] := by
  funext p
  cases p with
  | zero => rfl
  | succ p => simp [TrackedBankPreparation.freshTape,MultitapeTM.tapeOf]

private theorem bootstrapframes_root_initial_empty (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k+2)) (hi : i.val ≠ 0) :
    ((TrackedRootInputCopy.machine M).initCfg x y).cells i = (TrackedRootInputCopy.machine M).tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem root_preparation_ready (M : MultitapeTM) (x y : List Bool) :
    TrackedBankPreparation.initialFrame M (rootPreparationBase M x y) 1 (fun _ => 1) x y=
      rootPreparationBase M x y := by
  apply bootstrapframes_cfg_ext
  · rfl
  · funext i
    simp only [TrackedBankPreparation.initialFrame,rootPreparationBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,
        if_neg (by omega : i.val ≠ 1)]
      rw [bootstrapframes_root_initial_empty M x y i (by omega)]
      exact bootstrapframes_fresh_native M
    · simp only [dif_neg hw]
      by_cases hi : i.val=1
      · simp only [if_pos hi,TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,
          if_pos hi,List.take_length]
        exact bootstrapframes_source_idem M _ 1 _
      · simp only [if_neg hi]
  · funext i
    simp only [TrackedBankPreparation.initialFrame,rootPreparationBase]
    by_cases hw : 2 ≤ i.val
    · simp only [dif_pos hw,TrackedRootInputCopy.finalFrame,if_neg (by omega : i.val ≠ 0)]
    · simp only [dif_neg hw]
      by_cases hi : i.val=1
      · simp only [if_pos hi,TrackedRootInputCopy.finalFrame,if_neg (by omega : i.val ≠ 0)]
      · simp only [if_neg hi]

private theorem bootstrapframes_old_ne_stack (M : MultitapeTM) (j : Fin (M.k+2)) :
    FixedTapeExtension.oldTape (TrackedBankPreparation.machine M) j ≠ stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,stackTape,FiniteContinuationStack.stackTape] at h
  omega

private theorem root_preparation_start_ready (M : MultitapeTM) (x y : List Bool) :
    rootPreparationStart M x y=rootPreparationPadBase M x y := by
  rw [rootPreparationStart,root_preparation_ready]
  apply bootstrapframes_cfg_ext
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
    simp only [rootPreparationPadBase,Function.update_of_ne (bootstrapframes_old_ne_stack M j),bootFinal]
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

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

private theorem nativeframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem nativeframes_bank_empty_buffer (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) :
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

private theorem nativeframes_return_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma
  · simp only [TrackedOutputReturn.bufferTape,if_pos hp]
  · simp only [TrackedOutputReturn.bufferTape,if_neg hp]

private theorem nativeframes_initial_zero (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) :
    (N.initCfg x y).cells i 0=N.startSym := by
  simp only [MultitapeTM.initCfg]
  split <;> rfl

private theorem nativeframes_initial_empty (N : MultitapeTM) (x y : List Bool) (i : Fin N.k) (hi : i.val ≠ 0) :
    (N.initCfg x y).cells i=N.tapeOf [] := by
  simp only [MultitapeTM.initCfg]
  rw [if_neg (by intro h; exact hi (congrArg Fin.val h))]

private theorem nativeframes_root_final_zero (M : MultitapeTM) (x y : List Bool) (i : Fin (M.k+2)) :
    (TrackedRootInputCopy.finalFrame M x y).cells i 0=none := by
  simp only [TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame]
  by_cases hi : i.val=1
  · simp only [if_pos hi,TrackedBankPreparation.sourceTape,if_pos (by omega : (0 : ℕ) < 1)]
    exact nativeframes_initial_zero _ _ _ _
  · simp only [if_neg hi]
    exact nativeframes_initial_zero _ _ _ _

private theorem nativeframes_native_old_cells (M : MultitapeTM) (n : ℕ)
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
  · rw [hc,nativeframes_bank_empty_buffer]
    exact (nativeframes_return_idem M _ 1 []).symm
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
  apply nativeframes_cfg_ext
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
          rw [nativeframes_root_final_zero,nativeframes_initial_zero]
        · simp only [if_neg hp]
      · simp only [dif_neg hw]
        by_cases hb : i.val=1
        · simp only [if_pos hb]
          rw [nativeframes_bank_empty_buffer]
          by_cases hp : p < 1
          · have hp0 : p=0 := by omega
            subst p
            simp only [TrackedOutputReturn.bufferTape,if_pos (by omega : (0 : ℕ) < 1),nativeBase]
            rw [nativeframes_root_final_zero,nativeframes_initial_zero]
          · simp only [TrackedOutputReturn.bufferTape,if_neg hp]
        · simp only [if_neg hb]
          simp only [TrackedRootInputCopy.finalFrame,TrackedRootInputCopy.copyFrame,if_neg hb,nativeBase]
          exact congrFun (nativeframes_native_old_cells M n request resume x y ⟨i.val,hi⟩) p
    · simp only [dif_neg hi]
      have he : i=stackTape M := by apply Fin.ext; simp only [stackTape,FiniteContinuationStack.stackTape]; omega
      subst i
      simp only [rootPreparationPadBase,bootFinal,FixedTapeExtension.embed,
        dif_neg hi,stackBase,if_true,nativeBase]
      cases p with
      | zero =>
        simp only [FiniteContinuationStack.freshTape,if_pos (by omega : (0 : ℕ) < 1)]
        rw [nativeframes_initial_zero,nativeframes_initial_zero]
      | succ p =>
        rw [nativeframes_initial_empty (bootMachine M) x y (stackTape M) (by change M.k+2 ≠ 0; omega)]
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

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem programs_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem programs_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem programs_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply programs_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem programs_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,programs_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem boot_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) (live : c.state≠(bootMachine M).qHalt) :
    (machine M n request resume).step (liftBoot M n request resume c)=
      liftBoot M n request resume ((bootMachine M).step c) := by
  have ht : transition M n request resume (.boot c.state) (fun i => c.cells i (c.head i))=
      (let r := (bootMachine M).δ c.state (fun i => c.cells i (c.head i)); (.boot r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (bootMachine M)
    (fun q => q=(bootMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [boot_iterate M n request resume c s hlive,he]

private theorem preparation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (live : c.state≠(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=
      liftPreparation M n request resume ((preparationMachine M).step c) := by
  have ht : transition M n request resume (.preparation c.state) (fun i => c.cells i (c.head i))=
      (let r := (preparationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.preparation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (preparationMachine M)
    (fun q => q=(preparationMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
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
    simp only [transition,if_neg live,no_request]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (bodyMachine M)
    (fun q => q=(bodyMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [body_iterate M n request resume c s hlive (by intro r hr; exact no_request r (by omega)),he]

private theorem input_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (live : c.state≠(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=
      liftInput M n request resume label ((inputMachine M).step c) := by
  have ht : transition M n request resume (.input label c.state) (fun i => c.cells i (c.head i))=
      (let r := (inputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.input label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (inputMachine M)
    (fun q => q=(inputMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [input_iterate M n request resume label c s hlive,he]

private theorem reservation_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (live : c.state≠(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=
      liftReservation M n request resume ((reservationMachine M).step c) := by
  have ht : transition M n request resume (.reservation c.state) (fun i => c.cells i (c.head i))=
      (let r := (reservationMachine M).δ c.state (fun i => c.cells i (c.head i)); (.reservation r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (reservationMachine M)
    (fun q => q=(reservationMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [reservation_iterate M n request resume c s hlive,he]

private theorem return_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (live : c.state≠(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=
      liftReturn M n request resume ((returnMachine M).step c) := by
  have ht : transition M n request resume (.returning c.state) (fun i => c.cells i (c.head i))=
      (let r := (returnMachine M).δ c.state (fun i => c.cells i (c.head i)); (.returning r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (returnMachine M)
    (fun q => q=(returnMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [return_iterate M n request resume c s hlive,he]

private theorem cleanup_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (live : c.state≠(cleanupMachine M).qHalt) :
    (machine M n request resume).step (liftCleanup M n request resume c)=
      liftCleanup M n request resume ((cleanupMachine M).step c) := by
  have ht : transition M n request resume (.cleanup c.state) (fun i => c.cells i (c.head i))=
      (let r := (cleanupMachine M).δ c.state (fun i => c.cells i (c.head i)); (.cleanup r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (cleanupMachine M)
    (fun q => q=(cleanupMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [cleanup_iterate M n request resume c s hlive,he]

private theorem restore_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step c) := by
  have ht : transition M n request resume (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem restore_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n request resume).step^[T] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      restore_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem restore_to_halt (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n request resume).step^[s] (liftRestore M n request resume c)=
      liftRestore M n request resume ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [restore_iterate M n request resume c s hlive,he]

private theorem output_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=
      liftOutput M n request resume label ((outputMachine M).step c) := by
  have ht : transition M n request resume (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [output_iterate M n request resume label c s hlive,he]

private theorem finish_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (live : c.state≠(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=
      liftFinish M n request resume ((finishMachine M).step c) := by
  have ht : transition M n request resume (.finish c.state) (fun i => c.cells i (c.head i))=
      (let r := (finishMachine M).δ c.state (fun i => c.cells i (c.head i)); (.finish r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply programs_cfg_ext
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
  obtain ⟨s,hs,he,hlive⟩ := programs_first_exit (finishMachine M)
    (fun q => q=(finishMachine M).qHalt) (by intro d hd; exact programs_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [finish_iterate M n request resume c s hlive,he]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem dispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem dispatch_right_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (tape : Fin (M.k+3)) : moveActions M a tape .right=
      fun i => (a i,if i=tape then .right else .stay) := by
  classical
  funext i
  simp only [moveActions]
  split_ifs <;> cases a i <;> rfl

private theorem dispatch_left_actions (M : MultitapeTM) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
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
  apply dispatch_cfg_ext
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
  rw [dispatch_right_actions] at ht
  apply dispatch_cfg_ext
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
  rw [dispatch_left_actions M _ tape present] at ht
  apply dispatch_cfg_ext
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
  simp only [transition,if_pos exit]

private theorem preparation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) (exit : c.state=(preparationMachine M).qHalt) :
    (machine M n request resume).step (liftPreparation M n request resume c)=relabel M n request resume (.resetBuffer) (liftPreparation M n request resume c) := by
  apply stay_step
  change transition M n request resume (.preparation c.state) _=_
  simp only [transition,if_pos exit]

private theorem input_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) (exit : c.state=(inputMachine M).qHalt) :
    (machine M n request resume).step (liftInput M n request resume label c)=relabel M n request resume (.push (.pushStart label)) (liftInput M n request resume label c) := by
  apply stay_step
  change transition M n request resume (.input label c.state) _=_
  simp only [transition,if_pos exit]

private theorem reservation_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) (exit : c.state=(reservationMachine M).qHalt) :
    (machine M n request resume).step (liftReservation M n request resume c)=relabel M n request resume (.preparation .mark) (liftReservation M n request resume c) := by
  apply stay_step
  change transition M n request resume (.reservation c.state) _=_
  simp only [transition,if_pos exit]

private theorem return_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) (exit : c.state=(returnMachine M).qHalt) :
    (machine M n request resume).step (liftReturn M n request resume c)=relabel M n request resume (.cleanup .rewind) (liftReturn M n request resume c) := by
  apply stay_step
  change transition M n request resume (.returning c.state) _=_
  simp only [transition,if_pos exit]

private theorem cleanup_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) (exit : c.state=(cleanupMachine M).qHalt)
    (present : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step (liftCleanup M n request resume c)=headFrame M n request resume (.inspectStack) (liftCleanup M n request resume c) (stackTape M) (c.head (stackTape M)-1) := by
  apply left_step M n request resume _ _ _ present
  change transition M n request resume (.cleanup c.state) _=_
  simp only [transition,if_pos exit]

private theorem restore_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) (exit : c.state=(restoreMachine M).qHalt) :
    (machine M n request resume).step (liftRestore M n request resume c)=relabel M n request resume (.pop .popStart) (liftRestore M n request resume c) := by
  apply stay_step
  change transition M n request resume (.restore c.state) _=_
  simp only [transition,if_pos exit]

private theorem output_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) (exit : c.state=(outputMachine M).qHalt) :
    (machine M n request resume).step (liftOutput M n request resume label c)=relabel M n request resume (.body (resume label)) (liftOutput M n request resume label c) := by
  apply stay_step
  change transition M n request resume (.output label c.state) _=_
  simp only [transition,if_pos exit]

private theorem finish_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) (exit : c.state=(finishMachine M).qHalt) :
    (machine M n request resume).step (liftFinish M n request resume c)=relabel M n request resume (.halt) (liftFinish M n request resume c) := by
  apply stay_step
  change transition M n request resume (.finish c.state) _=_
  simp only [transition,if_pos exit]

private theorem body_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (exit : c.state=(bodyMachine M).qHalt) :
    (machine M n request resume).step (liftBody M n request resume c)=relabel M n request resume ( .returning (returnMachine M).qStart) (liftBody M n request resume c) := by
  apply stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_pos exit]

private theorem body_request_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (label : Fin n) (live : c.state≠M.qHalt)
    (call : request c.state=some label) :
    (machine M n request resume).step (liftBody M n request resume c)=
      relabel M n request resume (.input label .before) (liftBody M n request resume c) := by
  apply stay_step
  change transition M n request resume (.body c.state) _=_
  simp only [transition,if_neg live,call]

private theorem push_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (exit : c.state=.pushDone) :
    (machine M n request resume).step (liftPush M n request resume c)=
      relabel M n request resume (.reservation .seek) (liftPush M n request resume c) := by
  apply stay_step
  change transition M n request resume (.push c.state) _=_
  simp only [transition,if_pos exit]

private theorem pop_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) (label : Fin n) (exit : c.state=.resume label) :
    (machine M n request resume).step (liftPop M n request resume c)=
      relabel M n request resume (.output label .before) (liftPop M n request resume c) := by
  apply stay_step
  change transition M n request resume (.pop c.state) _=_
  simp only [transition,exit]

private theorem inspect_root_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (root : c.cells (stackTape M) (c.head (stackTape M))=none) :
    (machine M n request resume).step c=relabel M n request resume (.finish .rewind) c := by
  apply stay_step
  simp only [phase,transition,if_pos root]

private theorem inspect_parent_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.inspectStack)
    (parent : c.cells (stackTape M) (c.head (stackTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume (.restore .rewind) c (stackTape M) (c.head (stackTape M)+1) := by
  apply right_step
  simp only [phase,transition,if_neg parent]

private theorem reset_marker_dispatch (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))=some (M.startSym,true)) :
    (machine M n request resume).step c=
      headFrame M n request resume (.body M.qStart) c (bufferTape M) (c.head (bufferTape M)+1) := by
  apply right_step
  simp only [phase,transition,if_pos marker]

private theorem reset_live_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (phase : c.state=.resetBuffer)
    (marker : c.cells (bufferTape M) (c.head (bufferTape M))≠some (M.startSym,true))
    (present : c.cells (bufferTape M) (c.head (bufferTape M))≠none) :
    (machine M n request resume).step c=
      headFrame M n request resume .resetBuffer c (bufferTape M) (c.head (bufferTape M)-1) := by
  apply left_step M n request resume _ _ _ present
  simp only [phase,transition,if_neg marker]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

private theorem reset_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

noncomputable def resetFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (machine M n request resume).Cfg) (sigma a r : ℕ) : (machine M n request resume).Cfg where
  state := .resetBuffer
  cells := c.cells
  head := Function.update c.head (bufferTape M) (sigma+(a-r))

private theorem reset_empty_return_scan (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
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
  rw [empty,reset_empty_return_scan]
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
  apply reset_cfg_ext
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
    apply reset_cfg_ext
    · exact phase
    · rfl
    · simp only [resetFrame,Nat.sub_zero,←head]
      exact (Function.update_eq_self _ _).symm
  rw [hstart,Function.iterate_succ_apply',reset_run M n request resume _ sigma a a empty le_rfl]
  have hm := reset_scan M n request resume c sigma a a empty
  rw [if_pos le_rfl] at hm
  rw [reset_marker_dispatch M n request resume _ rfl hm]
  apply reset_cfg_ext
  · rfl
  · rfl
  · simp only [headFrame,resetFrame,Nat.sub_self,Nat.add_zero,Function.update_self,Function.update_idem]

end IntMul.FlatRecursiveScheduler



namespace IntMul.FlatRecursiveScheduler

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

end IntMul.FlatRecursiveScheduler


open IntMul IntMul.FlatRecursiveScheduler IntMul.TrackedBankPreparation

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    ∃ t, t ≤ 5*(inputWord M x y).length+12 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        bodyFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1)
          (initialExtent M x y) (M.initCfg x y) [] :=
  IntMul.FlatRecursiveScheduler.bootstrap_correct M n request resume x y

#print axioms solution
