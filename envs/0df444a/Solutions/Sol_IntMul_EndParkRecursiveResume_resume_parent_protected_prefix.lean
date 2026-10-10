-- Prove2me | solution 1 for IntMul.EndParkRecursiveResume.resume_parent_protected_prefix
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T07:41:53.81673+00:00
-- url     : https://prove2.me/submissions/1ada4581-8195-44d3-8660-034be6681337

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Theorems.Thm_IntMul_EndParkResume_resume_protected_prefix
import Mathlib.Tactic


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

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    workTape M j≠TrackedChildInputBridge.bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [workTape,TrackedChildInputBridge.bufferTape] at h
  omega

private theorem embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
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
      have hw : workTape M j=i := work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankReservation (newOffsets)

private noncomputable def physicalWork (M : MultitapeTM) (j : Fin M.k) : Fin (M.k+3) :=
  FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j)

private theorem work_not_stack (M : MultitapeTM) (j : Fin M.k) : physicalWork M j≠stackTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [physicalWork,FixedTapeExtension.oldTape,workTape,stackTape,FiniteContinuationStack.stackTape] at h
  have := j.isLt
  omega

private theorem child_work (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (j : Fin M.k) :
    (childBase M n request resume base rho sigma offset extent c label).cells (physicalWork M j)=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma []) offset extent c).cells
        (workTape M j) := by
  simp only [childBase,if_neg (work_not_stack M j)]
  have hn : (physicalWork M j).val≠1 := by simp only [physicalWork,FixedTapeExtension.oldTape,workTape]; omega
  simp only [if_neg hn,bodyFrame,liftBody]
  simp only [physicalWork,extension_old_cells]

private theorem child_work_fresh (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    TrackedBankCleanup.freshTape M
      ((childBase M n request resume base rho sigma offset extent c label).cells (physicalWork M j))
      (newOffsets M offset extent j)=
      (childBase M n request resume base rho sigma offset extent c label).cells (physicalWork M j) := by
  funext p
  by_cases hp : p < newOffsets M offset extent j
  · simp only [TrackedBankCleanup.freshTape,if_pos hp]
  · simp only [TrackedBankCleanup.freshTape,if_neg hp]
    have ho : offset j≤ p := by unfold newOffsets at hp; omega
    have he : extent j < p-offset j := by unfold newOffsets at hp; omega
    rw [child_work]
    have h := embed_work M (parentBase M n request resume base sigma []) offset extent c j (p-offset j)
    rw [show offset j+(p-offset j)=p by omega] at h
    rw [h,tail j (p-offset j) he]
    simp only [decide_eq_false_iff_not.mpr (by omega : ¬p-offset j≤ extent j)]

private theorem inspection_work (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) (j : Fin M.k) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (physicalWork M j)=
      (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma []) offset extent c).cells
        (workTape M j) := by
  simp only [childInspection,EndParkRecursiveReturn.inspectionFrame,physicalWork,FixedTapeExtension.oldTape,workTape]
  rw [dif_pos (by have := j.isLt; omega),dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by have := j.isLt; omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext; simp [innerTape]
  rw [hi]
  change TrackedBankCleanup.freshTape M
    ((childBase M n request resume base rho sigma offset extent c label).cells (physicalWork M j))
    (newOffsets M offset extent j)=_
  rw [child_work_fresh M n request resume base rho sigma offset extent c label tail j,child_work]
  rfl

private theorem inspection_work_head (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (childInspection M n request resume base rho sigma offset extent c label w).head (physicalWork M j)=
      newOffsets M offset extent j := by
  simp only [childInspection,EndParkRecursiveReturn.inspectionFrame,physicalWork,FixedTapeExtension.oldTape,workTape]
  rw [dif_pos (by have := j.isLt; omega),dif_pos (by omega)]
  congr 1

private theorem inspection_stack (M : MultitapeTM) (n : ℕ)
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

private theorem inspection_nonroot (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (childInspection M n request resume base rho sigma offset extent c label w).cells (stackTape M)
      ((childInspection M n request resume base rho sigma offset extent c label w).head (stackTape M))≠none := by
  have h := inspection_stack M n request resume base rho sigma offset extent c label w
  rw [h.1,h.2]
  have hn : 0 < n := by have := label.isLt; omega
  simp [FiniteContinuationStack.recordTape,hn.ne',show ¬rho+n < rho by omega,show rho+n≠rho by omega]

end IntMul.EndParkRecursiveResume



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkrecursiveresumelowframes_buffer_replace (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (v w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma v) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem inspection_buffer (M : MultitapeTM) (n : ℕ)
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
    exact owned_intmulendparkrecursiveresumelowframes_buffer_replace M _ sigma [] w
  · simp [childInspection,EndParkRecursiveReturn.inspectionFrame,bufferTape]

private theorem inspection_root (M : MultitapeTM) (n : ℕ)
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

private theorem owned_intmulendparkresumepadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
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


end IntMul.EndParkResume



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulfinitecontinuationstacktape_zero_ne_one (M : MultitapeTM) : M.zero ≠ M.one := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem decode_onehot (M : MultitapeTM) (n : ℕ) (q : Fin n) (j : ℕ) :
    TrackedBankedSimulation.decode M (some (M.bitSym (decide (j = q.val)),true)) = M.one ↔ j = q.val := by
  by_cases hj : j = q.val
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode]
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode,owned_intmulfinitecontinuationstacktape_zero_ne_one M]

private theorem record_bit (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (r : ℕ) (hr : r < j) :
    recordTape M n base rho q j (rho + r + 1) = some (M.bitSym (decide (r = q.val)),true) := by
  simp [recordTape,show ¬rho + r + 1 < rho by omega,
    show rho + r + 1 ≠ rho by omega,show rho + r + 1 < rho + j + 1 by omega,
    show rho + r + 1 - rho - 1 = r by omega]

private theorem record_marker (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    recordTape M n base rho q j rho = some (M.sep,true) := by simp [recordTape]

private theorem fresh_at (M : MultitapeTM) (base : ℕ → Sym M) (rho p : ℕ) (hp : rho ≤ p) :
    freshTape M base rho p = some (M.blank,false) := by simp [freshTape,show ¬p < rho by omega]

private theorem marker_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (freshTape M base rho) rho (some (M.sep,true)) = recordTape M n base rho q 0 := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [recordTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [freshTape,recordTape,hp]
    · simp [freshTape,recordTape,hp,he,show ¬p < rho + 0 + 1 by omega]

private theorem bit_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
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

private theorem bit_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
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

private theorem marker_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
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
private theorem recovered_step (n : ℕ) (q : Fin n) (j : ℕ) (hj : j < n) :
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

private theorem pop_scan (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (popFrame M n base rho q j).cells (stackTape M) ((popFrame M n base rho q j).head (stackTape M)) =
      some (M.bitSym (decide (n - 1 - j = q.val)),true) := by
  simp only [popFrame,ite_true]
  have he : rho + (n - j) = rho + (n - 1 - j) + 1 := by omega
  rw [he,record_bit M n _ rho q (n - j) (n - 1 - j) (by omega)]

end IntMul.FiniteContinuationStack



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulfinitecontinuationstacksteps_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulfinitecontinuationstacksteps_raw_other (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (i : Fin (M.k + 3)) (hi : i ≠ stackTape M) :
    (rawTransition M n q a).2 i = (a i,.stay) := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;> simp_all

private theorem owned_intmulfinitecontinuationstacksteps_protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

/-- A tagged scan and tagged write make the physical protection wrapper
transparent; every non-stack tape remains exact and its head stays. -/
private theorem owned_intmulfinitecontinuationstacksteps_physical_transition (M : MultitapeTM) (n : ℕ) (q : State n)
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
    · rw [owned_intmulfinitecontinuationstacksteps_raw_other M n q a i hi,owned_intmulfinitecontinuationstacksteps_protect_same_stay]
      simp only [if_neg hi]

private theorem push_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushStartFrame M n base rho q) = pushFrame M n base rho q 0 := by
  let a := fun i => (pushStartFrame M n base rho q).cells i ((pushStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushStartFrame,freshTape]
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n (.pushStart q) a (pushFrame M n base rho q 0).state
    (M.blank,false) (M.sep,true) .right hs
    (by simp [rawTransition,pushFrame,show 0 < n by have := q.isLt; omega]) (by simp [rawTransition])
  dsimp only [a] at ht
  change transition M n (pushStartFrame M n base rho q).state _ = _ at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true]
      exact marker_write M n _ rho q
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]
      exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushStartFrame,pushFrame,ite_true,Nat.add_zero]
    · simp only [if_neg hi,pushStartFrame,pushFrame,if_neg hi]

private theorem push_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (pushFrame M n base rho q j) = pushFrame M n base rho q (j + 1) := by
  let a := fun i => (pushFrame M n base rho q j).cells i ((pushFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushFrame,recordTape,show ¬rho + j + 1 < rho by omega,show rho + j + 1 ≠ rho by omega]
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n (pushFrame M n base rho q j).state a
    (pushFrame M n base rho q (j + 1)).state (M.blank,false) (M.bitSym (decide (j = q.val)),true) .right hs
    (by simp only [pushFrame,dif_pos hj,rawTransition])
    (by simp only [pushFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,pushFrame,ite_true]
      exact bit_write M n _ rho q j
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
private theorem push_dispatch (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushFrame M n base rho q n) = popStartFrame M n base rho q := by
  have ht : transition M n (pushFrame M n base rho q n).state
      (fun i => (pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i)) =
      (.popStart,fun i => ((pushFrame M n base rho q n).cells i ((pushFrame M n base rho q n).head i),.stay)) := by
    simp only [pushFrame,dif_neg (by omega : ¬n < n),transition,rawTransition,owned_intmulfinitecontinuationstacksteps_protect_same_stay]
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

private theorem pop_start_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popStartFrame M n base rho q) = popFrame M n base rho q 0 := by
  let a := fun i => (popStartFrame M n base rho q).cells i ((popStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,popStartFrame,pushFrame,recordTape,show ¬rho + n + 1 < rho by omega,
      show rho + n + 1 ≠ rho by omega]
  have hf : recovered n q 0 = none := by
    simp [recovered,show ¬n - q.val ≤ 0 by have := q.isLt; omega]
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n .popStart a (popFrame M n base rho q 0).state
    (M.blank,false) (M.blank,false) .left hs
    (by simp only [rawTransition,if_pos (by have := q.isLt; omega : 0 < n),popFrame,
      dif_pos (by have := q.isLt; omega : 0 < n),hf])
    (by simp [rawTransition,show 0 < n by have := q.isLt; omega,hs])
  dsimp only [a] at ht
  change transition M n (popStartFrame M n base rho q).state _ = _ at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
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

private theorem pop_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (popFrame M n base rho q j) = popFrame M n base rho q (j + 1) := by
  classical
  let a := fun i => (popFrame M n base rho q j).cells i ((popFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.bitSym (decide (n - 1 - j = q.val)),true) :=
    pop_scan M n base rho q j hj
  have hpred : TrackedBankedSimulation.decode M (a (stackTape M)) = M.one ↔ n - 1 - j = q.val := by
    rw [hs]
    exact decode_onehot M n q (n - 1 - j)
  have hf : (if TrackedBankedSimulation.decode M (a (stackTape M)) = M.one then
      some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) = recovered n q (j + 1) := by
    simpa only [hpred] using recovered_step n q j hj
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q j).state a
    (popFrame M n base rho q (j + 1)).state
    (M.bitSym (decide (n - 1 - j = q.val)),true) (M.blank,false) .left hs
    (by simp only [popFrame,dif_pos hj,rawTransition]; rw [hf])
    (by simp only [popFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      exact bit_erase M n _ rho q j hj
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
private theorem pop_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popFrame M n base rho q n) = finalFrame M n base rho q := by
  let a := fun i => (popFrame M n base rho q n).cells i ((popFrame M n base rho q n).head i)
  have hs : a (stackTape M) = some (M.sep,true) := by
    simp [a,popFrame,recordTape]
  have hf : recovered n q n = some q := by simp [recovered]
  have ht := owned_intmulfinitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q n).state a (.resume q)
    (M.sep,true) (M.blank,false) .stay hs
    (by simp only [popFrame,dif_neg (by omega : ¬n < n),hf,rawTransition,if_pos hs])
    (by simp [popFrame,hf,rawTransition])
  dsimp only [a] at ht
  apply owned_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
      exact marker_erase M n _ rho q
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
private theorem push_run (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n).step^[j] (pushFrame M n base rho q 0) = pushFrame M n base rho q j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),push_bit_step M n base rho q j (by omega)]

private theorem push_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[n + 1] (pushStartFrame M n base rho q) = pushFrame M n base rho q n := by
  rw [Function.iterate_add_apply,Function.iterate_one,push_marker_step,push_run M n base rho q n le_rfl]

/-- Every read/erase is an actual left-moving transition, updating only a
finite recovered-label register while retaining all older prefix records. -/
private theorem pop_run (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n).step^[j] (popFrame M n base rho q 0) = popFrame M n base rho q j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),pop_bit_step M n base rho q j (by omega)]

private theorem pop_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[n + 2] (popStartFrame M n base rho q) = finalFrame M n base rho q := by
  have h : (machine M n).step^[n + 1] (popStartFrame M n base rho q) = popFrame M n base rho q n := by
    rw [Function.iterate_add_apply,Function.iterate_one,pop_start_step,pop_run M n base rho q n le_rfl]
  rw [show n + 2 = (n + 1) + 1 by omega,Function.iterate_succ_apply',h,pop_marker_step]

/-- One physical push-to-pop dispatch is included in the exact round trip.
The returned finite control state contains the recovered continuation q.
All tape cells and head positions equal the complete initial frame. -/
private theorem round_trip_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q) = finalFrame M n base rho q ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).state = .resume q ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).cells =
      (pushStartFrame M n base rho q).cells ∧
    ((machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q)).head =
      (pushStartFrame M n base rho q).head := by
  have h : (machine M n).step^[n + 2] (pushStartFrame M n base rho q) = popStartFrame M n base rho q := by
    rw [show n + 2 = (n + 1) + 1 by omega,Function.iterate_succ_apply',push_correct,push_dispatch]
  have hr : (machine M n).step^[2 * n + 4] (pushStartFrame M n base rho q) = finalFrame M n base rho q := by
    rw [show 2 * n + 4 = (n + 2) + (n + 2) by omega,Function.iterate_add_apply,h,pop_correct]
  refine ⟨hr,?_,?_,?_⟩ <;> rw [hr] <;> rfl

end IntMul.FiniteContinuationStack



namespace IntMul.EndParkResume

private theorem owned_intmulendparkresumeprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulendparkresumeprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem owned_intmulendparkresumeprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply owned_intmulendparkresumeprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem owned_intmulendparkresumeprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,owned_intmulendparkresumeprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem restore_step (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n).step (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step c) := by
  have ht : transition M n (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply owned_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem restore_iterate (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n).step^[T] (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      restore_step M n _ (live T (by omega)),Function.iterate_succ_apply']

private theorem restore_to_halt (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n).step^[s] (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkresumeprograms_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact owned_intmulendparkresumeprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [restore_iterate M n c s hlive,he]

private theorem output_step (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n).step (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step c) := by
  have ht : transition M n (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply owned_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem output_iterate (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n).step^[T] (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      output_step M n label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem output_to_halt (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n).step^[s] (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := owned_intmulendparkresumeprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact owned_intmulendparkresumeprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [output_iterate M n label c s hlive,he]

private theorem pop_step (M : MultitapeTM) (n : ℕ)
    
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : ∀ label, c.state≠.resume label) :
    (machine M n).step (liftPop M n c)=
      liftPop M n ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n (.pop c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.pop r.1,r.2)) := by
    cases hs : c.state <;> first | rfl | skip
    rename_i label
    exact False.elim (live label hs)
  apply owned_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]

private theorem pop_run (M : MultitapeTM) (n : ℕ)
    
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
    rw [Function.iterate_succ_apply',ih (by omega),pop_step M n _ hlive,
      FiniteContinuationStack.pop_bit_step M n base rho label j (by omega)]

private theorem pop_correct (M : MultitapeTM) (n : ℕ)
    
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
    rw [Function.iterate_add_apply,Function.iterate_one,pop_step M n _ hlive,
      FiniteContinuationStack.pop_start_step,pop_run M n base rho label n le_rfl]
  have hm : ∀ q, (FiniteContinuationStack.popFrame M n base rho label n).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popFrame]
  rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply',hr,pop_step M n _ hm,
    FiniteContinuationStack.pop_marker_step]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.FiniteContinuationStack (stackTape)
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkresumestackframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem restore_stack (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (restoreFinal M n base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n ∧
    (restoreFinal M n base rho sigma offset extent c label w).head (stackTape M)=rho+n+1 := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedSelectiveParentRestore.machine M (active M)) := by apply Fin.ext; rfl
  constructor
  · simp only [restoreFinal,he,extension_extra_cells,restorePadBase]
    rw [he.symm]
    simp only [if_true]
  · simp only [restoreFinal,he,extension_extra_heads,restorePadBase]
    rw [he.symm]
    simp only [if_true]

private theorem restore_pop_ready (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    relabel M n (.pop .popStart)
      (liftRestore M n (restoreFinal M n base rho sigma offset extent c label w))=
    liftPop M n (FiniteContinuationStack.popStartFrame M n
      (popParent M n base rho sigma offset extent c label w) rho label) := by
  have hs := restore_stack M n base rho sigma offset extent c label w
  apply owned_intmulendparkresumestackframes_cfg_ext
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

private theorem popped_stack (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (popped M n base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
    (popped M n base rho sigma offset extent c label w).head (stackTape M)=rho := by
  constructor
  · simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true,popParent,
      (restore_stack M n base rho sigma offset extent c label w).1]
    funext p
    by_cases hp : p < rho <;> simp only [FiniteContinuationStack.freshTape,FiniteContinuationStack.recordTape,hp,if_true,if_false]
  · simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.FiniteContinuationStack (stackTape)

private theorem owned_intmulendparkresumeworkframes_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (workTape M j).val := by simp [workTape]

private theorem owned_intmulendparkresumeworkframes_inner_work (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (workTape M j).val) : innerTape M (workTape M j) h=j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem owned_intmulendparkresumeworkframes_old_work_ne_stack (M : MultitapeTM) (j : Fin M.k) :
    FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)≠stackTape M := by
  intro h
  have hv := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,workTape,stackTape] at hv
  have := j.isLt
  omega

private theorem popped_other_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+3)) (hi : i≠stackTape M) :
    (popped M n base rho sigma offset extent c label w).cells i=
      (restoreFinal M n base rho sigma offset extent c label w).cells i := by
  simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg hi,popParent]

private theorem popped_other_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+3)) (hi : i≠stackTape M) :
    (popped M n base rho sigma offset extent c label w).head i=
      (restoreFinal M n base rho sigma offset extent c label w).head i := by
  simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg hi,popParent]

private theorem restore_work_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (restoreFinal M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)) p=
      if p < offset j then
        base.cells (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)) p
      else some (c.cells j (p-offset j),decide (p-offset j ≤ extent j)) := by
  simp only [restoreFinal,extension_old_cells,TrackedSelectiveParentRestore.finalFrame,
    TrackedBankedSimulation.embed,dif_pos (owned_intmulendparkresumeworkframes_work_ge M j),owned_intmulendparkresumeworkframes_inner_work,
    TrackedSelectiveParentRestore.parentBase,restorePlainBase]
  simp only [if_neg (by simp [workTape] : ¬(workTape M j).val=1)]

private theorem restore_work_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) :
    (restoreFinal M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j))=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  simp only [restoreFinal,extension_old_heads]
  simp only [TrackedSelectiveParentRestore.finalFrame,dif_pos (owned_intmulendparkresumeworkframes_work_ge M j),owned_intmulendparkresumeworkframes_inner_work,
    active,decide_eq_true_eq]

private theorem output_parent_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
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
  rw [popped_other_cells M n base rho sigma offset extent c label w _ (owned_intmulendparkresumeworkframes_old_work_ne_stack M j)]
  exact restore_work_cells M n base rho sigma offset extent c label w j p

private theorem output_parent_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) :
    (outputPlainBase M n base rho sigma offset extent c label w).head (workTape M j)=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  simp only [outputPlainBase]
  change (popped M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j))=
    offset j+(if j=M.outTape then 0 else extent j+1)
  rw [popped_other_heads M n base rho sigma offset extent c label w _ (owned_intmulendparkresumeworkframes_old_work_ne_stack M j)]
  exact restore_work_heads M n base rho sigma offset extent c label w j

private theorem restore_low (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+2)) (hi : i.val < 2) :
    (restoreFinal M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)=
      (restorePlainBase M n base sigma w).cells i ∧
    (restoreFinal M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)=
      (restorePlainBase M n base sigma w).head i := by
  constructor
  · simp only [restoreFinal,extension_old_cells,TrackedSelectiveParentRestore.finalFrame,
      TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),TrackedSelectiveParentRestore.parentBase]
  · simp only [restoreFinal,extension_old_heads,TrackedSelectiveParentRestore.finalFrame,
      dif_neg (by omega : ¬2 ≤ i.val)]

private theorem output_low (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
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
  · simp only [outputPlainBase,popped_other_cells M n base rho sigma offset extent c label w _ hs]
    exact (restore_low M n base rho sigma offset extent c label w i hi).1
  · simp only [outputPlainBase,popped_other_heads M n base rho sigma offset extent c label w _ hs]
    exact (restore_low M n base rho sigma offset extent c label w i hi).2

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
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
      have hw : workTape M j=i := work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmulendparkresumeoutputframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem output_parent_work (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (outputPlainBase M n base rho sigma offset extent c label w).cells (workTape M j) (offset j+p)=
      some ((parentAtEnds M extent c).cells j p,decide (p≤ extent j)) := by
  rw [output_parent_cells]
  simp only [if_neg (by omega : ¬offset j+p < offset j),Nat.add_sub_cancel_left,parentAtEnds]

private theorem output_parent_work_head (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (outputPlainBase M n base rho sigma offset extent c label w).head (workTape M j)=
      offset j+(parentAtEnds M extent c).head j := by
  exact output_parent_heads M n base rho sigma offset extent c label w j

private theorem output_parent_buffer (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (outputPlainBase M n base rho sigma offset extent c label w).cells (TrackedParentOutputBridge.bufferTape M)=
      TrackedOutputReturn.bufferTape M
        (base.cells (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M)
          (TrackedParentOutputBridge.bufferTape M))) sigma w ∧
    (outputPlainBase M n base rho sigma offset extent c label w).head (TrackedParentOutputBridge.bufferTape M)=
      sigma+w.length+1 := by
  have h := output_low M n base rho sigma offset extent c label w
    (TrackedParentOutputBridge.bufferTape M) (by simp [TrackedParentOutputBridge.bufferTape])
  constructor
  · rw [h.1]
    simp only [restorePlainBase,TrackedParentOutputBridge.bufferTape,if_true]
    rfl
  · rw [h.2]
    simp only [restorePlainBase,TrackedParentOutputBridge.bufferTape,if_true]

private theorem owned_intmulendparkresumeoutputframes_buffer_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem output_initial_ready (M : MultitapeTM) (n : ℕ)
    
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
  have hbuf := output_parent_buffer M n base rho sigma offset extent c label w
  have hbc : (TrackedParentOutputBridge.parentBase M B sigma w).cells=B.cells := by
    funext i
    simp only [TrackedParentOutputBridge.parentBase]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp only [if_true]
      rw [hbuf.1]
      exact owned_intmulendparkresumeoutputframes_buffer_idem M _ sigma w
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
    have h := embed_cells_ready M (TrackedParentOutputBridge.parentBase M B sigma w) offset extent (parentAtEnds M extent c)
      (by rw [hbc]; exact output_parent_work M n base rho sigma offset extent c label w)
    rw [hbc] at h
    exact h
  have hh : (TrackedBankedSimulation.embed M (TrackedParentOutputBridge.parentBase M B sigma w)
      offset extent (parentAtEnds M extent c)).head=B.head := by
    have h := embed_heads_ready M (TrackedParentOutputBridge.parentBase M B sigma w) offset extent (parentAtEnds M extent c)
      (by intro j; rw [hbh,output_parent_work_head])
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
        simpa only [parentAtEnds,if_true,Nat.add_zero,TrackedParentOutputBridge.targetTape] using (output_parent_work_head M n base rho sigma offset extent c label w M.outTape).symm
      · simp only [if_neg ht]
        exact congrFun hh i

private theorem pop_output_ready (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    relabel M n (.output label .before)
      (liftPop M n (popped M n base rho sigma offset extent c label w))=
    liftOutput M n label (outputStart M n base rho sigma offset extent c label w) := by
  have h := output_initial_ready M n base rho sigma offset extent c label w
  apply owned_intmulendparkresumeoutputframes_cfg_ext
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

private theorem final_work_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (finalFrame M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  change (outputFinal M n base rho sigma offset extent c label w).head _=_
  simp only [outputFinal,extension_old_heads,TrackedParentOutputBridge.finalFrame]
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
      exact work_injective M h
    rw [if_neg ht]
    have hh := congrFun
      (output_initial_ready M n base rho sigma offset extent c label w).2 (workTape M j)
    simpa only [TrackedParentOutputBridge.initialFrame,TrackedParentOutputBridge.beforeFrame,
      if_neg hb,Nat.sub_zero] using hh.trans
        (output_parent_heads M n base rho sigma offset extent c label w j)

private theorem final_output_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) (p : ℕ) :
    (finalFrame M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))
      (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length)) := by
  change (outputFinal M n base rho sigma offset extent c label w).cells _ _=_
  simp only [outputFinal,extension_old_cells,TrackedParentOutputBridge.finalFrame,
    if_pos (show workTape M M.outTape=TrackedParentOutputBridge.targetTape M by rfl)]
  simp only [TrackedBankPreparation.bankTape,
    if_neg (by omega : ¬offset M.outTape+p < offset M.outTape),Nat.add_sub_cancel_left,List.length_map]

private theorem final_stack (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
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
    simp only [outputFinal,he,extension_extra_cells,outputPadBase]
    rw [he.symm]
    exact (popped_stack M n base rho sigma offset extent c label w).1
  · change (outputFinal M n base rho sigma offset extent c label w).head _=_
    simp only [outputFinal,he,extension_extra_heads,outputPadBase]
    rw [he.symm]
    exact (popped_stack M n base rho sigma offset extent c label w).2

end IntMul.EndParkResume



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)

private theorem owned_intmulendparkrecursiveresumestartframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem inspection_resume_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    headFrame M n request resume (.restore .rewind)
      (childInspection M n request resume base rho sigma offset extent c label w)
      (stackTape M) (rho+n+1)=
    initialFrame M n request resume (serviceBase M n request resume base)
      rho sigma offset extent c label w := by
  apply owned_intmulendparkrecursiveresumestartframes_cfg_ext
  · rfl
  · funext i p
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : physicalWork M j=i := by
          apply Fin.ext
          simp only [physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he]
        change (childInspection M n request resume base rho sigma offset extent c label w).cells
          (physicalWork M j) p =
          (EndParkResume.restoreFinal M n (serviceBase M n request resume base)
            rho sigma offset extent c label w).cells
            (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (EndParkResume.active M)) (workTape M j)) p
        rw [inspection_work M n request resume base rho sigma offset extent c label w tail j,
          EndParkResume.restore_work_cells]
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
          rw [(inspection_buffer M n request resume base rho sigma offset extent c label w).1]
          simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
            EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.extension_old_cells,
            TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,TrackedBankedSimulation.embed,
            TrackedSelectiveParentRestore.parentBase,EndParkResume.restorePlainBase,
            serviceBase,bufferTape,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        · have hz : i.val=0 := by omega
          have he : i=⟨0,by omega⟩ := Fin.ext hz
          rw [he]
          change (childInspection M n request resume base rho sigma offset extent c label w).cells ⟨0,by omega⟩ p=_
          rw [(inspection_root M n request resume base rho sigma offset extent c label w).1]
          simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
            EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.extension_old_cells,
            TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,TrackedBankedSimulation.embed,
            TrackedSelectiveParentRestore.parentBase,EndParkResume.restorePlainBase,
            serviceBase,FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · have he : i=stackTape M := by
        apply Fin.ext
        simp only [stackTape,FiniteContinuationStack.stackTape]
        omega
      subst i
      change (childInspection M n request resume base rho sigma offset extent c label w).cells (stackTape M) p=_
      rw [(inspection_stack M n request resume base rho sigma offset extent c label w).1]
      simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
        EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.extension_extra_cells,
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
        have he : physicalWork M j=i := by
          apply Fin.ext
          simp only [physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he,inspection_work_head]
        simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
          EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.extension_old_heads,
          TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,
          physicalWork,workTape,innerTape,j,FixedTapeExtension.oldTape,FixedTapeExtension.innerTape,
          TrackedBankReservation.newOffsets,Nat.add_assoc,hi,hw]
      · by_cases hb : i.val=1
        · have he : i=bufferTape M := Fin.ext hb
          subst i
          rw [(inspection_buffer M n request resume base rho sigma offset extent c label w).2]
          simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
            EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.extension_old_heads,
            TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,
            EndParkResume.restorePlainBase,serviceBase,bufferTape,
            FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
        · have hz : i.val=0 := by omega
          have he : i=⟨0,by omega⟩ := Fin.ext hz
          rw [he]
          rw [(inspection_root M n request resume base rho sigma offset extent c label w).2]
          simp [initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
            EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.extension_old_heads,
            TrackedSelectiveParentRestore.initialFrame,TrackedSelectiveParentRestore.rewindFrame,
            EndParkResume.restorePlainBase,serviceBase,
            FixedTapeExtension.innerTape,FixedTapeExtension.oldTape]
    · have he : i=stackTape M := by
        apply Fin.ext
        simp only [stackTape,FiniteContinuationStack.stackTape]
        omega
      subst i
      simp [headFrame,initialFrame,liftResume,EndParkResume.initialFrame,EndParkResume.liftRestore,
        EndParkResume.restoreStart,FixedTapeExtension.embed,EndParkResume.extension_extra_heads,
        EndParkResume.restorePadBase,serviceBase,stackTape,FiniteContinuationStack.stackTape,
        FixedTapeExtension.extraTape,FixedTapeExtension.oldTape]

end IntMul.EndParkRecursiveResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)

private theorem final_work_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
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
  simp only [outputFinal,extension_old_cells]
  by_cases hj : j=M.outTape
  · subst j
    simp only [TrackedParentOutputBridge.finalFrame,
      if_pos (show workTape M M.outTape=TrackedParentOutputBridge.targetTape M by rfl),
      TrackedBankPreparation.bankTape,List.length_map,if_true]
    by_cases hp : p < offset M.outTape
    · simp only [if_pos hp]
      rw [output_parent_cells,if_pos hp]
    · simp only [if_neg hp]
  · have ht : workTape M j≠TrackedParentOutputBridge.targetTape M := by
      intro h
      exact hj (work_injective M h)
    simp only [TrackedParentOutputBridge.finalFrame,if_neg ht,if_neg hj]
    change (TrackedParentOutputBridge.initialFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w).cells (workTape M j) p=_
    rw [(output_initial_ready M n base rho sigma offset extent c label w).1,
      output_parent_cells]

private theorem final_low (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
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
    simp only [outputFinal,extension_old_cells,TrackedParentOutputBridge.finalFrame,if_neg ht]
    change (TrackedParentOutputBridge.initialFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w).cells i=_
    rw [(output_initial_ready M n base rho sigma offset extent c label w).1]
    exact (output_low M n base rho sigma offset extent c label w i hi).1
  · change (outputFinal M n base rho sigma offset extent c label w).head _=_
    simp only [outputFinal,extension_old_heads,TrackedParentOutputBridge.finalFrame,if_neg ht]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp [restorePlainBase,TrackedParentOutputBridge.bufferTape]
    · rw [if_neg hb]
      have hh := congrFun (output_initial_ready M n base rho sigma offset extent c label w).2 i
      have hl := (output_low M n base rho sigma offset extent c label w i hi).2
      simpa only [TrackedParentOutputBridge.initialFrame,TrackedParentOutputBridge.beforeFrame,
        if_neg hb,Nat.sub_zero] using hh.trans hl


end IntMul.EndParkResume



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.BankedSimulation (workTape innerTape)

private theorem owned_intmulendparkrecursiveresumefinalframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem resumed_ready (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    finalFrame M n request resume (serviceBase M n request resume base)
      rho sigma offset extent c label w =
    resumedFrame M n request resume base rho sigma offset extent c label w := by
  apply owned_intmulendparkrecursiveresumefinalframes_cfg_ext
  · rfl
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : physicalWork M j=i := by
          apply Fin.ext
          simp only [physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he]
        change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
          rho sigma offset extent c label w).cells
            (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
          (FixedTapeExtension.embed (TrackedBankedSimulation.machine M) _
            (TrackedBankedSimulation.embed M _ _ _ _)).cells
            (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j))
        rw [extension_old_cells]
        funext p
        rw [EndParkResume.final_work_cells]
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
          rw [(EndParkResume.final_low M n (serviceBase M n request resume base)
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
          rw [(EndParkResume.final_low M n (serviceBase M n request resume base)
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
      rw [(EndParkResume.final_stack M n (serviceBase M n request resume base)
        rho sigma offset extent c label w).1]
      simp [resumedFrame,bodyFrame,liftBody,FixedTapeExtension.embed,stackBase,serviceBase,
        stackTape,FiniteContinuationStack.stackTape]
  · funext i
    have hik : i.val < M.k+3 := i.isLt
    by_cases hi : i.val < M.k+2
    · by_cases hw : 2 ≤ i.val
      · let j := innerTape M ⟨i.val,hi⟩ hw
        have he : physicalWork M j=i := by
          apply Fin.ext
          simp only [physicalWork,FixedTapeExtension.oldTape,workTape,innerTape,j]
          omega
        rw [←he]
        change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
          rho sigma offset extent c label w).head
            (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
          (FixedTapeExtension.embed (TrackedBankedSimulation.machine M) _
            (TrackedBankedSimulation.embed M _ _ _ _)).head
            (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) (workTape M j))
        rw [EndParkResume.final_work_heads,extension_old_heads,embed_work_head]
        rfl
      · by_cases hb : i.val=1
        · have he : i=bufferTape M := Fin.ext hb
          subst i
          change (EndParkResume.finalFrame M n (serviceBase M n request resume base)
            rho sigma offset extent c label w).head
              (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) ⟨1,by change 1 < M.k+2; omega⟩)=_
          rw [(EndParkResume.final_low M n (serviceBase M n request resume base)
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
          rw [(EndParkResume.final_low M n (serviceBase M n request resume base)
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
      rw [(EndParkResume.final_stack M n (serviceBase M n request resume base)
        rho sigma offset extent c label w).2]
      simp [resumedFrame,bodyFrame,liftBody,FixedTapeExtension.embed,stackBase,serviceBase,
        stackTape,FiniteContinuationStack.stackTape]

end IntMul.EndParkRecursiveResume



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



namespace IntMul.EndParkRecursiveScheduler

private theorem owned_intmulendparkrecursiveresumewindow_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmulendparkrecursiveresumewindow_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem owned_intmulendparkrecursiveresumewindow_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply owned_intmulendparkrecursiveresumewindow_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem owned_intmulendparkrecursiveresumewindow_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,owned_intmulendparkrecursiveresumewindow_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

/-- Every actual return-service transition is the corresponding transition
of the complete scheduler, until its recovered body continuation is entered. -/
private theorem owned_intmulendparkrecursiveresumewindow_resume_transition (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (q : EndParkResume.State n) (a : Fin (M.k+3) → TrackedBankedSimulation.Sym M)
    (live : ∀ label, q≠.ready label) :
    transition M n request resume (resumeControl M n resume q) a =
      (resumeControl M n resume (EndParkResume.transition M n q a).1,
        (EndParkResume.transition M n q a).2) := by
  classical
  cases q with
  | restore s =>
    cases s <;> simp only [transition,resumeControl,restoreControl,
      EndParkResume.transition,FlatRecursiveScheduler.transition,
      FlatRecursiveScheduler.State.restore.injEq,reduceCtorEq,if_true,if_false]
    all_goals rfl
  | pop s =>
    cases s <;> simp only [transition,resumeControl,EndParkResume.transition,
      FlatRecursiveScheduler.transition,reduceCtorEq,if_false]
    all_goals rfl
  | output label s =>
    simp only [transition,resumeControl,reduceCtorEq,if_false,
      EndParkResume.transition,FlatRecursiveScheduler.transition]
    by_cases h : s=(EndParkResume.outputMachine M).qHalt
    · simp only [h,if_true,resumeControl]
    · simp only [if_neg h]
  | ready label => exact False.elim (live label rfl)
  | halt =>
    simp only [transition,resumeControl,EndParkResume.transition,
      FlatRecursiveScheduler.transition,reduceCtorEq,if_false]

private theorem owned_intmulendparkrecursiveresumewindow_resume_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (EndParkResume.machine M n).Cfg) (live : ∀ label, c.state≠.ready label) :
    (machine M n request resume).step (liftResume M n request resume c)=
      liftResume M n request resume ((EndParkResume.machine M n).step c) := by
  have ht := owned_intmulendparkrecursiveresumewindow_resume_transition M n request resume c.state (fun i => c.cells i (c.head i)) live
  apply owned_intmulendparkrecursiveresumewindow_cfg_ext
  · simp only [MultitapeTM.step,liftResume,ht]
  · simp only [MultitapeTM.step,liftResume,ht]
  · simp only [MultitapeTM.step,liftResume,ht]

private theorem owned_intmulendparkrecursiveresumewindow_resume_iterate (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (EndParkResume.machine M n).Cfg) (T : ℕ)
    (live : ∀ s, s< T → ∀ label, ((EndParkResume.machine M n).step^[s] c).state≠.ready label) :
    (machine M n request resume).step^[T] (liftResume M n request resume c)=
      liftResume M n request resume ((EndParkResume.machine M n).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      owned_intmulendparkrecursiveresumewindow_resume_step M n request resume _ (live T (by omega)),Function.iterate_succ_apply']

private theorem owned_intmulendparkrecursiveresumewindow_ready_fixed (M : MultitapeTM) (n : ℕ)
    (c : (EndParkResume.machine M n).Cfg) (label : Fin n) (ready : c.state=.ready label) :
    (EndParkResume.machine M n).step c=c := by
  apply owned_intmulendparkrecursiveresumewindow_cfg_ext
  · simp [MultitapeTM.step,ready,EndParkResume.transition]
  · funext i
    simp only [MultitapeTM.step,ready,EndParkResume.transition]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,ready,EndParkResume.transition]


end IntMul.EndParkRecursiveScheduler

namespace IntMul.EndParkRecursiveScheduler

/-- The actual scheduler executes the protected parent-return service with
its exact clock and enters the recovered real body continuation. -/
private theorem resume_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (EndParkResume.machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n request resume).step^[t]
        (initialFrame M n request resume base rho sigma offset extent c label w)=
        finalFrame M n request resume base rho sigma offset extent c label w ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[s]
          (initialFrame M n request resume base rho sigma offset extent c label w)).head i := by
  obtain ⟨T,hT,hRun,hSafe⟩ := EndParkResume.resume_protected_prefix M n base rho sigma offset extent c label w
    positive hrho hsigma unique tail
  let start := EndParkResume.initialFrame M n base rho sigma offset extent c label w
  have hReady : ∃ q, ((EndParkResume.machine M n).step^[T] start).state=.ready q := by
    rw [hRun]
    exact ⟨label,rfl⟩
  obtain ⟨t,ht,he,hlive⟩ := owned_intmulendparkrecursiveresumewindow_first_exit (EndParkResume.machine M n)
    (fun q => ∃ label, q=.ready label)
    (by intro d hd; obtain ⟨label,hl⟩ := hd; exact owned_intmulendparkrecursiveresumewindow_ready_fixed M n d label hl) start T hReady
  refine ⟨t,le_trans ht hT,?_,?_⟩
  · change (machine M n request resume).step^[t] (liftResume M n request resume start)=_
    rw [owned_intmulendparkrecursiveresumewindow_resume_iterate M n request resume start t (by
      intro s hs label heq
      exact hlive s hs ⟨label,heq⟩),he,hRun]
    rfl
  · intro s hs i hi
    change 1 ≤ ((machine M n request resume).step^[s] (liftResume M n request resume start)).head i
    rw [owned_intmulendparkrecursiveresumewindow_resume_iterate M n request resume start s (by
      intro r hr label heq
      exact hlive r (by omega) ⟨label,heq⟩)]
    exact hSafe s (le_trans hs ht) i hi

end IntMul.EndParkRecursiveScheduler



namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall

private theorem inspection_head_safe (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (i : Fin (M.k+3)) (hi : i ≠ (machine M n request resume).inTape) :
    1 ≤ (childInspection M n request resume base rho sigma offset extent c label w).head i := by
  have hilim : i.val < M.k+3 := i.isLt
  by_cases hwork : 2 ≤ i.val ∧ i.val < M.k+2
  · let j : Fin M.k := ⟨i.val-2,by omega⟩
    have he : physicalWork M j=i := by
      apply Fin.ext
      simp only [physicalWork,FixedTapeExtension.oldTape,BankedSimulation.workTape,j]
      omega
    rw [←he,inspection_work_head]
    have hp := positive j
    simp only [TrackedBankReservation.newOffsets]
    omega
  · by_cases hbuffer : i.val=1
    · have he : i=bufferTape M := Fin.ext hbuffer
      rw [he,(inspection_buffer M n request resume base rho sigma offset extent c label w).2]
      omega
    · have hz : i.val≠0 := by
        intro hz
        apply hi
        apply Fin.ext
        exact hz
      have he : i=stackTape M := by
        apply Fin.ext
        simp only [stackTape,FiniteContinuationStack.stackTape]
        omega
      rw [he,(inspection_stack M n request resume base rho sigma offset extent c label w).2]
      omega

/-- The actual child inspection, parent restoration, continuation pop and
result placement reach the resumed body while retaining every protected floor. -/
private theorem resume_parent_protected_prefix (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+13 ∧
      (machine M n request resume).step^[t]
        (childInspection M n request resume base rho sigma offset extent c label w)=
        resumedFrame M n request resume base rho sigma offset extent c label w ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[s]
          (childInspection M n request resume base rho sigma offset extent c label w)).head i := by
  have hinspect : (machine M n request resume).step
      (childInspection M n request resume base rho sigma offset extent c label w)=
      initialFrame M n request resume (serviceBase M n request resume base)
        rho sigma offset extent c label w := by
    rw [inspect_parent_dispatch M n request resume _ rfl
      (inspection_nonroot M n request resume base rho sigma offset extent c label w)]
    rw [(inspection_stack M n request resume base rho sigma offset extent c label w).2]
    exact inspection_resume_ready M n request resume base rho sigma offset extent c label w tail
  obtain ⟨t,ht,hrun,hsafe⟩ := EndParkRecursiveScheduler.resume_protected_prefix M n request resume
    (serviceBase M n request resume base) rho sigma offset extent c label w
    positive hrho hsigma unique (tail M.outTape)
  refine ⟨t+1,by omega,?_,?_⟩
  · rw [Function.iterate_succ_apply,hinspect,hrun,resumed_ready]
  · intro s hs i hi
    cases s with
    | zero =>
      exact inspection_head_safe M n request resume base rho sigma offset extent c label w
        positive hrho hsigma i hi
    | succ s =>
      rw [Function.iterate_succ_apply,hinspect]
      exact hsafe s (by omega) i hi

end IntMul.EndParkRecursiveResume


open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveCall IntMul.EndParkRecursiveResume

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+13 ∧
      (machine M n request resume).step^[t]
        (childInspection M n request resume base rho sigma offset extent c label w)=
        resumedFrame M n request resume base rho sigma offset extent c label w ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n request resume).inTape →
        1 ≤ ((machine M n request resume).step^[s]
          (childInspection M n request resume base rho sigma offset extent c label w)).head i :=
  IntMul.EndParkRecursiveResume.resume_parent_protected_prefix M n request resume base rho sigma offset extent c label w positive hrho hsigma unique tail

#print axioms solution
