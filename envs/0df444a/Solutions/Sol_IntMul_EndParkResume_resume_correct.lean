-- Prove2me | solution 1 for IntMul.EndParkResume.resume_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T03:46:56.761481+00:00
-- url     : https://prove2.me/submissions/faafa7b3-5e35-4861-bc5b-0af7ada966fd

import Definitions.Def_IntMul_EndParkResume
import Theorems.Thm_IntMul_TrackedSelectiveParentRestore_restore_correct
import Theorems.Thm_IntMul_TrackedParentOutputBridge_output_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Tactic


namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem end_park_internal_intmulfinitecontinuationstacktape_zero_ne_one (M : MultitapeTM) : M.zero ≠ M.one := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem end_park_internal_decode_onehot (M : MultitapeTM) (n : ℕ) (q : Fin n) (j : ℕ) :
    TrackedBankedSimulation.decode M (some (M.bitSym (decide (j = q.val)),true)) = M.one ↔ j = q.val := by
  by_cases hj : j = q.val
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode]
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode,end_park_internal_intmulfinitecontinuationstacktape_zero_ne_one M]

private theorem end_park_internal_record_bit (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
    (j : ℕ) (r : ℕ) (hr : r < j) :
    recordTape M n base rho q j (rho + r + 1) = some (M.bitSym (decide (r = q.val)),true) := by
  simp [recordTape,show ¬rho + r + 1 < rho by omega,
    show rho + r + 1 ≠ rho by omega,show rho + r + 1 < rho + j + 1 by omega,
    show rho + r + 1 - rho - 1 = r by omega]

private theorem end_park_internal_record_marker (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
    recordTape M n base rho q j rho = some (M.sep,true) := by simp [recordTape]

private theorem end_park_internal_fresh_at (M : MultitapeTM) (base : ℕ → Sym M) (rho p : ℕ) (hp : rho ≤ p) :
    freshTape M base rho p = some (M.blank,false) := by simp [freshTape,show ¬p < rho by omega]

private theorem end_park_internal_marker_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
    Function.update (freshTape M base rho) rho (some (M.sep,true)) = recordTape M n base rho q 0 := by
  funext p
  by_cases he : p = rho
  · subst p
    simp [recordTape]
  · rw [Function.update_of_ne he]
    by_cases hp : p < rho
    · simp [freshTape,recordTape,hp]
    · simp [freshTape,recordTape,hp,he,show ¬p < rho + 0 + 1 by omega]

private theorem end_park_internal_bit_write (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j : ℕ) :
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

private theorem end_park_internal_bit_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n)
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

private theorem end_park_internal_marker_erase (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) :
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
private theorem end_park_internal_recovered_step (n : ℕ) (q : Fin n) (j : ℕ) (hj : j < n) :
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

private theorem end_park_internal_pop_scan (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (popFrame M n base rho q j).cells (stackTape M) ((popFrame M n base rho q j).head (stackTape M)) =
      some (M.bitSym (decide (n - 1 - j = q.val)),true) := by
  simp only [popFrame,ite_true]
  have he : rho + (n - j) = rho + (n - 1 - j) + 1 := by omega
  rw [he,end_park_internal_record_bit M n _ rho q (n - j) (n - 1 - j) (by omega)]

end IntMul.FiniteContinuationStack



namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem end_park_internal_intmulfinitecontinuationstacksteps_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem end_park_internal_intmulfinitecontinuationstacksteps_raw_other (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (i : Fin (M.k + 3)) (hi : i ≠ stackTape M) :
    (rawTransition M n q a).2 i = (a i,.stay) := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;> simp_all

private theorem end_park_internal_intmulfinitecontinuationstacksteps_protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

/-- A tagged scan and tagged write make the physical protection wrapper
transparent; every non-stack tape remains exact and its head stays. -/
private theorem end_park_internal_intmulfinitecontinuationstacksteps_physical_transition (M : MultitapeTM) (n : ℕ) (q : State n)
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
    · rw [end_park_internal_intmulfinitecontinuationstacksteps_raw_other M n q a i hi,end_park_internal_intmulfinitecontinuationstacksteps_protect_same_stay]
      simp only [if_neg hi]

private theorem end_park_internal_pop_start_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popStartFrame M n base rho q) = popFrame M n base rho q 0 := by
  let a := fun i => (popStartFrame M n base rho q).cells i ((popStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,popStartFrame,pushFrame,recordTape,show ¬rho + n + 1 < rho by omega,
      show rho + n + 1 ≠ rho by omega]
  have hf : recovered n q 0 = none := by
    simp [recovered,show ¬n - q.val ≤ 0 by have := q.isLt; omega]
  have ht := end_park_internal_intmulfinitecontinuationstacksteps_physical_transition M n .popStart a (popFrame M n base rho q 0).state
    (M.blank,false) (M.blank,false) .left hs
    (by simp only [rawTransition,if_pos (by have := q.isLt; omega : 0 < n),popFrame,
      dif_pos (by have := q.isLt; omega : 0 < n),hf])
    (by simp [rawTransition,show 0 < n by have := q.isLt; omega,hs])
  dsimp only [a] at ht
  change transition M n (popStartFrame M n base rho q).state _ = _ at ht
  apply end_park_internal_intmulfinitecontinuationstacksteps_cfg_ext
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

private theorem end_park_internal_pop_bit_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j < n) :
    (machine M n).step (popFrame M n base rho q j) = popFrame M n base rho q (j + 1) := by
  classical
  let a := fun i => (popFrame M n base rho q j).cells i ((popFrame M n base rho q j).head i)
  have hs : a (stackTape M) = some (M.bitSym (decide (n - 1 - j = q.val)),true) :=
    end_park_internal_pop_scan M n base rho q j hj
  have hpred : TrackedBankedSimulation.decode M (a (stackTape M)) = M.one ↔ n - 1 - j = q.val := by
    rw [hs]
    exact end_park_internal_decode_onehot M n q (n - 1 - j)
  have hf : (if TrackedBankedSimulation.decode M (a (stackTape M)) = M.one then
      some (⟨n - 1 - j,by omega⟩ : Fin n) else recovered n q j) = recovered n q (j + 1) := by
    simpa only [hpred] using end_park_internal_recovered_step n q j hj
  have ht := end_park_internal_intmulfinitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q j).state a
    (popFrame M n base rho q (j + 1)).state
    (M.bitSym (decide (n - 1 - j = q.val)),true) (M.blank,false) .left hs
    (by simp only [popFrame,dif_pos hj,rawTransition]; rw [hf])
    (by simp only [popFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply end_park_internal_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,ite_true]
      exact end_park_internal_bit_erase M n _ rho q j hj
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
private theorem end_park_internal_pop_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (popFrame M n base rho q n) = finalFrame M n base rho q := by
  let a := fun i => (popFrame M n base rho q n).cells i ((popFrame M n base rho q n).head i)
  have hs : a (stackTape M) = some (M.sep,true) := by
    simp [a,popFrame,recordTape]
  have hf : recovered n q n = some q := by simp [recovered]
  have ht := end_park_internal_intmulfinitecontinuationstacksteps_physical_transition M n (popFrame M n base rho q n).state a (.resume q)
    (M.sep,true) (M.blank,false) .stay hs
    (by simp only [popFrame,dif_neg (by omega : ¬n < n),hf,rawTransition,if_pos hs])
    (by simp [popFrame,hf,rawTransition])
  dsimp only [a] at ht
  apply end_park_internal_intmulfinitecontinuationstacksteps_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i = stackTape M
    · subst i
      simp only [ite_true,popFrame,finalFrame,pushStartFrame,ite_true,Nat.sub_self,Nat.add_zero]
      exact end_park_internal_marker_erase M n _ rho q
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

/-- Every read/erase is an actual left-moving transition, updating only a
finite recovered-label register while retaining all older prefix records. -/
private theorem end_park_internal_pop_run (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ)
    (q : Fin n) (j : ℕ) (hj : j ≤ n) :
    (machine M n).step^[j] (popFrame M n base rho q 0) = popFrame M n base rho q j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),end_park_internal_pop_bit_step M n base rho q j (by omega)]

private theorem end_park_internal_pop_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step^[n + 2] (popStartFrame M n base rho q) = finalFrame M n base rho q := by
  have h : (machine M n).step^[n + 1] (popStartFrame M n base rho q) = popFrame M n base rho q n := by
    rw [Function.iterate_add_apply,Function.iterate_one,end_park_internal_pop_start_step,end_park_internal_pop_run M n base rho q n le_rfl]
  rw [show n + 2 = (n + 1) + 1 by omega,Function.iterate_succ_apply',h,end_park_internal_pop_marker_step]


end IntMul.FiniteContinuationStack


namespace IntMul.EndParkResume

private theorem end_park_internal_intmulendparkresumepadding_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem end_park_internal_extension_old_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.oldTape N j)=c.cells j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem end_park_internal_extension_old_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) (j : Fin N.k) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.oldTape N j)=c.head j := by
  simp only [FixedTapeExtension.embed,FixedTapeExtension.oldTape,dif_pos j.isLt]
  have h : FixedTapeExtension.innerTape N ⟨j.val,by have := j.isLt; omega⟩ j.isLt=j := by apply Fin.ext; rfl
  rw [h]

private theorem end_park_internal_extension_extra_cells (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).cells (FixedTapeExtension.extraTape N)=base.cells (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem end_park_internal_extension_extra_heads (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg) :
    (FixedTapeExtension.embed N base c).head (FixedTapeExtension.extraTape N)=base.head (FixedTapeExtension.extraTape N) := by
  simp [FixedTapeExtension.embed,FixedTapeExtension.extraTape]

private theorem end_park_internal_extension_cells_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem end_park_internal_extension_heads_ready (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg) (c : N.Cfg)
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

private theorem end_park_internal_intmulendparkresumeprograms_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem end_park_internal_intmulendparkresumeprograms_fixed_iterate (N : MultitapeTM) (c : N.Cfg) (fixed : N.step c=c) (T : ℕ) :
    N.step^[T] c=c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,fixed]

private theorem end_park_internal_intmulendparkresumeprograms_halted_step (N : MultitapeTM) (c : N.Cfg) (halt : c.state=N.qHalt) : N.step c=c := by
  apply end_park_internal_intmulendparkresumeprograms_cfg_ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

/-- First entry to any family of quiescent service exits preserves the exact
complete supplied terminal configuration, including all tape heads. -/
private theorem end_park_internal_intmulendparkresumeprograms_first_exit (N : MultitapeTM) (P : N.K → Prop)
    (fixed : ∀ d : N.Cfg, P d.state → N.step d=d) (c : N.Cfg) (T : ℕ)
    (exit : P (N.step^[T] c).state) :
    ∃ t, t≤ T ∧ N.step^[t] c=N.step^[T] c ∧ ∀ s, s< t → ¬P (N.step^[s] c).state := by
  classical
  have hex : ∃ t, P (N.step^[t] c).state := ⟨T,exit⟩
  let t := Nat.find hex
  have ht : t≤ T := Nat.find_min' hex exit
  have hp : P (N.step^[t] c).state := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T=(T-t)+t by omega,Function.iterate_add_apply,end_park_internal_intmulendparkresumeprograms_fixed_iterate N _ (fixed _ hp)]
  · intro s hs
    exact Nat.find_min hex hs

private theorem end_park_internal_restore_step (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (live : c.state≠(restoreMachine M).qHalt) :
    (machine M n).step (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step c) := by
  have ht : transition M n (.restore c.state) (fun i => c.cells i (c.head i))=
      (let r := (restoreMachine M).δ c.state (fun i => c.cells i (c.head i)); (.restore r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply end_park_internal_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]
  · simp only [MultitapeTM.step,liftRestore,ht]

private theorem end_park_internal_restore_iterate (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((restoreMachine M).step^[s] c).state≠(restoreMachine M).qHalt) :
    (machine M n).step^[T] (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      end_park_internal_restore_step M n _ (live T (by omega)),Function.iterate_succ_apply']

private theorem end_park_internal_restore_to_halt (M : MultitapeTM) (n : ℕ)
    
    (c : (restoreMachine M).Cfg) (T : ℕ)
    (exit : ((restoreMachine M).step^[T] c).state=(restoreMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n).step^[s] (liftRestore M n c)=
      liftRestore M n ((restoreMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := end_park_internal_intmulendparkresumeprograms_first_exit (restoreMachine M)
    (fun q => q=(restoreMachine M).qHalt) (by intro d hd; exact end_park_internal_intmulendparkresumeprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [end_park_internal_restore_iterate M n c s hlive,he]

private theorem end_park_internal_output_step (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (live : c.state≠(outputMachine M).qHalt) :
    (machine M n).step (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step c) := by
  have ht : transition M n (.output label c.state) (fun i => c.cells i (c.head i))=
      (let r := (outputMachine M).δ c.state (fun i => c.cells i (c.head i)); (.output label r.1,r.2)) := by
    simp only [transition,if_neg live]
  apply end_park_internal_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]
  · simp only [MultitapeTM.step,liftOutput,ht]

private theorem end_park_internal_output_iterate (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((outputMachine M).step^[s] c).state≠(outputMachine M).qHalt) :
    (machine M n).step^[T] (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
      end_park_internal_output_step M n label _ (live T (by omega)),Function.iterate_succ_apply']

private theorem end_park_internal_output_to_halt (M : MultitapeTM) (n : ℕ)
     (label : Fin n)
    (c : (outputMachine M).Cfg) (T : ℕ)
    (exit : ((outputMachine M).step^[T] c).state=(outputMachine M).qHalt) :
    ∃ s, s ≤ T ∧ (machine M n).step^[s] (liftOutput M n label c)=
      liftOutput M n label ((outputMachine M).step^[T] c) := by
  obtain ⟨s,hs,he,hlive⟩ := end_park_internal_intmulendparkresumeprograms_first_exit (outputMachine M)
    (fun q => q=(outputMachine M).qHalt) (by intro d hd; exact end_park_internal_intmulendparkresumeprograms_halted_step _ d hd) c T exit
  refine ⟨s,hs,?_⟩
  rw [end_park_internal_output_iterate M n label c s hlive,he]

private theorem end_park_internal_pop_step (M : MultitapeTM) (n : ℕ)
    
    (c : (FiniteContinuationStack.machine M n).Cfg) (live : ∀ label, c.state≠.resume label) :
    (machine M n).step (liftPop M n c)=
      liftPop M n ((FiniteContinuationStack.machine M n).step c) := by
  have ht : transition M n (.pop c.state) (fun i => c.cells i (c.head i))=
      (let r := FiniteContinuationStack.transition M n c.state (fun i => c.cells i (c.head i)); (.pop r.1,r.2)) := by
    cases hs : c.state <;> first | rfl | skip
    rename_i label
    exact False.elim (live label hs)
  apply end_park_internal_intmulendparkresumeprograms_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]
  · simp only [MultitapeTM.step,liftPop,ht]

private theorem end_park_internal_pop_run (M : MultitapeTM) (n : ℕ)
    
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
    rw [Function.iterate_succ_apply',ih (by omega),end_park_internal_pop_step M n _ hlive,
      FiniteContinuationStack.end_park_internal_pop_bit_step M n base rho label j (by omega)]

private theorem end_park_internal_pop_correct (M : MultitapeTM) (n : ℕ)
    
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
    rw [Function.iterate_add_apply,Function.iterate_one,end_park_internal_pop_step M n _ hlive,
      FiniteContinuationStack.end_park_internal_pop_start_step,end_park_internal_pop_run M n base rho label n le_rfl]
  have hm : ∀ q, (FiniteContinuationStack.popFrame M n base rho label n).state≠.resume q := by
    intro q
    simp [FiniteContinuationStack.popFrame]
  rw [show n+2=(n+1)+1 by omega,Function.iterate_succ_apply',hr,end_park_internal_pop_step M n _ hm,
    FiniteContinuationStack.end_park_internal_pop_marker_step]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.FiniteContinuationStack (stackTape)
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem end_park_internal_intmulendparkresumestackframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem end_park_internal_restore_stack (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (restoreFinal M n base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.recordTape M n (base.cells (stackTape M)) rho label n ∧
    (restoreFinal M n base rho sigma offset extent c label w).head (stackTape M)=rho+n+1 := by
  have he : stackTape M=FixedTapeExtension.extraTape (TrackedSelectiveParentRestore.machine M (active M)) := by apply Fin.ext; rfl
  constructor
  · simp only [restoreFinal,he,end_park_internal_extension_extra_cells,restorePadBase]
    rw [he.symm]
    simp only [if_true]
  · simp only [restoreFinal,he,end_park_internal_extension_extra_heads,restorePadBase]
    rw [he.symm]
    simp only [if_true]

private theorem end_park_internal_restore_pop_ready (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    relabel M n (.pop .popStart)
      (liftRestore M n (restoreFinal M n base rho sigma offset extent c label w))=
    liftPop M n (FiniteContinuationStack.popStartFrame M n
      (popParent M n base rho sigma offset extent c label w) rho label) := by
  have hs := end_park_internal_restore_stack M n base rho sigma offset extent c label w
  apply end_park_internal_intmulendparkresumestackframes_cfg_ext
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

private theorem end_park_internal_popped_stack (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (popped M n base rho sigma offset extent c label w).cells (stackTape M)=
      FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
    (popped M n base rho sigma offset extent c label w).head (stackTape M)=rho := by
  constructor
  · simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true,popParent,
      (end_park_internal_restore_stack M n base rho sigma offset extent c label w).1]
    funext p
    by_cases hp : p < rho <;> simp only [FiniteContinuationStack.freshTape,FiniteContinuationStack.recordTape,hp,if_true,if_false]
  · simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.FiniteContinuationStack (stackTape)

private theorem end_park_internal_intmulendparkresumeworkframes_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (workTape M j).val := by simp [workTape]

private theorem end_park_internal_intmulendparkresumeworkframes_inner_work (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (workTape M j).val) : innerTape M (workTape M j) h=j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem end_park_internal_intmulendparkresumeworkframes_old_work_ne_stack (M : MultitapeTM) (j : Fin M.k) :
    FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)≠stackTape M := by
  intro h
  have hv := congrArg Fin.val h
  simp only [FixedTapeExtension.oldTape,workTape,stackTape] at hv
  have := j.isLt
  omega

private theorem end_park_internal_popped_other_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+3)) (hi : i≠stackTape M) :
    (popped M n base rho sigma offset extent c label w).cells i=
      (restoreFinal M n base rho sigma offset extent c label w).cells i := by
  simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg hi,popParent]

private theorem end_park_internal_popped_other_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+3)) (hi : i≠stackTape M) :
    (popped M n base rho sigma offset extent c label w).head i=
      (restoreFinal M n base rho sigma offset extent c label w).head i := by
  simp only [popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg hi,popParent]

private theorem end_park_internal_restore_work_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (restoreFinal M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)) p=
      if p < offset j then
        base.cells (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j)) p
      else some (c.cells j (p-offset j),decide (p-offset j ≤ extent j)) := by
  simp only [restoreFinal,end_park_internal_extension_old_cells,TrackedSelectiveParentRestore.finalFrame,
    TrackedBankedSimulation.embed,dif_pos (end_park_internal_intmulendparkresumeworkframes_work_ge M j),end_park_internal_intmulendparkresumeworkframes_inner_work,
    TrackedSelectiveParentRestore.parentBase,restorePlainBase]
  simp only [if_neg (by simp [workTape] : ¬(workTape M j).val=1)]

private theorem end_park_internal_restore_work_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) :
    (restoreFinal M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j))=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  simp only [restoreFinal,end_park_internal_extension_old_heads]
  simp only [TrackedSelectiveParentRestore.finalFrame,dif_pos (end_park_internal_intmulendparkresumeworkframes_work_ge M j),end_park_internal_intmulendparkresumeworkframes_inner_work,
    active,decide_eq_true_eq]

private theorem end_park_internal_output_parent_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
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
  rw [end_park_internal_popped_other_cells M n base rho sigma offset extent c label w _ (end_park_internal_intmulendparkresumeworkframes_old_work_ne_stack M j)]
  exact end_park_internal_restore_work_cells M n base rho sigma offset extent c label w j p

private theorem end_park_internal_output_parent_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (j : Fin M.k) :
    (outputPlainBase M n base rho sigma offset extent c label w).head (workTape M j)=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  simp only [outputPlainBase]
  change (popped M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) (workTape M j))=
    offset j+(if j=M.outTape then 0 else extent j+1)
  rw [end_park_internal_popped_other_heads M n base rho sigma offset extent c label w _ (end_park_internal_intmulendparkresumeworkframes_old_work_ne_stack M j)]
  exact end_park_internal_restore_work_heads M n base rho sigma offset extent c label w j

private theorem end_park_internal_restore_low (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n)
    (w : List Bool) (i : Fin (M.k+2)) (hi : i.val < 2) :
    (restoreFinal M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)=
      (restorePlainBase M n base sigma w).cells i ∧
    (restoreFinal M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedSelectiveParentRestore.machine M (active M)) i)=
      (restorePlainBase M n base sigma w).head i := by
  constructor
  · simp only [restoreFinal,end_park_internal_extension_old_cells,TrackedSelectiveParentRestore.finalFrame,
      TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),TrackedSelectiveParentRestore.parentBase]
  · simp only [restoreFinal,end_park_internal_extension_old_heads,TrackedSelectiveParentRestore.finalFrame,
      dif_neg (by omega : ¬2 ≤ i.val)]

private theorem end_park_internal_output_low (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
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
  · simp only [outputPlainBase,end_park_internal_popped_other_cells M n base rho sigma offset extent c label w _ hs]
    exact (end_park_internal_restore_low M n base rho sigma offset extent c label w i hi).1
  · simp only [outputPlainBase,end_park_internal_popped_other_heads M n base rho sigma offset extent c label w _ hs]
    exact (end_park_internal_restore_low M n base rho sigma offset extent c label w i hi).2

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem end_park_internal_work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem end_park_internal_work_injective (M : MultitapeTM) : Function.Injective (workTape M) := by
  intro i j h
  apply Fin.ext
  have h := congrArg Fin.val h
  simp only [workTape] at h
  omega

private theorem end_park_internal_embed_work (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p< offset j),show offset j+p-offset j=p by omega]

private theorem end_park_internal_embed_work_head (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (TrackedBankedSimulation.embed M base offset extent c).head (workTape M j)=offset j+c.head j := by
  simp only [TrackedBankedSimulation.embed,workTape]
  rw [dif_pos (by omega)]
  have hi : innerTape M ⟨j.val+2,by omega⟩ (by change 2≤ j.val+2; omega)=j := by
    apply Fin.ext
    simp [innerTape]
  rw [hi]

private theorem end_park_internal_embed_cells_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
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
      have hw : workTape M j=i := end_park_internal_work_inner M i hi
      rw [hw,show offset j+(p-offset j)=p by omega] at h
      exact h.symm
  · simp only [dif_neg hi]

private theorem end_park_internal_embed_heads_ready (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (heads : ∀ j, base.head (workTape M j)=offset j+c.head j) :
    (TrackedBankedSimulation.embed M base offset extent c).head=base.head := by
  funext i
  dsimp only [TrackedBankedSimulation.embed]
  by_cases hi : 2≤ i.val
  · rw [dif_pos hi]
    have h := heads (innerTape M i hi)
    rw [end_park_internal_work_inner M i hi] at h
    exact h.symm
  · simp only [dif_neg hi]


end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem end_park_internal_intmulendparkresumeoutputframes_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem end_park_internal_output_parent_work (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) (p : ℕ) :
    (outputPlainBase M n base rho sigma offset extent c label w).cells (workTape M j) (offset j+p)=
      some ((parentAtEnds M extent c).cells j p,decide (p≤ extent j)) := by
  rw [end_park_internal_output_parent_cells]
  simp only [if_neg (by omega : ¬offset j+p < offset j),Nat.add_sub_cancel_left,parentAtEnds]

private theorem end_park_internal_output_parent_work_head (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (outputPlainBase M n base rho sigma offset extent c label w).head (workTape M j)=
      offset j+(parentAtEnds M extent c).head j := by
  exact end_park_internal_output_parent_heads M n base rho sigma offset extent c label w j

private theorem end_park_internal_output_parent_buffer (M : MultitapeTM) (n : ℕ)
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (outputPlainBase M n base rho sigma offset extent c label w).cells (TrackedParentOutputBridge.bufferTape M)=
      TrackedOutputReturn.bufferTape M
        (base.cells (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M)
          (TrackedParentOutputBridge.bufferTape M))) sigma w ∧
    (outputPlainBase M n base rho sigma offset extent c label w).head (TrackedParentOutputBridge.bufferTape M)=
      sigma+w.length+1 := by
  have h := end_park_internal_output_low M n base rho sigma offset extent c label w
    (TrackedParentOutputBridge.bufferTape M) (by simp [TrackedParentOutputBridge.bufferTape])
  constructor
  · rw [h.1]
    simp only [restorePlainBase,TrackedParentOutputBridge.bufferTape,if_true]
    rfl
  · rw [h.2]
    simp only [restorePlainBase,TrackedParentOutputBridge.bufferTape,if_true]

private theorem end_park_internal_intmulendparkresumeoutputframes_buffer_idem (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    TrackedOutputReturn.bufferTape M (TrackedOutputReturn.bufferTape M base sigma w) sigma w=
      TrackedOutputReturn.bufferTape M base sigma w := by
  funext p
  by_cases hp : p < sigma <;> simp only [TrackedOutputReturn.bufferTape,hp,if_true,if_false]

private theorem end_park_internal_output_initial_ready (M : MultitapeTM) (n : ℕ)
    
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
  have hbuf := end_park_internal_output_parent_buffer M n base rho sigma offset extent c label w
  have hbc : (TrackedParentOutputBridge.parentBase M B sigma w).cells=B.cells := by
    funext i
    simp only [TrackedParentOutputBridge.parentBase]
    by_cases hb : i=TrackedParentOutputBridge.bufferTape M
    · subst i
      simp only [if_true]
      rw [hbuf.1]
      exact end_park_internal_intmulendparkresumeoutputframes_buffer_idem M _ sigma w
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
    have h := end_park_internal_embed_cells_ready M (TrackedParentOutputBridge.parentBase M B sigma w) offset extent (parentAtEnds M extent c)
      (by rw [hbc]; exact end_park_internal_output_parent_work M n base rho sigma offset extent c label w)
    rw [hbc] at h
    exact h
  have hh : (TrackedBankedSimulation.embed M (TrackedParentOutputBridge.parentBase M B sigma w)
      offset extent (parentAtEnds M extent c)).head=B.head := by
    have h := end_park_internal_embed_heads_ready M (TrackedParentOutputBridge.parentBase M B sigma w) offset extent (parentAtEnds M extent c)
      (by intro j; rw [hbh,end_park_internal_output_parent_work_head])
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
        simpa only [parentAtEnds,if_true,Nat.add_zero,TrackedParentOutputBridge.targetTape] using (end_park_internal_output_parent_work_head M n base rho sigma offset extent c label w M.outTape).symm
      · simp only [if_neg ht]
        exact congrFun hh i

private theorem end_park_internal_pop_output_ready (M : MultitapeTM) (n : ℕ)
    
    (base : (machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    relabel M n (.output label .before)
      (liftPop M n (popped M n base rho sigma offset extent c label w))=
    liftOutput M n label (outputStart M n base rho sigma offset extent c label w) := by
  have h := end_park_internal_output_initial_ready M n base rho sigma offset extent c label w
  apply end_park_internal_intmulendparkresumeoutputframes_cfg_ext
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

private theorem end_park_internal_final_work_heads (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) (j : Fin M.k) :
    (finalFrame M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
      offset j+(if j=M.outTape then 0 else extent j+1) := by
  change (outputFinal M n base rho sigma offset extent c label w).head _=_
  simp only [outputFinal,end_park_internal_extension_old_heads,TrackedParentOutputBridge.finalFrame]
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
      exact end_park_internal_work_injective M h
    rw [if_neg ht]
    have hh := congrFun
      (end_park_internal_output_initial_ready M n base rho sigma offset extent c label w).2 (workTape M j)
    simpa only [TrackedParentOutputBridge.initialFrame,TrackedParentOutputBridge.beforeFrame,
      if_neg hb,Nat.sub_zero] using hh.trans
        (end_park_internal_output_parent_heads M n base rho sigma offset extent c label w j)

private theorem end_park_internal_final_output_cells (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool) (p : ℕ) :
    (finalFrame M n base rho sigma offset extent c label w).cells
      (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))
      (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length)) := by
  change (outputFinal M n base rho sigma offset extent c label w).cells _ _=_
  simp only [outputFinal,end_park_internal_extension_old_cells,TrackedParentOutputBridge.finalFrame,
    if_pos (show workTape M M.outTape=TrackedParentOutputBridge.targetTape M by rfl)]
  simp only [TrackedBankPreparation.bankTape,
    if_neg (by omega : ¬offset M.outTape+p < offset M.outTape),Nat.add_sub_cancel_left,List.length_map]

private theorem end_park_internal_final_stack (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
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
    simp only [outputFinal,he,end_park_internal_extension_extra_cells,outputPadBase]
    rw [he.symm]
    exact (end_park_internal_popped_stack M n base rho sigma offset extent c label w).1
  · change (outputFinal M n base rho sigma offset extent c label w).head _=_
    simp only [outputFinal,he,end_park_internal_extension_extra_heads,outputPadBase]
    rw [he.symm]
    exact (end_park_internal_popped_stack M n base rho sigma offset extent c label w).2

end IntMul.EndParkResume



namespace IntMul.EndParkResume

private theorem end_park_internal_intmulendparkresumedispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem end_park_internal_restore_dispatch (M : MultitapeTM) (n : ℕ) 
    (c : (restoreMachine M).Cfg) (halt : c.state=(restoreMachine M).qHalt) :
    (machine M n).step (liftRestore M n c)=relabel M n (.pop .popStart) (liftRestore M n c) := by
  have ht : transition M n (.restore c.state) (fun i => c.cells i (c.head i))=
      (.pop .popStart,fun i => (c.cells i (c.head i),.stay)) := by
    simp only [transition,halt,if_true]
  apply end_park_internal_intmulendparkresumedispatch_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht,relabel]
  · simp only [MultitapeTM.step,liftRestore,ht,relabel]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,liftRestore,ht,relabel]

private theorem end_park_internal_pop_dispatch (M : MultitapeTM) (n : ℕ) (label : Fin n)
    (c : (FiniteContinuationStack.machine M n).Cfg) (halt : c.state=.resume label) :
    (machine M n).step (liftPop M n c)=relabel M n (.output label .before) (liftPop M n c) := by
  have ht : transition M n (.pop c.state) (fun i => c.cells i (c.head i))=
      (.output label .before,fun i => (c.cells i (c.head i),.stay)) := by
    simp only [transition,halt,if_true]
  apply end_park_internal_intmulendparkresumedispatch_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht,relabel]
  · simp only [MultitapeTM.step,liftPop,ht,relabel]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,liftPop,ht,relabel]

private theorem end_park_internal_output_dispatch (M : MultitapeTM) (n : ℕ) (label : Fin n)
    (c : (outputMachine M).Cfg) (halt : c.state=(outputMachine M).qHalt) :
    (machine M n).step (liftOutput M n label c)=relabel M n (.ready label) (liftOutput M n label c) := by
  have ht : transition M n (.output label c.state) (fun i => c.cells i (c.head i))=
      (.ready label,fun i => (c.cells i (c.head i),.stay)) := by
    simp only [transition,halt,if_true]
  apply end_park_internal_intmulendparkresumedispatch_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht,relabel]
  · simp only [MultitapeTM.step,liftOutput,ht,relabel]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,liftOutput,ht,relabel]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape)
open IntMul.FiniteContinuationStack (stackTape)

private theorem end_park_internal_result_rewind_span (M : MultitapeTM) (extent : Fin M.k → ℕ) :
    TrackedSelectiveParentRestore.selectedSpan M (active M) (fun j => extent j+1)=
      extent M.outTape+1 := by
  classical
  unfold TrackedSelectiveParentRestore.selectedSpan TrackedBankCleanup.span
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro j _
    by_cases hj : j=M.outTape
    · subst j
      simp [active]
    · simp [active,hj]
  · have h := Finset.le_sup (s:=Finset.univ)
      (f:=fun j => if active M j=true then extent j+1 else 0) (Finset.mem_univ M.outTape)
    simpa only [active,decide_true,if_true] using h

/-- A complete physical return path with result-only restoration. All child
result, stack recovery and placement operations are real charged transitions. -/
private theorem resume_correct (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n).step^[t] (initialFrame M n base rho sigma offset extent c label w)=
        finalFrame M n base rho sigma offset extent c label w ∧
      (finalFrame M n base rho sigma offset extent c label w).state=.ready label ∧
      (∀ j, (finalFrame M n base rho sigma offset extent c label w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
        offset j+(if j=M.outTape then 0 else extent j+1)) ∧
      (∀ p, (finalFrame M n base rho sigma offset extent c label w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))
        (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length))) ∧
      (finalFrame M n base rho sigma offset extent c label w).cells (stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
      (finalFrame M n base rho sigma offset extent c label w).head (stackTape M)=rho := by
  have hrestore : (restoreMachine M).step^[extent M.outTape+2]
      (restoreStart M n base rho sigma offset extent c label w)=
      restoreFinal M n base rho sigma offset extent c label w := by
    have h := (FixedTapeExtension.simulate_run
      (TrackedSelectiveParentRestore.machine M (active M))
      (restorePadBase M n base rho label)
      (TrackedSelectiveParentRestore.initialFrame M (active M)
        (restorePlainBase M n base sigma w) offset extent c (fun j => extent j+1))
      (extent M.outTape+2)).1
    have r := TrackedSelectiveParentRestore.restore_correct M (active M)
      (restorePlainBase M n base sigma w) offset extent c unique (fun j => extent j+1)
    rw [end_park_internal_result_rewind_span] at r
    rw [show extent M.outTape+1+1=extent M.outTape+2 by omega] at r
    rw [r.1] at h
    exact h
  have hrhalt : ((restoreMachine M).step^[extent M.outTape+2]
      (restoreStart M n base rho sigma offset extent c label w)).state=(restoreMachine M).qHalt := by
    rw [hrestore]
    rfl
  obtain ⟨s,hs,hsrun⟩ := end_park_internal_restore_to_halt M n
    (restoreStart M n base rho sigma offset extent c label w) (extent M.outTape+2) hrhalt
  rw [hrestore] at hsrun
  have hdown : (machine M n).step^[s+1]
      (initialFrame M n base rho sigma offset extent c label w)=
      liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label) := by
    change (machine M n).step^[s+1]
      (liftRestore M n (restoreStart M n base rho sigma offset extent c label w))=_
    rw [Function.iterate_succ_apply',hsrun,end_park_internal_restore_dispatch M n _ rfl,end_park_internal_restore_pop_ready]
  have hpop : (machine M n).step^[n+3]
      (liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label))=
      liftOutput M n label (outputStart M n base rho sigma offset extent c label w) := by
    rw [show n+3=(n+2)+1 by omega,Function.iterate_succ_apply',end_park_internal_pop_correct]
    change (machine M n).step (liftPop M n (popped M n base rho sigma offset extent c label w))=_
    rw [end_park_internal_pop_dispatch M n label _ rfl,end_park_internal_pop_output_ready]
  have houtput : (outputMachine M).step^[w.length+2*max w.length (extent M.outTape)+5]
      (outputStart M n base rho sigma offset extent c label w)=
      outputFinal M n base rho sigma offset extent c label w := by
    have h := (FixedTapeExtension.simulate_run (TrackedParentOutputBridge.machine M)
      (outputPadBase M n base rho sigma offset extent c label w)
      (TrackedParentOutputBridge.initialFrame M
        (outputPlainBase M n base rho sigma offset extent c label w)
        sigma offset extent (parentAtEnds M extent c) w)
      (w.length+2*max w.length (extent M.outTape)+5)).1
    rw [(TrackedParentOutputBridge.output_correct M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w
      ((unique M.outTape 0).mpr rfl) tail).1] at h
    exact h
  have hohalt : ((outputMachine M).step^[w.length+2*max w.length (extent M.outTape)+5]
      (outputStart M n base rho sigma offset extent c label w)).state=(outputMachine M).qHalt := by
    rw [houtput]
    rfl
  obtain ⟨u,hu,hurun⟩ := end_park_internal_output_to_halt M n label
    (outputStart M n base rho sigma offset extent c label w)
    (w.length+2*max w.length (extent M.outTape)+5) hohalt
  rw [houtput] at hurun
  have hup : (machine M n).step^[u+1]
      (liftOutput M n label (outputStart M n base rho sigma offset extent c label w))=
      finalFrame M n base rho sigma offset extent c label w := by
    rw [Function.iterate_succ_apply',hurun,end_park_internal_output_dispatch M n label _ rfl]
    rfl
  refine ⟨(u+1)+((n+3)+(s+1)),by omega,?_,rfl,
    end_park_internal_final_work_heads M n base rho sigma offset extent c label w,
    end_park_internal_final_output_cells M n base rho sigma offset extent c label w,
    (end_park_internal_final_stack M n base rho sigma offset extent c label w).1,
    (end_park_internal_final_stack M n base rho sigma offset extent c label w).2⟩
  rw [Function.iterate_add_apply (machine M n).step (u+1) ((n+3)+(s+1)),
    Function.iterate_add_apply (machine M n).step (n+3) (s+1),hdown,hpop,hup]

end IntMul.EndParkResume


open IntMul IntMul.EndParkResume
open IntMul.BankedSimulation (workTape)
open IntMul.FiniteContinuationStack (stackTape)

theorem solution (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n).step^[t] (initialFrame M n base rho sigma offset extent c label w)=
        finalFrame M n base rho sigma offset extent c label w ∧
      (finalFrame M n base rho sigma offset extent c label w).state=.ready label ∧
      (∀ j, (finalFrame M n base rho sigma offset extent c label w).head
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M j))=
        offset j+(if j=M.outTape then 0 else extent j+1)) ∧
      (∀ p, (finalFrame M n base rho sigma offset extent c label w).cells
        (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) (workTape M M.outTape))
        (offset M.outTape+p)=some (M.tapeOf (w.map M.bitSym) p,decide (p ≤ w.length))) ∧
      (finalFrame M n base rho sigma offset extent c label w).cells (stackTape M)=
        FiniteContinuationStack.freshTape M (base.cells (stackTape M)) rho ∧
      (finalFrame M n base rho sigma offset extent c label w).head (stackTape M)=rho :=
  IntMul.EndParkResume.resume_correct M n base rho sigma offset extent c label w unique tail

#print axioms solution
