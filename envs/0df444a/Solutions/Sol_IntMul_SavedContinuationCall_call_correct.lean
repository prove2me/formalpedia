-- Prove2me | solution 1 for IntMul.SavedContinuationCall.call_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T00:19:41.130898+00:00
-- url     : https://prove2.me/submissions/c74b420d-2cb6-423e-8b98-e3809f711156

import Definitions.Def_IntMul_SavedContinuationCall
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedReentrantCall_call_correct
import Mathlib.Tactic
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)


namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

private theorem stack_tape_zero_ne_one (M : MultitapeTM) : M.zero ≠ M.one := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,and_true] at hd
  tauto

private theorem decode_onehot (M : MultitapeTM) (n : ℕ) (q : Fin n) (j : ℕ) :
    TrackedBankedSimulation.decode M (some (M.bitSym (decide (j = q.val)),true)) = M.one ↔ j = q.val := by
  by_cases hj : j = q.val
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode]
  · simp [hj,MultitapeTM.bitSym,TrackedBankedSimulation.decode,stack_tape_zero_ne_one M]

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

private theorem stack_step_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem stack_step_raw_other (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (i : Fin (M.k + 3)) (hi : i ≠ stackTape M) :
    (rawTransition M n q a).2 i = (a i,.stay) := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;> simp_all

private theorem stack_step_protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

/-- A tagged scan and tagged write make the physical protection wrapper
transparent; every non-stack tape remains exact and its head stays. -/
private theorem stack_step_physical_transition (M : MultitapeTM) (n : ℕ) (q : State n)
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
    · rw [stack_step_raw_other M n q a i hi,stack_step_protect_same_stay]
      simp only [if_neg hi]

private theorem push_marker_step (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n).step (pushStartFrame M n base rho q) = pushFrame M n base rho q 0 := by
  let a := fun i => (pushStartFrame M n base rho q).cells i ((pushStartFrame M n base rho q).head i)
  have hs : a (stackTape M) = some (M.blank,false) := by
    simp [a,pushStartFrame,freshTape]
  have ht := stack_step_physical_transition M n (.pushStart q) a (pushFrame M n base rho q 0).state
    (M.blank,false) (M.sep,true) .right hs
    (by simp [rawTransition,pushFrame,show 0 < n by have := q.isLt; omega]) (by simp [rawTransition])
  dsimp only [a] at ht
  change transition M n (pushStartFrame M n base rho q).state _ = _ at ht
  apply stack_step_cfg_ext
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
  have ht := stack_step_physical_transition M n (pushFrame M n base rho q j).state a
    (pushFrame M n base rho q (j + 1)).state (M.blank,false) (M.bitSym (decide (j = q.val)),true) .right hs
    (by simp only [pushFrame,dif_pos hj,rawTransition])
    (by simp only [pushFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply stack_step_cfg_ext
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
    simp only [pushFrame,dif_neg (by omega : ¬n < n),transition,rawTransition,stack_step_protect_same_stay]
  apply stack_step_cfg_ext
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
  have ht := stack_step_physical_transition M n .popStart a (popFrame M n base rho q 0).state
    (M.blank,false) (M.blank,false) .left hs
    (by simp only [rawTransition,if_pos (by have := q.isLt; omega : 0 < n),popFrame,
      dif_pos (by have := q.isLt; omega : 0 < n),hf])
    (by simp [rawTransition,show 0 < n by have := q.isLt; omega,hs])
  dsimp only [a] at ht
  change transition M n (popStartFrame M n base rho q).state _ = _ at ht
  apply stack_step_cfg_ext
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
  have ht := stack_step_physical_transition M n (popFrame M n base rho q j).state a
    (popFrame M n base rho q (j + 1)).state
    (M.bitSym (decide (n - 1 - j = q.val)),true) (M.blank,false) .left hs
    (by simp only [popFrame,dif_pos hj,rawTransition]; rw [hf])
    (by simp only [popFrame,dif_pos hj,rawTransition]; split_ifs <;> simp)
  dsimp only [a] at ht
  apply stack_step_cfg_ext
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
  have ht := stack_step_physical_transition M n (popFrame M n base rho q n).state a (.resume q)
    (M.sep,true) (M.blank,false) .stay hs
    (by simp only [popFrame,dif_neg (by omega : ¬n < n),hf,rawTransition,if_pos hs])
    (by simp [popFrame,hf,rawTransition])
  dsimp only [a] at ht
  apply stack_step_cfg_ext
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



namespace IntMul.SavedContinuationCall

private theorem program_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

noncomputable def startChild (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (FiniteContinuationStack.machine M n).Cfg) :
    (childMachine M).Cfg where
  state := (childMachine M).qStart
  cells := c.cells
  head := c.head

noncomputable def startPop (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (childMachine M).Cfg) :
    (FiniteContinuationStack.machine M n).Cfg where
  state := .popStart
  cells := c.cells
  head := c.head

private theorem program_lift_push_step (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (FiniteContinuationStack.machine M n).Cfg)
    (live : c.state ≠ .pushDone) :
    (machine M n initial).step (liftPush M n initial c) = liftPush M n initial ((FiniteContinuationStack.machine M n).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftPush,transition,live]
  · simp [MultitapeTM.step,liftPush,transition,live]
  · simp [MultitapeTM.step,liftPush,transition,live]

private theorem program_lift_child_step (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (childMachine M).Cfg)
    (live : c.state ≠ (childMachine M).qHalt) :
    (machine M n initial).step (liftChild M n initial c) = liftChild M n initial ((childMachine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftChild,transition,live]
  · simp [MultitapeTM.step,liftChild,transition,live]
  · simp [MultitapeTM.step,liftChild,transition,live]

private theorem lift_pop_step (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (FiniteContinuationStack.machine M n).Cfg) :
    (machine M n initial).step (liftPop M n initial c) = liftPop M n initial ((FiniteContinuationStack.machine M n).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftPop,transition]
  · simp [MultitapeTM.step,liftPop,transition]
  · simp [MultitapeTM.step,liftPop,transition]

private theorem program_lift_push_iterate (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (FiniteContinuationStack.machine M n).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((FiniteContinuationStack.machine M n).step^[s] c).state ≠ .pushDone) :
    (machine M n initial).step^[T] (liftPush M n initial c) = liftPush M n initial ((FiniteContinuationStack.machine M n).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_push_step M n initial _ (live T (by omega)),Function.iterate_succ_apply']

private theorem program_lift_child_iterate (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (childMachine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((childMachine M).step^[s] c).state ≠ (childMachine M).qHalt) :
    (machine M n initial).step^[T] (liftChild M n initial c) = liftChild M n initial ((childMachine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_child_step M n initial _ (live T (by omega)),Function.iterate_succ_apply']

private theorem lift_pop_iterate (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (FiniteContinuationStack.machine M n).Cfg) (T : ℕ) :
    (machine M n initial).step^[T] (liftPop M n initial c) = liftPop M n initial ((FiniteContinuationStack.machine M n).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,lift_pop_step,Function.iterate_succ_apply']

private theorem program_push_dispatch (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (FiniteContinuationStack.machine M n).Cfg)
    (halt : c.state = .pushDone) :
    (machine M n initial).step (liftPush M n initial c) = liftChild M n initial (startChild M n initial c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftPush,liftChild,startChild,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftPush,liftChild,startChild,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftPush,liftChild,startChild,transition,halt]

private theorem program_child_dispatch (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (childMachine M).Cfg)
    (halt : c.state = (childMachine M).qHalt) :
    (machine M n initial).step (liftChild M n initial c) = liftPop M n initial (startPop M n initial c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftChild,liftPop,startPop,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftChild,liftPop,startPop,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftChild,liftPop,startPop,transition,halt]

private theorem program_halted_step (N : MultitapeTM) (c : N.Cfg) (h : c.state = N.qHalt) : N.step c = c := by
  apply program_cfg_ext
  · simp [MultitapeTM.step,h,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,h,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,h,N.halt_fixed]

private theorem program_halted_iterate (N : MultitapeTM) (c : N.Cfg) (h : c.state = N.qHalt) (T : ℕ) :
    N.step^[T] c = c := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,program_halted_step N c h]

private theorem program_first_halt (N : MultitapeTM) (c : N.Cfg) (T : ℕ) (h : (N.step^[T] c).state = N.qHalt) :
    ∃ t, t ≤ T ∧ N.step^[t] c = N.step^[T] c ∧ ∀ s, s < t → (N.step^[s] c).state ≠ N.qHalt := by
  classical
  have hex : ∃ t, (N.step^[t] c).state = N.qHalt := ⟨T,h⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex h
  have hh : (N.step^[t] c).state = N.qHalt := Nat.find_spec hex
  refine ⟨t,ht,?_,?_⟩
  · rw [show T = (T - t) + t by omega,Function.iterate_add_apply,program_halted_iterate N _ hh]
  · intro s hs
    exact Nat.find_min hex hs

/-- Output return likewise dispatches at its first halt, preserving its
entire returned buffer and child banks, including a charged switch step. -/
private theorem run_child_to_pop (M : MultitapeTM) (n : ℕ) (initial : Fin n) (c : (childMachine M).Cfg) (T : ℕ)
    (halt : ((childMachine M).step^[T] c).state = (childMachine M).qHalt) :
    ∃ t, t ≤ T + 1 ∧ (machine M n initial).step^[t] (liftChild M n initial c) =
      liftPop M n initial (startPop M n initial ((childMachine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := program_first_halt (childMachine M) c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',program_lift_child_iterate M n initial c t hn,he,program_child_dispatch M n initial _ halt]

private theorem program_push_liveness (M : MultitapeTM) (n : ℕ)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (q : Fin n) (s : ℕ) (hs : s < n + 1) :
    ((FiniteContinuationStack.machine M n).step^[s] (FiniteContinuationStack.pushStartFrame M n base rho q)).state ≠ .pushDone := by
  cases s with
  | zero => simp [FiniteContinuationStack.pushStartFrame]
  | succ s =>
      rw [Function.iterate_add_apply,Function.iterate_one,FiniteContinuationStack.push_marker_step,
        FiniteContinuationStack.push_run M n base rho q s (by omega)]
      simp only [FiniteContinuationStack.pushFrame,dif_pos (by omega : s < n)]
      simp

/-- Physical finite-label push and one charged outer dispatch into the child
phase. Explicit frame liveness prevents a premature completed-push switch. -/
private theorem run_push_to_child (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (q : Fin n) :
    (machine M n initial).step^[n + 2] (liftPush M n initial (FiniteContinuationStack.pushStartFrame M n base rho q)) =
      liftChild M n initial (startChild M n initial (FiniteContinuationStack.pushFrame M n base rho q n)) := by
  rw [show n + 2 = (n + 1) + 1 by omega,Function.iterate_succ_apply',
    program_lift_push_iterate M n initial _ (n + 1) (by intro s hs; exact program_push_liveness M n base rho q s hs),
    FiniteContinuationStack.push_correct,program_push_dispatch M n initial _
      (by simp [FiniteContinuationStack.pushFrame])]

end IntMul.SavedContinuationCall




namespace IntMul.SavedContinuationCall

private theorem frame_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

noncomputable def pushBase (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (c : (TrackedReentrantCall.machine M).Cfg) :
    (FiniteContinuationStack.machine M n).Cfg :=
  stackBase M n (FixedTapeExtension.embed (TrackedReentrantCall.machine M) (childBase M n initial base) c)

noncomputable def pushed (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (c : (TrackedReentrantCall.machine M).Cfg) : (FiniteContinuationStack.machine M n).Cfg :=
  FiniteContinuationStack.pushFrame M n (pushBase M n initial base c) rho q n

private theorem frame_stack_high (M : MultitapeTM) :
    ¬(FiniteContinuationStack.stackTape M).val < (TrackedReentrantCall.machine M).k := by
  change ¬M.k + 2 < M.k + 2
  omega

private theorem frame_nonstack_low (M : MultitapeTM) (i : Fin (M.k + 3))
    (hi : i ≠ FiniteContinuationStack.stackTape M) : i.val < (TrackedReentrantCall.machine M).k := by
  change i.val < M.k + 2
  have hb : i.val < M.k + 3 := i.isLt
  have hn : i.val ≠ M.k + 2 := by
    intro h
    apply hi
    apply Fin.ext
    exact h
  omega

/-- The completed physical push leaves the child starting configuration
verbatim on the old tapes, and the actual stack record is the added tape. -/
private theorem push_ready (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (c : (TrackedReentrantCall.machine M).Cfg) (start : c.state = (TrackedReentrantCall.machine M).qStart) :
    startChild M n initial (pushed M n initial base rho q c) =
      FixedTapeExtension.embed (TrackedReentrantCall.machine M)
        (startChild M n initial (pushed M n initial base rho q c)) c := by
  apply frame_cfg_ext
  · exact start.symm
  · funext i
    by_cases hi : i = FiniteContinuationStack.stackTape M
    · subst i
      simp only [FixedTapeExtension.embed,dif_neg (frame_stack_high M)]
    · have hl := frame_nonstack_low M i hi
      simp only [startChild,pushed,FiniteContinuationStack.pushFrame,if_neg hi,
        pushBase,stackBase,FixedTapeExtension.embed,dif_pos hl]
  · funext i
    by_cases hi : i = FiniteContinuationStack.stackTape M
    · subst i
      simp only [FixedTapeExtension.embed,dif_neg (frame_stack_high M)]
    · have hl := frame_nonstack_low M i hi
      simp only [startChild,pushed,FiniteContinuationStack.pushFrame,if_neg hi,
        pushBase,stackBase,FixedTapeExtension.embed,dif_pos hl]

/-- Exact-time child execution preserves the physical pushed record and
its parked head. The charged dispatch enters the pop frame without a write. -/
private theorem child_ready (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (c d : (TrackedReentrantCall.machine M).Cfg) :
    startPop M n initial (FixedTapeExtension.embed (TrackedReentrantCall.machine M)
      (startChild M n initial (pushed M n initial base rho q c)) d) =
      FiniteContinuationStack.popStartFrame M n (pushBase M n initial base d) rho q := by
  apply frame_cfg_ext
  · rfl
  · funext i
    by_cases hi : i = FiniteContinuationStack.stackTape M
    · subst i
      simp only [startPop,FixedTapeExtension.embed,dif_neg (frame_stack_high M),startChild,pushed,
        FiniteContinuationStack.pushFrame,ite_true,FiniteContinuationStack.popStartFrame,
        pushBase,stackBase,childBase]
    · have hl := frame_nonstack_low M i hi
      simp only [startPop,FixedTapeExtension.embed,dif_pos hl,FiniteContinuationStack.popStartFrame,
        FiniteContinuationStack.pushFrame,if_neg hi,pushBase,stackBase]
  · funext i
    by_cases hi : i = FiniteContinuationStack.stackTape M
    · subst i
      simp only [startPop,FixedTapeExtension.embed,dif_neg (frame_stack_high M),startChild,pushed,
        FiniteContinuationStack.pushFrame,ite_true,FiniteContinuationStack.popStartFrame,
        pushBase,stackBase,childBase]
    · have hl := frame_nonstack_low M i hi
      simp only [startPop,FixedTapeExtension.embed,dif_pos hl,FiniteContinuationStack.popStartFrame,
        FiniteContinuationStack.pushFrame,if_neg hi,pushBase,stackBase]

private theorem frame_old_ne_stack (M : MultitapeTM) (j : Fin (TrackedReentrantCall.machine M).k) :
    FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j ≠ FiniteContinuationStack.stackTape M := by
  intro h
  have he := congrArg Fin.val h
  have hj := j.isLt
  change j.val = M.k + 2 at he
  change j.val < M.k + 2 at hj
  omega

private theorem frame_inner_old (M : MultitapeTM) (j : Fin (TrackedReentrantCall.machine M).k)
    (h : (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j).val < (TrackedReentrantCall.machine M).k) :
    FixedTapeExtension.innerTape (TrackedReentrantCall.machine M)
      (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j) h = j := by
  apply Fin.ext
  rfl

private theorem final_old_cells (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (c : (TrackedReentrantCall.machine M).Cfg) (j : Fin (TrackedReentrantCall.machine M).k) :
    (finalFrame M n initial base rho q c).cells (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j) = c.cells j := by
  simp only [finalFrame,liftPop,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg (frame_old_ne_stack M j),stackBase,FixedTapeExtension.embed,
    dif_pos (show (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j).val <
      (TrackedReentrantCall.machine M).k from j.isLt),frame_inner_old]

private theorem final_old_heads (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (c : (TrackedReentrantCall.machine M).Cfg) (j : Fin (TrackedReentrantCall.machine M).k) :
    (finalFrame M n initial base rho q c).head (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j) = c.head j := by
  simp only [finalFrame,liftPop,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    if_neg (frame_old_ne_stack M j),stackBase,FixedTapeExtension.embed,
    dif_pos (show (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) j).val <
      (TrackedReentrantCall.machine M).k from j.isLt),frame_inner_old]

/-- Every continuation-record cell is restored to its initial fresh suffix,
all older records are retained, and the physical stack head is back at rho. -/
private theorem final_stack (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n) (c : (TrackedReentrantCall.machine M).Cfg) :
    (finalFrame M n initial base rho q c).cells (FiniteContinuationStack.stackTape M) =
      FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
    (finalFrame M n initial base rho q c).head (FiniteContinuationStack.stackTape M) = rho := by
  simp only [finalFrame,liftPop,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,
    ite_true,stackBase,FixedTapeExtension.embed,dif_neg (frame_stack_high M),childBase]
  exact ⟨trivial,trivial⟩

end IntMul.SavedContinuationCall




namespace IntMul.SavedContinuationCall

/-- Actual finite-label push, exact-time stack-preserving child execution,
then actual pop recovering the label. Both outer dispatches are charged. -/
private theorem run_correct (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n)
    (c : (TrackedReentrantCall.machine M).Cfg)
    (start : c.state = (TrackedReentrantCall.machine M).qStart) (T : ℕ)
    (halt : ((TrackedReentrantCall.machine M).step^[T] c).state = (TrackedReentrantCall.machine M).qHalt) :
    ∃ t, t ≤ T + 2 * n + 5 ∧ (machine M n initial).step^[t] (initialFrame M n initial base rho q c) =
      finalFrame M n initial base rho q ((TrackedReentrantCall.machine M).step^[T] c) := by
  have push := run_push_to_child M n initial (pushBase M n initial base c) rho q
  change (machine M n initial).step^[n + 2] (initialFrame M n initial base rho q c) =
    liftChild M n initial (startChild M n initial (pushed M n initial base rho q c)) at push
  have childrun : (childMachine M).step^[T] (startChild M n initial (pushed M n initial base rho q c)) =
      FixedTapeExtension.embed (TrackedReentrantCall.machine M)
        (startChild M n initial (pushed M n initial base rho q c)) ((TrackedReentrantCall.machine M).step^[T] c) := by
    calc
      _ = (childMachine M).step^[T] (FixedTapeExtension.embed (TrackedReentrantCall.machine M)
          (startChild M n initial (pushed M n initial base rho q c)) c) :=
        congrArg ((childMachine M).step^[T]) (push_ready M n initial base rho q c start)
      _ = _ := (FixedTapeExtension.simulate_run (TrackedReentrantCall.machine M)
        (startChild M n initial (pushed M n initial base rho q c)) c T).1
  have chalt : ((childMachine M).step^[T] (startChild M n initial (pushed M n initial base rho q c))).state =
      (childMachine M).qHalt := by
    rw [childrun]
    exact halt
  obtain ⟨s,hs,hsrun⟩ := run_child_to_pop M n initial (startChild M n initial (pushed M n initial base rho q c)) T chalt
  rw [childrun,child_ready] at hsrun
  have hsp : (machine M n initial).step^[s + (n + 2)] (initialFrame M n initial base rho q c) =
      liftPop M n initial (FiniteContinuationStack.popStartFrame M n
        (pushBase M n initial base ((TrackedReentrantCall.machine M).step^[T] c)) rho q) := by
    rw [Function.iterate_add_apply,push,hsrun]
  refine ⟨(n + 2) + (s + (n + 2)),by omega,?_⟩
  rw [Function.iterate_add_apply,hsp,lift_pop_iterate,FiniteContinuationStack.pop_correct]
  rfl

open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- Complete physical child call with saved finite continuation recovery. -/
private theorem call_correct (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n) (parent : (TrackedReentrantCall.machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (x y : List Bool)
    (source : parent.cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedBankPreparation.sourceTape M (parent.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (inputWord M x y))
    (source_head : parent.head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 2 * span M extent + 2 * n + 24 ∧
      (machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c) =
        callFinalFrame M n initial base rho q parent sigma offset extent c x y T w ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).state =
        .inr (.inr (.resume q)) ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FiniteContinuationStack.stackTape M) =
          FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FiniteContinuationStack.stackTape M) = rho ∧
      (∀ j, ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (BankedSimulation.workTape M j)) =
        (TrackedReentrantCall.initialFrame M parent offset extent c).cells (BankedSimulation.workTape M j)) ∧
      (∀ j, ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (BankedSimulation.workTape M j)) = offset j) ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) ⟨1,by change 1 < M.k + 2; omega⟩) =
        TrackedOutputReturn.bufferTape M (parent.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) ⟨1,by change 1 < M.k + 2; omega⟩) =
          sigma + w.length + 1 := by
  obtain ⟨r,hr,he,hcells,hheads,hbuf,hbufhead⟩ := TrackedReentrantCall.call_correct M parent sigma offset extent c
    near tail unique x y source source_head T halt w out
  have chalt : ((TrackedReentrantCall.machine M).step^[r]
      (TrackedReentrantCall.initialFrame M parent offset extent c)).state = (TrackedReentrantCall.machine M).qHalt := by
    rw [he]
    rfl
  obtain ⟨t,ht,htrun⟩ := run_correct M n initial base rho q
    (TrackedReentrantCall.initialFrame M parent offset extent c) (by rfl) r chalt
  rw [he] at htrun
  change (machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c) =
    callFinalFrame M n initial base rho q parent sigma offset extent c x y T w at htrun
  refine ⟨t,by omega,htrun,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [htrun]
    rfl
  · rw [htrun]
    exact (final_stack M n initial base rho q _).1
  · rw [htrun]
    exact (final_stack M n initial base rho q _).2
  · intro j
    rw [htrun]
    change (finalFrame M n initial base rho q _).cells _ = _
    rw [final_old_cells,←he]
    exact hcells j
  · intro j
    rw [htrun]
    change (finalFrame M n initial base rho q _).head _ = _
    rw [final_old_heads,←he]
    exact hheads j
  · rw [htrun]
    change (finalFrame M n initial base rho q _).cells _ = _
    rw [final_old_cells,←he]
    exact hbuf
  · rw [htrun]
    change (finalFrame M n initial base rho q _).head _ = _
    rw [final_old_heads,←he]
    exact hbufhead

end IntMul.SavedContinuationCall



open IntMul IntMul.SavedContinuationCall

theorem solution (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n) (parent : (TrackedReentrantCall.machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (x y : List Bool)
    (source : parent.cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedBankPreparation.sourceTape M (parent.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (inputWord M x y))
    (source_head : parent.head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 2 * span M extent + 2 * n + 24 ∧
      (machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c) =
        callFinalFrame M n initial base rho q parent sigma offset extent c x y T w ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).state =
        .inr (.inr (.resume q)) ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FiniteContinuationStack.stackTape M) =
          FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FiniteContinuationStack.stackTape M) = rho ∧
      (∀ j, ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (BankedSimulation.workTape M j)) =
        (TrackedReentrantCall.initialFrame M parent offset extent c).cells (BankedSimulation.workTape M j)) ∧
      (∀ j, ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (BankedSimulation.workTape M j)) = offset j) ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) ⟨1,by change 1 < M.k + 2; omega⟩) =
        TrackedOutputReturn.bufferTape M (parent.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) ⟨1,by change 1 < M.k + 2; omega⟩) =
          sigma + w.length + 1 :=
  IntMul.SavedContinuationCall.call_correct M n initial base rho q parent sigma offset extent c near tail unique x y source source_head T halt w out

#print axioms solution
