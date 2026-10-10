-- Prove2me | solution 1 for IntMul.TrackedParentRestore.restore_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T23:37:58.250305+00:00
-- url     : https://prove2.me/submissions/85126807-d1e0-4db7-b346-07ac77750cfe

import Definitions.Def_IntMul_TrackedParentRestore
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)


namespace IntMul.TrackedParentRestore

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankCleanup (span)

private theorem frame_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (workTape M j).val := by simp [workTape]

private theorem frame_inner_work (M : MultitapeTM) (j : Fin M.k) (h : 2 ≤ (workTape M j).val) :
    innerTape M (workTape M j) h = j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem frame_work_inner (M : MultitapeTM) (i : Fin (M.k + 2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h) = i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem frame_cells (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) (p : ℕ) :
    (rewindFrame M base offset extent c pos r).cells (workTape M j) (offset j + p) =
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [rewindFrame,TrackedBankedSimulation.embed,dif_pos (frame_work_ge M j),frame_inner_work,parentBase]
  simp only [if_neg (by omega : ¬offset j + p < offset j),Nat.add_sub_cancel_left]

private theorem frame_heads (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M base offset extent c pos r).head (workTape M j) = offset j + (pos j - r) := by
  simp [rewindFrame,frame_work_ge,frame_inner_work]

private theorem frame_scan (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M base offset extent c pos r).head (workTape M j)) =
      some (c.cells j (pos j - r),decide (pos j - r ≤ extent j)) := by
  rw [frame_heads,frame_cells]

/-- Head j sees its retained parent marker exactly when its rewind is done.
Unique parent markers exclude an earlier stop inside the parent's payload. -/
private theorem frame_marker_iff (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M base offset extent c pos r).head (workTape M j)) = some (M.startSym,true) ↔ pos j ≤ r := by
  rw [frame_scan]
  constructor
  · intro h
    have hp := (unique j (pos j - r)).mp (congrArg Prod.fst (Option.some.inj h))
    omega
  · intro h
    simp only [Nat.sub_eq_zero_of_le h,(unique j 0).mpr rfl,
      show (0 : ℕ) ≤ extent j by omega,decide_true]

private theorem frame_not_global (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M base offset extent c pos r).head (workTape M j)) ≠ none := by
  rw [frame_scan]
  simp

private theorem all_markers_iff (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) (pos : Fin M.k → ℕ) (r : ℕ) :
    (∀ j, (rewindFrame M base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M base offset extent c pos r).head (workTape M j)) = some (M.startSym,true)) ↔ span M pos ≤ r := by
  simp only [frame_marker_iff M base offset extent c unique]
  constructor
  · intro h
    exact Finset.sup_le (by intro j _; exact h j)
  · intro h j
    exact (Finset.le_sup (Finset.mem_univ j)).trans h

/-- All parent bank cells and flags are retained, with every head restored to
its local boundary. Root input, caller output and their heads stay fixed. -/
private theorem final_heads (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ) (c : M.Cfg) :
    ∀ j, (finalFrame M base offset extent c).head (workTape M j) = offset j := by
  intro j
  simp [finalFrame,frame_work_ge,frame_inner_work]

end IntMul.TrackedParentRestore



namespace IntMul.TrackedParentRestore

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankCleanup (span)

private theorem complete_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem complete_work_inner (M : MultitapeTM) (i : Fin (M.k + 2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h) = i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem complete_protect_same_stay (M : MultitapeTM) (a : TrackedBankedSimulation.Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem rewind_step (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (pos : Fin M.k → ℕ) (r : ℕ) (hr : r < span M pos) :
    (machine M).step (rewindFrame M base offset extent c pos r) =
      rewindFrame M base offset extent c pos (r + 1) := by
  classical
  let a := fun i => (rewindFrame M base offset extent c pos r).cells i
    ((rewindFrame M base offset extent c pos r).head i)
  have hn : ¬∀ j, a (workTape M j) = some (M.startSym,true) := by
    intro h
    have hh := (all_markers_iff M base offset extent c unique pos r).mp h
    omega
  have ht : transition M .rewind a =
      (.rewind,fun i => (a i,if 2 ≤ i.val ∧ a i ≠ some (M.startSym,true) then .left else .stay)) := by
    dsimp only [transition,rawTransition]
    rw [if_neg hn]
    apply Prod.ext
    · rfl
    · funext i
      change TrackedBankCleanup.protect M (a i) (a i)
        (if 2 ≤ i.val ∧ a i ≠ some (M.startSym,true) then .left else .stay) =
        (a i,if 2 ≤ i.val ∧ a i ≠ some (M.startSym,true) then .left else .stay)
      by_cases hi : 2 ≤ i.val
      · have ha : a i ≠ none := by
          have h := frame_not_global M base offset extent c pos r (innerTape M i hi)
          rw [complete_work_inner M i hi] at h
          exact h
        cases hs : a i with
        | none => exact False.elim (ha hs)
        | some s => simp only [hs,TrackedBankCleanup.protect]
      · rw [if_neg (by intro h; exact hi h.1)]
        exact complete_protect_same_stay M (a i)
  dsimp only [a] at ht
  change transition M (rewindFrame M base offset extent c pos r).state _ = _ at ht
  apply complete_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · have hm : a i = some (M.startSym,true) ↔ pos (innerTape M i hi) ≤ r := by
        have h := frame_marker_iff M base offset extent c unique pos r (innerTape M i hi)
        rw [complete_work_inner M i hi] at h
        exact h
      by_cases hd : r < pos (innerTape M i hi)
      · rw [if_pos ⟨hi,by intro h; have hp := hm.mp h; omega⟩]
        simp only [rewindFrame,dif_pos hi]
        omega
      · rw [if_neg (by intro h; apply h.2; exact hm.mpr (by omega))]
        simp only [rewindFrame,dif_pos hi,Nat.sub_eq_zero_of_le (by omega : pos (innerTape M i hi) ≤ r),
          Nat.sub_eq_zero_of_le (by omega : pos (innerTape M i hi) ≤ r + 1)]
    · rw [if_neg (by intro h; exact hi h.1)]
      simp only [rewindFrame,dif_neg hi]

private theorem rewind_run (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (pos : Fin M.k → ℕ) (r : ℕ) (hr : r ≤ span M pos) :
    (machine M).step^[r] (rewindFrame M base offset extent c pos 0) = rewindFrame M base offset extent c pos r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply',ih (by omega),rewind_step M base offset extent c unique pos r (by omega)]

private theorem rewind_end (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) (pos : Fin M.k → ℕ) :
    (machine M).step (rewindFrame M base offset extent c pos (span M pos)) =
      finalFrame M base offset extent c := by
  have hf := (all_markers_iff M base offset extent c unique pos (span M pos)).mpr le_rfl
  have ht : transition M .rewind
      (fun i => (rewindFrame M base offset extent c pos (span M pos)).cells i
        ((rewindFrame M base offset extent c pos (span M pos)).head i)) =
      (.halt,fun i => ((rewindFrame M base offset extent c pos (span M pos)).cells i
        ((rewindFrame M base offset extent c pos (span M pos)).head i),.stay)) := by
    simp only [transition,rawTransition,if_pos hf,complete_protect_same_stay]
  change transition M (rewindFrame M base offset extent c pos (span M pos)).state _ = _ at ht
  apply complete_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · have hs : pos (innerTape M i hi) ≤ span M pos := Finset.le_sup (Finset.mem_univ _)
      simp only [rewindFrame,finalFrame,dif_pos hi,Nat.sub_eq_zero_of_le hs,Nat.add_zero]
    · simp only [rewindFrame,finalFrame,dif_neg hi]

/-- Every bank head is physically rewound to its retained parent marker.
All parent symbols and flags, root input and caller output remain exact. -/
private theorem restore_correct (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) (pos : Fin M.k → ℕ) :
    (machine M).step^[span M pos + 1] (initialFrame M base offset extent c pos) =
      finalFrame M base offset extent c ∧
    (∀ j, (finalFrame M base offset extent c).head (workTape M j) = offset j) := by
  constructor
  · change (machine M).step^[span M pos + 1] (rewindFrame M base offset extent c pos 0) = _
    rw [Function.iterate_succ_apply',rewind_run M base offset extent c unique pos _ le_rfl,
      rewind_end M base offset extent c unique pos]
  · exact final_heads M base offset extent c

private theorem restoration_workspace_bound (M : MultitapeTM) (extent : Fin M.k → ℕ) :
    span M (fun j => extent j + 1) + 1 ≤ span M extent + 2 := by
  have h : span M (fun j => extent j + 1) ≤ span M extent + 1 := by
    apply Finset.sup_le
    intro j _
    have hj : extent j ≤ span M extent := Finset.le_sup (Finset.mem_univ j)
    omega
  omega

end IntMul.TrackedParentRestore


open IntMul IntMul.TrackedParentRestore

theorem solution (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) (pos : Fin M.k → ℕ) :
    (machine M).step^[span M pos + 1] (initialFrame M base offset extent c pos) =
      finalFrame M base offset extent c ∧
    (∀ j, (finalFrame M base offset extent c).head (workTape M j) = offset j) :=
  IntMul.TrackedParentRestore.restore_correct M base offset extent c unique pos

#print axioms solution
