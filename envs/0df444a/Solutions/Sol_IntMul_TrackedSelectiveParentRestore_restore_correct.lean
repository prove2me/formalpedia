-- Prove2me | solution 1 for IntMul.TrackedSelectiveParentRestore.restore_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T03:20:36.910912+00:00
-- url     : https://prove2.me/submissions/d1adbb40-a2be-4f50-ad1a-b8e9260fd5d4

import Definitions.Def_IntMul_TrackedSelectiveParentRestore
import Mathlib.Tactic


namespace IntMul.TrackedSelectiveParentRestore

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankCleanup (span)

private theorem selective_restore_internal_intmultrackedselectiveparentrestoreframes_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (workTape M j).val := by simp [workTape]

private theorem selective_restore_internal_intmultrackedselectiveparentrestoreframes_inner_work (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (workTape M j).val) : innerTape M (workTape M j) h=j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem selective_restore_internal_frame_cells (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) (p : ℕ) :
    (rewindFrame M active base offset extent c pos r).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [rewindFrame,TrackedBankedSimulation.embed,dif_pos (selective_restore_internal_intmultrackedselectiveparentrestoreframes_work_ge M j),selective_restore_internal_intmultrackedselectiveparentrestoreframes_inner_work,parentBase]
  simp only [if_neg (by omega : ¬offset j+p < offset j),Nat.add_sub_cancel_left]

private theorem selective_restore_internal_frame_heads (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M active base offset extent c pos r).head (workTape M j)=
      offset j+(if active j=true then pos j-r else pos j) := by
  simp [rewindFrame,selective_restore_internal_intmultrackedselectiveparentrestoreframes_work_ge,selective_restore_internal_intmultrackedselectiveparentrestoreframes_inner_work]

private theorem selective_restore_internal_frame_scan (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M active base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M active base offset extent c pos r).head (workTape M j))=
      some (c.cells j (if active j=true then pos j-r else pos j),
        decide ((if active j=true then pos j-r else pos j) ≤ extent j)) := by
  rw [selective_restore_internal_frame_heads,selective_restore_internal_frame_cells]

private theorem selective_restore_internal_frame_marker_iff (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) (hj : active j=true) :
    (rewindFrame M active base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M active base offset extent c pos r).head (workTape M j))=
      some (M.startSym,true) ↔ pos j ≤ r := by
  rw [selective_restore_internal_frame_scan]
  simp only [if_pos hj]
  constructor
  · intro h
    have hp := (unique j (pos j-r)).mp (congrArg Prod.fst (Option.some.inj h))
    omega
  · intro h
    simp only [Nat.sub_eq_zero_of_le h,(unique j 0).mpr rfl,
      show (0:ℕ) ≤ extent j by omega,decide_true]

private theorem selective_restore_internal_frame_not_global (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M active base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M active base offset extent c pos r).head (workTape M j))≠none := by
  rw [selective_restore_internal_frame_scan]
  simp

private theorem selective_restore_internal_selected_le_span (M : MultitapeTM) (active : Fin M.k → Bool)
    (pos : Fin M.k → ℕ) (j : Fin M.k) (hj : active j=true) :
    pos j ≤ selectedSpan M active pos := by
  have h := Finset.le_sup (s:=Finset.univ)
    (f:=fun j => if active j=true then pos j else 0) (Finset.mem_univ j)
  simpa only [selectedSpan,span,if_pos hj] using h

private theorem selective_restore_internal_all_markers_iff (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) (r : ℕ) :
    (∀ j, active j=true →
      (rewindFrame M active base offset extent c pos r).cells (workTape M j)
        ((rewindFrame M active base offset extent c pos r).head (workTape M j))=
        some (M.startSym,true)) ↔ selectedSpan M active pos ≤ r := by
  constructor
  · intro h
    unfold selectedSpan span
    apply Finset.sup_le
    intro j _
    by_cases hj : active j=true
    · rw [if_pos hj]
      exact (selective_restore_internal_frame_marker_iff M active base offset extent c unique pos r j hj).mp (h j hj)
    · simp [hj]
  · intro hr j hj
    apply (selective_restore_internal_frame_marker_iff M active base offset extent c unique pos r j hj).mpr
    exact (selective_restore_internal_selected_le_span M active pos j hj).trans hr

private theorem selective_restore_internal_final_heads (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) :
    ∀ j, (finalFrame M active base offset extent c pos).head (workTape M j)=
      offset j+(if active j=true then 0 else pos j) := by
  intro j
  simp [finalFrame,selective_restore_internal_intmultrackedselectiveparentrestoreframes_work_ge,selective_restore_internal_intmultrackedselectiveparentrestoreframes_inner_work]

end IntMul.TrackedSelectiveParentRestore



namespace IntMul.TrackedSelectiveParentRestore

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankCleanup (span)

private theorem selective_restore_internal_intmultrackedselectiveparentrestore_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem selective_restore_internal_intmultrackedselectiveparentrestore_work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem selective_restore_internal_intmultrackedselectiveparentrestore_protect_same_stay (M : MultitapeTM) (a : TrackedBankedSimulation.Sym M) :
    TrackedBankCleanup.protect M a a .stay=(a,.stay) := by cases a <;> rfl

private theorem selective_restore_internal_rewind_step (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) (r : ℕ) (hr : r < selectedSpan M active pos) :
    (machine M active).step (rewindFrame M active base offset extent c pos r)=
      rewindFrame M active base offset extent c pos (r+1) := by
  classical
  let a := fun i => (rewindFrame M active base offset extent c pos r).cells i
    ((rewindFrame M active base offset extent c pos r).head i)
  have hn : ¬∀ j, active j=true → a (workTape M j)=some (M.startSym,true) := by
    intro h
    have hh := (selective_restore_internal_all_markers_iff M active base offset extent c unique pos r).mp h
    omega
  have ht : transition M active .rewind a=
      (.rewind,fun i => (a i,if h : 2 ≤ i.val then
        if active (innerTape M i h)=true ∧ a i≠some (M.startSym,true) then .left else .stay
        else .stay)) := by
    dsimp only [transition,rawTransition]
    rw [if_neg hn]
    apply Prod.ext
    · rfl
    · funext i
      change TrackedBankCleanup.protect M (a i) (a i) _=(a i,_)
      by_cases hi : 2 ≤ i.val
      · have ha : a i≠none := by
          have h := selective_restore_internal_frame_not_global M active base offset extent c pos r (innerTape M i hi)
          rw [selective_restore_internal_intmultrackedselectiveparentrestore_work_inner M i hi] at h
          exact h
        cases hs : a i with
        | none => exact False.elim (ha hs)
        | some s => simp only [hs,TrackedBankCleanup.protect]
      · simp only [dif_neg hi]
        exact selective_restore_internal_intmultrackedselectiveparentrestore_protect_same_stay M (a i)
  dsimp only [a] at ht
  change transition M active (rewindFrame M active base offset extent c pos r).state _=_ at ht
  apply selective_restore_internal_intmultrackedselectiveparentrestore_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [dif_pos hi]
      by_cases hj : active (innerTape M i hi)=true
      · have hm : a i=some (M.startSym,true) ↔ pos (innerTape M i hi) ≤ r := by
          have h := selective_restore_internal_frame_marker_iff M active base offset extent c unique pos r (innerTape M i hi) hj
          rw [selective_restore_internal_intmultrackedselectiveparentrestore_work_inner M i hi] at h
          exact h
        by_cases hd : r < pos (innerTape M i hi)
        · rw [if_pos ⟨hj,by intro h; have hp := hm.mp h; omega⟩]
          simp only [rewindFrame,dif_pos hi,if_pos hj]
          omega
        · rw [if_neg (by intro h; apply h.2; exact hm.mpr (by omega))]
          simp only [rewindFrame,dif_pos hi,if_pos hj,
            Nat.sub_eq_zero_of_le (by omega : pos (innerTape M i hi) ≤ r),
            Nat.sub_eq_zero_of_le (by omega : pos (innerTape M i hi) ≤ r+1)]
      · rw [if_neg (by intro h; exact hj h.1)]
        simp only [rewindFrame,dif_pos hi,if_neg hj]
    · simp only [dif_neg hi,rewindFrame]

private theorem selective_restore_internal_rewind_run (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) (r : ℕ) (hr : r ≤ selectedSpan M active pos) :
    (machine M active).step^[r] (rewindFrame M active base offset extent c pos 0)=
      rewindFrame M active base offset extent c pos r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),
      selective_restore_internal_rewind_step M active base offset extent c unique pos r (by omega)]

private theorem selective_restore_internal_rewind_end (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) :
    (machine M active).step
      (rewindFrame M active base offset extent c pos (selectedSpan M active pos))=
      finalFrame M active base offset extent c pos := by
  have hf := (selective_restore_internal_all_markers_iff M active base offset extent c unique pos
    (selectedSpan M active pos)).mpr le_rfl
  have ht : transition M active .rewind
      (fun i => (rewindFrame M active base offset extent c pos (selectedSpan M active pos)).cells i
        ((rewindFrame M active base offset extent c pos (selectedSpan M active pos)).head i))=
      (.halt,fun i =>
        ((rewindFrame M active base offset extent c pos (selectedSpan M active pos)).cells i
          ((rewindFrame M active base offset extent c pos (selectedSpan M active pos)).head i),.stay)) := by
    simp only [transition,rawTransition,if_pos hf,selective_restore_internal_intmultrackedselectiveparentrestore_protect_same_stay]
  change transition M active
    (rewindFrame M active base offset extent c pos (selectedSpan M active pos)).state _=_ at ht
  apply selective_restore_internal_intmultrackedselectiveparentrestore_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [rewindFrame,finalFrame,dif_pos hi]
      by_cases hj : active (innerTape M i hi)=true
      · have hs := selective_restore_internal_selected_le_span M active pos (innerTape M i hi) hj
        simp only [if_pos hj,Nat.sub_eq_zero_of_le hs,Nat.add_zero]
      · simp only [if_neg hj]
    · simp only [rewindFrame,finalFrame,dif_neg hi]

/-- Exact whole-configuration selective restoration. The clock ignores
unselected distances, every cell is retained and unselected heads stay exact. -/
private theorem restore_correct (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) :
    (machine M active).step^[selectedSpan M active pos+1]
      (initialFrame M active base offset extent c pos)=finalFrame M active base offset extent c pos ∧
    (finalFrame M active base offset extent c pos).cells=
      (initialFrame M active base offset extent c pos).cells ∧
    (∀ j, (finalFrame M active base offset extent c pos).head (workTape M j)=
      offset j+(if active j=true then 0 else pos j)) ∧
    (∀ j, active j=false →
      (finalFrame M active base offset extent c pos).head (workTape M j)=
        (initialFrame M active base offset extent c pos).head (workTape M j)) ∧
    (∀ i, i.val < 2 → (finalFrame M active base offset extent c pos).head i=
      (initialFrame M active base offset extent c pos).head i) := by
  refine ⟨?_,rfl,selective_restore_internal_final_heads M active base offset extent c pos,?_,?_⟩
  · change (machine M active).step^[selectedSpan M active pos+1]
      (rewindFrame M active base offset extent c pos 0)=_
    rw [Function.iterate_succ_apply',selective_restore_internal_rewind_run M active base offset extent c unique pos _ le_rfl,
      selective_restore_internal_rewind_end M active base offset extent c unique pos]
  · intro j hj
    rw [selective_restore_internal_final_heads,initialFrame,selective_restore_internal_frame_heads]
    simp [hj]
  · intro i hi
    simp only [finalFrame,initialFrame,rewindFrame,dif_neg (by omega : ¬2 ≤ i.val)]

end IntMul.TrackedSelectiveParentRestore


open IntMul IntMul.TrackedSelectiveParentRestore IntMul.BankedSimulation

theorem solution (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) :
    (machine M active).step^[selectedSpan M active pos+1]
      (initialFrame M active base offset extent c pos)=finalFrame M active base offset extent c pos ∧
    (finalFrame M active base offset extent c pos).cells=
      (initialFrame M active base offset extent c pos).cells ∧
    (∀ j, (finalFrame M active base offset extent c pos).head (workTape M j)=
      offset j+(if active j=true then 0 else pos j)) ∧
    (∀ j, active j=false →
      (finalFrame M active base offset extent c pos).head (workTape M j)=
        (initialFrame M active base offset extent c pos).head (workTape M j)) ∧
    (∀ i, i.val < 2 → (finalFrame M active base offset extent c pos).head i=
      (initialFrame M active base offset extent c pos).head i) :=
  IntMul.TrackedSelectiveParentRestore.restore_correct M active base offset extent c unique pos

#print axioms solution
