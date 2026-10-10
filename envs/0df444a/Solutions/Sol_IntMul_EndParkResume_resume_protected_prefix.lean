-- Prove2me | solution 1 for IntMul.EndParkResume.resume_protected_prefix
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T07:32:50.136505+00:00
-- url     : https://prove2.me/submissions/c5c1db5d-bc8b-4195-a279-5c692a6b7746

import Definitions.Def_IntMul_EndParkResume
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic


namespace IntMul.TrackedSelectiveParentRestore

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankCleanup (span)

private theorem owned_intmultrackedselectiveparentrestoreframes_work_ge (M : MultitapeTM) (j : Fin M.k) :
    2 ≤ (workTape M j).val := by simp [workTape]

private theorem owned_intmultrackedselectiveparentrestoreframes_inner_work (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (workTape M j).val) : innerTape M (workTape M j) h=j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem frame_cells (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) (p : ℕ) :
    (rewindFrame M active base offset extent c pos r).cells (workTape M j) (offset j+p)=
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [rewindFrame,TrackedBankedSimulation.embed,dif_pos (owned_intmultrackedselectiveparentrestoreframes_work_ge M j),owned_intmultrackedselectiveparentrestoreframes_inner_work,parentBase]
  simp only [if_neg (by omega : ¬offset j+p < offset j),Nat.add_sub_cancel_left]

private theorem frame_heads (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M active base offset extent c pos r).head (workTape M j)=
      offset j+(if active j=true then pos j-r else pos j) := by
  simp [rewindFrame,owned_intmultrackedselectiveparentrestoreframes_work_ge,owned_intmultrackedselectiveparentrestoreframes_inner_work]

private theorem frame_scan (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M active base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M active base offset extent c pos r).head (workTape M j))=
      some (c.cells j (if active j=true then pos j-r else pos j),
        decide ((if active j=true then pos j-r else pos j) ≤ extent j)) := by
  rw [frame_heads,frame_cells]

private theorem frame_marker_iff (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) (hj : active j=true) :
    (rewindFrame M active base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M active base offset extent c pos r).head (workTape M j))=
      some (M.startSym,true) ↔ pos j ≤ r := by
  rw [frame_scan]
  simp only [if_pos hj]
  constructor
  · intro h
    have hp := (unique j (pos j-r)).mp (congrArg Prod.fst (Option.some.inj h))
    omega
  · intro h
    simp only [Nat.sub_eq_zero_of_le h,(unique j 0).mpr rfl,
      show (0:ℕ) ≤ extent j by omega,decide_true]

private theorem frame_not_global (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (rewindFrame M active base offset extent c pos r).cells (workTape M j)
      ((rewindFrame M active base offset extent c pos r).head (workTape M j))≠none := by
  rw [frame_scan]
  simp

private theorem selected_le_span (M : MultitapeTM) (active : Fin M.k → Bool)
    (pos : Fin M.k → ℕ) (j : Fin M.k) (hj : active j=true) :
    pos j ≤ selectedSpan M active pos := by
  have h := Finset.le_sup (s:=Finset.univ)
    (f:=fun j => if active j=true then pos j else 0) (Finset.mem_univ j)
  simpa only [selectedSpan,span,if_pos hj] using h

private theorem all_markers_iff (M : MultitapeTM) (active : Fin M.k → Bool)
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
      exact (frame_marker_iff M active base offset extent c unique pos r j hj).mp (h j hj)
    · simp [hj]
  · intro hr j hj
    apply (frame_marker_iff M active base offset extent c unique pos r j hj).mpr
    exact (selected_le_span M active pos j hj).trans hr

private theorem final_heads (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) :
    ∀ j, (finalFrame M active base offset extent c pos).head (workTape M j)=
      offset j+(if active j=true then 0 else pos j) := by
  intro j
  simp [finalFrame,owned_intmultrackedselectiveparentrestoreframes_work_ge,owned_intmultrackedselectiveparentrestoreframes_inner_work]

end IntMul.TrackedSelectiveParentRestore



namespace IntMul.TrackedSelectiveParentRestore

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankCleanup (span)

private theorem owned_intmultrackedselectiveparentrestore_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem owned_intmultrackedselectiveparentrestore_work_inner (M : MultitapeTM) (i : Fin (M.k+2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h)=i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem owned_intmultrackedselectiveparentrestore_protect_same_stay (M : MultitapeTM) (a : TrackedBankedSimulation.Sym M) :
    TrackedBankCleanup.protect M a a .stay=(a,.stay) := by cases a <;> rfl

private theorem rewind_step (M : MultitapeTM) (active : Fin M.k → Bool)
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
    have hh := (all_markers_iff M active base offset extent c unique pos r).mp h
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
          have h := frame_not_global M active base offset extent c pos r (innerTape M i hi)
          rw [owned_intmultrackedselectiveparentrestore_work_inner M i hi] at h
          exact h
        cases hs : a i with
        | none => exact False.elim (ha hs)
        | some s => simp only [hs,TrackedBankCleanup.protect]
      · simp only [dif_neg hi]
        exact owned_intmultrackedselectiveparentrestore_protect_same_stay M (a i)
  dsimp only [a] at ht
  change transition M active (rewindFrame M active base offset extent c pos r).state _=_ at ht
  apply owned_intmultrackedselectiveparentrestore_cfg_ext
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
          have h := frame_marker_iff M active base offset extent c unique pos r (innerTape M i hi) hj
          rw [owned_intmultrackedselectiveparentrestore_work_inner M i hi] at h
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

private theorem rewind_run (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) (r : ℕ) (hr : r ≤ selectedSpan M active pos) :
    (machine M active).step^[r] (rewindFrame M active base offset extent c pos 0)=
      rewindFrame M active base offset extent c pos r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),
      rewind_step M active base offset extent c unique pos r (by omega)]

private theorem rewind_end (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) :
    (machine M active).step
      (rewindFrame M active base offset extent c pos (selectedSpan M active pos))=
      finalFrame M active base offset extent c pos := by
  have hf := (all_markers_iff M active base offset extent c unique pos
    (selectedSpan M active pos)).mpr le_rfl
  have ht : transition M active .rewind
      (fun i => (rewindFrame M active base offset extent c pos (selectedSpan M active pos)).cells i
        ((rewindFrame M active base offset extent c pos (selectedSpan M active pos)).head i))=
      (.halt,fun i =>
        ((rewindFrame M active base offset extent c pos (selectedSpan M active pos)).cells i
          ((rewindFrame M active base offset extent c pos (selectedSpan M active pos)).head i),.stay)) := by
    simp only [transition,rawTransition,if_pos hf,owned_intmultrackedselectiveparentrestore_protect_same_stay]
  change transition M active
    (rewindFrame M active base offset extent c pos (selectedSpan M active pos)).state _=_ at ht
  apply owned_intmultrackedselectiveparentrestore_cfg_ext
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
      · have hs := selected_le_span M active pos (innerTape M i hi) hj
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
  refine ⟨?_,rfl,final_heads M active base offset extent c pos,?_,?_⟩
  · change (machine M active).step^[selectedSpan M active pos+1]
      (rewindFrame M active base offset extent c pos 0)=_
    rw [Function.iterate_succ_apply',rewind_run M active base offset extent c unique pos _ le_rfl,
      rewind_end M active base offset extent c unique pos]
  · intro j hj
    rw [final_heads,initialFrame,frame_heads]
    simp [hj]
  · intro i hi
    simp only [finalFrame,initialFrame,rewindFrame,dif_neg (by omega : ¬2 ≤ i.val)]

end IntMul.TrackedSelectiveParentRestore



namespace IntMul.TrackedSelectiveParentRestore

private theorem owned_intmultrackedselectiveparentrestorewindow_halted_step_window (N : MultitapeTM) (d : N.Cfg) (halt : d.state=N.qHalt) :
    N.step d=d := by
  have ext : ∀ (a b : N.Cfg), a.state=b.state → a.cells=b.cells → a.head=b.head → a=b := by
    intro a b hs hc hh
    cases a; cases b; cases hs; cases hc; cases hh; rfl
  apply ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

private theorem owned_intmultrackedselectiveparentrestorewindow_halted_iterate_window (N : MultitapeTM) (d : N.Cfg)
    (halt : d.state=N.qHalt) (t : ℕ) : N.step^[t] d=d := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,owned_intmultrackedselectiveparentrestorewindow_halted_step_window N d halt]

/-- Selective parent restoration protects every bank boundary, retains every
cell and fixes both caller heads at all intermediate and halted times. -/
private theorem restore_trajectory (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (pos : Fin M.k → ℕ) (t : ℕ) :
    ((machine M active).step^[t] (initialFrame M active base offset extent c pos)).cells=
      (initialFrame M active base offset extent c pos).cells ∧
      (∀ j, offset j ≤ ((machine M active).step^[t]
        (initialFrame M active base offset extent c pos)).head (BankedSimulation.workTape M j)) ∧
      (∀ i, i.val < 2 → ((machine M active).step^[t]
        (initialFrame M active base offset extent c pos)).head i=base.head i) := by
  let S := selectedSpan M active pos
  by_cases rewinding : t ≤ S
  · have hrun : (machine M active).step^[t] (initialFrame M active base offset extent c pos)=
        rewindFrame M active base offset extent c pos t :=
      rewind_run M active base offset extent c unique pos t rewinding
    rw [hrun]
    refine ⟨rfl,?_,?_⟩
    · intro j
      rw [frame_heads]
      omega
    · intro i hi
      simp only [rewindFrame,dif_neg (by omega : ¬2 ≤ i.val)]
  · rw [show t=(t-(S+1))+(S+1) by omega,Function.iterate_add_apply,
      (restore_correct M active base offset extent c unique pos).1,
      owned_intmultrackedselectiveparentrestorewindow_halted_iterate_window (machine M active) (finalFrame M active base offset extent c pos) rfl]
    refine ⟨rfl,?_,?_⟩
    · intro j
      rw [final_heads]
      omega
    · intro i hi
      simp only [finalFrame,dif_neg (by omega : ¬2 ≤ i.val)]

end IntMul.TrackedSelectiveParentRestore



namespace IntMul.TrackedParentOutputBridge

open IntMul.TrackedBankedSimulation (Sym)

private theorem owned_intmultrackedparentoutputbridgetape_symbols_distinct (M : MultitapeTM) :
    M.blank≠M.startSym ∧ M.zero≠M.startSym ∧ M.one≠M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true] at hd
  tauto

private theorem bit_word_letter (M : MultitapeTM) (w : List Bool) (j : ℕ) (hj : j< w.length) :
    (w.map M.bitSym).getD j M.blank=M.zero ∨ (w.map M.bitSym).getD j M.blank=M.one := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map]
  cases w[j] <;> simp [MultitapeTM.bitSym]

private theorem bit_word_not_start (M : MultitapeTM) (w : List Bool) (j : ℕ) :
    (w.map M.bitSym).getD j M.blank≠M.startSym := by
  by_cases hj : j< w.length
  · rcases bit_word_letter M w j hj with h | h
    · rw [h]; exact (owned_intmultrackedparentoutputbridgetape_symbols_distinct M).2.1
    · rw [h]; exact (owned_intmultrackedparentoutputbridgetape_symbols_distinct M).2.2
  · rw [List.getD_eq_default _ _ (by simp only [List.length_map]; omega)]
    exact (owned_intmultrackedparentoutputbridgetape_symbols_distinct M).1

private theorem bit_tape_marker (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    M.tapeOf (w.map M.bitSym) p=M.startSym ↔ p=0 := by
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
    change (w.map M.bitSym).getD p M.blank=M.startSym ↔ p+1=0
    constructor
    · intro h; exact False.elim (bit_word_not_start M w p h)
    · intro h; omega

private theorem buffer_marker (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) (p : ℕ) :
    TrackedOutputReturn.bufferTape M base sigma w (sigma+p)=some (M.startSym,true) ↔ p=0 := by
  cases p with
  | zero => simp [TrackedOutputReturn.bufferTape]
  | succ p =>
    simp only [TrackedOutputReturn.bufferTape,if_neg (by omega : ¬sigma+(p+1)< sigma),
      if_neg (by omega : sigma+(p+1)≠sigma),show sigma+(p+1)-sigma-1=p by omega]
    constructor
    · intro h
      have h := congrArg Prod.fst (Option.some.inj h)
      exact False.elim (bit_word_not_start M w p h)
    · intro h; omega

private theorem buffer_payload (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) (p : ℕ) :
    TrackedOutputReturn.bufferTape M base sigma w (sigma+p+1)=
      some ((w.map M.bitSym).getD p M.blank,decide (p< w.length)) := by
  simp only [TrackedOutputReturn.bufferTape,if_neg (by omega : ¬sigma+p+1< sigma),
    if_neg (by omega : sigma+p+1≠sigma),show sigma+p+1-sigma-1=p by omega]

private theorem old_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (p : ℕ) :
    oldTape M base offset extent cells (offset+p)=some (cells p,decide (p≤ extent)) := by
  simp only [oldTape,if_neg (by omega : ¬offset+p< offset),show offset+p-offset=p by omega]

private theorem copy_write (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (j : ℕ) :
    Function.update (copiedTape M base offset extent cells w j) (offset+j+1)
      (some ((w.map M.bitSym).getD j M.blank,true)) = copiedTape M base offset extent cells w (j+1) := by
  funext p
  by_cases he : p=offset+j+1
  · subst p
    simp [copiedTape,show ¬offset+j+1< offset by omega,show offset+j+1≠offset by omega,
      show offset+j+1-offset-1=j by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p< offset
    · simp [copiedTape,hp]
    · by_cases hm : p=offset
      · simp [copiedTape,hm]
      · by_cases hj : p< offset+j+1
        · simp [copiedTape,hp,hm,hj,show p< offset+(j+1)+1 by omega]
        · simp [copiedTape,hp,hm,hj,show ¬p< offset+(j+1)+1 by omega]

private theorem copied_zero (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (marker : cells 0=M.startSym) (w : List Bool) :
    copiedTape M base offset extent cells w 0 = oldTape M base offset extent cells := by
  funext p
  by_cases hp : p< offset
  · simp [copiedTape,oldTape,hp]
  · by_cases hm : p=offset
    · subst p
      simp [copiedTape,oldTape,marker]
    · simp only [copiedTape,if_neg hp,if_neg hm,if_neg (by omega : ¬p< offset+0+1)]

private theorem copied_complete (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) :
    copiedTape M base offset extent cells w w.length=clearedTape M base offset extent cells w 0 := by
  funext p
  simp only [copiedTape,clearedTape,Nat.add_zero]
  split_ifs <;> rfl

private theorem tail_read (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (d : ℕ) :
    clearedTape M base offset extent cells w d (offset+w.length+d+1)=
      some (cells (w.length+d+1),decide (w.length+d+1≤ extent)) := by
  simp only [clearedTape,if_neg (by omega : ¬offset+w.length+d+1< offset),
    if_neg (by omega : offset+w.length+d+1≠offset),
    if_neg (by omega : ¬offset+w.length+d+1< offset+w.length+1),
    if_neg (by omega : ¬offset+w.length+d+1< offset+w.length+d+1),oldTape,
    show offset+w.length+d+1-offset=w.length+d+1 by omega]

private theorem tail_erase (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (d : ℕ) :
    Function.update (clearedTape M base offset extent cells w d) (offset+w.length+d+1)
      (some (M.blank,false)) = clearedTape M base offset extent cells w (d+1) := by
  funext p
  by_cases he : p=offset+w.length+d+1
  · subst p
    simp [clearedTape,show ¬offset+w.length+d+1< offset by omega,
      show offset+w.length+d+1≠offset by omega,show ¬offset+w.length+d+1< offset+w.length+1 by omega]
  · rw [Function.update_of_ne he]
    by_cases hp : p< offset
    · simp [clearedTape,hp]
    · by_cases hm : p=offset
      · simp [clearedTape,hm]
      · by_cases hw : p< offset+w.length+1
        · simp [clearedTape,hp,hm,hw]
        · by_cases hd : p< offset+w.length+d+1
          · simp [clearedTape,hp,hm,hw,hd,show p< offset+w.length+(d+1)+1 by omega]
          · simp [clearedTape,hp,hm,hw,hd,show ¬p< offset+w.length+(d+1)+1 by omega]

private theorem marked_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) (w : List Bool) (p : ℕ) :
    TrackedBankPreparation.bankTape M base offset (w.map M.bitSym) (offset+p+1)=
      some ((w.map M.bitSym).getD p M.blank,decide (p< w.length)) := by
  simp only [TrackedBankPreparation.bankTape,if_neg (by omega : ¬offset+p+1< offset),
    show offset+p+1-offset=p+1 by omega,MultitapeTM.tapeOf,List.length_map,
    show p+1≤ w.length ↔ p< w.length by omega]

private theorem cleared_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (d p : ℕ) :
    clearedTape M base offset extent cells w d (offset+p+1)=
      if p< w.length then some ((w.map M.bitSym).getD p M.blank,true)
      else if p< w.length+d then some (M.blank,false)
      else some (cells (p+1),decide (p+1≤ extent)) := by
  simp only [clearedTape,if_neg (by omega : ¬offset+p+1< offset),
    if_neg (by omega : offset+p+1≠offset),show offset+p+1-offset-1=p by omega,
    show offset+p+1< offset+w.length+1 ↔ p< w.length by omega,
    show offset+p+1< offset+w.length+d+1 ↔ p< w.length+d by omega,oldTape,
    show offset+p+1-offset=p+1 by omega,Nat.add_sub_cancel]

private theorem cleared_complete (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (tail : ∀ p, extent< p → cells p=M.blank) (w : List Bool) :
    clearedTape M base offset extent cells w (max w.length extent-w.length)=
      TrackedBankPreparation.bankTape M base offset (w.map M.bitSym) := by
  funext p
  by_cases hp : p< offset
  · simp [clearedTape,TrackedBankPreparation.bankTape,hp]
  · by_cases hm : p=offset
    · subst p
      simp [clearedTape,TrackedBankPreparation.bankTape,MultitapeTM.tapeOf]
    · have he : p=offset+(p-offset-1)+1 := by omega
      rw [he,cleared_payload,marked_payload]
      by_cases hw : p-offset-1< w.length
      · simp only [hw,if_true,decide_true]
      · rw [if_neg hw,List.getD_eq_default _ _ (by simp only [List.length_map]; omega)]
        by_cases hd : p-offset-1< w.length+(max w.length extent-w.length)
        · simp only [if_pos hd,hw,decide_false]
        · rw [if_neg hd,tail _ (by omega)]
          have hf : ¬p-offset-1+1≤ extent := by omega
          simp only [hw,hf,decide_false]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

open IntMul.TrackedBankedSimulation (Sym)

private theorem buffer_ne_target (M : MultitapeTM) : bufferTape M ≠ targetTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [bufferTape,targetTape,BankedSimulation.workTape,MultitapeTM.outTape] at h
  omega

private theorem work_ne_buffer (M : MultitapeTM) (j : Fin M.k) :
    BankedSimulation.workTape M j ≠ bufferTape M := by
  intro h
  have h := congrArg Fin.val h
  simp only [bufferTape,BankedSimulation.workTape] at h
  omega

private theorem initial_buffer (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    initialCells M base sigma offset extent c w (bufferTape M) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w := by
  funext p
  simp [initialCells,TrackedBankedSimulation.embed,parentBase,bufferTape]

private theorem initial_work (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : Fin M.k) (p : ℕ) :
    initialCells M base sigma offset extent c w (BankedSimulation.workTape M j) (offset j + p) =
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [initialCells,TrackedBankedSimulation.embed,BankedSimulation.workTape]
  rw [dif_pos (by omega)]
  have hi : BankedSimulation.innerTape M ⟨j.val+2,by omega⟩ (by change 2 ≤ j.val+2; omega) = j := by
    apply Fin.ext
    simp [BankedSimulation.innerTape]
  simp only [hi,if_neg (by omega : ¬offset j+p < offset j),show offset j+p-offset j=p by omega]
private theorem initial_target (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    initialCells M base sigma offset extent c w (targetTape M) =
      oldTape M (base.cells (targetTape M)) (offset M.outTape) (extent M.outTape) (c.cells M.outTape) := by
  funext p
  simp only [initialCells,TrackedBankedSimulation.embed,targetTape,BankedSimulation.workTape]
  rw [dif_pos (by omega)]
  have hi : BankedSimulation.innerTape M ⟨M.outTape.val+2,by omega⟩
      (by change 2≤ M.outTape.val+2; omega)=M.outTape := by
    apply Fin.ext
    simp [BankedSimulation.innerTape]
  simp only [hi,oldTape]
  by_cases hp : p< offset M.outTape
  · simp only [if_pos hp,parentBase]
    split_ifs with h
    · have h := congrArg Fin.val h
      simp only [bufferTape] at h
      omega
    · rfl
  · simp only [if_neg hp]

private theorem initial_target_head (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    initialHeads M base sigma offset extent c w (targetTape M)=offset M.outTape := by
  simp only [initialHeads,eq_self,if_true]

private theorem before_buffer_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c w r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c w r).head (bufferTape M)) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w (sigma+(w.length+1-r)) := by
  simp only [beforeFrame,eq_self,if_true,initial_buffer]

private theorem before_target_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) (r : ℕ) :
    (beforeFrame M base sigma offset extent c w r).cells (targetTape M)
      ((beforeFrame M base sigma offset extent c w r).head (targetTape M)) = some (M.startSym,true) := by
  simp only [beforeFrame,if_neg (buffer_ne_target M).symm,initial_target_head,initial_target]
  have h := old_payload M (base.cells (targetTape M)) (offset M.outTape) (extent M.outTape) (c.cells M.outTape) 0
  simpa only [Nat.add_zero,marker,Nat.zero_le,decide_true] using h

private theorem before_buffer_marker (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c w r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c w r).head (bufferTape M)) = some (M.startSym,true) ↔ w.length+1≤ r := by
  rw [before_buffer_scan,buffer_marker]
  omega

private theorem before_markers (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) (r : ℕ) :
    ((beforeFrame M base sigma offset extent c w r).cells (bufferTape M)
        ((beforeFrame M base sigma offset extent c w r).head (bufferTape M)) = some (M.startSym,true) ∧
      (beforeFrame M base sigma offset extent c w r).cells (targetTape M)
        ((beforeFrame M base sigma offset extent c w r).head (targetTape M)) = some (M.startSym,true)) ↔ w.length+1≤ r := by
  rw [before_buffer_marker,before_target_scan M base sigma offset extent c w marker]
  simp only [and_true]

private theorem before_buffer_not_global (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (beforeFrame M base sigma offset extent c w r).cells (bufferTape M)
      ((beforeFrame M base sigma offset extent c w r).head (bufferTape M)) ≠ none := by
  rw [before_buffer_scan]
  simp only [TrackedOutputReturn.bufferTape,if_neg (by omega : ¬sigma+(w.length+1-r)< sigma)]
  split_ifs <;> exact Option.some_ne_none _

private theorem copy_buffer_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : ℕ) :
    (copyFrame M base sigma offset extent c w j).cells (bufferTape M)
      ((copyFrame M base sigma offset extent c w j).head (bufferTape M)) =
      some ((w.map M.bitSym).getD j M.blank,decide (j< w.length)) := by
  simp only [copyFrame,if_neg (buffer_ne_target M),eq_self,if_true,initial_buffer,buffer_payload]

private theorem copy_target_not_global (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : ℕ) :
    (copyFrame M base sigma offset extent c w j).cells (targetTape M)
      ((copyFrame M base sigma offset extent c w j).head (targetTape M)) ≠ none := by
  simp only [copyFrame,eq_self,if_true,if_neg (buffer_ne_target M).symm,copiedTape,
    if_neg (by omega : ¬offset M.outTape+j+1< offset M.outTape),
    if_neg (by omega : offset M.outTape+j+1≠offset M.outTape),
    if_neg (by omega : ¬offset M.outTape+j+1< offset M.outTape+j+1)]
  simp [oldTape,show ¬offset M.outTape+j+1< offset M.outTape by omega]

private theorem clear_target_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (d : ℕ) :
    (clearFrame M base sigma offset extent c w d).cells (targetTape M)
      ((clearFrame M base sigma offset extent c w d).head (targetTape M)) =
      some (c.cells M.outTape (w.length+d+1),decide (w.length+d+1≤ extent M.outTape)) := by
  simp only [clearFrame,eq_self,if_true,if_neg (buffer_ne_target M).symm,tail_read]

private theorem rewind_target_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (rewindFrame M base sigma offset extent c w r).cells (targetTape M)
      ((rewindFrame M base sigma offset extent c w r).head (targetTape M)) =
      some (M.tapeOf (w.map M.bitSym) (max w.length (extent M.outTape)-r),
        decide (max w.length (extent M.outTape)-r≤ w.length)) := by
  simp only [rewindFrame,eq_self,if_true,if_neg (buffer_ne_target M).symm,TrackedBankPreparation.bankTape,
    if_neg (by omega : ¬offset M.outTape+(max w.length (extent M.outTape)-r)< offset M.outTape),
    show offset M.outTape+(max w.length (extent M.outTape)-r)-offset M.outTape=max w.length (extent M.outTape)-r by omega,
    List.length_map]

private theorem rewind_target_marker (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    (rewindFrame M base sigma offset extent c w r).cells (targetTape M)
      ((rewindFrame M base sigma offset extent c w r).head (targetTape M)) = some (M.startSym,true) ↔
      max w.length (extent M.outTape)≤ r := by
  rw [rewind_target_scan]
  constructor
  · intro h
    have hs := congrArg Prod.fst (Option.some.inj h)
    have hp := (bit_tape_marker M w _).mp hs
    omega
  · intro h
    rw [Nat.sub_eq_zero_of_le h]
    simp [MultitapeTM.tapeOf]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

open IntMul.TrackedBankedSimulation (Sym)

attribute [local instance] Classical.propDecidable

private theorem owned_intmultrackedparentoutputbridgetransitions_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem owned_intmultrackedparentoutputbridgetransitions_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by cases a <;> rfl

private theorem owned_intmultrackedparentoutputbridgetransitions_protect_present (M : MultitapeTM) (a : Sym M) (move : Move) (h : a ≠ none) :
    TrackedBankCleanup.protect M a a move = (a,move) := by
  cases ha : a with
  | none => exact False.elim (h ha)
  | some s => rfl

private theorem owned_intmultrackedparentoutputbridgetransitions_protect_write (M : MultitapeTM) (a : Sym M) (s : M.Sym × Bool)
    (move : Move) (h : a ≠ none) :
    TrackedBankCleanup.protect M a (some s) move = (some s,move) := by
  cases ha : a with
  | none => exact False.elim (h ha)
  | some old => rfl

private theorem before_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (done : a (bufferTape M) = some (M.startSym,true) ∧ a (targetTape M) = some (M.startSym,true)) :
    transition M .before a = (.copy,fun i => (a i,
      if i=bufferTape M ∨ i=targetTape M then .right else .stay)) := by
  classical
  simp only [transition,rawTransition,if_pos done]
  congr 1
  funext i
  split
  · exact owned_intmultrackedparentoutputbridgetransitions_protect_right M _
  · exact owned_intmultrackedparentoutputbridgetransitions_protect_stay M _

private theorem copy_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (s : M.Sym) (b : Bool) (source : a (bufferTape M) = some (s,b))
    (letter : s=M.zero ∨ s=M.one) (target : a (targetTape M) ≠ none) :
    transition M .copy a = (.copy,fun i =>
      (if i=targetTape M then some (s,true) else a i,
        if i=bufferTape M ∨ i=targetTape M then .right else .stay)) := by
  classical
  have h : TrackedBankedSimulation.decode M (a (bufferTape M))=M.zero ∨
      TrackedBankedSimulation.decode M (a (bufferTape M))=M.one := by
    simpa only [source,TrackedBankedSimulation.decode] using letter
  dsimp only [transition,rawTransition]
  rw [if_pos h]
  simp only [source,TrackedBankedSimulation.decode]
  congr 1
  funext i
  by_cases hi : i=targetTape M
  · subst i
    simp only [eq_self,if_true,true_or]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_write M _ _ _ target
  · simp only [if_neg hi]
    split
    · exact owned_intmultrackedparentoutputbridgetransitions_protect_right M _
    · exact owned_intmultrackedparentoutputbridgetransitions_protect_stay M _

private theorem copy_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (source : TrackedBankedSimulation.decode M (a (bufferTape M))=M.blank) :
    transition M .copy a = (.clearTail,fun i => (a i,.stay)) := by
  classical
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true] at hd
  have hn : ¬(TrackedBankedSimulation.decode M (a (bufferTape M))=M.zero ∨
      TrackedBankedSimulation.decode M (a (bufferTape M))=M.one) := by
    rw [source]
    tauto
  simp only [transition,rawTransition,if_neg hn,owned_intmultrackedparentoutputbridgetransitions_protect_stay]

private theorem clear_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (flag : TrackedBankCleanup.visited M (a (targetTape M))=true) :
    transition M .clearTail a = (.clearTail,fun i =>
      (if i=targetTape M then some (M.blank,false) else a i,
        if i=targetTape M then .right else .stay)) := by
  classical
  have hb : a (targetTape M) ≠ none := by
    intro h
    simp only [h,TrackedBankCleanup.visited] at flag
    cases flag
  simp only [transition,rawTransition,if_pos flag]
  congr 1
  funext i
  by_cases hi : i=targetTape M
  · subst i
    simp only [eq_self,if_true]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_write M _ _ _ hb
  · simp only [if_neg hi]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_stay M _

private theorem before_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (not_done : ¬(a (bufferTape M)=some (M.startSym,true) ∧ a (targetTape M)=some (M.startSym,true)))
    (buffer : a (bufferTape M)≠none) :
    transition M .before a=(.before,fun i => (a i,
      if i=bufferTape M ∧ a i≠some (M.startSym,true) then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg not_done]
  congr 1
  funext i
  by_cases hi : i=bufferTape M ∧ a i≠some (M.startSym,true)
  · rw [if_pos hi]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_present M _ _ (by simpa only [hi.1] using buffer)
  · rw [if_neg hi]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_stay M _

private theorem clear_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (flag : TrackedBankCleanup.visited M (a (targetTape M))=false)
    (target : a (targetTape M)≠none) :
    transition M .clearTail a=(.rewind,fun i => (a i,if i=targetTape M then .left else .stay)) := by
  classical
  have hn : ¬TrackedBankCleanup.visited M (a (targetTape M))=true := by rw [flag]; decide
  simp only [transition,rawTransition,if_neg hn]
  congr 1
  funext i
  by_cases hi : i=targetTape M
  · rw [if_pos hi]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_present M _ _ (by simpa only [hi] using target)
  · rw [if_neg hi]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_stay M _

private theorem rewind_transition (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (not_done : a (targetTape M)≠some (M.startSym,true)) (target : a (targetTape M)≠none) :
    transition M .rewind a=(.rewind,fun i => (a i,if i=targetTape M then .left else .stay)) := by
  classical
  simp only [transition,rawTransition,if_neg not_done]
  congr 1
  funext i
  by_cases hi : i=targetTape M
  · rw [if_pos hi]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_present M _ _ (by simpa only [hi] using target)
  · rw [if_neg hi]
    exact owned_intmultrackedparentoutputbridgetransitions_protect_stay M _

private theorem rewind_dispatch (M : MultitapeTM) (a : Fin (M.k+2) → Sym M)
    (done : a (targetTape M)=some (M.startSym,true)) :
    transition M .rewind a=(.halt,fun i => (a i,.stay)) := by
  simp only [transition,rawTransition,if_pos done,owned_intmultrackedparentoutputbridgetransitions_protect_stay]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

private theorem owned_intmultrackedparentoutputbridgebefore_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem before_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) (r : ℕ) (hr : r< w.length+1) :
    (machine M).step (beforeFrame M base sigma offset extent c w r) =
      beforeFrame M base sigma offset extent c w (r+1) := by
  classical
  let a := fun i => (beforeFrame M base sigma offset extent c w r).cells i
    ((beforeFrame M base sigma offset extent c w r).head i)
  have hn : ¬(a (bufferTape M)=some (M.startSym,true) ∧ a (targetTape M)=some (M.startSym,true)) := by
    intro h
    have h := (before_markers M base sigma offset extent c w marker r).mp h
    omega
  have ht := before_transition M a hn (before_buffer_not_global M base sigma offset extent c w r)
  dsimp only [a] at ht
  change transition M (beforeFrame M base sigma offset extent c w r).state _ = _ at ht
  apply owned_intmultrackedparentoutputbridgebefore_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      have hm := before_buffer_marker M base sigma offset extent c w r
      rw [if_pos ⟨rfl,by intro h; have h := hm.mp h; omega⟩]
      simp only [beforeFrame,eq_self,if_true]
      omega
    · rw [if_neg (by intro h; exact hi h.1)]
      simp only [beforeFrame,if_neg hi]

private theorem before_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) (r : ℕ) (hr : r≤ w.length+1) :
    (machine M).step^[r] (beforeFrame M base sigma offset extent c w 0) =
      beforeFrame M base sigma offset extent c w r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),before_step M base sigma offset extent c w marker r (by omega)]

private theorem before_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym) :
    (machine M).step (beforeFrame M base sigma offset extent c w (w.length+1)) =
      copyFrame M base sigma offset extent c w 0 := by
  have ht := before_dispatch M
    (fun i => (beforeFrame M base sigma offset extent c w (w.length+1)).cells i
      ((beforeFrame M base sigma offset extent c w (w.length+1)).head i))
    ((before_markers M base sigma offset extent c w marker _).mpr le_rfl)
  change transition M (beforeFrame M base sigma offset extent c w (w.length+1)).state _ = _ at ht
  apply owned_intmultrackedparentoutputbridgebefore_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    by_cases hi : i=targetTape M
    · subst i
      simp only [beforeFrame,copyFrame,eq_self,if_true,initial_target,copied_zero M _ _ _ _ marker]
    · simp only [beforeFrame,copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,true_or,if_true,beforeFrame,copyFrame,Nat.sub_self,Nat.add_zero]
    · by_cases hp : i=targetTape M
      · subst i
        simp only [eq_self,or_true,if_true,beforeFrame,copyFrame,if_neg hi,initial_target_head,Nat.add_zero]
      · simp only [if_neg (not_or.mpr ⟨hi,hp⟩),beforeFrame,copyFrame,if_neg hi,if_neg hp]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge


private theorem owned_intmultrackedparentoutputbridgecopy_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem copy_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (j : ℕ) (hj : j < w.length) :
    (machine M).step (copyFrame M base sigma offset extent c w j) =
      copyFrame M base sigma offset extent c w (j+1) := by
  classical
  let a := fun i => (copyFrame M base sigma offset extent c w j).cells i
    ((copyFrame M base sigma offset extent c w j).head i)
  have ht := copy_transition M a ((w.map M.bitSym).getD j M.blank)
    (decide (j< w.length))
    (copy_buffer_scan M base sigma offset extent c w j)
    (bit_word_letter M w j hj) (copy_target_not_global M base sigma offset extent c w j)
  dsimp only [a] at ht
  change transition M (copyFrame M base sigma offset extent c w j).state _ = _ at ht
  apply owned_intmultrackedparentoutputbridgecopy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,copyFrame]
      exact copy_write M _ (offset M.outTape) (extent M.outTape) (c.cells M.outTape) w j
    · rw [if_neg hi,Function.update_eq_self]
      simp only [copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=bufferTape M
    · subst i
      simp only [eq_self,true_or,if_true,copyFrame]
      omega
    · by_cases hp : i=targetTape M
      · subst i
        simp only [eq_self,or_true,if_true,copyFrame,if_neg hi]
        omega
      · simp only [if_neg (not_or.mpr ⟨hi,hp⟩),copyFrame,if_neg hi,if_neg hp]

private theorem copy_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (j : ℕ) (hj : j ≤ w.length) :
    (machine M).step^[j] (copyFrame M base sigma offset extent c w 0) =
      copyFrame M base sigma offset extent c w j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih (by omega),copy_step M base sigma offset extent c w j (by omega)]

private theorem copy_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (machine M).step (copyFrame M base sigma offset extent c w w.length) =
      clearFrame M base sigma offset extent c w 0 := by
  have hs : TrackedBankedSimulation.decode M
      ((copyFrame M base sigma offset extent c w w.length).cells (bufferTape M)
        ((copyFrame M base sigma offset extent c w w.length).head (bufferTape M))) = M.blank := by
    rw [copy_buffer_scan M base sigma offset extent c w]
    change (w.map M.bitSym).getD w.length M.blank=M.blank
    apply List.getD_eq_default
    simp only [List.length_map]
    exact le_rfl
  have ht := copy_dispatch M
    (fun i => (copyFrame M base sigma offset extent c w w.length).cells i
      ((copyFrame M base sigma offset extent c w w.length).head i)) hs
  change transition M (copyFrame M base sigma offset extent c w w.length).state _ = _ at ht
  apply owned_intmultrackedparentoutputbridgecopy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [copyFrame,clearFrame,copied_complete]
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [copyFrame,clearFrame,Nat.add_zero]
private theorem clear_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (d : ℕ)
    (hd : d< max w.length (extent M.outTape)-w.length) :
    (machine M).step (clearFrame M base sigma offset extent c w d) =
      clearFrame M base sigma offset extent c w (d+1) := by
  classical
  have hv : w.length+d+1≤ extent M.outTape := by omega
  have hf : TrackedBankCleanup.visited M
      ((clearFrame M base sigma offset extent c w d).cells (targetTape M)
        ((clearFrame M base sigma offset extent c w d).head (targetTape M)))=true := by
    rw [clear_target_scan]
    simp only [TrackedBankCleanup.visited,decide_eq_true hv]
  have ht := clear_transition M
    (fun i => (clearFrame M base sigma offset extent c w d).cells i
      ((clearFrame M base sigma offset extent c w d).head i)) hf
  change transition M (clearFrame M base sigma offset extent c w d).state _ = _ at ht
  apply owned_intmultrackedparentoutputbridgecopy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,clearFrame,if_neg (buffer_ne_target M).symm]
      exact tail_erase M _ (offset M.outTape) (extent M.outTape) (c.cells M.outTape) w d
    · rw [if_neg hi,Function.update_eq_self]
      simp only [clearFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,clearFrame,if_neg (buffer_ne_target M).symm]
      omega
    · simp only [if_neg hi,clearFrame,if_neg hi]

private theorem clear_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (d : ℕ)
    (hd : d≤ max w.length (extent M.outTape)-w.length) :
    (machine M).step^[d] (clearFrame M base sigma offset extent c w 0) =
      clearFrame M base sigma offset extent c w d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Function.iterate_succ_apply',ih (by omega),clear_step M base sigma offset extent c w d (by omega)]

private theorem clear_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (tail : ∀ p, extent M.outTape< p → c.cells M.outTape p=M.blank) :
    (machine M).step (clearFrame M base sigma offset extent c w (max w.length (extent M.outTape)-w.length)) =
      rewindFrame M base sigma offset extent c w 0 := by
  classical
  let D := max w.length (extent M.outTape)-w.length
  change (machine M).step (clearFrame M base sigma offset extent c w D) = _
  have hlen : w.length+D=max w.length (extent M.outTape) := by dsimp [D]; omega
  have hv : ¬w.length+D+1≤ extent M.outTape := by omega
  have hf : TrackedBankCleanup.visited M
      ((clearFrame M base sigma offset extent c w D).cells (targetTape M)
        ((clearFrame M base sigma offset extent c w D).head (targetTape M)))=false := by
    rw [clear_target_scan]
    simp only [TrackedBankCleanup.visited,decide_eq_false hv]
  have hb : (clearFrame M base sigma offset extent c w D).cells (targetTape M)
      ((clearFrame M base sigma offset extent c w D).head (targetTape M))≠none := by
    rw [clear_target_scan]
    exact Option.some_ne_none _
  have ht := clear_dispatch M
    (fun i => (clearFrame M base sigma offset extent c w D).cells i
      ((clearFrame M base sigma offset extent c w D).head i)) hf hb
  change transition M (clearFrame M base sigma offset extent c w D).state _ = _ at ht
  apply owned_intmultrackedparentoutputbridgecopy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    simp only [clearFrame,rewindFrame]
    by_cases hi : i=targetTape M
    · simp only [if_pos hi]
      exact cleared_complete M _ (offset M.outTape) (extent M.outTape) (c.cells M.outTape) tail w
    · simp only [if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,clearFrame,rewindFrame,if_neg (buffer_ne_target M).symm,Nat.sub_zero]
      omega
    · simp only [if_neg hi,clearFrame,rewindFrame,if_neg hi]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

private theorem owned_intmultrackedparentoutputbridgerewind_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem rewind_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (r : ℕ) (hr : r< max w.length (extent M.outTape)) :
    (machine M).step (rewindFrame M base sigma offset extent c w r) =
      rewindFrame M base sigma offset extent c w (r+1) := by
  classical
  let a := fun i => (rewindFrame M base sigma offset extent c w r).cells i
    ((rewindFrame M base sigma offset extent c w r).head i)
  have hn : a (targetTape M)≠some (M.startSym,true) := by
    intro h
    have h := (rewind_target_marker M base sigma offset extent c w r).mp h
    omega
  have hp : a (targetTape M)≠none := by
    dsimp only [a]
    rw [rewind_target_scan]
    exact Option.some_ne_none _
  have ht := rewind_transition M a hn hp
  dsimp only [a] at ht
  change transition M (rewindFrame M base sigma offset extent c w r).state _ = _ at ht
  apply owned_intmultrackedparentoutputbridgerewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i=targetTape M
    · subst i
      simp only [eq_self,if_true,rewindFrame,if_neg (buffer_ne_target M).symm]
      omega
    · simp only [if_neg hi,rewindFrame,if_neg hi]

private theorem rewind_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (r : ℕ) (hr : r≤ max w.length (extent M.outTape)) :
    (machine M).step^[r] (rewindFrame M base sigma offset extent c w 0) =
      rewindFrame M base sigma offset extent c w r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),rewind_step M base sigma offset extent c w r (by omega)]

private theorem rewind_end (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (machine M).step (rewindFrame M base sigma offset extent c w (max w.length (extent M.outTape))) =
      finalFrame M base sigma offset extent c w := by
  have ht := rewind_dispatch M
    (fun i => (rewindFrame M base sigma offset extent c w (max w.length (extent M.outTape))).cells i
      ((rewindFrame M base sigma offset extent c w (max w.length (extent M.outTape))).head i))
    ((rewind_target_marker M base sigma offset extent c w _).mpr le_rfl)
  change transition M (rewindFrame M base sigma offset extent c w (max w.length (extent M.outTape))).state _ = _ at ht
  apply owned_intmultrackedparentoutputbridgerewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [rewindFrame,finalFrame,Nat.sub_self,Nat.add_zero]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

private theorem run_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym)
    (tail : ∀ p, extent M.outTape< p → c.cells M.outTape p=M.blank) :
    (machine M).step^[w.length+2*max w.length (extent M.outTape)+5]
      (initialFrame M base sigma offset extent c w) = finalFrame M base sigma offset extent c w := by
  let H := max w.length (extent M.outTape)
  let D := H-w.length
  have hlen : w.length+D=H := by dsimp [D,H]; omega
  have hbefore : (machine M).step^[w.length+2] (initialFrame M base sigma offset extent c w) =
      copyFrame M base sigma offset extent c w 0 := by
    change (machine M).step^[(w.length+1)+1] (beforeFrame M base sigma offset extent c w 0) = _
    rw [Function.iterate_succ_apply',before_run M base sigma offset extent c w marker _ le_rfl,
      before_end M base sigma offset extent c w marker]
  have hcopy : (machine M).step^[w.length+1] (copyFrame M base sigma offset extent c w 0) =
      clearFrame M base sigma offset extent c w 0 := by
    rw [Function.iterate_succ_apply',copy_run M base sigma offset extent c w _ le_rfl,
      copy_end M base sigma offset extent c w]
  have hclear : (machine M).step^[D+1] (clearFrame M base sigma offset extent c w 0) =
      rewindFrame M base sigma offset extent c w 0 := by
    rw [Function.iterate_succ_apply',clear_run M base sigma offset extent c w D le_rfl,
      clear_end M base sigma offset extent c w tail]
  have hrewind : (machine M).step^[H+1] (rewindFrame M base sigma offset extent c w 0) =
      finalFrame M base sigma offset extent c w := by
    rw [Function.iterate_succ_apply',rewind_run M base sigma offset extent c w H le_rfl,
      rewind_end M base sigma offset extent c w]
  have hcopybefore : (machine M).step^[(w.length+1)+(w.length+2)] (initialFrame M base sigma offset extent c w) =
      clearFrame M base sigma offset extent c w 0 := by
    rw [Function.iterate_add_apply,hbefore,hcopy]
  have hclearcopy : (machine M).step^[(D+1)+((w.length+1)+(w.length+2))] (initialFrame M base sigma offset extent c w) =
      rewindFrame M base sigma offset extent c w 0 := by
    rw [Function.iterate_add_apply,hcopybefore,hclear]
  change (machine M).step^[w.length+2*H+5] (initialFrame M base sigma offset extent c w) = _
  rw [show w.length+2*H+5=(H+1)+((D+1)+((w.length+1)+(w.length+2))) by omega,
    Function.iterate_add_apply,hclearcopy,hrewind]

/-- Place a physical child return word into a parent output bank, erase all
remaining old visited cells, retain the parent marker and restore its head.
Every other tape and head, including the caller buffer, stays exact. -/
private theorem output_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym)
    (tail : ∀ p, extent M.outTape< p → c.cells M.outTape p=M.blank) :
    (machine M).step^[w.length+2*max w.length (extent M.outTape)+5]
      (initialFrame M base sigma offset extent c w) = finalFrame M base sigma offset extent c w ∧
    (finalFrame M base sigma offset extent c w).state = (machine M).qHalt ∧
    (finalFrame M base sigma offset extent c w).cells (targetTape M) =
      TrackedBankPreparation.bankTape M (base.cells (targetTape M)) (offset M.outTape) (w.map M.bitSym) ∧
    (∀ p, (finalFrame M base sigma offset extent c w).cells (targetTape M) (offset M.outTape+p)=
      some (M.tapeOf (w.map M.bitSym) p,decide (p≤ w.length))) ∧
    (finalFrame M base sigma offset extent c w).head (targetTape M) = offset M.outTape ∧
    (finalFrame M base sigma offset extent c w).cells (bufferTape M) =
      TrackedOutputReturn.bufferTape M (base.cells (bufferTape M)) sigma w ∧
    (finalFrame M base sigma offset extent c w).head (bufferTape M) = sigma+w.length+1 ∧
    (∀ i, i≠targetTape M → (finalFrame M base sigma offset extent c w).cells i =
      (initialFrame M base sigma offset extent c w).cells i) ∧
    (∀ i, i≠targetTape M → (finalFrame M base sigma offset extent c w).head i =
      (initialFrame M base sigma offset extent c w).head i) := by
  refine ⟨run_correct M base sigma offset extent c w marker tail,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [finalFrame,eq_self,if_true]
  · intro p
    simp only [finalFrame,eq_self,if_true,TrackedBankPreparation.bankTape,
      if_neg (by omega : ¬offset M.outTape+p< offset M.outTape),
      show offset M.outTape+p-offset M.outTape=p by omega,List.length_map]
  · simp only [finalFrame,if_neg (buffer_ne_target M).symm,eq_self,if_true]
  · simp only [finalFrame,if_neg (buffer_ne_target M),initial_buffer]
  · simp only [finalFrame,eq_self,if_true]
  · intro i hi
    simp only [finalFrame,if_neg hi,initialFrame,beforeFrame]
  · intro i hi
    simp only [finalFrame,if_neg hi,initialFrame,beforeFrame,Nat.sub_zero,Nat.add_assoc]

end IntMul.TrackedParentOutputBridge



namespace IntMul.TrackedParentOutputBridge

private def owned_intmultrackedparentoutputbridgewindow_windowSafe (M : MultitapeTM) (sigma : ℕ) (offset : Fin M.k → ℕ)
    (d : (machine M).Cfg) : Prop :=
  sigma ≤ d.head (bufferTape M) ∧ ∀ j, offset j ≤ d.head (BankedSimulation.workTape M j)

private theorem owned_intmultrackedparentoutputbridgewindow_target_index (M : MultitapeTM) (j : Fin M.k)
    (h : BankedSimulation.workTape M j=targetTape M) : j=M.outTape := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [BankedSimulation.workTape,targetTape] at hv
  omega

private theorem owned_intmultrackedparentoutputbridgewindow_initial_work_floor (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : Fin M.k) :
    offset j ≤ initialHeads M base sigma offset extent c w (BankedSimulation.workTape M j) := by
  simp only [initialHeads]
  by_cases target : BankedSimulation.workTape M j=targetTape M
  · rw [if_pos target,owned_intmultrackedparentoutputbridgewindow_target_index M j target]
  · rw [if_neg target]
    simp [TrackedBankedSimulation.embed,BankedSimulation.workTape,BankedSimulation.innerTape]

private theorem owned_intmultrackedparentoutputbridgewindow_before_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    owned_intmultrackedparentoutputbridgewindow_windowSafe M sigma offset (beforeFrame M base sigma offset extent c w r) := by
  constructor
  · simp only [beforeFrame,eq_self,if_true]
    omega
  · intro j
    simp only [beforeFrame,if_neg (work_ne_buffer M j)]
    exact owned_intmultrackedparentoutputbridgewindow_initial_work_floor M base sigma offset extent c w j

private theorem owned_intmultrackedparentoutputbridgewindow_copy_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    owned_intmultrackedparentoutputbridgewindow_windowSafe M sigma offset (copyFrame M base sigma offset extent c w r) := by
  constructor
  · simp only [copyFrame,eq_self,if_true]
    omega
  · intro j
    simp only [copyFrame,if_neg (work_ne_buffer M j)]
    by_cases target : BankedSimulation.workTape M j=targetTape M
    · rw [if_pos target,owned_intmultrackedparentoutputbridgewindow_target_index M j target]
      omega
    · rw [if_neg target]
      exact owned_intmultrackedparentoutputbridgewindow_initial_work_floor M base sigma offset extent c w j

private theorem owned_intmultrackedparentoutputbridgewindow_clear_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    owned_intmultrackedparentoutputbridgewindow_windowSafe M sigma offset (clearFrame M base sigma offset extent c w r) := by
  constructor
  · simp only [clearFrame,eq_self,if_true]
    omega
  · intro j
    simp only [clearFrame,if_neg (work_ne_buffer M j)]
    by_cases target : BankedSimulation.workTape M j=targetTape M
    · rw [if_pos target,owned_intmultrackedparentoutputbridgewindow_target_index M j target]
      omega
    · rw [if_neg target]
      exact owned_intmultrackedparentoutputbridgewindow_initial_work_floor M base sigma offset extent c w j

private theorem owned_intmultrackedparentoutputbridgewindow_rewind_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) :
    owned_intmultrackedparentoutputbridgewindow_windowSafe M sigma offset (rewindFrame M base sigma offset extent c w r) := by
  constructor
  · simp only [rewindFrame,eq_self,if_true]
    omega
  · intro j
    simp only [rewindFrame,if_neg (work_ne_buffer M j)]
    by_cases target : BankedSimulation.workTape M j=targetTape M
    · rw [if_pos target,owned_intmultrackedparentoutputbridgewindow_target_index M j target]
      omega
    · rw [if_neg target]
      exact owned_intmultrackedparentoutputbridgewindow_initial_work_floor M base sigma offset extent c w j

private theorem owned_intmultrackedparentoutputbridgewindow_final_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    owned_intmultrackedparentoutputbridgewindow_windowSafe M sigma offset (finalFrame M base sigma offset extent c w) := by
  constructor
  · simp only [finalFrame,eq_self,if_true]
    omega
  · intro j
    simp only [finalFrame,if_neg (work_ne_buffer M j)]
    by_cases target : BankedSimulation.workTape M j=targetTape M
    · rw [if_pos target,owned_intmultrackedparentoutputbridgewindow_target_index M j target]
    · rw [if_neg target]
      exact owned_intmultrackedparentoutputbridgewindow_initial_work_floor M base sigma offset extent c w j

private theorem owned_intmultrackedparentoutputbridgewindow_halted_step_window (N : MultitapeTM) (d : N.Cfg) (halt : d.state=N.qHalt) :
    N.step d=d := by
  have ext : ∀ (a b : N.Cfg), a.state=b.state → a.cells=b.cells → a.head=b.head → a=b := by
    intro a b hs hc hh
    cases a; cases b; cases hs; cases hc; cases hh; rfl
  apply ext
  · simp [MultitapeTM.step,halt,N.halt_fixed]
  · funext i
    simp only [MultitapeTM.step,halt,N.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,N.halt_fixed]

private theorem owned_intmultrackedparentoutputbridgewindow_halted_iterate_window (N : MultitapeTM) (d : N.Cfg)
    (halt : d.state=N.qHalt) (t : ℕ) : N.step^[t] d=d := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,owned_intmultrackedparentoutputbridgewindow_halted_step_window N d halt]

/-- Physical parent result placement protects its source buffer and every
parent bank at all times, including old-tail erasure and output rewind. -/
private theorem output_window_safe (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool)
    (marker : c.cells M.outTape 0=M.startSym)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∀ t, sigma ≤ ((machine M).step^[t] (initialFrame M base sigma offset extent c w)).head (bufferTape M) ∧
      ∀ j, offset j ≤ ((machine M).step^[t] (initialFrame M base sigma offset extent c w)).head
        (BankedSimulation.workTape M j) := by
  let A := w.length+1
  let L := w.length
  let H := max L (extent M.outTape)
  let D := H-L
  have hlen : L+D=H := by dsimp only [D,H]; omega
  have hbefore : (machine M).step^[A+1] (initialFrame M base sigma offset extent c w)=
      copyFrame M base sigma offset extent c w 0 := by
    change (machine M).step^[A+1] (beforeFrame M base sigma offset extent c w 0)=_
    rw [Function.iterate_succ_apply',before_run M base sigma offset extent c w marker A le_rfl,
      before_end M base sigma offset extent c w marker]
  have hcopy : (machine M).step^[A+L+2] (initialFrame M base sigma offset extent c w)=
      clearFrame M base sigma offset extent c w 0 := by
    rw [show A+L+2=(L+1)+(A+1) by omega,Function.iterate_add_apply,hbefore,
      Function.iterate_succ_apply',copy_run M base sigma offset extent c w L le_rfl,
      copy_end M base sigma offset extent c w]
  have hclear : (machine M).step^[A+H+3] (initialFrame M base sigma offset extent c w)=
      rewindFrame M base sigma offset extent c w 0 := by
    rw [show A+H+3=(D+1)+(A+L+2) by omega,Function.iterate_add_apply,hcopy,
      Function.iterate_succ_apply',clear_run M base sigma offset extent c w D le_rfl,
      clear_end M base sigma offset extent c w tail]
  have hfinal : (machine M).step^[A+2*H+4] (initialFrame M base sigma offset extent c w)=
      finalFrame M base sigma offset extent c w := by
    rw [show A+2*H+4=w.length+2*max w.length (extent M.outTape)+5 by dsimp only [A,H,L]; omega]
    exact run_correct M base sigma offset extent c w marker tail
  intro t
  change owned_intmultrackedparentoutputbridgewindow_windowSafe M sigma offset ((machine M).step^[t] (initialFrame M base sigma offset extent c w))
  by_cases before : t ≤ A
  · change owned_intmultrackedparentoutputbridgewindow_windowSafe M sigma offset ((machine M).step^[t] (beforeFrame M base sigma offset extent c w 0))
    rw [before_run M base sigma offset extent c w marker t before]
    exact owned_intmultrackedparentoutputbridgewindow_before_safe M base sigma offset extent c w t
  · by_cases copying : t ≤ A+L+1
    · rw [show t=(t-(A+1))+(A+1) by omega,Function.iterate_add_apply,hbefore,
        copy_run M base sigma offset extent c w _ (by omega)]
      exact owned_intmultrackedparentoutputbridgewindow_copy_safe M base sigma offset extent c w _
    · by_cases clearing : t ≤ A+H+2
      · rw [show t=(t-(A+L+2))+(A+L+2) by omega,Function.iterate_add_apply,hcopy,
          clear_run M base sigma offset extent c w _ (by omega)]
        exact owned_intmultrackedparentoutputbridgewindow_clear_safe M base sigma offset extent c w _
      · by_cases rewinding : t ≤ A+2*H+3
        · rw [show t=(t-(A+H+3))+(A+H+3) by omega,Function.iterate_add_apply,hclear,
            rewind_run M base sigma offset extent c w _ (by omega)]
          exact owned_intmultrackedparentoutputbridgewindow_rewind_safe M base sigma offset extent c w _
        · rw [show t=(t-(A+2*H+4))+(A+2*H+4) by omega,Function.iterate_add_apply,hfinal,
            owned_intmultrackedparentoutputbridgewindow_halted_iterate_window (machine M) (finalFrame M base sigma offset extent c w) rfl]
          exact owned_intmultrackedparentoutputbridgewindow_final_safe M base sigma offset extent c w

end IntMul.TrackedParentOutputBridge



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



namespace IntMul.EndParkResume

private theorem owned_intmulendparkresumedispatch_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem restore_dispatch (M : MultitapeTM) (n : ℕ) 
    (c : (restoreMachine M).Cfg) (halt : c.state=(restoreMachine M).qHalt) :
    (machine M n).step (liftRestore M n c)=relabel M n (.pop .popStart) (liftRestore M n c) := by
  have ht : transition M n (.restore c.state) (fun i => c.cells i (c.head i))=
      (.pop .popStart,fun i => (c.cells i (c.head i),.stay)) := by
    simp only [transition,halt,if_true]
  apply owned_intmulendparkresumedispatch_cfg_ext
  · simp only [MultitapeTM.step,liftRestore,ht,relabel]
  · simp only [MultitapeTM.step,liftRestore,ht,relabel]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,liftRestore,ht,relabel]

private theorem pop_dispatch (M : MultitapeTM) (n : ℕ) (label : Fin n)
    (c : (FiniteContinuationStack.machine M n).Cfg) (halt : c.state=.resume label) :
    (machine M n).step (liftPop M n c)=relabel M n (.output label .before) (liftPop M n c) := by
  have ht : transition M n (.pop c.state) (fun i => c.cells i (c.head i))=
      (.output label .before,fun i => (c.cells i (c.head i),.stay)) := by
    simp only [transition,halt,if_true]
  apply owned_intmulendparkresumedispatch_cfg_ext
  · simp only [MultitapeTM.step,liftPop,ht,relabel]
  · simp only [MultitapeTM.step,liftPop,ht,relabel]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,liftPop,ht,relabel]

private theorem output_dispatch (M : MultitapeTM) (n : ℕ) (label : Fin n)
    (c : (outputMachine M).Cfg) (halt : c.state=(outputMachine M).qHalt) :
    (machine M n).step (liftOutput M n label c)=relabel M n (.ready label) (liftOutput M n label c) := by
  have ht : transition M n (.output label c.state) (fun i => c.cells i (c.head i))=
      (.ready label,fun i => (c.cells i (c.head i),.stay)) := by
    simp only [transition,halt,if_true]
  apply owned_intmulendparkresumedispatch_cfg_ext
  · simp only [MultitapeTM.step,liftOutput,ht,relabel]
  · simp only [MultitapeTM.step,liftOutput,ht,relabel]
    funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,liftOutput,ht,relabel]

end IntMul.EndParkResume



namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape)
open IntMul.FiniteContinuationStack (stackTape)

private theorem result_rewind_span (M : MultitapeTM) (extent : Fin M.k → ℕ) :
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
    rw [result_rewind_span] at r
    rw [show extent M.outTape+1+1=extent M.outTape+2 by omega] at r
    rw [r.1] at h
    exact h
  have hrhalt : ((restoreMachine M).step^[extent M.outTape+2]
      (restoreStart M n base rho sigma offset extent c label w)).state=(restoreMachine M).qHalt := by
    rw [hrestore]
    rfl
  obtain ⟨s,hs,hsrun⟩ := restore_to_halt M n
    (restoreStart M n base rho sigma offset extent c label w) (extent M.outTape+2) hrhalt
  rw [hrestore] at hsrun
  have hdown : (machine M n).step^[s+1]
      (initialFrame M n base rho sigma offset extent c label w)=
      liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label) := by
    change (machine M n).step^[s+1]
      (liftRestore M n (restoreStart M n base rho sigma offset extent c label w))=_
    rw [Function.iterate_succ_apply',hsrun,restore_dispatch M n _ rfl,restore_pop_ready]
  have hpop : (machine M n).step^[n+3]
      (liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label))=
      liftOutput M n label (outputStart M n base rho sigma offset extent c label w) := by
    rw [show n+3=(n+2)+1 by omega,Function.iterate_succ_apply',pop_correct]
    change (machine M n).step (liftPop M n (popped M n base rho sigma offset extent c label w))=_
    rw [pop_dispatch M n label _ rfl,pop_output_ready]
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
  obtain ⟨u,hu,hurun⟩ := output_to_halt M n label
    (outputStart M n base rho sigma offset extent c label w)
    (w.length+2*max w.length (extent M.outTape)+5) hohalt
  rw [houtput] at hurun
  have hup : (machine M n).step^[u+1]
      (liftOutput M n label (outputStart M n base rho sigma offset extent c label w))=
      finalFrame M n base rho sigma offset extent c label w := by
    rw [Function.iterate_succ_apply',hurun,output_dispatch M n label _ rfl]
    rfl
  refine ⟨(u+1)+((n+3)+(s+1)),by omega,?_,rfl,
    final_work_heads M n base rho sigma offset extent c label w,
    final_output_cells M n base rho sigma offset extent c label w,
    (final_stack M n base rho sigma offset extent c label w).1,
    (final_stack M n base rho sigma offset extent c label w).2⟩
  rw [Function.iterate_add_apply (machine M n).step (u+1) ((n+3)+(s+1)),
    Function.iterate_add_apply (machine M n).step (n+3) (s+1),hdown,hpop,hup]

end IntMul.EndParkResume


namespace IntMul.EndParkResume


open IntMul.TrackedBankPreparation (inputWord)
open IntMul.TrackedBankCleanup (span)

private def headSafe (N : MultitapeTM) (d : N.Cfg) : Prop :=
  ∀ i, i ≠ N.inTape → 1 ≤ d.head i

private def safePrefix (N : MultitapeTM) (c : N.Cfg) (T : ℕ) : Prop :=
  ∀ s, s ≤ T → headSafe N (N.step^[s] c)

private theorem safe_concat (N : MultitapeTM) (c d : N.Cfg) (A B : ℕ)
    (run : N.step^[A] c=d) (first : safePrefix N c A) (second : safePrefix N d B) :
    safePrefix N c (B+A) := by
  intro s hs i hi
  by_cases before : s ≤ A
  · exact first s before i hi
  · rw [show s=(s-A)+A by omega,Function.iterate_add_apply,run]
    exact second (s-A) (by omega) i hi

private theorem lifted_first_exit (N S : MultitapeTM) (lift : S.Cfg → N.Cfg)
    (c : S.Cfg) (T : ℕ) (exit : (S.step^[T] c).state=S.qHalt)
    (runs : ∀ t, (∀ r, r < t → (S.step^[r] c).state≠S.qHalt) →
      N.step^[t] (lift c)=lift (S.step^[t] c))
    (safe : ∀ t, headSafe N (lift (S.step^[t] c))) :
    ∃ t, t ≤ T ∧ N.step^[t] (lift c)=lift (S.step^[T] c) ∧ safePrefix N (lift c) t := by
  obtain ⟨t,ht,he,live⟩ := EndParkResume.owned_intmulendparkresumeprograms_first_exit S
    (fun q => q=S.qHalt)
    (by intro d hd; exact EndParkResume.owned_intmulendparkresumeprograms_halted_step S d hd)
    c T exit
  refine ⟨t,ht,?_,?_⟩
  · rw [runs t live,he]
  · intro s hs
    rw [runs s (by intro r hr; exact live r (by omega))]
    exact safe s

private theorem padded_head_safe (N : MultitapeTM) (base : (FixedTapeExtension.machine N).Cfg)
    (c : N.Cfg) (t : ℕ) (oldSafe : headSafe N (N.step^[t] c))
    (extraSafe : 1 ≤ base.head (FixedTapeExtension.extraTape N)) :
    headSafe (FixedTapeExtension.machine N)
      ((FixedTapeExtension.machine N).step^[t] (FixedTapeExtension.embed N base c)) := by
  rw [(FixedTapeExtension.simulate_run N base c t).1]
  intro i hi
  simp only [FixedTapeExtension.embed]
  by_cases old : i.val < N.k
  · rw [dif_pos old]
    apply oldSafe
    intro he
    have hz : i.val=0 := congrArg Fin.val he
    exact hi (Fin.ext hz)
  · rw [dif_neg old]
    have he : i=FixedTapeExtension.extraTape N := by
      apply Fin.ext
      change i.val=N.k
      have hilim : i.val < N.k+1 := i.isLt
      omega
    rw [he]
    exact extraSafe


end IntMul.EndParkResume


namespace IntMul.EndParkResume

private theorem safe_one (N : MultitapeTM) (c d : N.Cfg) (run : N.step c=d)
    (first : headSafe N c) (last : headSafe N d) : safePrefix N c 1 := by
  intro t ht
  by_cases zero : t=0
  · subst t
    exact first
  · have one : t=1 := by omega
    rw [one,Function.iterate_one,run]
    exact last

private theorem restore_heads_safe (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0) (t : ℕ) :
    headSafe (machine M n) (liftRestore M n ((restoreMachine M).step^[t]
      (restoreStart M n base rho sigma offset extent c label w))) := by
  have oldSafe : headSafe (TrackedSelectiveParentRestore.machine M (active M))
      ((TrackedSelectiveParentRestore.machine M (active M)).step^[t]
        (TrackedSelectiveParentRestore.initialFrame M (active M)
          (restorePlainBase M n base sigma w) offset extent c (fun j => extent j+1))) := by
    intro i hi
    have nonzero : i.val≠0 := by intro hz; exact hi (Fin.ext hz)
    have h := TrackedSelectiveParentRestore.restore_trajectory M (active M)
      (restorePlainBase M n base sigma w) offset extent c unique (fun j => extent j+1) t
    by_cases work : 2 ≤ i.val
    · let j := BankedSimulation.innerTape M i work
      have he : BankedSimulation.workTape M j=i := by
        apply Fin.ext
        dsimp only [j,BankedSimulation.innerTape,BankedSimulation.workTape]
        omega
      rw [←he]
      exact le_trans (positive j) (h.2.1 j)
    · rw [h.2.2 i (by omega)]
      simp only [restorePlainBase]
      rw [if_pos (by omega : i.val=1)]
      omega
  have extraSafe : 1 ≤ (restorePadBase M n base rho label).head
      (FixedTapeExtension.extraTape (TrackedSelectiveParentRestore.machine M (active M))) := by
    change 1 ≤ (restorePadBase M n base rho label).head (FiniteContinuationStack.stackTape M)
    simp only [restorePadBase,if_true]
    omega
  exact padded_head_safe (TrackedSelectiveParentRestore.machine M (active M))
    (restorePadBase M n base rho label)
    (TrackedSelectiveParentRestore.initialFrame M (active M)
      (restorePlainBase M n base sigma w) offset extent c (fun j => extent j+1)) t oldSafe extraSafe

private theorem output_heads_safe (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) (t : ℕ) :
    headSafe (machine M n) (liftOutput M n label ((outputMachine M).step^[t]
      (outputStart M n base rho sigma offset extent c label w))) := by
  have oldSafe : headSafe (TrackedParentOutputBridge.machine M)
      ((TrackedParentOutputBridge.machine M).step^[t]
        (TrackedParentOutputBridge.initialFrame M
          (outputPlainBase M n base rho sigma offset extent c label w)
          sigma offset extent (parentAtEnds M extent c) w)) := by
    intro i hi
    have nonzero : i.val≠0 := by intro hz; exact hi (Fin.ext hz)
    have h := TrackedParentOutputBridge.output_window_safe M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w ((unique M.outTape 0).2 rfl) tail t
    by_cases work : 2 ≤ i.val
    · let j := BankedSimulation.innerTape M i work
      have he : BankedSimulation.workTape M j=i := by
        apply Fin.ext
        dsimp only [j,BankedSimulation.innerTape,BankedSimulation.workTape]
        omega
      rw [←he]
      exact le_trans (positive j) (h.2 j)
    · have he : i=TrackedParentOutputBridge.bufferTape M := by
        apply Fin.ext
        change i.val=1
        omega
      rw [he]
      exact le_trans hsigma h.1
  have extraSafe : 1 ≤ (outputPadBase M n base rho sigma offset extent c label w).head
      (FixedTapeExtension.extraTape (TrackedParentOutputBridge.machine M)) := by
    change 1 ≤ (outputPadBase M n base rho sigma offset extent c label w).head (FiniteContinuationStack.stackTape M)
    simp only [outputPadBase,popped,FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame,if_true]
    exact hrho
  exact padded_head_safe (TrackedParentOutputBridge.machine M)
    (outputPadBase M n base rho sigma offset extent c label w)
    (TrackedParentOutputBridge.initialFrame M
      (outputPlainBase M n base rho sigma offset extent c label w)
      sigma offset extent (parentAtEnds M extent c) w) t oldSafe extraSafe

private theorem pop_heads_safe (M : MultitapeTM) (n : ℕ)
    (base : (FiniteContinuationStack.machine M n).Cfg) (rho : ℕ) (label : Fin n)
    (hrho : 1 ≤ rho) (safe : headSafe (FiniteContinuationStack.machine M n) base) :
    safePrefix (machine M n)
      (liftPop M n (FiniteContinuationStack.popStartFrame M n base rho label)) (n+2) := by
  intro t ht i hi
  by_cases zero : t=0
  · subst t
    change 1 ≤ (FiniteContinuationStack.popStartFrame M n base rho label).head i
    simp only [FiniteContinuationStack.popStartFrame,FiniteContinuationStack.pushFrame]
    by_cases stack : i=FiniteContinuationStack.stackTape M
    · rw [if_pos stack]
      omega
    · rw [if_neg stack]
      exact safe i hi
  · by_cases scanning : t ≤ n+1
    · rw [show t=(t-1)+1 by omega,Function.iterate_add_apply,Function.iterate_one,
        pop_step M n _ (by intro q; simp [FiniteContinuationStack.popStartFrame]),
        FiniteContinuationStack.pop_start_step,pop_run M n base rho label (t-1) (by omega)]
      change 1 ≤ (FiniteContinuationStack.popFrame M n base rho label (t-1)).head i
      simp only [FiniteContinuationStack.popFrame]
      by_cases stack : i=FiniteContinuationStack.stackTape M
      · rw [if_pos stack]
        omega
      · rw [if_neg stack]
        exact safe i hi
    · have last : t=n+2 := by omega
      rw [last,pop_correct]
      change 1 ≤ (FiniteContinuationStack.finalFrame M n base rho label).head i
      simp only [FiniteContinuationStack.finalFrame,FiniteContinuationStack.pushStartFrame]
      by_cases stack : i=FiniteContinuationStack.stackTape M
      · rw [if_pos stack]
        exact hrho
      · rw [if_neg stack]
        exact safe i hi

end IntMul.EndParkResume


-- Complete protected resume service follows.
namespace IntMul.EndParkResume

open IntMul.BankedSimulation (workTape)
open IntMul.FiniteContinuationStack (stackTape)

private theorem result_rewind_span_owned (M : MultitapeTM) (extent : Fin M.k → ℕ) :
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
private theorem resume_protected_prefix (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n).step^[t] (initialFrame M n base rho sigma offset extent c label w)=
        finalFrame M n base rho sigma offset extent c label w ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n).inTape →
        1 ≤ ((machine M n).step^[s]
          (initialFrame M n base rho sigma offset extent c label w)).head i := by
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
    rw [result_rewind_span_owned] at r
    rw [show extent M.outTape+1+1=extent M.outTape+2 by omega] at r
    rw [r.1] at h
    exact h
  have hrhalt : ((restoreMachine M).step^[extent M.outTape+2]
      (restoreStart M n base rho sigma offset extent c label w)).state=(restoreMachine M).qHalt := by
    rw [hrestore]
    rfl
  obtain ⟨s,hs,hsrun,hssafe⟩ := lifted_first_exit (machine M n) (restoreMachine M)
    (liftRestore M n) (restoreStart M n base rho sigma offset extent c label w) (extent M.outTape+2) hrhalt
    (by intro t live; exact restore_iterate M n _ t live)
    (restore_heads_safe M n base rho sigma offset extent c label w positive hrho hsigma unique)
  rw [hrestore] at hsrun
  have hrestoreFinalSafe : headSafe (machine M n)
      (liftRestore M n (restoreFinal M n base rho sigma offset extent c label w)) := by
    have h := hssafe s le_rfl
    rw [hsrun] at h
    exact h
  have hpopSafe := pop_heads_safe M n
    (popParent M n base rho sigma offset extent c label w) rho label hrho hrestoreFinalSafe
  have hrestoreDispatch : (machine M n).step
      (liftRestore M n (restoreFinal M n base rho sigma offset extent c label w))=
      liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label) := by
    rw [restore_dispatch M n _ rfl,restore_pop_ready]
  have hrestoreServiceSafe := safe_concat (machine M n)
    (liftRestore M n (restoreStart M n base rho sigma offset extent c label w))
    (liftRestore M n (restoreFinal M n base rho sigma offset extent c label w)) s 1 hsrun hssafe
    (safe_one _ _ _ hrestoreDispatch hrestoreFinalSafe (hpopSafe 0 (Nat.zero_le _)))
  have hdown : (machine M n).step^[s+1]
      (initialFrame M n base rho sigma offset extent c label w)=
      liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label) := by
    change (machine M n).step^[s+1]
      (liftRestore M n (restoreStart M n base rho sigma offset extent c label w))=_
    rw [Function.iterate_succ_apply',hsrun,restore_dispatch M n _ rfl,restore_pop_ready]
  have hpop : (machine M n).step^[n+3]
      (liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label))=
      liftOutput M n label (outputStart M n base rho sigma offset extent c label w) := by
    rw [show n+3=(n+2)+1 by omega,Function.iterate_succ_apply',pop_correct]
    change (machine M n).step (liftPop M n (popped M n base rho sigma offset extent c label w))=_
    rw [pop_dispatch M n label _ rfl,pop_output_ready]
  have hpoppedSafe : headSafe (machine M n) (liftPop M n (popped M n base rho sigma offset extent c label w)) := by
    have h := hpopSafe (n+2) le_rfl
    rw [pop_correct] at h
    exact h
  have hpopDispatch : (machine M n).step (liftPop M n (popped M n base rho sigma offset extent c label w))=
      liftOutput M n label (outputStart M n base rho sigma offset extent c label w) := by
    rw [pop_dispatch M n label _ rfl,pop_output_ready]
  have houtputAll := output_heads_safe M n base rho sigma offset extent c label w
    positive hrho hsigma unique tail
  have hpopServiceSafe := safe_concat (machine M n)
    (liftPop M n (FiniteContinuationStack.popStartFrame M n
      (popParent M n base rho sigma offset extent c label w) rho label))
    (liftPop M n (popped M n base rho sigma offset extent c label w)) (n+2) 1
    (pop_correct M n _ rho label) hpopSafe (safe_one _ _ _ hpopDispatch hpoppedSafe (houtputAll 0))
  rw [show 1+(n+2)=n+3 by omega] at hpopServiceSafe
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
  obtain ⟨u,hu,hurun,husafe⟩ := lifted_first_exit (machine M n) (outputMachine M)
    (liftOutput M n label) (outputStart M n base rho sigma offset extent c label w)
    (w.length+2*max w.length (extent M.outTape)+5) hohalt
    (by intro t live; exact output_iterate M n label _ t live) houtputAll
  rw [houtput] at hurun
  have houtputFinalSafe : headSafe (machine M n)
      (liftOutput M n label (outputFinal M n base rho sigma offset extent c label w)) := by
    have h := husafe u le_rfl
    rw [hurun] at h
    exact h
  have houtputDispatch : (machine M n).step
      (liftOutput M n label (outputFinal M n base rho sigma offset extent c label w))=
      finalFrame M n base rho sigma offset extent c label w := by
    rw [output_dispatch M n label _ rfl]
    rfl
  have houtputServiceSafe := safe_concat (machine M n)
    (liftOutput M n label (outputStart M n base rho sigma offset extent c label w))
    (liftOutput M n label (outputFinal M n base rho sigma offset extent c label w)) u 1 hurun husafe
    (safe_one _ _ _ houtputDispatch houtputFinalSafe houtputFinalSafe)
  have hup : (machine M n).step^[u+1]
      (liftOutput M n label (outputStart M n base rho sigma offset extent c label w))=
      finalFrame M n base rho sigma offset extent c label w := by
    rw [Function.iterate_succ_apply',hurun,output_dispatch M n label _ rfl]
    rfl
  refine ⟨(u+1)+((n+3)+(s+1)),by omega,?_,?_⟩
  · rw [Function.iterate_add_apply (machine M n).step (u+1) ((n+3)+(s+1)),
      Function.iterate_add_apply (machine M n).step (n+3) (s+1),hdown,hpop,hup]
  · change safePrefix (machine M n) (initialFrame M n base rho sigma offset extent c label w)
      ((u+1)+((n+3)+(s+1)))
    have hrest := safe_concat (machine M n)
      (liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label))
      (liftOutput M n label (outputStart M n base rho sigma offset extent c label w)) (n+3) (u+1)
      hpop hpopServiceSafe (by simpa only [Nat.add_comm] using houtputServiceSafe)
    have hwhole := safe_concat (machine M n)
      (initialFrame M n base rho sigma offset extent c label w)
      (liftPop M n (FiniteContinuationStack.popStartFrame M n
        (popParent M n base rho sigma offset extent c label w) rho label)) (s+1) ((u+1)+(n+3))
      hdown (by simpa only [Nat.add_comm,initialFrame] using hrestoreServiceSafe) hrest
    convert hwhole using 1 <;> omega


end IntMul.EndParkResume


open IntMul IntMul.EndParkResume

theorem solution (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (label : Fin n) (w : List Bool)
    (positive : ∀ j, 1 ≤ offset j) (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ p, extent M.outTape < p → c.cells M.outTape p=M.blank) :
    ∃ t, t ≤ extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n).step^[t] (initialFrame M n base rho sigma offset extent c label w)=
        finalFrame M n base rho sigma offset extent c label w ∧
      ∀ s, s ≤ t → ∀ i, i ≠ (machine M n).inTape →
        1 ≤ ((machine M n).step^[s]
          (initialFrame M n base rho sigma offset extent c label w)).head i :=
  IntMul.EndParkResume.resume_protected_prefix M n base rho sigma offset extent c label w positive hrho hsigma unique tail

#print axioms solution
