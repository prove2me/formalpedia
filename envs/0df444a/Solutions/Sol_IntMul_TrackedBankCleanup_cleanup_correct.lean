-- Prove2me | solution 1 for IntMul.TrackedBankCleanup.cleanup_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T22:14:58.597856+00:00
-- url     : https://prove2.me/submissions/e1f9b2a2-0e45-4cd3-9d58-3a8a95282502

import Definitions.Def_IntMul_TrackedBankCleanup
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)


namespace IntMul.TrackedBankCleanup

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem work_ge (M : MultitapeTM) (j : Fin M.k) : 2 ≤ (workTape M j).val := by simp [workTape]

private theorem inner_work (M : MultitapeTM) (j : Fin M.k) (h : 2 ≤ (workTape M j).val) :
    innerTape M (workTape M j) h = j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem work_inner (M : MultitapeTM) (i : Fin (M.k + 2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h) = i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem span_le (M : MultitapeTM) (f : Fin M.k → ℕ) (n : ℕ) :
    span M f ≤ n ↔ ∀ j, f j ≤ n := by
  constructor
  · intro h j
    exact (Finset.le_sup (s := Finset.univ) (f := f) (Finset.mem_univ j)).trans h
  · intro h
    exact Finset.sup_le (by intro j _; exact h j)

private theorem le_span (M : MultitapeTM) (f : Fin M.k → ℕ) (j : Fin M.k) : f j ≤ span M f :=
  Finset.le_sup (Finset.mem_univ j)

private theorem span_zero (M : MultitapeTM) (f : Fin M.k → ℕ) : span M f = 0 ↔ ∀ j, f j = 0 := by
  constructor
  · intro h j
    have hj := le_span M f j
    omega
  · intro h
    have hs : span M f ≤ 0 := (span_le M f 0).mpr (by intro j; rw [h j])
    omega

private theorem span_pred (M : MultitapeTM) (f : Fin M.k → ℕ) :
    span M (fun j => f j - 1) = span M f - 1 := by
  apply le_antisymm
  · apply (span_le M _ _).mpr
    intro j
    have h := le_span M f j
    omega
  · obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨M.inTape,Finset.mem_univ _⟩ f
    have h := le_span M (fun j => f j - 1) j
    change f j - 1 ≤ span M (fun j => f j - 1) at h
    change span M f = f j at hj
    rw [←hj] at h
    exact h

private theorem protect_self_stay (M : MultitapeTM) (a : Sym M) : protect M a a .stay = (a,.stay) := by
  cases a <;> rfl

private theorem protect_self_right (M : MultitapeTM) (a : Sym M) : protect M a a .right = (a,.right) := by
  cases a <;> rfl

private theorem protect_self_left (M : MultitapeTM) (a : Sym M) (h : a ≠ none) :
    protect M a a .left = (a,.left) := by
  cases a with
  | none => exact False.elim (h rfl)
  | some s => rfl

private theorem marker_boundary (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) :
    markerTape M base offset offset = some (M.startSym,true) := by simp [markerTape]

private theorem marker_payload (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) (p : ℕ) :
    markerTape M base offset (offset + p + 1) = some (M.blank,false) := by
  simp [markerTape,show ¬offset + p + 1 < offset by omega,show offset + p + 1 ≠ offset by omega]

private theorem marker_erase (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) :
    Function.update (markerTape M base offset) offset (some (M.blank,false)) = freshTape M base offset := by
  classical
  funext p
  by_cases he : p = offset
  · subst p
    simp [freshTape]
  · rw [Function.update_of_ne he]
    simp only [markerTape,freshTape]
    split <;> simp only [if_neg he]

end IntMul.TrackedBankCleanup



namespace IntMul.TrackedBankCleanup

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem rewind_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem rewind_rewind_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ) (j : Fin M.k) :
    (rewindFrame M base offset extent c pos).cells (workTape M j)
      ((rewindFrame M base offset extent c pos).head (workTape M j)) =
        some (c.cells j (pos j),decide (pos j ≤ extent j)) := by
  simp only [rewindFrame,TrackedBankedSimulation.embed,dif_pos (work_ge M j),inner_work]
  simp

private theorem rewind_rewind_scan_iff (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) (j : Fin M.k) :
    (rewindFrame M base offset extent c pos).cells (workTape M j)
      ((rewindFrame M base offset extent c pos).head (workTape M j)) = some (M.startSym,true) ↔ pos j = 0 := by
  rw [rewind_rewind_scan]
  constructor
  · intro h
    exact (unique j _).mp (congrArg Prod.fst (Option.some.inj h))
  · intro h
    simp only [h,(unique j 0).mpr rfl,Nat.zero_le,decide_true]

private theorem rewind_parallel_left_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (pos : Fin M.k → ℕ)
    (marker : ∀ j, a (workTape M j) = some (M.startSym,true) ↔ pos j = 0)
    (nonnull : ∀ j, a (workTape M j) ≠ none) (active : ¬∀ j, pos j = 0) :
    transition M .rewind a = (.rewind,fun i => (a i,
      if h : 2 ≤ i.val then (if pos (innerTape M i h) = 0 then .stay else .left) else .stay)) := by
  classical
  have hm : ¬∀ j, a (workTape M j) = some (M.startSym,true) := by
    intro h
    exact active (by intro j; exact (marker j).mp (h j))
  simp only [transition,rawTransition,if_neg hm]
  congr 1
  funext i
  by_cases hi : 2 ≤ i.val
  · have hj : a i = some (M.startSym,true) ↔ pos (innerTape M i hi) = 0 := by
      have h := marker (innerTape M i hi)
      rw [work_inner] at h
      exact h
    have hn : a i ≠ none := by
      have h := nonnull (innerTape M i hi)
      rw [work_inner] at h
      exact h
    simp only [dif_pos hi]
    by_cases hz : pos (innerTape M i hi) = 0
    · have hd : ¬(2 ≤ i.val ∧ a i ≠ some (M.startSym,true)) := by intro h; exact h.2 (hj.mpr hz)
      simp only [if_neg hd,if_pos hz,protect_self_stay]
    · have hd : 2 ≤ i.val ∧ a i ≠ some (M.startSym,true) := ⟨hi,mt hj.mp hz⟩
      simp only [if_pos hd,if_neg hz]
      exact protect_self_left M _ hn
  · have hd : ¬(2 ≤ i.val ∧ a i ≠ some (M.startSym,true)) := by tauto
    simp only [dif_neg hi,if_neg hd,protect_self_stay]

private theorem rewind_rewind_left_step (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) (active : ¬∀ j, pos j = 0) :
    (machine M).step (rewindFrame M base offset extent c pos) =
      rewindFrame M base offset extent c (fun j => pos j - 1) := by
  have ht := rewind_parallel_left_transition M
    (fun i => (rewindFrame M base offset extent c pos).cells i ((rewindFrame M base offset extent c pos).head i))
    pos (rewind_rewind_scan_iff M base offset extent c pos unique)
    (by intro j; rw [rewind_rewind_scan]; exact Option.some_ne_none _) active
  change transition M (rewindFrame M base offset extent c pos).state
    (fun i => (rewindFrame M base offset extent c pos).cells i ((rewindFrame M base offset extent c pos).head i)) = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [rewindFrame,dif_pos hi]
      by_cases hz : pos (innerTape M i hi) = 0
      · simp only [hz,if_true,Nat.add_zero,Nat.zero_sub]
      · simp only [if_neg hz]
        omega
    · simp only [rewindFrame,dif_neg hi]

/-- All bank heads rewind in parallel; each independently stops at its local
marker. No prefix cell is crossed, even when other heads finish later. -/
private theorem rewind_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    (machine M).step^[span M pos] (rewindFrame M base offset extent c pos) =
      rewindFrame M base offset extent c (fun _ => 0) := by
  generalize hn : span M pos = n
  induction n using Nat.strong_induction_on generalizing pos with
  | h n ih =>
      by_cases hz : ∀ j, pos j = 0
      · have he : pos = (fun _ => 0) := funext hz
        have hspan := (span_zero M pos).mpr hz
        have hzero : n = 0 := by omega
        rw [hzero,Function.iterate_zero_apply,he]
      · have hnpos : 0 < n := by
          have hspan : span M pos ≠ 0 := mt (span_zero M pos).mp hz
          omega
        have he : n = span M (fun j => pos j - 1) + 1 := by rw [span_pred]; omega
        rw [he,Function.iterate_succ_apply,rewind_rewind_left_step M base offset extent c pos unique hz]
        exact ih _ (by rw [span_pred]; omega) _ rfl

/-- One physical dispatch moves all stopped heads onto the first payload cell.
The caller tapes and every saved prefix are retained. -/
private theorem rewind_enter_sweep (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    (machine M).step (rewindFrame M base offset extent c (fun _ => 0)) =
      sweepFrame M base offset extent (fun _ => 0) c := by
  have hm : ∀ j, (rewindFrame M base offset extent c (fun _ => 0)).cells
      (workTape M j) ((rewindFrame M base offset extent c (fun _ => 0)).head (workTape M j)) =
        some (M.startSym,true) := by
    intro j
    exact (rewind_rewind_scan_iff M base offset extent c (fun _ => 0) unique j).mpr rfl
  have ht : transition M .rewind
      (fun i => (rewindFrame M base offset extent c (fun _ => 0)).cells i
        ((rewindFrame M base offset extent c (fun _ => 0)).head i)) =
      (.sweep,fun i => ((rewindFrame M base offset extent c (fun _ => 0)).cells i
        ((rewindFrame M base offset extent c (fun _ => 0)).head i),
          if 2 ≤ i.val then .right else .stay)) := by
    classical
    simp only [transition,rawTransition,if_pos hm]
    congr 1
    funext i
    split <;> first | exact protect_self_right M _ | exact protect_self_stay M _
  change transition M (rewindFrame M base offset extent c (fun _ => 0)).state
    (fun i => (rewindFrame M base offset extent c (fun _ => 0)).cells i
      ((rewindFrame M base offset extent c (fun _ => 0)).head i)) = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    funext p
    simp only [rewindFrame,TrackedBankedSimulation.embed,parentBase,sweepFrame]
    simp only [sweepCells]
    by_cases hi : 2 ≤ i.val
    · simp only [dif_pos hi]
      split
      · rfl
      · by_cases hz : p - offset (innerTape M i hi) = 0
        · simp only [hz,if_true,(unique _ 0).mpr rfl,Nat.zero_le,decide_true]
        · have hn : ¬p - offset (innerTape M i hi) ≤ 0 := by omega
          simp only [if_neg hz,if_neg hn]
    · simp only [dif_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp [rewindFrame,sweepFrame,hi]
    · simp [rewindFrame,sweepFrame,hi]

end IntMul.TrackedBankCleanup



namespace IntMul.TrackedBankCleanup

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

/-- A single bank's proof-side description during physical erasure. -/
private def payloadTape (M : MultitapeTM) (base : ℕ → Sym M) (offset extent cleared : ℕ)
    (cells : ℕ → M.Sym) (p : ℕ) : Sym M :=
  if p < offset then base p else
    let v := p - offset
    if v = 0 then some (M.startSym,true)
    else if v ≤ cleared then some (M.blank,false)
    else some (cells v,decide (v ≤ extent))

private theorem sweep_work (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent cleared : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    sweepCells M base offset extent cleared c (workTape M j) =
      payloadTape M (base.cells (workTape M j)) (offset j) (extent j) (cleared j) (c.cells j) := by
  funext p
  simp only [sweepCells,dif_pos (work_ge M j),inner_work,payloadTape]

private theorem payload_next (M : MultitapeTM) (base : ℕ → Sym M) (offset extent cleared : ℕ)
    (cells : ℕ → M.Sym) :
    payloadTape M base offset extent cleared cells (offset + cleared + 1) =
      some (cells (cleared + 1),decide (cleared + 1 ≤ extent)) := by
  simp [payloadTape,show ¬offset + cleared + 1 < offset by omega,
    show offset + cleared + 1 - offset = cleared + 1 by omega]

private theorem payload_erase_next (M : MultitapeTM) (base : ℕ → Sym M)
    (offset extent cleared : ℕ) (cells : ℕ → M.Sym) :
    Function.update (payloadTape M base offset extent cleared cells)
      (offset + cleared + 1) (some (M.blank,false)) =
        payloadTape M base offset extent (cleared + 1) cells := by
  classical
  funext p
  by_cases he : p = offset + cleared + 1
  · subst p
    simp [payloadTape,show ¬offset + cleared + 1 < offset by omega,
      show offset + cleared + 1 - offset = cleared + 1 by omega]
  · rw [Function.update_of_ne he]
    simp only [payloadTape]
    by_cases hp : p < offset
    · simp only [if_pos hp]
    · simp only [if_neg hp]
      by_cases hz : p - offset = 0
      · simp only [if_pos hz]
      · simp only [if_neg hz]
        have hc : p - offset ≤ cleared + 1 ↔ p - offset ≤ cleared := by omega
        simp only [hc]

private theorem payload_finished (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (tail : ∀ p, extent < p → cells p = M.blank) :
    payloadTape M base offset extent extent cells = markerTape M base offset := by
  funext p
  simp only [payloadTape,markerTape]
  by_cases hp : p < offset
  · simp only [if_pos hp]
  · simp only [if_neg hp]
    by_cases he : p = offset
    · subst p
      simp
    · have hz : p - offset ≠ 0 := by omega
      simp only [if_neg he,if_neg hz]
      by_cases hc : p - offset ≤ extent
      · simp only [if_pos hc]
      · have ht := tail (p - offset) (by omega)
        simp only [ht,hc,decide_false,if_false]

private theorem sweep_finished_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    (sweepFrame M base offset extent extent c).cells =
      (restoreFrame M base offset extent).cells := by
  funext i
  by_cases hi : 2 ≤ i.val
  · have hj := sweep_work M base offset extent extent c (innerTape M i hi)
    rw [work_inner] at hj
    change sweepCells M base offset extent extent c i = _
    rw [hj,payload_finished M _ _ _ _ (tail (innerTape M i hi))]
    simp only [restoreFrame,dif_pos hi]
  · funext p
    simp [sweepFrame,sweepCells,restoreFrame,hi]

end IntMul.TrackedBankCleanup



namespace IntMul.TrackedBankCleanup

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem sweep_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private def advance (M : MultitapeTM) (extent cleared : Fin M.k → ℕ) : Fin M.k → ℕ :=
  fun j => if cleared j < extent j then cleared j + 1 else cleared j

private theorem sweep_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent cleared : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (sweepFrame M base offset extent cleared c).cells (workTape M j)
      ((sweepFrame M base offset extent cleared c).head (workTape M j)) =
        some (c.cells j (cleared j + 1),decide (cleared j + 1 ≤ extent j)) := by
  simp only [sweepFrame,dif_pos (work_ge M j),inner_work]
  rw [sweep_work,payload_next]

private theorem sweep_visit_iff (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent cleared : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    visited M ((sweepFrame M base offset extent cleared c).cells (workTape M j)
      ((sweepFrame M base offset extent cleared c).head (workTape M j))) = true ↔
        cleared j < extent j := by
  rw [sweep_scan]
  simp only [visited,decide_eq_true_eq]
  omega

private theorem sweep_sweep_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (extent cleared : Fin M.k → ℕ)
    (flags : ∀ j, visited M (a (workTape M j)) = true ↔ cleared j < extent j)
    (nonnull : ∀ j, a (workTape M j) ≠ none)
    (active : ∃ j, cleared j < extent j) :
    transition M .sweep a = (.sweep,fun i => if h : 2 ≤ i.val then
      if cleared (innerTape M i h) < extent (innerTape M i h) then
        (some (M.blank,false),.right) else (a i,.stay) else (a i,.stay)) := by
  classical
  have ha : ¬∀ j, visited M (a (workTape M j)) = false := by
    obtain ⟨j,hj⟩ := active
    intro h
    have ht := (flags j).mpr hj
    rw [h j] at ht
    exact Bool.false_ne_true ht
  simp only [transition,rawTransition,if_neg ha]
  congr 1
  funext i
  by_cases hi : 2 ≤ i.val
  · have hf := flags (innerTape M i hi)
    have hn := nonnull (innerTape M i hi)
    rw [work_inner] at hf hn
    simp only [dif_pos hi]
    by_cases hl : cleared (innerTape M i hi) < extent (innerTape M i hi)
    · have hs : 2 ≤ i.val ∧ visited M (a i) = true := ⟨hi,hf.mpr hl⟩
      simp only [if_pos hs,if_pos hl]
      cases he : a i with
      | none => exact False.elim (hn he)
      | some s => rfl
    · have hs : ¬(2 ≤ i.val ∧ visited M (a i) = true) := by
        intro h
        exact hl (hf.mp h.2)
      simp only [if_neg hs,if_neg hl,protect_self_stay]
  · have hs : ¬(2 ≤ i.val ∧ visited M (a i) = true) := by tauto
    simp only [dif_neg hi,if_neg hs,protect_self_stay]

/-- One transition clears precisely the next still-visited cell on each
unfinished bank; finished bank heads and all caller tapes stay put. -/
private theorem sweep_step (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent cleared : Fin M.k → ℕ) (c : M.Cfg)
    (active : ∃ j, cleared j < extent j) :
    (machine M).step (sweepFrame M base offset extent cleared c) =
      sweepFrame M base offset extent (advance M extent cleared) c := by
  have ht := sweep_sweep_transition M
    (fun i => (sweepFrame M base offset extent cleared c).cells i
      ((sweepFrame M base offset extent cleared c).head i)) extent cleared
    (sweep_visit_iff M base offset extent cleared c)
    (by intro j; rw [sweep_scan]; exact Option.some_ne_none _) active
  change transition M (sweepFrame M base offset extent cleared c).state
    (fun i => (sweepFrame M base offset extent cleared c).cells i
      ((sweepFrame M base offset extent cleared c).head i)) = _ at ht
  apply sweep_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [dif_pos hi]
      by_cases hl : cleared (innerTape M i hi) < extent (innerTape M i hi)
      · simp only [if_pos hl]
        simp only [sweepFrame,dif_pos hi]
        change Function.update (sweepCells M base offset extent cleared c i)
          (offset (innerTape M i hi) + cleared (innerTape M i hi) + 1) (some (M.blank,false)) = _
        have hleft := sweep_work M base offset extent cleared c (innerTape M i hi)
        have hright := sweep_work M base offset extent (advance M extent cleared) c (innerTape M i hi)
        rw [work_inner] at hleft hright
        change _ = sweepCells M base offset extent (advance M extent cleared) c i
        rw [hleft,hright]
        simp only [advance,if_pos hl]
        exact payload_erase_next M _ _ _ _ _
      · simp only [if_neg hl]
        rw [Function.update_eq_self]
        have hleft := sweep_work M base offset extent cleared c (innerTape M i hi)
        have hright := sweep_work M base offset extent (advance M extent cleared) c (innerTape M i hi)
        rw [work_inner] at hleft hright
        change sweepCells M base offset extent cleared c i = sweepCells M base offset extent (advance M extent cleared) c i
        rw [hleft,hright]
        simp only [advance,if_neg hl]
    · simp only [dif_neg hi]
      rw [Function.update_eq_self]
      funext p
      simp only [sweepFrame]
      simp only [sweepCells,dif_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [dif_pos hi]
      by_cases hl : cleared (innerTape M i hi) < extent (innerTape M i hi)
      · simp only [if_pos hl,sweepFrame,dif_pos hi,advance,if_pos hl]
        omega
      · simp only [if_neg hl,sweepFrame,dif_pos hi,advance,if_neg hl]
    · simp only [dif_neg hi,sweepFrame,dif_neg hi]

private theorem sweep_advance_min (M : MultitapeTM) (extent : Fin M.k → ℕ) (n : ℕ) :
    advance M extent (fun j => min n (extent j)) = fun j => min (n + 1) (extent j) := by
  funext j
  simp only [advance]
  split <;> omega

/-- The parallel erasure finishes in the largest visited payload extent.
Smaller banks stop at their own fresh cells without entering saved prefixes. -/
private theorem sweep_prefix_run (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (n : ℕ) (hn : n ≤ span M extent) :
    (machine M).step^[n] (sweepFrame M base offset extent (fun _ => 0) c) =
      sweepFrame M base offset extent (fun j => min n (extent j)) c := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn' : n ≤ span M extent := by omega
      have ha : ∃ j, min n (extent j) < extent j := by
        by_contra h
        have hs : span M extent ≤ n := (span_le M extent n).mpr (by
          intro j
          have hj : ¬min n (extent j) < extent j := by intro hj; exact h ⟨j,hj⟩
          omega)
        omega
      rw [Function.iterate_succ_apply',ih hn',sweep_step M base offset extent _ c ha,sweep_advance_min]

private theorem sweep_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) :
    (machine M).step^[span M extent] (sweepFrame M base offset extent (fun _ => 0) c) =
      sweepFrame M base offset extent extent c := by
  rw [sweep_prefix_run M base offset extent c _ le_rfl]
  have he : (fun j => min (span M extent) (extent j)) = extent := by
    funext j
    exact Nat.min_eq_right (le_span M extent j)
  rw [he]

/-- The first simultaneous fresh flags trigger one real left-step dispatch.
Blank-tail initialization certifies the entire erased bank suffix. -/
private theorem sweep_enter_restore (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    (machine M).step (sweepFrame M base offset extent extent c) =
      restoreFrame M base offset extent := by
  have hf : ∀ j, visited M ((sweepFrame M base offset extent extent c).cells (workTape M j)
      ((sweepFrame M base offset extent extent c).head (workTape M j))) = false := by
    intro j
    rw [sweep_scan]
    simp [visited]
  have ht : transition M .sweep (fun i => (sweepFrame M base offset extent extent c).cells i
      ((sweepFrame M base offset extent extent c).head i)) =
      (.restore,fun i => ((sweepFrame M base offset extent extent c).cells i
        ((sweepFrame M base offset extent extent c).head i),if 2 ≤ i.val then .left else .stay)) := by
    classical
    simp only [transition,rawTransition,if_pos hf]
    congr 1
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [if_pos hi]
      apply protect_self_left
      have hs := sweep_scan M base offset extent extent c (innerTape M i hi)
      rw [work_inner] at hs
      rw [hs]
      exact Option.some_ne_none _
    · simp only [if_neg hi,protect_self_stay]
  change transition M (sweepFrame M base offset extent extent c).state
    (fun i => (sweepFrame M base offset extent extent c).cells i
      ((sweepFrame M base offset extent extent c).head i)) = _ at ht
  apply sweep_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    exact congrFun (sweep_finished_cells M base offset extent c tail) i
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [if_pos hi,sweepFrame,restoreFrame,dif_pos hi]
      omega
    · simp only [if_neg hi,sweepFrame,restoreFrame,dif_neg hi]

end IntMul.TrackedBankCleanup



namespace IntMul.TrackedBankCleanup

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem restore_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem restore_restore_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (offset pos : Fin M.k → ℕ) (j : Fin M.k) :
    (restoreFrame M base offset pos).cells (workTape M j)
      ((restoreFrame M base offset pos).head (workTape M j)) =
        if pos j = 0 then some (M.startSym,true) else some (M.blank,false) := by
  simp only [restoreFrame,dif_pos (work_ge M j),inner_work]
  by_cases hz : pos j = 0
  · simp [hz,marker_boundary]
  · simp [markerTape,hz,show ¬offset j + pos j < offset j by omega,
      show offset j + pos j ≠ offset j by omega]

private theorem restore_restore_scan_iff (M : MultitapeTM) (base : (machine M).Cfg)
    (offset pos : Fin M.k → ℕ) (j : Fin M.k) :
    (restoreFrame M base offset pos).cells (workTape M j)
      ((restoreFrame M base offset pos).head (workTape M j)) = some (M.startSym,true) ↔ pos j = 0 := by
  rw [restore_restore_scan]
  by_cases hz : pos j = 0 <;> simp [hz]

private theorem restore_restore_left_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (pos : Fin M.k → ℕ)
    (marker : ∀ j, a (workTape M j) = some (M.startSym,true) ↔ pos j = 0)
    (nonnull : ∀ j, a (workTape M j) ≠ none) (active : ¬∀ j, pos j = 0) :
    transition M .restore a = (.restore,fun i => (a i,
      if h : 2 ≤ i.val then (if pos (innerTape M i h) = 0 then .stay else .left) else .stay)) := by
  classical
  have hm : ¬∀ j, a (workTape M j) = some (M.startSym,true) := by
    intro h
    exact active (by intro j; exact (marker j).mp (h j))
  simp only [transition,rawTransition,if_neg hm]
  congr 1
  funext i
  by_cases hi : 2 ≤ i.val
  · have hj := marker (innerTape M i hi)
    have hn := nonnull (innerTape M i hi)
    rw [work_inner] at hj hn
    simp only [dif_pos hi]
    by_cases hz : pos (innerTape M i hi) = 0
    · have hd : ¬(2 ≤ i.val ∧ a i ≠ some (M.startSym,true)) := by intro h; exact h.2 (hj.mpr hz)
      simp only [if_neg hd,if_pos hz,protect_self_stay]
    · have hd : 2 ≤ i.val ∧ a i ≠ some (M.startSym,true) := ⟨hi,mt hj.mp hz⟩
      simp only [if_pos hd,if_neg hz]
      exact protect_self_left M _ hn
  · have hd : ¬(2 ≤ i.val ∧ a i ≠ some (M.startSym,true)) := by tauto
    simp only [dif_neg hi,if_neg hd,protect_self_stay]

private theorem restore_restore_left_step (M : MultitapeTM) (base : (machine M).Cfg)
    (offset pos : Fin M.k → ℕ) (active : ¬∀ j, pos j = 0) :
    (machine M).step (restoreFrame M base offset pos) =
      restoreFrame M base offset (fun j => pos j - 1) := by
  have ht := restore_restore_left_transition M
    (fun i => (restoreFrame M base offset pos).cells i ((restoreFrame M base offset pos).head i))
    pos (restore_restore_scan_iff M base offset pos)
    (by intro j; rw [restore_restore_scan]; split <;> exact Option.some_ne_none _) active
  change transition M (restoreFrame M base offset pos).state
    (fun i => (restoreFrame M base offset pos).cells i ((restoreFrame M base offset pos).head i)) = _ at ht
  apply restore_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [restoreFrame,dif_pos hi]
      by_cases hz : pos (innerTape M i hi) = 0
      · simp only [hz,if_true,Nat.add_zero,Nat.zero_sub]
      · simp only [if_neg hz]
        omega
    · simp only [restoreFrame,dif_neg hi]

/-- The erased banks return in parallel to their retained local markers. -/
private theorem restore_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset pos : Fin M.k → ℕ) :
    (machine M).step^[span M pos] (restoreFrame M base offset pos) =
      restoreFrame M base offset (fun _ => 0) := by
  generalize hn : span M pos = n
  induction n using Nat.strong_induction_on generalizing pos with
  | h n ih =>
      by_cases hz : ∀ j, pos j = 0
      · have he : pos = (fun _ => 0) := funext hz
        have hspan := (span_zero M pos).mpr hz
        have hzero : n = 0 := by omega
        rw [hzero,Function.iterate_zero_apply,he]
      · have hnpos : 0 < n := by
          have hspan : span M pos ≠ 0 := mt (span_zero M pos).mp hz
          omega
        have he : n = span M (fun j => pos j - 1) + 1 := by rw [span_pred]; omega
        rw [he,Function.iterate_succ_apply,restore_restore_left_step M base offset pos hz]
        exact ih _ (by rw [span_pred]; omega) _ rfl

/-- One real final transition erases the temporary local markers and halts,
leaving genuinely fresh blank suffixes and heads at the same boundaries. -/
private theorem restore_finish (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) :
    (machine M).step (restoreFrame M base offset (fun _ => 0)) = finalFrame M base offset := by
  have hm : ∀ j, (restoreFrame M base offset (fun _ => 0)).cells (workTape M j)
      ((restoreFrame M base offset (fun _ => 0)).head (workTape M j)) = some (M.startSym,true) := by
    intro j
    exact (restore_restore_scan_iff M base offset (fun _ => 0) j).mpr rfl
  have ht : transition M .restore
      (fun i => (restoreFrame M base offset (fun _ => 0)).cells i
        ((restoreFrame M base offset (fun _ => 0)).head i)) =
      (.halt,fun i => (if 2 ≤ i.val then some (M.blank,false) else
        (restoreFrame M base offset (fun _ => 0)).cells i
          ((restoreFrame M base offset (fun _ => 0)).head i),.stay)) := by
    classical
    simp only [transition,rawTransition,if_pos hm]
    congr 1
    funext i
    by_cases hi : 2 ≤ i.val
    · have hs := hm (innerTape M i hi)
      rw [work_inner] at hs
      simp only [if_pos hi,hs,protect]
    · simp only [if_neg hi,protect_self_stay]
  change transition M (restoreFrame M base offset (fun _ => 0)).state
    (fun i => (restoreFrame M base offset (fun _ => 0)).cells i
      ((restoreFrame M base offset (fun _ => 0)).head i)) = _ at ht
  apply restore_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : 2 ≤ i.val
    · simp only [if_pos hi,restoreFrame,finalFrame,dif_pos hi,Nat.add_zero]
      exact marker_erase M _ _
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp only [restoreFrame,finalFrame,dif_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    simp only [restoreFrame,finalFrame]
    split <;> simp

end IntMul.TrackedBankCleanup



namespace IntMul.TrackedBankCleanup

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

/-- Every seek, sweep, return and local-marker erasure is an actual transition
of one four-state fixed-tape finite machine. -/
private theorem cleanup_run (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    (machine M).step^[span M pos + 2 * span M extent + 3]
      (rewindFrame M base offset extent c pos) = finalFrame M base offset := by
  have hfirst : (machine M).step^[span M pos + 1]
      (rewindFrame M base offset extent c pos) = sweepFrame M base offset extent (fun _ => 0) c := by
    rw [Function.iterate_succ_apply',rewind_correct M base offset extent c pos unique,
      rewind_enter_sweep M base offset extent c unique]
  have hsecond : (machine M).step^[span M extent + 1]
      (sweepFrame M base offset extent (fun _ => 0) c) = restoreFrame M base offset extent := by
    rw [Function.iterate_succ_apply',sweep_correct M base offset extent c,
      sweep_enter_restore M base offset extent c tail]
  have hthird : (machine M).step^[span M extent + 1]
      (restoreFrame M base offset extent) = finalFrame M base offset := by
    rw [Function.iterate_succ_apply',restore_correct M base offset extent,restore_finish]
  have hboth : (machine M).step^[(span M extent + 1) + (span M pos + 1)]
      (rewindFrame M base offset extent c pos) = restoreFrame M base offset extent := by
    rw [Function.iterate_add_apply,hfirst,hsecond]
  have hc : span M pos + 2 * span M extent + 3 =
      (span M extent + 1) + ((span M extent + 1) + (span M pos + 1)) := by omega
  rw [hc,Function.iterate_add_apply,hboth,hthird]

/-- A reusable cleanup contract: both caller tapes and their heads, all older
bank prefixes and the global markers remain intact; every used bank suffix is
fresh blank and its head is parked exactly at its old boundary. -/
private theorem cleanup_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    let final := (machine M).step^[span M pos + 2 * span M extent + 3]
      (rewindFrame M base offset extent c pos)
    final = finalFrame M base offset ∧
      (∀ i : Fin (M.k + 2), i.val < 2 → final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j p, p < offset j → final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) ∧
      (∀ j p, offset j ≤ p → final.cells (workTape M j) p = some (M.blank,false)) ∧
      (∀ j, final.head (workTape M j) = offset j) := by
  dsimp only
  rw [cleanup_run M base offset extent c pos unique tail]
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · intro i hi
    have hn : ¬2 ≤ i.val := by omega
    simp [finalFrame,hn]
  · intro j p hp
    simp only [finalFrame,dif_pos (work_ge M j),inner_work,freshTape,if_pos hp]
  · intro j
    have hp : 0 < offset j := by have h := positive j; omega
    simp only [finalFrame,dif_pos (work_ge M j),inner_work,freshTape,if_pos hp]
  · intro j p hp
    have hn : ¬p < offset j := by omega
    simp only [finalFrame,dif_pos (work_ge M j),inner_work,freshTape,if_neg hn]
  · intro j
    simp only [finalFrame,dif_pos (work_ge M j),inner_work]

/-- For actual tracked child heads the overhead is bounded by workspace,
without multiplying the child's execution time. -/
private theorem cleanup_workspace_bound (M : MultitapeTM) (extent pos : Fin M.k → ℕ)
    (near : ∀ j, pos j ≤ extent j + 1) :
    span M pos + 2 * span M extent + 3 ≤ 3 * span M extent + 4 := by
  have hp : span M pos ≤ span M extent + 1 := (span_le M pos _).mpr (by
    intro j
    have he := le_span M extent j
    have hh := near j
    omega)
  omega

end IntMul.TrackedBankCleanup


open IntMul IntMul.TrackedBankCleanup

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (pos : Fin M.k → ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    let final := (machine M).step^[span M pos + 2 * span M extent + 3]
      (rewindFrame M base offset extent c pos)
    final = finalFrame M base offset ∧
      (∀ i : Fin (M.k + 2), i.val < 2 → final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j p, p < offset j → final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) ∧
      (∀ j p, offset j ≤ p → final.cells (workTape M j) p = some (M.blank,false)) ∧
      (∀ j, final.head (workTape M j) = offset j) :=
  IntMul.TrackedBankCleanup.cleanup_correct M base offset extent positive c pos unique tail

#print axioms solution
