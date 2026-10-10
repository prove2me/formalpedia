-- Prove2me | solution 1 for IntMul.TrackedBankReservation.reserve_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T23:35:53.328552+00:00
-- url     : https://prove2.me/submissions/ce9fa7ec-eec3-400a-88ba-9dda5739cbd6

import Definitions.Def_IntMul_TrackedBankReservation
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)


namespace IntMul.TrackedBankReservation

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
    (seekFrame M base offset extent c pos r).cells (workTape M j) (offset j + p) =
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [seekFrame,TrackedBankedSimulation.embed,dif_pos (frame_work_ge M j),frame_inner_work,parentBase]
  simp only [if_neg (by omega : ¬offset j + p < offset j),Nat.add_sub_cancel_left]

private theorem frame_heads (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    (seekFrame M base offset extent c pos r).head (workTape M j) =
      offset j + pos j + min r (distance M extent pos j) := by
  simp [seekFrame,frame_work_ge,frame_inner_work]

private theorem frame_scan (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) (j : Fin M.k) :
    visited M ((seekFrame M base offset extent c pos r).cells (workTape M j)
      ((seekFrame M base offset extent c pos r).head (workTape M j))) =
      decide (pos j + min r (distance M extent pos j) ≤ extent j) := by
  rw [frame_heads,show offset j + pos j + min r (distance M extent pos j) =
    offset j + (pos j + min r (distance M extent pos j)) by omega,frame_cells]
  rfl

/-- A head sees fresh exactly when it has finished its independent seek. -/
private theorem frame_fresh_iff (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (near : ∀ j, pos j ≤ extent j + 1) (r : ℕ) (j : Fin M.k) :
    visited M ((seekFrame M base offset extent c pos r).cells (workTape M j)
      ((seekFrame M base offset extent c pos r).head (workTape M j))) = false ↔
        distance M extent pos j ≤ r := by
  rw [frame_scan,decide_eq_false_iff_not]
  have hn := near j
  unfold distance
  omega

private theorem frame_visited_iff (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (near : ∀ j, pos j ≤ extent j + 1) (r : ℕ) (j : Fin M.k) :
    visited M ((seekFrame M base offset extent c pos r).cells (workTape M j)
      ((seekFrame M base offset extent c pos r).head (workTape M j))) = true ↔
        r < distance M extent pos j := by
  rw [frame_scan,decide_eq_true_iff]
  have hn := near j
  unfold distance
  omega

private theorem all_fresh_iff (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (near : ∀ j, pos j ≤ extent j + 1) (r : ℕ) :
    (∀ j, visited M ((seekFrame M base offset extent c pos r).cells (workTape M j)
      ((seekFrame M base offset extent c pos r).head (workTape M j))) = false) ↔
        span M (distance M extent pos) ≤ r := by
  simp only [frame_fresh_iff M base offset extent c pos near]
  constructor
  · intro h
    exact Finset.sup_le (by intro j _; exact h j)
  · intro h j
    exact (Finset.le_sup (Finset.mem_univ j)).trans h

/-- Blank-tail initialization proves these physically found new offsets
have entirely fresh suffixes, while all saved parent cells are retained. -/
private theorem final_fresh (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    (∀ j p, newOffsets M offset extent j ≤ p →
      (finalFrame M base offset extent c).cells (workTape M j) p = some (M.blank,false)) ∧
    (∀ j, (finalFrame M base offset extent c).head (workTape M j) = newOffsets M offset extent j) := by
  constructor
  · intro j p hp
    have ho : offset j ≤ p := by unfold newOffsets at hp; omega
    have he : extent j < p - offset j := by unfold newOffsets at hp; omega
    simp only [finalFrame,TrackedBankedSimulation.embed,dif_pos (frame_work_ge M j),frame_inner_work,parentBase,
      if_neg (by omega : ¬p < offset j)]
    rw [tail j _ he]
    simp [show ¬p - offset j ≤ extent j by omega]
  · intro j
    simp [finalFrame,frame_work_ge,frame_inner_work]

end IntMul.TrackedBankReservation



namespace IntMul.TrackedBankReservation

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

private theorem seek_step (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (near : ∀ j, pos j ≤ extent j + 1) (r : ℕ)
    (hr : r < span M (distance M extent pos)) :
    (machine M).step (seekFrame M base offset extent c pos r) =
      seekFrame M base offset extent c pos (r + 1) := by
  classical
  have hn : ¬∀ j, visited M ((seekFrame M base offset extent c pos r).cells (workTape M j)
      ((seekFrame M base offset extent c pos r).head (workTape M j))) = false := by
    intro h
    have hh := (all_fresh_iff M base offset extent c pos near r).mp h
    omega
  have ht : transition M .seek
      (fun i => (seekFrame M base offset extent c pos r).cells i ((seekFrame M base offset extent c pos r).head i)) =
      (.seek,fun i => ((seekFrame M base offset extent c pos r).cells i ((seekFrame M base offset extent c pos r).head i),
        if 2 ≤ i.val ∧ visited M ((seekFrame M base offset extent c pos r).cells i
          ((seekFrame M base offset extent c pos r).head i)) = true then .right else .stay)) := by
    simp only [transition,if_neg hn]
  change transition M (seekFrame M base offset extent c pos r).state _ = _ at ht
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
    · have hv : visited M ((seekFrame M base offset extent c pos r).cells i
          ((seekFrame M base offset extent c pos r).head i)) = true ↔
            r < distance M extent pos (innerTape M i hi) := by
        have h := frame_visited_iff M base offset extent c pos near r (innerTape M i hi)
        rw [complete_work_inner M i hi] at h
        exact h
      by_cases hd : r < distance M extent pos (innerTape M i hi)
      · rw [if_pos ⟨hi,hv.mpr hd⟩]
        simp only [seekFrame,dif_pos hi,Nat.min_eq_left hd.le,
          Nat.min_eq_left (by omega : r + 1 ≤ distance M extent pos (innerTape M i hi))]
        omega
      · rw [if_neg (by intro h; exact hd (hv.mp h.2))]
        simp only [seekFrame,dif_pos hi,Nat.min_eq_right (by omega : distance M extent pos (innerTape M i hi) ≤ r),
          Nat.min_eq_right (by omega : distance M extent pos (innerTape M i hi) ≤ r + 1)]
    · rw [if_neg (by intro h; exact hi h.1)]
      simp only [seekFrame,dif_neg hi]

private theorem seek_run (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (near : ∀ j, pos j ≤ extent j + 1) (r : ℕ)
    (hr : r ≤ span M (distance M extent pos)) :
    (machine M).step^[r] (seekFrame M base offset extent c pos 0) = seekFrame M base offset extent c pos r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply',ih (by omega),seek_step M base offset extent c pos near r (by omega)]

private theorem seek_end (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (near : ∀ j, pos j ≤ extent j + 1) :
    (machine M).step (seekFrame M base offset extent c pos (span M (distance M extent pos))) =
      finalFrame M base offset extent c := by
  have hf := (all_fresh_iff M base offset extent c pos near (span M (distance M extent pos))).mpr le_rfl
  have ht : transition M .seek
      (fun i => (seekFrame M base offset extent c pos (span M (distance M extent pos))).cells i
        ((seekFrame M base offset extent c pos (span M (distance M extent pos))).head i)) =
      (.halt,fun i => ((seekFrame M base offset extent c pos (span M (distance M extent pos))).cells i
        ((seekFrame M base offset extent c pos (span M (distance M extent pos))).head i),.stay)) := by
    simp only [transition,if_pos hf]
  change transition M (seekFrame M base offset extent c pos (span M (distance M extent pos))).state _ = _ at ht
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
    · have hj := near (innerTape M i hi)
      have hs : distance M extent pos (innerTape M i hi) ≤ span M (distance M extent pos) :=
        Finset.le_sup (Finset.mem_univ (innerTape M i hi))
      simp only [seekFrame,finalFrame,dif_pos hi]
      rw [Nat.min_eq_right hs]
      simp only [newOffsets,distance]
      omega
    · simp only [seekFrame,finalFrame,dif_neg hi]

/-- Fresh child suffixes are located by actual independent seeks, preserving
the full parent cells. The exact clock is the maximum remaining distance
plus one charged halt transition; no offsets or extents enter delta. -/
private theorem reserve_correct (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    (machine M).step^[span M (distance M extent c.head) + 1] (initialFrame M base offset extent c) =
      finalFrame M base offset extent c ∧
    (∀ j p, newOffsets M offset extent j ≤ p →
      (finalFrame M base offset extent c).cells (workTape M j) p = some (M.blank,false)) ∧
    (∀ j, (finalFrame M base offset extent c).head (workTape M j) = newOffsets M offset extent j) := by
  constructor
  · change (machine M).step^[span M (distance M extent c.head) + 1]
      (seekFrame M base offset extent c c.head 0) = _
    rw [Function.iterate_succ_apply',seek_run M base offset extent c c.head near _ le_rfl,seek_end M base offset extent c c.head near]
  · exact final_fresh M base offset extent c tail

private theorem reservation_workspace_bound (M : MultitapeTM) (extent pos : Fin M.k → ℕ) :
    span M (distance M extent pos) + 1 ≤ span M extent + 2 := by
  have h : span M (distance M extent pos) ≤ span M extent + 1 := by
    apply Finset.sup_le
    intro j _
    have hj : extent j ≤ span M extent := Finset.le_sup (Finset.mem_univ j)
    unfold distance
    omega
  omega

end IntMul.TrackedBankReservation


open IntMul IntMul.TrackedBankReservation

theorem solution (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    (machine M).step^[span M (distance M extent c.head) + 1] (initialFrame M base offset extent c) =
      finalFrame M base offset extent c ∧
    (∀ j p, newOffsets M offset extent j ≤ p →
      (finalFrame M base offset extent c).cells (workTape M j) p = some (M.blank,false)) ∧
    (∀ j, (finalFrame M base offset extent c).head (workTape M j) = newOffsets M offset extent j) :=
  IntMul.TrackedBankReservation.reserve_correct M base offset extent c near tail

#print axioms solution
