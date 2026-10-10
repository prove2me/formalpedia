-- Prove2me | solution 1 for IntMul.TrackedBankedSimulation.simulate_run
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T22:02:52.710673+00:00
-- url     : https://prove2.me/submissions/d440642b-152d-48bd-8f3c-d4399775d9c1

import Definitions.Def_IntMul_TrackedBankedSimulation
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)


namespace IntMul.TrackedBankedSimulation

open IntMul.BankedSimulation (workTape innerTape)

private theorem sim_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem sim_work_ge (M : MultitapeTM) (j : Fin M.k) : 2 ≤ (workTape M j).val := by simp [workTape]

private theorem sim_inner_work (M : MultitapeTM) (j : Fin M.k)
    (h : 2 ≤ (workTape M j).val) : innerTape M (workTape M j) h = j := by
  apply Fin.ext
  simp [innerTape,workTape]

private theorem sim_work_inner (M : MultitapeTM) (i : Fin (M.k + 2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h) = i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem sim_embed_work_head (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (embed M base offset extent c).head (workTape M j) = offset j + c.head j := by
  simp only [embed,dif_pos (sim_work_ge M j),sim_inner_work]

private theorem sim_embed_work_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (embed M base offset extent c).cells (workTape M j) p =
      if p < offset j then base.cells (workTape M j) p
      else some (c.cells j (p - offset j),decide (p - offset j ≤ extent j)) := by
  simp only [embed,dif_pos (sim_work_ge M j),sim_inner_work]

private theorem sim_embed_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (embed M base offset extent c).cells (workTape M j) ((embed M base offset extent c).head (workTape M j)) =
      some (c.cells j (c.head j),decide (c.head j ≤ extent j)) := by
  rw [sim_embed_work_head,sim_embed_work_cells]
  simp

private theorem sim_decoded_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) :
    (fun j => decode M ((embed M base offset extent c).cells (workTape M j)
      ((embed M base offset extent c).head (workTape M j)))) = (fun j => c.cells j (c.head j)) := by
  funext j
  rw [sim_embed_scan]
  rfl

private theorem sim_transition_state (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (live : c.state ≠ M.qHalt) :
    (transition M (embed M base offset extent c).state
      (fun i => (embed M base offset extent c).cells i ((embed M base offset extent c).head i))).1 =
      (M.δ c.state (fun j => c.cells j (c.head j))).1 := by
  classical
  simp only [transition,show (embed M base offset extent c).state = c.state from rfl,if_neg live]
  rw [sim_decoded_scan]

private theorem sim_transition_work (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (live : c.state ≠ M.qHalt) (j : Fin M.k) :
    ((transition M (embed M base offset extent c).state
      (fun i => (embed M base offset extent c).cells i ((embed M base offset extent c).head i))).2 (workTape M j)) =
      (some (((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1,true),
        ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).2) := by
  classical
  simp only [transition,show (embed M base offset extent c).state = c.state from rfl,
    if_neg live,sim_decoded_scan,dif_pos (sim_work_ge M j),sim_inner_work,sim_embed_scan,protect]
  rfl

private theorem sim_transition_global (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (live : c.state ≠ M.qHalt)
    (i : Fin (M.k + 2)) (hi : i.val < 2) :
    ((transition M (embed M base offset extent c).state
      (fun i => (embed M base offset extent c).cells i ((embed M base offset extent c).head i))).2 i) =
      ((embed M base offset extent c).cells i ((embed M base offset extent c).head i),.stay) := by
  classical
  simp only [transition,show (embed M base offset extent c).state = c.state from rfl,
    if_neg live,dif_neg (by omega : ¬2 ≤ i.val)]

private theorem sim_update_bank (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (write : M.Sym)
    (near : c.head j ≤ extent j + 1) :
    Function.update ((embed M base offset extent c).cells (workTape M j))
      (offset j + c.head j) (some (write,true)) =
        fun p => if p < offset j then base.cells (workTape M j) p else
          some ((Function.update (c.cells j) (c.head j) write) (p - offset j),
            decide (p - offset j ≤ max (extent j) (c.head j))) := by
  classical
  funext p
  by_cases hp : p < offset j
  · rw [Function.update_of_ne (by omega : p ≠ offset j + c.head j),sim_embed_work_cells,if_pos hp,if_pos hp]
  · rw [if_neg hp]
    by_cases he : p = offset j + c.head j
    · subst p
      rw [Function.update_self]
      simp
    · rw [Function.update_of_ne he,sim_embed_work_cells,if_neg hp,
        Function.update_of_ne (by omega : p - offset j ≠ c.head j)]
      have hf : p - offset j ≤ extent j ↔ p - offset j ≤ max (extent j) (c.head j) := by omega
      simp only [hf]

private theorem sim_move_offset (M : MultitapeTM) (c : M.Cfg)
    (marker : ∀ j, c.cells j 0 = M.startSym) (j : Fin M.k) (offset : ℕ) :
    (match ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).2 with
      | .left => offset + c.head j - 1
      | .stay => offset + c.head j
      | .right => offset + c.head j + 1) =
    offset + (match ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).2 with
      | .left => c.head j - 1
      | .stay => c.head j
      | .right => c.head j + 1) := by
  cases hd : ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).2 with
  | left =>
      have hh : 0 < c.head j := by
        by_contra hn
        have hz : c.head j = 0 := by omega
        have hs := (M.start_preserved c.state (fun j => c.cells j (c.head j)) j
          (by rw [hz,marker j])).2
        exact hs hd
      simp only
      omega
  | stay => rfl
  | right => simp only; omega

/-- Marking a newly touched bank cell is part of the ordinary child write,
so execution still costs exactly one outer transition per child transition. -/
private theorem live_step_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (live : c.state ≠ M.qHalt)
    (marker : ∀ j, c.cells j 0 = M.startSym) (near : ∀ j, c.head j ≤ extent j + 1) :
    (machine M).step (embed M base offset extent c) =
      embed M base offset (fun j => max (extent j) (c.head j)) (M.step c) := by
  classical
  apply sim_cfg_ext
  · exact sim_transition_state M base offset extent c live
  · funext i
    by_cases hi : 2 ≤ i.val
    · let j := innerTape M i hi
      have he : workTape M j = i := sim_work_inner M i hi
      rw [←he]
      change Function.update ((embed M base offset extent c).cells (workTape M j))
        ((embed M base offset extent c).head (workTape M j))
        ((transition M (embed M base offset extent c).state
          (fun i => (embed M base offset extent c).cells i ((embed M base offset extent c).head i))).2 (workTape M j)).1 =
          (embed M base offset (fun j => max (extent j) (c.head j)) (M.step c)).cells (workTape M j)
      rw [sim_transition_work M base offset extent c live,sim_embed_work_head]
      funext p
      rw [sim_embed_work_cells]
      exact congrFun (sim_update_bank M base offset extent c j
        ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 (near j)) p
    · change Function.update ((embed M base offset extent c).cells i) ((embed M base offset extent c).head i)
        ((transition M (embed M base offset extent c).state
          (fun i => (embed M base offset extent c).cells i ((embed M base offset extent c).head i))).2 i).1 =
          (embed M base offset (fun j => max (extent j) (c.head j)) (M.step c)).cells i
      rw [sim_transition_global M base offset extent c live i (by omega),Function.update_eq_self]
      simp only [embed,dif_neg hi]
  · funext i
    by_cases hi : 2 ≤ i.val
    · let j := innerTape M i hi
      have he : workTape M j = i := sim_work_inner M i hi
      rw [←he]
      change (match ((transition M (embed M base offset extent c).state
          (fun i => (embed M base offset extent c).cells i ((embed M base offset extent c).head i))).2 (workTape M j)).2 with
        | .left => (embed M base offset extent c).head (workTape M j) - 1
        | .stay => (embed M base offset extent c).head (workTape M j)
        | .right => (embed M base offset extent c).head (workTape M j) + 1) =
          (embed M base offset (fun j => max (extent j) (c.head j)) (M.step c)).head (workTape M j)
      rw [sim_transition_work M base offset extent c live,sim_embed_work_head,sim_embed_work_head]
      exact sim_move_offset M c marker j (offset j)
    · change (match ((transition M (embed M base offset extent c).state
          (fun i => (embed M base offset extent c).cells i ((embed M base offset extent c).head i))).2 i).2 with
        | .left => (embed M base offset extent c).head i - 1
        | .stay => (embed M base offset extent c).head i
        | .right => (embed M base offset extent c).head i + 1) =
          (embed M base offset (fun j => max (extent j) (c.head j)) (M.step c)).head i
      rw [sim_transition_global M base offset extent c live i (by omega)]
      simp only [embed,dif_neg hi]

private theorem sim_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply sim_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem sim_markers_step (M : MultitapeTM) (c : M.Cfg)
    (marker : ∀ j, c.cells j 0 = M.startSym) : ∀ j, (M.step c).cells j 0 = M.startSym := by
  classical
  intro j
  change Function.update (c.cells j) (c.head j)
    ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 0 = _
  by_cases hh : c.head j = 0
  · rw [hh,Function.update_self]
    exact (M.start_preserved c.state (fun j => c.cells j (c.head j)) j (by rw [hh,marker j])).1
  · rw [Function.update_of_ne (by omega : 0 ≠ c.head j)]
    exact marker j

private theorem sim_markers_iterate (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) :
    ∀ j, (M.step^[T] c).cells j 0 = M.startSym := by
  induction T with
  | zero => exact marker
  | succ T ih => rw [Function.iterate_succ_apply']; exact sim_markers_step M _ ih

private theorem sim_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem sim_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [sim_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := sim_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem sim_near_iterate (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact sim_near_step M _ _ ih

/-- Both live and padded halted steps are matched, with the exact physical
visited-prefix flags and unchanged caller data. -/
private theorem step_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (marker : ∀ j, c.cells j 0 = M.startSym) (near : ∀ j, c.head j ≤ extent j + 1) :
    (machine M).step (embed M base offset extent c) =
      embed M base offset (nextExtent M c extent) (M.step c) := by
  classical
  by_cases halt : c.state = M.qHalt
  · rw [sim_halted_step (machine M) (embed M base offset extent c) halt,sim_halted_step M c halt]
    simp only [nextExtent,if_pos halt]
  · simpa only [nextExtent,if_neg halt] using live_step_correct M base offset extent c halt marker near

private theorem sim_iterate_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) (near : ∀ j, c.head j ≤ extent j + 1) :
    (machine M).step^[T] (embed M base offset extent c) =
      embed M base offset (extents M c extent T) (M.step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih,step_correct M base offset _ _
        (sim_markers_iterate M c T marker) (sim_near_iterate M c extent T near),Function.iterate_succ_apply']
      rfl

/-- Tracking is exact, with no extra execution transitions. The complete
caller frame and every bank prefix survive the run. Extents are proof-only
history and can later be located by scanning the finite visited flags. -/
private theorem simulate_run (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (marker : ∀ j, c.cells j 0 = M.startSym)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    let final := (machine M).step^[T] (embed M base offset extent c)
    final = embed M base offset (extents M c extent T) (M.step^[T] c) ∧
      (∀ i : Fin (M.k + 2), i.val < 2 → final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j : Fin M.k, ∀ p : ℕ, p < offset j →
        final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j : Fin M.k, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) := by
  dsimp only
  have h := sim_iterate_correct M base offset extent c T marker near
  refine ⟨h,?_,?_,?_⟩
  · intro i hi
    rw [h]
    simp [embed,show ¬2 ≤ i.val by omega]
  · intro j p hp
    rw [h,sim_embed_work_cells,if_pos hp]
  · intro j
    rw [h,sim_embed_work_cells,if_pos (by have := positive j; omega)]

/-- Extents can grow by at most one per transition; stopping at halt does
not create phantom visited cells from padded clocks. -/
private theorem extent_bound (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, extents M c extent T j ≤ extent j + T := by
  classical
  induction T with
  | zero => intro j; exact le_rfl
  | succ T ih =>
      intro j
      have hn := sim_near_iterate M c extent T near j
      have hi := ih j
      by_cases halt : (M.step^[T] c).state = M.qHalt
      · simp only [extents,nextExtent,if_pos halt]
        omega
      · simp only [extents,nextExtent,if_neg halt]
        change max (extents M c extent T j) ((M.step^[T] c).head j) ≤ extent j + (T + 1)
        omega

end IntMul.TrackedBankedSimulation



namespace IntMul.TrackedBankedSimulation

private theorem invariant_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem invariant_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply invariant_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem invariant_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [invariant_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact invariant_blank_tail_step M _ _ ih

private theorem invariant_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step c).cells j p = M.startSym ↔ p = 0 := by
  classical
  intro j p
  change Function.update (c.cells j) (c.head j)
    ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = M.startSym ↔ p = 0
  by_cases hp : p = c.head j
  · rw [hp,Function.update_self]
    by_cases hz : c.head j = 0
    · have hs := (M.start_preserved c.state (fun j => c.cells j (c.head j)) j ((unique j _).mpr hz)).1
      simp only [hs,hz,iff_true]
    · have hn := M.start_only_at_start c.state (fun j => c.cells j (c.head j)) j
        (mt (unique j _).mp hz)
      simp only [hn,hz,iff_false]
  · rw [Function.update_of_ne hp]
    exact unique j p

/-- Local markers stay unique in every actual child run, so a physical
rewind cannot stop at an interior payload cell. -/
private theorem unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact invariant_unique_marker_step M _ ih

end IntMul.TrackedBankedSimulation


open IntMul IntMul.TrackedBankedSimulation

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (marker : ∀ j, c.cells j 0 = M.startSym)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    let final := (machine M).step^[T] (embed M base offset extent c)
    final = embed M base offset (extents M c extent T) (M.step^[T] c) ∧
      (∀ i : Fin (M.k + 2), i.val < 2 → final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j : Fin M.k, ∀ p : ℕ, p < offset j →
        final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j : Fin M.k, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) :=
  IntMul.TrackedBankedSimulation.simulate_run M base offset extent positive c T marker near

#print axioms solution
