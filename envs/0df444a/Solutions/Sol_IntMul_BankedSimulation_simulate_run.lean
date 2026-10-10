-- Prove2me | solution 1 for IntMul.BankedSimulation.simulate_run
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T20:43:55.615044+00:00
-- url     : https://prove2.me/submissions/5e71e2a5-3251-455d-896c-478caa0edad5

import Definitions.Def_IntMul_BankedSimulation
import Mathlib.Tactic


namespace IntMul.BankedSimulation

private theorem cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem work_ge (M : MultitapeTM) (i : Fin M.k) :
    2 ≤ (workTape M i).val := by simp [workTape]

private theorem inner_work (M : MultitapeTM) (i : Fin M.k)
    (h : 2 ≤ (workTape M i).val) : innerTape M (workTape M i) h = i := by
  apply Fin.ext
  simp [innerTape,workTape]

private theorem work_inner (M : MultitapeTM) (i : Fin (M.k + 2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h) = i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem embed_work_head (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (embed M base offset c).head (workTape M j) = offset j + c.head j := by
  simp only [embed,dif_pos (work_ge M j),inner_work]

private theorem embed_work_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (embed M base offset c).cells (workTape M j) p =
      if p < offset j then base.cells (workTape M j) p else some (c.cells j (p - offset j)) := by
  simp only [embed,dif_pos (work_ge M j),inner_work]

private theorem embed_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    (embed M base offset c).cells (workTape M j) ((embed M base offset c).head (workTape M j)) =
      some (c.cells j (c.head j)) := by
  rw [embed_work_head,embed_work_cells]
  simp

private theorem decoded_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) :
    (fun j => decode M ((embed M base offset c).cells (workTape M j)
      ((embed M base offset c).head (workTape M j)))) = (fun j => c.cells j (c.head j)) := by
  funext j
  rw [embed_scan]
  rfl

private theorem transition_state (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) :
    ((machine M).δ (embed M base offset c).state
      (fun i => (embed M base offset c).cells i ((embed M base offset c).head i))).1 =
      (M.δ c.state (fun j => c.cells j (c.head j))).1 := by
  change (M.δ c.state _).1 = _
  rw [decoded_scan]

private theorem transition_work (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) :
    ((transition M (embed M base offset c).state
      (fun i => (embed M base offset c).cells i ((embed M base offset c).head i))).2 (workTape M j)) =
      (some ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1,
        ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).2) := by
  simp only [transition,decoded_scan,dif_pos (work_ge M j),inner_work,embed_scan,protect]
  rfl

private theorem transition_global (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) (i : Fin (M.k + 2)) (h : i.val < 2) :
    ((transition M (embed M base offset c).state
      (fun i => (embed M base offset c).cells i ((embed M base offset c).head i))).2 i) =
      ((embed M base offset c).cells i ((embed M base offset c).head i),.stay) := by
  change (if hi : 2 ≤ i.val then _ else _) = _
  rw [dif_neg (by omega)]

private theorem update_bank (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (write : M.Sym) :
    Function.update ((embed M base offset c).cells (workTape M j))
      (offset j + c.head j) (some write) =
        fun p => if p < offset j then base.cells (workTape M j) p else
          some ((Function.update (c.cells j) (c.head j) write) (p - offset j)) := by
  classical
  funext p
  by_cases hp : p < offset j
  · rw [Function.update_of_ne (by omega : p ≠ offset j + c.head j),embed_work_cells,if_pos hp,if_pos hp]
  · rw [if_neg hp]
    by_cases he : p = offset j + c.head j
    · subst p
      simp
    · rw [Function.update_of_ne he,embed_work_cells,if_neg hp,
        Function.update_of_ne (by omega : p - offset j ≠ c.head j)]

private theorem move_offset (M : MultitapeTM) (c : M.Cfg)
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
      simp only at ⊢
      omega
  | stay => rfl
  | right => simp only; omega

/-- One outer transition implements exactly one inner transition on prepared
work-tape banks. No seek, bank setup, or caller dispatch is supplied for free. -/
private theorem step_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg)
    (marker : ∀ j, c.cells j 0 = M.startSym) :
    (machine M).step (embed M base offset c) = embed M base offset (M.step c) := by
  classical
  apply cfg_ext
  · exact transition_state M base offset c
  · funext i
    by_cases hi : 2 ≤ i.val
    · let j := innerTape M i hi
      have he : workTape M j = i := work_inner M i hi
      rw [← he]
      change Function.update ((embed M base offset c).cells (workTape M j))
        ((embed M base offset c).head (workTape M j))
        ((transition M (embed M base offset c).state
          (fun i => (embed M base offset c).cells i ((embed M base offset c).head i))).2 (workTape M j)).1 =
          (embed M base offset (M.step c)).cells (workTape M j)
      rw [transition_work,embed_work_head]
      funext p
      rw [embed_work_cells]
      exact congrFun (update_bank M base offset c j
        ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1) p
    · change Function.update ((embed M base offset c).cells i) ((embed M base offset c).head i)
        ((transition M (embed M base offset c).state
          (fun i => (embed M base offset c).cells i ((embed M base offset c).head i))).2 i).1 =
          (embed M base offset (M.step c)).cells i
      rw [transition_global M base offset c i (by omega)]
      rw [Function.update_eq_self]
      simp only [embed,dif_neg hi]
  · funext i
    by_cases hi : 2 ≤ i.val
    · let j := innerTape M i hi
      have he : workTape M j = i := work_inner M i hi
      rw [← he]
      change (match ((transition M (embed M base offset c).state
          (fun i => (embed M base offset c).cells i ((embed M base offset c).head i))).2 (workTape M j)).2 with
        | .left => (embed M base offset c).head (workTape M j) - 1
        | .stay => (embed M base offset c).head (workTape M j)
        | .right => (embed M base offset c).head (workTape M j) + 1) =
          (embed M base offset (M.step c)).head (workTape M j)
      rw [transition_work,embed_work_head,embed_work_head]
      exact move_offset M c marker j (offset j)
    · change (match ((transition M (embed M base offset c).state
          (fun i => (embed M base offset c).cells i ((embed M base offset c).head i))).2 i).2 with
        | .left => (embed M base offset c).head i - 1
        | .stay => (embed M base offset c).head i
        | .right => (embed M base offset c).head i + 1) = (embed M base offset (M.step c)).head i
      rw [transition_global M base offset c i (by omega)]
      simp only [embed,dif_neg hi]

private theorem markers_step (M : MultitapeTM) (c : M.Cfg)
    (marker : ∀ j, c.cells j 0 = M.startSym) :
    ∀ j, (M.step c).cells j 0 = M.startSym := by
  classical
  intro j
  change Function.update (c.cells j) (c.head j)
    ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 0 = _
  by_cases hh : c.head j = 0
  · rw [hh,Function.update_self]
    exact (M.start_preserved c.state (fun j => c.cells j (c.head j)) j
      (by rw [hh,marker j])).1
  · rw [Function.update_of_ne (by omega : 0 ≠ c.head j)]
    exact marker j

private theorem markers_iterate (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) :
    ∀ j, (M.step^[T] c).cells j 0 = M.startSym := by
  induction T with
  | zero => exact marker
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact markers_step M _ ih

private theorem iterate_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) (T : ℕ)
    (marker : ∀ j, c.cells j 0 = M.startSym) :
    (machine M).step^[T] (embed M base offset c) = embed M base offset (M.step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih,
        step_correct M base offset _ (markers_iterate M c T marker),Function.iterate_succ_apply']

/-- Exact execution in prepared interior banks, with the complete outer
input/output frame and every prefix cell retained. Offsets are positive and
absent from the transition table; preparing banks, seeking heads, and returning
to a caller must be paid for by the caller's separate physical trace. -/
private theorem simulate_run (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (marker : ∀ j, c.cells j 0 = M.startSym) :
    let final := (machine M).step^[T] (embed M base offset c)
    final = embed M base offset (M.step^[T] c) ∧
      (∀ i : Fin (M.k + 2), i.val < 2 →
        final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j : Fin M.k, ∀ p : ℕ, p < offset j →
        final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j : Fin M.k, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) := by
  dsimp only
  have h := iterate_correct M base offset c T marker
  refine ⟨h, ?_, ?_, ?_⟩
  · intro i hi
    rw [h]
    simp [embed,show ¬2 ≤ i.val by omega]
  · intro j p hp
    rw [h,embed_work_cells,if_pos hp]
  · intro j
    rw [h,embed_work_cells,if_pos (by have := positive j; omega)]

end IntMul.BankedSimulation


open IntMul IntMul.BankedSimulation

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (marker : ∀ j, c.cells j 0 = M.startSym) :
    let final := (machine M).step^[T] (embed M base offset c)
    final = embed M base offset (M.step^[T] c) ∧
      (∀ i : Fin (M.k + 2), i.val < 2 →
        final.cells i = base.cells i ∧ final.head i = base.head i) ∧
      (∀ j : Fin M.k, ∀ p : ℕ, p < offset j →
        final.cells (workTape M j) p = base.cells (workTape M j) p) ∧
      (∀ j : Fin M.k, final.cells (workTape M j) 0 = base.cells (workTape M j) 0) :=
  IntMul.BankedSimulation.simulate_run M base offset positive c T marker

#print axioms solution
