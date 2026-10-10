-- Prove2me | solution 1 for IntMul.TrackedReturnCall.call_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T22:42:41.353393+00:00
-- url     : https://prove2.me/submissions/84037701-c30e-4a71-8099-49352be9a84d

import Definitions.Def_IntMul_TrackedReturnCall
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_TrackedOutputReturn_output_correct
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)


namespace IntMul.TrackedOutputReturn

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

private theorem buffer_boundary (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    bufferTape M base sigma w sigma = some (M.startSym,true) := by simp [bufferTape]

private theorem buffer_payload (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List Bool) (p : ℕ) :
    bufferTape M base sigma w (sigma + p + 1) =
      some ((w.map M.bitSym).getD p M.blank,decide (p < w.length)) := by
  simp only [bufferTape,if_neg (by omega : ¬sigma + p + 1 < sigma),
    if_neg (by omega : sigma + p + 1 ≠ sigma),
    show sigma + p + 1 - sigma - 1 = p by omega]

private theorem buffer_append (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List Bool) (b : Bool) :
    Function.update (bufferTape M base sigma w) (sigma + w.length + 1) (some (M.bitSym b,true)) =
      bufferTape M base sigma (w ++ [b]) := by
  classical
  funext p
  by_cases hp : p < sigma
  · rw [Function.update_of_ne (by omega : p ≠ sigma + w.length + 1)]
    simp only [bufferTape,if_pos hp]
  · by_cases he : p = sigma + w.length + 1
    · subst p
      rw [Function.update_self,buffer_payload]
      simp
    · rw [Function.update_of_ne he]
      by_cases hs : p = sigma
      · subst p
        rw [buffer_boundary,buffer_boundary]
      · have hg : sigma < p := by omega
        have hn : p = sigma + (p - sigma - 1) + 1 := by omega
        rw [hn,buffer_payload,buffer_payload]
        have hq : p - sigma - 1 ≠ w.length := by omega
        simp only [List.map_append,List.map_singleton,List.length_append,List.length_singleton]
        by_cases hl : p - sigma - 1 < w.length
        · rw [List.getD_append _ _ _ _ (by simpa using hl)]
          simp only [hl,show p - sigma - 1 < w.length + 1 by omega,decide_true]
        · have hb : w.length ≤ p - sigma - 1 := by omega
          rw [List.getD_eq_default _ _ (by simpa using hb),
            List.getD_append_right _ _ _ _ (by simpa using hb),
            List.getD_eq_default _ _ (by simp; omega)]
          simp only [hl,show ¬p - sigma - 1 < w.length + 1 by omega,decide_false]

private theorem buffer_next_blank (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    bufferTape M base sigma w (sigma + w.length + 1) = some (M.blank,false) := by
  rw [buffer_payload]
  simp

private theorem payload_not_marker (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    (w.map M.bitSym).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map]
    cases w[p] <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true] <;> aesop
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    aesop

private theorem buffer_marker_iff (M : MultitapeTM) (base : ℕ → Sym M)
    (sigma : ℕ) (w : List Bool) (p : ℕ) :
    bufferTape M base sigma w (sigma + p) = some (M.startSym,true) ↔ p = 0 := by
  cases p with
  | zero => simp only [Nat.add_zero,buffer_boundary,iff_true]
  | succ p =>
      rw [show sigma + (p + 1) = sigma + p + 1 by omega,buffer_payload]
      constructor
      · intro h
        exact False.elim (payload_not_marker M w p (congrArg Prod.fst (Option.some.inj h)))
      · intro h
        omega

private theorem buffer_not_none (M : MultitapeTM) (base : ℕ → Sym M)
    (sigma : ℕ) (w : List Bool) (p : ℕ) :
    bufferTape M base sigma w (sigma + p) ≠ none := by
  simp only [bufferTape,if_neg (by omega : ¬sigma + p < sigma)]
  split <;> exact Option.some_ne_none _

private theorem tracked_scan (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j + p) =
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,dif_pos (work_ge M j),inner_work,
    if_neg (by omega : ¬offset j + p < offset j),Nat.add_sub_cancel_left]

private theorem tracked_marker_iff (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j + p) =
      some (M.startSym,true) ↔ p = 0 := by
  rw [tracked_scan]
  constructor
  · intro h
    exact (unique j p).mp (congrArg Prod.fst (Option.some.inj h))
  · intro h
    simp only [h,(unique j 0).mpr rfl,Nat.zero_le,decide_true]

end IntMul.TrackedOutputReturn


namespace IntMul.TrackedOutputReturn
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)
/-- Every child-bank cell, including its finite visited flag, is unchanged;
the caller input is unchanged, and the output buffer has the returned word. -/
private theorem call_returned_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (a b : ℕ) :
    (∀ i : Fin (M.k + 2), i.val ≠ 1 →
      (finalFrame M base sigma offset extent c w).cells i =
        (returnFrame M base sigma offset extent c a b).cells i) ∧
      (finalFrame M base sigma offset extent c w).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
        bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w := by
  constructor
  · intro i hi
    simp only [finalFrame,copyFrame,returnFrame,if_neg hi]
    rfl
  · simp [finalFrame,copyFrame]

/-- Only the two copy heads move; all other heads retain their original
child/caller positions. Work prefixes remain outside every local seek. -/
private theorem call_returned_heads (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (finalFrame M base sigma offset extent c w).head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma + w.length + 1 ∧
      (∀ j, (finalFrame M base sigma offset extent c w).head (workTape M j) =
        offset j + (if j = M.outTape then w.length + 1 else c.head j)) := by
  constructor
  · simp [finalFrame,copyFrame]
  · intro j
    have hn : (workTape M j).val ≠ 1 := by simp [workTape]
    have ho : (workTape M j).val = 3 ↔ j = M.outTape := by
      simp only [workTape,MultitapeTM.outTape,Fin.ext_iff]
      omega
    by_cases hj : j = M.outTape
    · subst j
      simp [finalFrame,copyFrame,workTape,MultitapeTM.outTape,Nat.add_assoc]
    · have hv : (workTape M j).val ≠ 3 := mt ho.mp hj
      simp only [finalFrame,copyFrame,if_neg hn,if_neg hv,if_neg hj,
        TrackedBankedSimulation.embed,dif_pos (work_ge M j),inner_work]


end IntMul.TrackedOutputReturn


namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem space_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem space_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply space_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem space_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [space_halted_step M c halt]
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
      exact space_blank_tail_step M _ _ ih

private theorem space_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
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
  | succ T ih => rw [Function.iterate_succ_apply']; exact space_unique_marker_step M _ ih

private theorem space_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem space_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [space_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := space_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact space_near_step M _ _ ih


end IntMul.TrackedBankedSpace




namespace IntMul.TrackedReturnCall

private theorem program_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private noncomputable def startReturn (M : MultitapeTM) (c : (TrackedBankedSimulation.machine M).Cfg) :
    (TrackedOutputReturn.machine M).Cfg where
  state := .rewind
  cells := c.cells
  head := c.head

private noncomputable def startCleanup (M : MultitapeTM) (c : (TrackedOutputReturn.machine M).Cfg) :
    (TrackedBankCleanup.machine M).Cfg where
  state := .rewind
  cells := c.cells
  head := c.head

private theorem program_lift_child_step (M : MultitapeTM) (c : (TrackedBankedSimulation.machine M).Cfg)
    (live : c.state ≠ M.qHalt) :
    (machine M).step (liftChild M c) = liftChild M ((TrackedBankedSimulation.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftChild,transition,live]
  · simp [MultitapeTM.step,liftChild,transition,live]
  · simp [MultitapeTM.step,liftChild,transition,live]

private theorem program_lift_return_step (M : MultitapeTM) (c : (TrackedOutputReturn.machine M).Cfg)
    (live : c.state ≠ .halt) :
    (machine M).step (liftReturn M c) = liftReturn M ((TrackedOutputReturn.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftReturn,transition,live]
  · simp [MultitapeTM.step,liftReturn,transition,live]
  · simp [MultitapeTM.step,liftReturn,transition,live]

private theorem lift_cleanup_step (M : MultitapeTM) (c : (TrackedBankCleanup.machine M).Cfg) :
    (machine M).step (liftCleanup M c) = liftCleanup M ((TrackedBankCleanup.machine M).step c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftCleanup,transition]
  · simp [MultitapeTM.step,liftCleanup,transition]
  · simp [MultitapeTM.step,liftCleanup,transition]

private theorem program_lift_child_iterate (M : MultitapeTM) (c : (TrackedBankedSimulation.machine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((TrackedBankedSimulation.machine M).step^[s] c).state ≠ M.qHalt) :
    (machine M).step^[T] (liftChild M c) = liftChild M ((TrackedBankedSimulation.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_child_step M _ (live T (by omega)),Function.iterate_succ_apply']

private theorem program_lift_return_iterate (M : MultitapeTM) (c : (TrackedOutputReturn.machine M).Cfg) (T : ℕ)
    (live : ∀ s, s < T → ((TrackedOutputReturn.machine M).step^[s] c).state ≠ .halt) :
    (machine M).step^[T] (liftReturn M c) = liftReturn M ((TrackedOutputReturn.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [Function.iterate_succ_apply',ih (by intro s hs; exact live s (by omega)),
        program_lift_return_step M _ (live T (by omega)),Function.iterate_succ_apply']

private theorem lift_cleanup_iterate (M : MultitapeTM) (c : (TrackedBankCleanup.machine M).Cfg) (T : ℕ) :
    (machine M).step^[T] (liftCleanup M c) = liftCleanup M ((TrackedBankCleanup.machine M).step^[T] c) := by
  induction T with
  | zero => rfl
  | succ T ih => rw [Function.iterate_succ_apply',ih,lift_cleanup_step,Function.iterate_succ_apply']

private theorem program_child_dispatch (M : MultitapeTM) (c : (TrackedBankedSimulation.machine M).Cfg)
    (halt : c.state = M.qHalt) :
    (machine M).step (liftChild M c) = liftReturn M (startReturn M c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftChild,liftReturn,startReturn,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftChild,liftReturn,startReturn,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftChild,liftReturn,startReturn,transition,halt]

private theorem program_return_dispatch (M : MultitapeTM) (c : (TrackedOutputReturn.machine M).Cfg)
    (halt : c.state = .halt) :
    (machine M).step (liftReturn M c) = liftCleanup M (startCleanup M c) := by
  classical
  apply program_cfg_ext
  · simp [MultitapeTM.step,liftReturn,liftCleanup,startCleanup,transition,halt]
  · funext i
    simp only [MultitapeTM.step,liftReturn,liftCleanup,startCleanup,transition,if_pos halt]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,liftReturn,liftCleanup,startCleanup,transition,halt]

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

/-- Child execution stops at its first halt; the full terminal flags and
cells are those of the supplied padded clock, then one dispatch is charged. -/
private theorem run_child_to_return (M : MultitapeTM) (c : (TrackedBankedSimulation.machine M).Cfg) (T : ℕ)
    (halt : ((TrackedBankedSimulation.machine M).step^[T] c).state = M.qHalt) :
    ∃ t, t ≤ T + 1 ∧ (machine M).step^[t] (liftChild M c) =
      liftReturn M (startReturn M ((TrackedBankedSimulation.machine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := program_first_halt (TrackedBankedSimulation.machine M) c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',program_lift_child_iterate M c t hn,he,program_child_dispatch M _ halt]

/-- Output return likewise dispatches at its first halt, preserving its
entire returned buffer and child banks, including a charged switch step. -/
private theorem run_return_to_cleanup (M : MultitapeTM) (c : (TrackedOutputReturn.machine M).Cfg) (T : ℕ)
    (halt : ((TrackedOutputReturn.machine M).step^[T] c).state = .halt) :
    ∃ t, t ≤ T + 1 ∧ (machine M).step^[t] (liftReturn M c) =
      liftCleanup M (startCleanup M ((TrackedOutputReturn.machine M).step^[T] c)) := by
  obtain ⟨t,ht,he,hn⟩ := program_first_halt (TrackedOutputReturn.machine M) c T halt
  refine ⟨t + 1,by omega,?_⟩
  rw [Function.iterate_succ_apply',program_lift_return_iterate M c t hn,he,program_return_dispatch M _ halt]

end IntMul.TrackedReturnCall



namespace IntMul.TrackedReturnCall

open IntMul.BankedSimulation (workTape innerTape)

private theorem frame_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

/-- The charged first child dispatch changes only finite control; its full
terminal tracked banks are exactly the output-return starting frame. -/
private theorem return_ready (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma a : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) :
    startReturn M (TrackedBankedSimulation.embed M (childBase M base sigma a) offset extent c) =
      TrackedOutputReturn.returnFrame M (returnBase M base) sigma offset extent c a (c.head M.outTape) := by
  apply frame_cfg_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i.val = 1
    · simp only [startReturn,TrackedOutputReturn.returnFrame,if_pos hi,
        TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),childBase,
        TrackedOutputReturn.callerBase,if_pos hi]
    · by_cases ho : i.val = 3
      · have hg : 2 ≤ i.val := by omega
        have he : innerTape M i hg = M.outTape := by
          apply Fin.ext
          simp only [innerTape,MultitapeTM.outTape]
          omega
        simp only [startReturn,TrackedOutputReturn.returnFrame,if_neg hi,if_pos ho,
          TrackedBankedSimulation.embed,dif_pos hg,he]
      · simp only [startReturn,TrackedOutputReturn.returnFrame,if_neg hi,if_neg ho]
        rfl

/-- After copying, all tracked bank cells remain intact. Only the output
work head has changed, so the cleanup frame needs no uncharged preparation. -/
private theorem cleanup_ready (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    cleanupBase M base sigma offset extent c w =
      TrackedBankCleanup.rewindFrame M (cleanupBase M base sigma offset extent c w)
        offset extent c (postCopyHeads M c w) := by
  apply frame_cfg_ext
  · rfl
  · funext i p
    by_cases hi : 2 ≤ i.val
    · have hn : i.val ≠ 1 := by omega
      simp [TrackedBankCleanup.rewindFrame,TrackedBankedSimulation.embed,
        TrackedBankCleanup.parentBase,hi,cleanupBase,TrackedOutputReturn.finalFrame,
        TrackedOutputReturn.copyFrame,hn]
      omega
    · simp only [TrackedBankCleanup.rewindFrame,TrackedBankedSimulation.embed,
        TrackedBankCleanup.parentBase,dif_neg hi]
  · funext i
    by_cases hi : 2 ≤ i.val
    · have h := (TrackedOutputReturn.call_returned_heads M (returnBase M base) sigma offset extent c w).2
        (innerTape M i hi)
      rw [TrackedOutputReturn.work_inner] at h
      simp only [cleanupBase,TrackedBankCleanup.rewindFrame,dif_pos hi,postCopyHeads]
      exact h
    · simp only [TrackedBankCleanup.rewindFrame,dif_neg hi]

private theorem cleanup_start_eq (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    startCleanup M (TrackedOutputReturn.finalFrame M (returnBase M base) sigma offset extent c w) =
      cleanupBase M base sigma offset extent c w := rfl

/-- The final cleanup preserves the returned canonical buffer and its head. -/
private theorem final_buffer (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (finalFrame M base sigma offset extent c w).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedOutputReturn.bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      (finalFrame M base sigma offset extent c w).head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma + w.length + 1 := by
  simp [finalFrame,liftCleanup,TrackedBankCleanup.finalFrame,cleanupBase,
    TrackedOutputReturn.finalFrame,TrackedOutputReturn.copyFrame,returnBase]

/-- Every child bank is returned as a fresh blank suffix at its old offset. -/
private theorem final_fresh_banks (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (∀ j p, offset j ≤ p → (finalFrame M base sigma offset extent c w).cells (workTape M j) p =
      some (M.blank,false)) ∧
      (∀ j, (finalFrame M base sigma offset extent c w).head (workTape M j) = offset j) := by
  constructor
  · intro j p hp
    simp [finalFrame,liftCleanup,TrackedBankCleanup.finalFrame,TrackedOutputReturn.work_ge,
      TrackedOutputReturn.inner_work,TrackedBankCleanup.freshTape,show ¬p < offset j by omega]
  · intro j
    simp [finalFrame,liftCleanup,TrackedBankCleanup.finalFrame,TrackedOutputReturn.work_ge,
      TrackedOutputReturn.inner_work]

end IntMul.TrackedReturnCall



namespace IntMul.TrackedReturnCall

open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)

/-- One finite caller executes a prepared child, returns its output, clears
all visited banks and parks them for reuse. Both stage switches are charged. -/
private theorem call_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma a : ℕ) (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (halt : (M.step^[T] c).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] c).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let d := M.step^[T] c
    let e := extents M c extent T
    ∃ t, t ≤ T + max a (d.head M.outTape) + w.length + span M (postCopyHeads M d w) + 2 * span M e + 7 ∧
      (machine M).step^[t] (initialFrame M base sigma a offset extent c) =
        finalFrame M base sigma offset e d w := by
  dsimp only
  have sim := (TrackedBankedSimulation.simulate_run M (childBase M base sigma a) offset extent
    positive c T (by intro j; exact (unique j 0).mpr rfl) near).1
  have hh : ((TrackedBankedSimulation.machine M).step^[T]
      (TrackedBankedSimulation.embed M (childBase M base sigma a) offset extent c)).state = M.qHalt := by
    rw [sim]
    exact halt
  obtain ⟨p,hp,hprun⟩ := run_child_to_return M
    (TrackedBankedSimulation.embed M (childBase M base sigma a) offset extent c) T hh
  rw [sim,return_ready M base sigma a offset _ _] at hprun
  have ret := TrackedOutputReturn.output_correct M (returnBase M base) sigma offset
    (extents M c extent T) (M.step^[T] c) w out a ((M.step^[T] c).head M.outTape)
  have hrhalt : ((TrackedOutputReturn.machine M).step^[max a ((M.step^[T] c).head M.outTape) + w.length + 2]
      (TrackedOutputReturn.returnFrame M (returnBase M base) sigma offset (extents M c extent T)
        (M.step^[T] c) a ((M.step^[T] c).head M.outTape))).state = .halt := by
    rw [ret]
    rfl
  obtain ⟨q,hq,hqrun⟩ := run_return_to_cleanup M
    (TrackedOutputReturn.returnFrame M (returnBase M base) sigma offset (extents M c extent T)
      (M.step^[T] c) a ((M.step^[T] c).head M.outTape))
    (max a ((M.step^[T] c).head M.outTape) + w.length + 2) hrhalt
  rw [ret,cleanup_start_eq] at hqrun
  have clean := (TrackedBankCleanup.cleanup_correct M
    (cleanupBase M base sigma offset (extents M c extent T) (M.step^[T] c) w)
    offset (extents M c extent T) positive (M.step^[T] c) (postCopyHeads M (M.step^[T] c) w)
    (TrackedBankedSpace.unique_marker_run M c T unique)
    (TrackedBankedSpace.blank_tail_run M c extent T tail)).1
  have hc : (machine M).step^[span M (postCopyHeads M (M.step^[T] c) w) + 2 * span M (extents M c extent T) + 3]
      (liftCleanup M (cleanupBase M base sigma offset (extents M c extent T) (M.step^[T] c) w)) =
      finalFrame M base sigma offset (extents M c extent T) (M.step^[T] c) w := by
    rw [lift_cleanup_iterate]
    have ready := cleanup_ready M base sigma offset (extents M c extent T) (M.step^[T] c) w
    rw [←ready] at clean
    rw [clean]
    rfl
  refine ⟨(span M (postCopyHeads M (M.step^[T] c) w) + 2 * span M (extents M c extent T) + 3) + (q + p),by omega,?_⟩
  have hpq : (machine M).step^[q + p] (initialFrame M base sigma a offset extent c) =
      liftCleanup M (cleanupBase M base sigma offset (extents M c extent T) (M.step^[T] c) w) := by
    change (machine M).step^[q + p]
      (liftChild M (TrackedBankedSimulation.embed M (childBase M base sigma a) offset extent c)) = _
    rw [Function.iterate_add_apply,hprun,hqrun]
  rw [Function.iterate_add_apply,hpq,hc]

private theorem complete_bit_ne_blank (M : MultitapeTM) (b : Bool) : M.bitSym b ≠ M.blank := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  cases b <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true] <;> aesop

/-- Blank-tail initialization forces every nonblank output bit to lie inside
the tracked extent; output copying therefore does not create a farther head. -/
private theorem output_length_le_extent (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym))
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) : w.length ≤ extent M.outTape := by
  by_contra h
  have hn : 0 < w.length := by omega
  have hj : w.length - 1 < w.length := by omega
  have hb := tail M.outTape w.length (by omega)
  have hv : c.cells M.outTape w.length = M.bitSym w[w.length - 1] := by
    rw [out]
    conv_lhs => rw [show w.length = (w.length - 1) + 1 by omega]
    change (w.map M.bitSym).getD (w.length - 1) M.blank = _
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  exact complete_bit_ne_blank M _ (hv.symm.trans hb)

private theorem post_copy_near (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (w : List Bool) (near : ∀ j, c.head j ≤ extent j + 1)
    (output_extent : w.length ≤ extent M.outTape) :
    ∀ j, postCopyHeads M c w j ≤ extent j + 1 := by
  classical
  intro j
  by_cases hj : j = M.outTape
  · subst j
    simp only [postCopyHeads,if_true]
    omega
  · simp only [postCopyHeads,if_neg hj]
    exact near j

private theorem complete_space_le (M : MultitapeTM) (f : Fin M.k → ℕ) (j : Fin M.k) :
    f j ≤ span M f := Finset.le_sup (Finset.mem_univ j)

private theorem complete_space_sup_le (M : MultitapeTM) (f : Fin M.k → ℕ) (n : ℕ)
    (h : ∀ j, f j ≤ n) : span M f ≤ n := Finset.sup_le (by intro j _; exact h j)

/-- The child-time coefficient is one. If the prepared buffer-head distance
is within the final tracked workspace, the entire call costs T+5*space+9. -/
private theorem call_workspace_bounded (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma a : ℕ) (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (halt : (M.step^[T] c).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] c).cells M.outTape = M.tapeOf (w.map M.bitSym))
    (buffer_near : a ≤ span M (extents M c extent T) + 1) :
    ∃ t, t ≤ T + 5 * span M (extents M c extent T) + 9 ∧
      (machine M).step^[t] (initialFrame M base sigma a offset extent c) =
        finalFrame M base sigma offset (extents M c extent T) (M.step^[T] c) w := by
  obtain ⟨t,ht,hr⟩ := call_correct M base sigma a offset extent positive c T unique tail near halt w out
  have he := TrackedBankedSpace.heads_near_run M c extent T near
  have htail := TrackedBankedSpace.blank_tail_run M c extent T tail
  have hw := output_length_le_extent M (M.step^[T] c) (extents M c extent T) w out htail
  have hout := complete_space_le M (extents M c extent T) M.outTape
  have hh := he M.outTape
  have hpost := complete_space_sup_le M (postCopyHeads M (M.step^[T] c) w) (span M (extents M c extent T) + 1) (by
    intro j
    have hj := post_copy_near M (M.step^[T] c) (extents M c extent T) w he hw j
    have hs := complete_space_le M (extents M c extent T) j
    exact show postCopyHeads M (M.step^[T] c) w j ≤ span M (extents M c extent T) + 1 by omega)
  exact ⟨t,by omega,hr⟩

end IntMul.TrackedReturnCall


open IntMul IntMul.TrackedReturnCall

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma a : ℕ) (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (halt : (M.step^[T] c).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] c).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let d := M.step^[T] c
    let e := extents M c extent T
    ∃ t, t ≤ T + max a (d.head M.outTape) + w.length + span M (postCopyHeads M d w) + 2 * span M e + 7 ∧
      (machine M).step^[t] (initialFrame M base sigma a offset extent c) =
        finalFrame M base sigma offset e d w :=
  IntMul.TrackedReturnCall.call_correct M base sigma a offset extent positive c T unique tail near halt w out

#print axioms solution
