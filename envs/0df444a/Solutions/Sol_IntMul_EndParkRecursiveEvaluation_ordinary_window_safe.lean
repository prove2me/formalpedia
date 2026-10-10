-- Prove2me | solution 1 for IntMul.EndParkRecursiveEvaluation.ordinary_window_safe
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T05:49:44.603996+00:00
-- url     : https://prove2.me/submissions/09ec2d7c-385c-448e-a994-d9496343b909

import Definitions.Def_IntMul_EndParkRecursiveRelocation
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Tactic

namespace IntMul.EndParkRecursiveRelocation

open IntMul.EndParkRecursiveScheduler

/-- Flat view of every physical body cell, including all retained prefixes. -/
private theorem ordinary_window_internal_body_cells (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (i : Fin (M.k+3)) (p : ℕ) :
    (bodyFrame M n request resume base rho sigma offset extent c v).cells i p=
      if h : i.val < M.k+2 then
        if hw : 2≤ i.val then
          if p< offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw) then base.cells i p
          else some (c.cells (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)
            (p-offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)),
            decide (p-offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)≤
              extent (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)))
        else if i.val=1 then TrackedOutputReturn.bufferTape M (base.cells i) sigma v p
        else base.cells i p
      else FiniteContinuationStack.freshTape M (base.cells i) rho p := by
  classical
  by_cases hi : i.val< M.k+2
  · by_cases hw : 2≤ i.val
    · have hnot : i.val≠1 := by omega
      simp only [bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
        TrackedBankedSimulation.embed,FixedTapeExtension.innerTape,dif_pos hw,
        parentBase,if_neg hnot,FixedTapeExtension.oldTape]
    · by_cases hb : i.val=1
      · simp only [bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
          TrackedBankedSimulation.embed,FixedTapeExtension.innerTape,dif_neg hw,
          parentBase,if_pos hb,FixedTapeExtension.oldTape]
      · simp only [bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
          TrackedBankedSimulation.embed,FixedTapeExtension.innerTape,dif_neg hw,
          parentBase,if_neg hb,FixedTapeExtension.oldTape]
  · have hstack : i=stackTape M := by
      apply Fin.ext
      have := i.isLt
      simp only [stackTape,FiniteContinuationStack.stackTape]
      omega
    simp only [bodyFrame,liftBody,FixedTapeExtension.embed,dif_neg hi,
      stackBase,if_pos hstack]

/-- Flat view of every physical body head. -/
private theorem ordinary_window_internal_body_heads (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (i : Fin (M.k+3)) :
    (bodyFrame M n request resume base rho sigma offset extent c v).head i=
      if h : i.val< M.k+2 then
        if hw : 2≤ i.val then offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)+
          c.head (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)
        else if i.val=1 then sigma+v.length+1 else base.head i
      else rho := by
  classical
  by_cases hi : i.val< M.k+2
  · by_cases hw : 2≤ i.val
    · simp only [bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
        TrackedBankedSimulation.embed,FixedTapeExtension.innerTape,dif_pos hw]
    · by_cases hb : i.val=1
      · simp only [bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
          TrackedBankedSimulation.embed,FixedTapeExtension.innerTape,dif_neg hw,
          parentBase,if_pos hb]
      · simp only [bodyFrame,liftBody,FixedTapeExtension.embed,dif_pos hi,
          TrackedBankedSimulation.embed,FixedTapeExtension.innerTape,dif_neg hw,
          parentBase,if_neg hb,FixedTapeExtension.oldTape]
  · have hstack : i=stackTape M := by
      apply Fin.ext
      have := i.isLt
      simp only [stackTape,FiniteContinuationStack.stackTape]
      omega
    simp only [bodyFrame,liftBody,FixedTapeExtension.embed,dif_neg hi,
      stackBase,if_pos hstack]

end IntMul.EndParkRecursiveRelocation



namespace IntMul.TrackedBankedSpace

open IntMul.TrackedBankedSimulation (nextExtent extents)

private theorem ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_cfg_ext (M : MultitapeTM) (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_halted_step (M : MultitapeTM) (c : M.Cfg) (halt : c.state = M.qHalt) : M.step c = c := by
  apply ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_cfg_ext
  · simp [MultitapeTM.step,halt,M.halt_fixed]
  · funext j
    simp only [MultitapeTM.step,halt,M.halt_fixed]
    exact Function.update_eq_self _ _
  · simp [MultitapeTM.step,halt,M.halt_fixed]

private theorem ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_blank_tail_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, nextExtent M c extent j < p → (M.step c).cells j p = M.blank := by
  classical
  intro j p hp
  by_cases halt : c.state = M.qHalt
  · rw [ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simp only [nextExtent,if_pos halt] at hp
    exact tail j p hp
  · simp only [nextExtent,if_neg halt] at hp
    change Function.update (c.cells j) (c.head j)
      ((M.δ c.state (fun j => c.cells j (c.head j))).2 j).1 p = _
    rw [Function.update_of_ne (by omega : p ≠ c.head j)]
    exact tail j p (by omega)

/-- Blank tails remain blank beyond the tracked extent. This is the explicit
precondition needed to turn a false visited flag into a fresh-bank boundary. -/
private theorem ordinary_window_internal_blank_tail_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    ∀ j p, extents M c extent T j < p → (M.step^[T] c).cells j p = M.blank := by
  induction T with
  | zero => exact tail
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_blank_tail_step M _ _ ih

private theorem ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_unique_marker_step (M : MultitapeTM) (c : M.Cfg)
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
private theorem ordinary_window_internal_unique_marker_run (M : MultitapeTM) (c : M.Cfg) (T : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    ∀ j p, (M.step^[T] c).cells j p = M.startSym ↔ p = 0 := by
  induction T with
  | zero => exact unique
  | succ T ih => rw [Function.iterate_succ_apply']; exact ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_unique_marker_step M _ ih

private theorem ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_head_step_bound (M : MultitapeTM) (c : M.Cfg) (j : Fin M.k) :
    (M.step c).head j ≤ c.head j + 1 := by
  simp only [MultitapeTM.step]
  split <;> omega

private theorem ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_near_step (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step c).head j ≤ nextExtent M c extent j + 1 := by
  classical
  intro j
  by_cases halt : c.state = M.qHalt
  · rw [ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_halted_step M c halt]
    simpa only [nextExtent,if_pos halt] using near j
  · simp only [nextExtent,if_neg halt]
    have hh := ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_head_step_bound M c j
    have hm := Nat.le_max_right (extent j) (c.head j)
    omega

private theorem ordinary_window_internal_heads_near_run (M : MultitapeTM) (c : M.Cfg) (extent : Fin M.k → ℕ) (T : ℕ)
    (near : ∀ j, c.head j ≤ extent j + 1) :
    ∀ j, (M.step^[T] c).head j ≤ extents M c extent T j + 1 := by
  induction T with
  | zero => exact near
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      exact ordinary_window_internal_solutions_intmultrackedbankedspaceinvariants_near_step M _ _ ih


end IntMul.TrackedBankedSpace




namespace IntMul.EndParkRecursiveScheduler

private theorem ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c=d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) (live : c.state≠(bodyMachine M).qHalt)
    (no_request : request c.state=none) :
    (machine M n request resume).step (liftBody M n request resume c)=
      liftBody M n request resume ((bodyMachine M).step c) := by
  have ht : transition M n request resume (.body c.state) (fun i => c.cells i (c.head i))=
      (let r := (bodyMachine M).δ c.state (fun i => c.cells i (c.head i)); (.body r.1,r.2)) := by
    simp only [transition,FlatRecursiveScheduler.transition,reduceCtorEq,if_false,if_neg live,no_request]
  apply ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_cfg_ext
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]
  · simp only [MultitapeTM.step,liftBody,ht]


end IntMul.EndParkRecursiveScheduler


namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankedSimulation (nextExtent extents)

private noncomputable def ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_evalBodyView (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (bodyMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c)

private theorem ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_ordinary_body_step (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1≤ offset j)
    (c : M.Cfg) (v : List Bool)
    (marker : ∀ j, c.cells j 0=M.startSym) (near : ∀ j, c.head j≤ extent j+1)
    (live : c.state≠M.qHalt) (ordinary : request c.state=none) :
    (machine M n request resume).step (bodyFrame M n request resume base rho sigma offset extent c v)=
      bodyFrame M n request resume base rho sigma offset (nextExtent M c extent) (M.step c) v := by
  have h := (FixedTapeExtension.simulate_run (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c) 1).1
  rw [(TrackedBankedSimulation.simulate_run M (parentBase M n request resume base sigma v)
    offset extent positive c 1 marker near).1] at h
  simp only [Function.iterate_one,extents,Function.iterate_zero,Function.id_def] at h
  change (machine M n request resume).step (liftBody M n request resume
    (ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_evalBodyView M n request resume base rho sigma offset extent c v))=_
  rw [ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_body_step M n request resume _ live ordinary]
  exact congrArg (liftBody M n request resume) h

end IntMul.EndParkRecursiveEvaluation


namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.TrackedBankedSimulation (extents)

private theorem ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_body_heads_positive (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (i : Fin (M.k+3)) (noninput : i ≠ (machine M n request resume).inTape) :
    1 ≤ (bodyFrame M n request resume base rho sigma offset extent c v).head i := by
  rw [EndParkRecursiveRelocation.ordinary_window_internal_body_heads]
  split_ifs with hi hw hb
  · have := hoffset (BankedSimulation.innerTape M ⟨i.val,hi⟩ hw)
    omega
  · omega
  · have h0 : i.val=0 := by omega
    have heq : i=(machine M n request resume).inTape := Fin.ext h0
    exact False.elim (noninput heq)
  · exact hrho

/-- Every actual ordinary body step stays inside positive noninput windows,
including every intermediate physical time before the next call or halt. -/
private theorem ordinary_window_safe (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (S : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (near : ∀ j, c.head j ≤ extent j+1)
    (live : ∀ s, s < S → (M.step^[s] c).state ≠ M.qHalt)
    (ordinary : ∀ s, s < S → request (M.step^[s] c).state=none) :
    ∀ t, t ≤ S → ∀ i, i ≠ (machine M n request resume).inTape →
      1 ≤ ((machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)).head i := by
  have physical : ∀ t, t ≤ S →
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        bodyFrame M n request resume base rho sigma offset (extents M c extent t)
          (M.step^[t] c) v := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply',ih (by omega)]
      rw [ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_ordinary_body_step M n request resume base rho sigma offset
        (extents M c extent t) hoffset (M.step^[t] c) v
        (by intro j; exact (TrackedBankedSpace.ordinary_window_internal_unique_marker_run M c t unique j 0).2 rfl)
        (TrackedBankedSpace.ordinary_window_internal_heads_near_run M c extent t near)
        (live t (by omega)) (ordinary t (by omega))]
      simp only [extents,Function.iterate_succ_apply']
  intro t ht i hi
  rw [physical t ht]
  exact ordinary_window_internal_solutions_intmulendparkrecursiveordinarywindow_body_heads_positive M n request resume base rho sigma offset _ _ v
    hrho hsigma hoffset i hi

end IntMul.EndParkRecursiveEvaluation


open IntMul IntMul.EndParkRecursiveEvaluation IntMul.EndParkRecursiveScheduler

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (S : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (near : ∀ j, c.head j ≤ extent j+1)
    (live : ∀ s, s < S → (M.step^[s] c).state ≠ M.qHalt)
    (ordinary : ∀ s, s < S → request (M.step^[s] c).state=none) :
    ∀ t, t ≤ S → ∀ i, i ≠ (machine M n request resume).inTape →
      1 ≤ ((machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)).head i :=
  IntMul.EndParkRecursiveEvaluation.ordinary_window_safe M n request resume base rho sigma offset extent c v S hrho hsigma hoffset unique near live ordinary

#print axioms solution
