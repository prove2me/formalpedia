-- Prove2me | solution 1 for IntMul.EndParkRecursiveRelocation.relocate_execution
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T05:20:09.90997+00:00
-- url     : https://prove2.me/submissions/3ff2f282-bf49-43e3-b9b0-1a7925dc8e91

import Definitions.Def_IntMul_EndParkRecursiveRelocation
import Mathlib.Tactic

namespace IntMul.TraceRelocation

private theorem scheduler_relocation_internal_solutions_intmultracerelocation_relocation_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem scheduler_relocation_internal_solutions_intmultracerelocation_input_cells_step (N : MultitapeTM) (c : N.Cfg) :
    (N.step c).cells N.inTape=c.cells N.inTape := by
  change Function.update (c.cells N.inTape) (c.head N.inTape)
    ((N.δ c.state (fun i => c.cells i (c.head i))).2 N.inTape).1=c.cells N.inTape
  have h := N.input_readonly c.state (fun i => c.cells i (c.head i))
  change ((N.δ c.state (fun i => c.cells i (c.head i))).2 N.inTape).1=
    c.cells N.inTape (c.head N.inTape) at h
  rw [h]
  exact Function.update_eq_self _ _

private theorem scheduler_relocation_internal_solutions_intmultracerelocation_input_cells_run (N : MultitapeTM) (c : N.Cfg) (t : ℕ) :
    (N.step^[t] c).cells N.inTape=c.cells N.inTape := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',scheduler_relocation_internal_solutions_intmultracerelocation_input_cells_step,ih]

/-- One identical physical transition in arbitrary translated tape windows.
No ancestor prefix or outer input payload is inspected or overwritten. -/
private theorem scheduler_relocation_internal_relocate_step (N : MultitapeTM) (base c : N.Cfg) (shift lower : Fin N.k → ℕ)
    (positive : ∀ i, i≠N.inTape → shift i≠0 → 1≤ lower i)
    (root_reads : base.cells N.inTape (base.head N.inTape)=c.cells N.inTape (c.head N.inTape))
    (root_stationary : ((N.δ c.state (fun i => c.cells i (c.head i))).2 N.inTape).2=Move.stay)
    (inside : ∀ i, i≠N.inTape → lower i≤ c.head i) :
    N.step (frame N base shift lower c)=frame N base shift lower (N.step c) := by
  have hread : (fun i => (frame N base shift lower c).cells i
      ((frame N base shift lower c).head i))=(fun i => c.cells i (c.head i)) := by
    funext i
    by_cases hi : i=N.inTape
    · subst i
      simp only [frame,if_true]
      exact root_reads
    · have hwindow : ¬shift i+c.head i< shift i+lower i := by have := inside i hi; omega
      simp only [frame,if_neg hi,if_neg hwindow,Nat.add_sub_cancel_left]
  have hdelta : N.δ (frame N base shift lower c).state
      (fun i => (frame N base shift lower c).cells i ((frame N base shift lower c).head i))=
      N.δ c.state (fun i => c.cells i (c.head i)) := by
    change N.δ c.state _=N.δ c.state _
    rw [hread]
  apply scheduler_relocation_internal_solutions_intmultracerelocation_relocation_cfg_ext
  · change (N.δ (frame N base shift lower c).state _).1=(N.δ c.state _).1
    rw [hdelta]
  · funext i p
    change Function.update ((frame N base shift lower c).cells i)
      ((frame N base shift lower c).head i)
      ((N.δ (frame N base shift lower c).state _).2 i).1 p=_
    rw [hdelta]
    by_cases hi : i=N.inTape
    · subst i
      have hwrite := N.input_readonly c.state (fun j => c.cells j (c.head j))
      change ((N.δ c.state (fun j => c.cells j (c.head j))).2 N.inTape).1=
        c.cells N.inTape (c.head N.inTape) at hwrite
      rw [←root_reads] at hwrite
      simp only [frame,if_true,hwrite]
      exact congrFun (Function.update_eq_self _ _) p
    · simp only [frame,if_neg hi]
      change Function.update
        (fun p => if p< shift i+lower i then base.cells i p else c.cells i (p-shift i))
        (shift i+c.head i) ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).1 p=
        (if p< shift i+lower i then base.cells i p else
          Function.update (c.cells i) (c.head i)
            ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).1 (p-shift i))
      by_cases hp : p< shift i+lower i
      · have hne : p≠shift i+c.head i := by have := inside i hi; omega
        simp only [Function.update_of_ne hne,if_pos hp]
      · by_cases heq : p=shift i+c.head i
        · subst p
          rw [Function.update_self,if_neg hp,Nat.add_sub_cancel_left,Function.update_self]
        · have hne : p-shift i≠c.head i := by omega
          simp only [Function.update_of_ne heq,if_neg hp,Function.update_of_ne hne]
  · funext i
    change (match ((N.δ (frame N base shift lower c).state _).2 i).2 with
      | Move.left => (frame N base shift lower c).head i-1
      | Move.stay => (frame N base shift lower c).head i
      | Move.right => (frame N base shift lower c).head i+1)=_
    rw [hdelta]
    by_cases hi : i=N.inTape
    · subst i
      simp only [frame,if_true,root_stationary]
    · simp only [frame,if_neg hi]
      change (match ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).2 with
        | Move.left => shift i+c.head i-1
        | Move.stay => shift i+c.head i
        | Move.right => shift i+c.head i+1)=
        shift i+(match ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).2 with
        | Move.left => c.head i-1
        | Move.stay => c.head i
        | Move.right => c.head i+1)
      have hzero : shift i=0 ∨ 1≤ c.head i := by
        by_cases hs : shift i=0
        · exact Or.inl hs
        · have := positive i hi hs
          have := inside i hi
          exact Or.inr (by omega)
      cases hmove : ((N.δ c.state (fun j => c.cells j (c.head j))).2 i).2 <;> simp only [hmove] <;> omega

/-- Relocate a complete physical T-step trace with exactly the SAME clock,
retaining arbitrary ancestor prefixes and the complete outer input tape.
Only source head bounds along that trace are required. -/
private theorem scheduler_relocation_internal_relocate_run (N : MultitapeTM) (base c : N.Cfg) (shift lower : Fin N.k → ℕ)
    (T : ℕ) (positive : ∀ i, i≠N.inTape → shift i≠0 → 1≤ lower i)
    (root_reads : base.cells N.inTape (base.head N.inTape)=c.cells N.inTape (c.head N.inTape))
    (root_quiet : ∀ t, t< T →
      ((N.δ (N.step^[t] c).state (fun i => (N.step^[t] c).cells i ((N.step^[t] c).head i))).2 N.inTape).2=Move.stay)
    (inside : ∀ t, t< T → ∀ i, i≠N.inTape → lower i≤ (N.step^[t] c).head i) :
    N.step^[T] (frame N base shift lower c)=frame N base shift lower (N.step^[T] c) := by
  have hhead : ∀ t, t≤ T → (N.step^[t] c).head N.inTape=c.head N.inTape := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply']
      change (match ((N.δ (N.step^[t] c).state
        (fun i => (N.step^[t] c).cells i ((N.step^[t] c).head i))).2 N.inTape).2 with
        | Move.left => (N.step^[t] c).head N.inTape-1
        | Move.stay => (N.step^[t] c).head N.inTape
        | Move.right => (N.step^[t] c).head N.inTape+1)=c.head N.inTape
      rw [root_quiet t (by omega)]
      exact ih (by omega)
  have hrun : ∀ t, t≤ T → N.step^[t] (frame N base shift lower c)=
      frame N base shift lower (N.step^[t] c) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply',ih (by omega),Function.iterate_succ_apply']
      apply scheduler_relocation_internal_relocate_step N base _ shift lower positive
      · rw [scheduler_relocation_internal_solutions_intmultracerelocation_input_cells_run,hhead t (by omega)]
        exact root_reads
      · exact root_quiet t (by omega)
      · exact inside t (by omega)
  exact hrun T (by omega)

end IntMul.TraceRelocation



namespace IntMul.EndParkRecursiveRelocation

open IntMul.EndParkRecursiveScheduler

/-- Flat view of every physical body cell, including all retained prefixes. -/
private theorem scheduler_relocation_internal_body_cells (M : MultitapeTM) (n : ℕ)
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
private theorem scheduler_relocation_internal_body_heads (M : MultitapeTM) (n : ℕ)
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



namespace IntMul.EndParkRecursiveRelocation

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveReturn

private theorem scheduler_relocation_internal_solutions_intmulendparkrecursiverelocationframes_relocation_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem scheduler_relocation_internal_solutions_intmulendparkrecursiverelocationframes_buffer_window (M : MultitapeTM) (base source : ℕ → TrackedBankedSimulation.Sym M)
    (sigma : ℕ) (positive : 1≤ sigma) (v : List Bool) (p : ℕ) :
    (if p< sigma-1+1 then base p else TrackedOutputReturn.bufferTape M source 1 v (p-(sigma-1)))=
      TrackedOutputReturn.bufferTape M base sigma v p := by
  have hb : sigma-1+1=sigma := by omega
  rw [hb]
  by_cases hp : p< sigma
  · simp only [if_pos hp,TrackedOutputReturn.bufferTape,if_pos hp]
  · have hq : ¬p-(sigma-1)< 1 := by omega
    have heq : p-(sigma-1)=1 ↔ p=sigma := by omega
    have hindex : p-(sigma-1)-1-1=p-sigma-1 := by omega
    simp only [if_neg hp,TrackedOutputReturn.bufferTape,if_neg hq,heq,hindex]

/-- The relocated unit-offset body frame is EXACTLY the arbitrary interior
body frame, for every source input and every retained ancestor prefix. -/
private theorem scheduler_relocation_internal_relocate_body_frame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base source : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (hrho : 1≤ rho) (hsigma : 1≤ sigma) (hoffset : ∀ j, 1≤ offset j) :
    TraceRelocation.frame (machine M n request resume) base (shifts M rho sigma offset) (fun _ => 1)
      (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)=
      bodyFrame M n request resume base rho sigma offset extent c v := by
  classical
  apply scheduler_relocation_internal_solutions_intmulendparkrecursiverelocationframes_relocation_cfg_ext
  · rfl
  · funext i p
    by_cases hroot : i=(machine M n request resume).inTape
    · have h0 : i.val=0 := by subst i; rfl
      have hi : i.val< M.k+2 := by omega
      have hw : ¬2≤ i.val := by omega
      have hb : i.val≠1 := by omega
      simp only [TraceRelocation.frame,if_pos hroot,scheduler_relocation_internal_body_cells,dif_pos hi,dif_neg hw,if_neg hb]
    · by_cases hi : i.val< M.k+2
      · by_cases hw : 2≤ i.val
        · let j := BankedSimulation.innerTape M ⟨i.val,hi⟩ hw
          have hj := hoffset j
          have hboundary : offset j-1+1=offset j := by omega
          have hindex : p-(offset j-1)-1=p-offset j := by omega
          simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_pos hi,dif_pos hw,scheduler_relocation_internal_body_cells]
          change (if p< offset j-1+1 then base.cells i p else
            if p-(offset j-1)< 1 then source.cells i (p-(offset j-1)) else
              some (c.cells j (p-(offset j-1)-1),decide (p-(offset j-1)-1≤ extent j)))=
            if p< offset j then base.cells i p else some (c.cells j (p-offset j),decide (p-offset j≤ extent j))
          rw [hboundary,hindex]
          by_cases hp : p< offset j
          · simp only [if_pos hp]
          · have hq : ¬p-(offset j-1)< 1 := by omega
            simp only [if_neg hp,if_neg hq]
        · have hb : i.val=1 := by
            have hz : i.val≠0 := by
              intro hz
              apply hroot
              apply Fin.ext
              simpa only [MultitapeTM.inTape] using hz
            omega
          simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_pos hi,dif_neg hw,if_pos hb,scheduler_relocation_internal_body_cells]
          exact scheduler_relocation_internal_solutions_intmulendparkrecursiverelocationframes_buffer_window M (base.cells i) (source.cells i) sigma hsigma v p
      · simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_neg hi,scheduler_relocation_internal_body_cells,FiniteContinuationStack.freshTape]
        have hb : rho-1+1=rho := by omega
        rw [hb]
        by_cases hp : p< rho
        · simp only [if_pos hp]
        · have hq : ¬p-(rho-1)< 1 := by omega
          simp only [if_neg hp,if_neg hq]
  · funext i
    by_cases hroot : i=(machine M n request resume).inTape
    · have h0 : i.val=0 := by subst i; rfl
      have hi : i.val< M.k+2 := by omega
      have hw : ¬2≤ i.val := by omega
      have hb : i.val≠1 := by omega
      simp only [TraceRelocation.frame,if_pos hroot,scheduler_relocation_internal_body_heads,dif_pos hi,dif_neg hw,if_neg hb]
    · by_cases hi : i.val< M.k+2
      · by_cases hw : 2≤ i.val
        · have hp := hoffset (BankedSimulation.innerTape M ⟨i.val,hi⟩ hw)
          simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_pos hi,dif_pos hw,scheduler_relocation_internal_body_heads]
          omega
        · have hb : i.val=1 := by
            have hz : i.val≠0 := by
              intro hz
              apply hroot
              apply Fin.ext
              simpa only [MultitapeTM.inTape] using hz
            omega
          simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_pos hi,dif_neg hw,if_pos hb,scheduler_relocation_internal_body_heads]
          omega
      · simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_neg hi,scheduler_relocation_internal_body_heads]
        omega

/-- The relocated unit-offset cleaned inspection frame is EXACTLY the
interior child return frame, including its ancestor continuation probe. -/
private theorem scheduler_relocation_internal_relocate_inspection_frame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base source : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset : Fin M.k → ℕ) (w : List Bool)
    (hrho : 1≤ rho) (hsigma : 1≤ sigma) (hoffset : ∀ j, 1≤ offset j) :
    TraceRelocation.frame (machine M n request resume) base (shifts M rho sigma offset) (fun _ => 1)
      (inspectionFrame M n request resume source 1 1 (fun _ => 1) w)=
      inspectionFrame M n request resume base rho sigma offset w := by
  classical
  apply scheduler_relocation_internal_solutions_intmulendparkrecursiverelocationframes_relocation_cfg_ext
  · rfl
  · funext i p
    by_cases hroot : i=(machine M n request resume).inTape
    · have h0 : i.val=0 := by subst i; rfl
      have hi : i.val< M.k+2 := by omega
      have hw : ¬2≤ i.val := by omega
      have hb : i.val≠1 := by omega
      simp only [TraceRelocation.frame,if_pos hroot,inspectionFrame,dif_pos hi,dif_neg hw,if_neg hb]
    · by_cases hi : i.val< M.k+2
      · by_cases hw : 2≤ i.val
        · let j := BankedSimulation.innerTape M ⟨i.val,hi⟩ hw
          have hj := hoffset j
          have hboundary : offset j-1+1=offset j := by omega
          simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_pos hi,dif_pos hw,inspectionFrame,TrackedBankCleanup.freshTape]
          change (if p< offset j-1+1 then base.cells i p else
              if p-(offset j-1)< 1 then source.cells i (p-(offset j-1)) else some (M.blank,false))=
            if p< offset j then base.cells i p else some (M.blank,false)
          rw [hboundary]
          by_cases hp : p< offset j
          · simp only [if_pos hp]
          · have hq : ¬p-(offset j-1)< 1 := by omega
            simp only [if_neg hp,if_neg hq]
        · have hb : i.val=1 := by
            have hz : i.val≠0 := by
              intro hz
              apply hroot
              apply Fin.ext
              simpa only [MultitapeTM.inTape] using hz
            omega
          simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_pos hi,dif_neg hw,if_pos hb,inspectionFrame]
          exact scheduler_relocation_internal_solutions_intmulendparkrecursiverelocationframes_buffer_window M (base.cells i) (source.cells i) sigma hsigma w p
      · simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_neg hi,inspectionFrame,FiniteContinuationStack.freshTape]
        have hb : rho-1+1=rho := by omega
        rw [hb]
        by_cases hp : p< rho
        · simp only [if_pos hp]
        · have hq : ¬p-(rho-1)< 1 := by omega
          simp only [if_neg hp,if_neg hq]
  · funext i
    by_cases hroot : i=(machine M n request resume).inTape
    · have h0 : i.val=0 := by subst i; rfl
      have hi : i.val< M.k+2 := by omega
      have hw : ¬2≤ i.val := by omega
      have hb : i.val≠1 := by omega
      simp only [TraceRelocation.frame,if_pos hroot,inspectionFrame,dif_pos hi,dif_neg hw,if_neg hb]
    · by_cases hi : i.val< M.k+2
      · by_cases hw : 2≤ i.val
        · have hp := hoffset (BankedSimulation.innerTape M ⟨i.val,hi⟩ hw)
          simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_pos hi,dif_pos hw,inspectionFrame]
          omega
        · have hb : i.val=1 := by
            have hz : i.val≠0 := by
              intro hz
              apply hroot
              apply Fin.ext
              simpa only [MultitapeTM.inTape] using hz
            omega
          simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_pos hi,dif_neg hw,if_pos hb,inspectionFrame]
          omega
      · simp only [TraceRelocation.frame,if_neg hroot,shifts,dif_neg hi,inspectionFrame]
        omega

end IntMul.EndParkRecursiveRelocation



namespace IntMul.EndParkRecursiveRelocation

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveReturn

/-- A complete unit-offset body/cleanup trace is reproduced in arbitrary
interior child windows with EXACTLY the same physical clock. -/
private theorem relocate_execution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base source : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (T : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (root_reads : base.cells (machine M n request resume).inTape
      (base.head (machine M n request resume).inTape)=
      source.cells (machine M n request resume).inTape
        (source.head (machine M n request resume).inTape))
    (root_quiet : ∀ t, t < T →
      let d := (machine M n request resume).step^[t]
        (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)
      (((machine M n request resume).δ d.state (fun i => d.cells i (d.head i))).2
        (machine M n request resume).inTape).2=Move.stay)
    (inside : ∀ t, t < T → ∀ i, i≠(machine M n request resume).inTape →
      1 ≤ ((machine M n request resume).step^[t]
        (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)).head i)
    (run : (machine M n request resume).step^[T]
      (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)=
      inspectionFrame M n request resume source 1 1 (fun _ => 1) w) :
    (machine M n request resume).step^[T]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      inspectionFrame M n request resume base rho sigma offset w := by
  have h0 : ((machine M n request resume).inTape).val=0 := rfl
  have hi : ((machine M n request resume).inTape).val < M.k+2 := by omega
  have hw : ¬2 ≤ ((machine M n request resume).inTape).val := by omega
  have hb : ((machine M n request resume).inTape).val≠1 := by omega
  have hreads : base.cells (machine M n request resume).inTape (base.head (machine M n request resume).inTape)=
      (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v).cells
        (machine M n request resume).inTape
        ((bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v).head
          (machine M n request resume).inTape) := by
    simp only [scheduler_relocation_internal_body_cells,scheduler_relocation_internal_body_heads,dif_pos hi,dif_neg hw,if_neg hb]
    exact root_reads
  have hrun := TraceRelocation.scheduler_relocation_internal_relocate_run (machine M n request resume) base
    (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)
    (shifts M rho sigma offset) (fun _ => 1) T (by intro i _ _; omega) hreads root_quiet inside
  rw [scheduler_relocation_internal_relocate_body_frame M n request resume base source rho sigma offset extent c v hrho hsigma hoffset,
    run,scheduler_relocation_internal_relocate_inspection_frame M n request resume base source rho sigma offset w hrho hsigma hoffset] at hrun
  exact hrun

end IntMul.EndParkRecursiveRelocation


open IntMul IntMul.EndParkRecursiveRelocation IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveReturn

theorem solution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base source : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (T : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (root_reads : base.cells (machine M n request resume).inTape
      (base.head (machine M n request resume).inTape)=
      source.cells (machine M n request resume).inTape
        (source.head (machine M n request resume).inTape))
    (root_quiet : ∀ t, t < T →
      let d := (machine M n request resume).step^[t]
        (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)
      (((machine M n request resume).δ d.state (fun i => d.cells i (d.head i))).2
        (machine M n request resume).inTape).2=Move.stay)
    (inside : ∀ t, t < T → ∀ i, i≠(machine M n request resume).inTape →
      1 ≤ ((machine M n request resume).step^[t]
        (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)).head i)
    (run : (machine M n request resume).step^[T]
      (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)=
      inspectionFrame M n request resume source 1 1 (fun _ => 1) w) :
    (machine M n request resume).step^[T]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      inspectionFrame M n request resume base rho sigma offset w :=
  IntMul.EndParkRecursiveRelocation.relocate_execution M n request resume base source rho sigma offset extent c v w T hrho hsigma hoffset root_reads root_quiet inside run

#print axioms solution
