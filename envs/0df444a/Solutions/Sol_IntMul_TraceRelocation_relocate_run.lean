-- Prove2me | solution 1 for IntMul.TraceRelocation.relocate_run
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T05:07:19.175698+00:00
-- url     : https://prove2.me/submissions/78a3d172-7b00-47b6-9080-6122d66f50bc

import Definitions.Def_IntMul_TraceRelocation
import Mathlib.Tactic

namespace IntMul.TraceRelocation

private theorem relocation_internal_relocation_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem relocation_internal_input_cells_step (N : MultitapeTM) (c : N.Cfg) :
    (N.step c).cells N.inTape=c.cells N.inTape := by
  change Function.update (c.cells N.inTape) (c.head N.inTape)
    ((N.δ c.state (fun i => c.cells i (c.head i))).2 N.inTape).1=c.cells N.inTape
  have h := N.input_readonly c.state (fun i => c.cells i (c.head i))
  change ((N.δ c.state (fun i => c.cells i (c.head i))).2 N.inTape).1=
    c.cells N.inTape (c.head N.inTape) at h
  rw [h]
  exact Function.update_eq_self _ _

private theorem relocation_internal_input_cells_run (N : MultitapeTM) (c : N.Cfg) (t : ℕ) :
    (N.step^[t] c).cells N.inTape=c.cells N.inTape := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',relocation_internal_input_cells_step,ih]

/-- One identical physical transition in arbitrary translated tape windows.
No ancestor prefix or outer input payload is inspected or overwritten. -/
private theorem relocation_internal_relocate_step (N : MultitapeTM) (base c : N.Cfg) (shift lower : Fin N.k → ℕ)
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
  apply relocation_internal_relocation_cfg_ext
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
private theorem relocate_run (N : MultitapeTM) (base c : N.Cfg) (shift lower : Fin N.k → ℕ)
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
      apply relocation_internal_relocate_step N base _ shift lower positive
      · rw [relocation_internal_input_cells_run,hhead t (by omega)]
        exact root_reads
      · exact root_quiet t (by omega)
      · exact inside t (by omega)
  exact hrun T (by omega)

end IntMul.TraceRelocation


open IntMul IntMul.TraceRelocation

theorem solution (N : MultitapeTM) (base c : N.Cfg) (shift lower : Fin N.k → ℕ)
    (T : ℕ) (positive : ∀ i, i≠N.inTape → shift i≠0 → 1≤ lower i)
    (root_reads : base.cells N.inTape (base.head N.inTape)=c.cells N.inTape (c.head N.inTape))
    (root_quiet : ∀ t, t< T →
      ((N.δ (N.step^[t] c).state (fun i => (N.step^[t] c).cells i ((N.step^[t] c).head i))).2 N.inTape).2=Move.stay)
    (inside : ∀ t, t< T → ∀ i, i≠N.inTape → lower i≤ (N.step^[t] c).head i) :
    N.step^[T] (frame N base shift lower c)=frame N base shift lower (N.step^[T] c) :=
  IntMul.TraceRelocation.relocate_run N base c shift lower T positive root_reads root_quiet inside

#print axioms solution
