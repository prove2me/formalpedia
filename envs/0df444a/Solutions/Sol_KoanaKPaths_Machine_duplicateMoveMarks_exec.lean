-- Prove2me | solution 1 for KoanaKPaths.Machine.duplicateMoveMarks_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:46:00.992106+00:00
-- url     : https://prove2.me/submissions/6cc50536-7d3c-4437-bf50-d9b5a59ebc86

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S P : ℕ}





























lemma replicate_cons_same {α : Type} (m : ℕ) (x : α) (L : List α) :
    List.replicate m x ++ x::L = x::(List.replicate m x ++ L) := by
  induction m with
  | zero => rfl
  | succ m ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons x) ih























end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]

@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]





lemma duplicateMoveMarks_exec (I : List Sym) (src dst : Fin S) (hne : src ≠ dst)
    (s : IState S) (m : ℕ) (tail : List Item) (ht : cls tail.head? ≠ Cls.mark)
    (hs : s.G src = List.replicate m .mark ++ tail) :
    IExec I Fin.elim0 (duplicateMoveMarks src dst) s
      ((s.upd src tail).upd dst (List.replicate (2*m) .mark ++ s.G dst)) (33*m+30) := by
  induction m generalizing s with
  | zero =>
    have hh : decide (s.cl src=Cls.mark) = false := by simp [IState.cl,hs,ht]
    have hsrc : s.upd src tail = s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    simp only [mul_zero,List.replicate_zero,List.nil_append,hsrc,upd_same,zero_add]
    exact IExec.loopF hh
  | succ m ih =>
    let s0 := s.upd src (List.replicate m .mark ++ tail)
    let s1 := s0.upd dst (.mark::.mark::s.G dst)
    have hbody : IExec I Fin.elim0
        (.seq (.op (.unmark src)) (.seq (.op (.mark dst)) (.op (.mark dst)))) s s1 3 := by
      have hU : IExec I Fin.elim0 (.op (.unmark src)) s s0 1 :=
        IExec.op (IOp.Step.unmark (by simpa [List.replicate_succ] using hs))
      have hM1 : IExec I Fin.elim0 (.op (.mark dst)) s0 (s0.upd dst (.mark::s.G dst)) 1 := by
        simpa only [s0,upd_G_ne s (Ne.symm hne)] using
          (IExec.op (IOp.Step.mark (s := s0) (i := dst)) : IExec I Fin.elim0 (.op (.mark dst)) _ _ 1)
      have hM2 : IExec I Fin.elim0 (.op (.mark dst)) (s0.upd dst (.mark::s.G dst)) s1 1 := by
        simpa only [upd_G_self,upd_upd,s1] using
          (IExec.op (IOp.Step.mark (s := s0.upd dst (.mark::s.G dst)) (i := dst)) :
            IExec I Fin.elim0 (.op (.mark dst)) _ _ 1)
      exact IExec.seq hU (IExec.seq hM1 hM2)
    have hs1 : s1.G src = List.replicate m .mark ++ tail := by simp [s1,s0,hne]
    have hh : decide (s.cl src=Cls.mark) = true := by simp [IState.cl,hs,List.replicate_succ,cls]
    have hrun := IExec.loopT hh hbody (ih s1 hs1)
    have hfinal : (s1.upd src tail).upd dst (List.replicate (2*m) .mark ++ s1.G dst) =
        (s.upd src tail).upd dst (List.replicate (2*(m+1)) .mark ++ s.G dst) := by
      cases s
      simp only [s1,s0,IState.upd]
      congr 1
      funext t
      by_cases hs : t=src <;> by_cases hd : t=dst <;>
        simp_all [Function.update_apply,Nat.mul_add,List.replicate_add,List.replicate_succ,
          replicate_cons_same,List.append_assoc]
    rw [hfinal] at hrun
    change IExec I Fin.elim0 (duplicateMoveMarks src dst) s _ (3+(33*m+30)+30) at hrun
    have hc : 3+(33*m+30)+30 = 33*(m+1)+30 := by omega
    simpa only [hc] using hrun














end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst : Fin S) (hne : @Ne.{1} (Fin S) src dst) (s : NLogN.IState S) (m : Nat)
  (tail : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.duplicateMoveMarks S src dst) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
          NLogN.Item.mark)
        (@NLogN.IState.G S s dst)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) m)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.duplicateMoveMarks_exec
