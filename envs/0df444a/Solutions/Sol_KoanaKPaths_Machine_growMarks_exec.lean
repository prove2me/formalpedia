-- Prove2me | solution 1 for KoanaKPaths.Machine.growMarks_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.09009+00:00
-- url     : https://prove2.me/submissions/ae987046-e5dc-464e-b880-7177531221ec

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Theorems.Thm_KoanaKPaths_Machine_duplicateMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
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

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]











lemma doubleMarks_exec (I : List Sym) (src tmp : Fin S) (hne : src ≠ tmp)
    (s : IState S) (m : ℕ) (tail : List Item) (ht : cls tail.head? ≠ Cls.mark)
    (hs : s.G src = List.replicate m .mark ++ tail) (hx : s.G tmp = []) :
    IExec I Fin.elim0 (doubleMarks src tmp) s
      (s.upd src (List.replicate (2*m) .mark ++ tail)) (97*m+60) := by
  let s1 := (s.upd src tail).upd tmp (List.replicate (2*m) .mark ++ s.G tmp)
  have hdup := duplicateMoveMarks_exec I src tmp hne s m tail ht hs
  have hsrc : s1.G tmp = List.replicate (2*m) .mark ++ [] := by simp [s1,hx]
  have hmov := moveMarks_exec I tmp src (Ne.symm hne) s1 (2*m) [] (by decide) hsrc
  have hrun := IExec.seq hdup hmov
  have he : (s1.upd tmp []).upd src (List.replicate (2*m) .mark ++ s1.G src) =
      s.upd src (List.replicate (2*m) .mark ++ tail) := by
    cases s
    simp only [s1,IState.upd]
    congr 1
    funext t
    by_cases ht : t=src <;> by_cases hu : t=tmp <;> simp_all [Function.update_apply]
  rw [he] at hrun
  change IExec I Fin.elim0 (doubleMarks src tmp) s _ ((33*m+30)+(32*(2*m)+30)) at hrun
  have hc : (33*m+30)+(32*(2*m)+30) = 97*m+60 := by omega
  simpa only [hc] using hrun










end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}





lemma growMarks_exec (I : List Sym) (control count tmp : Fin S)
    (hcc : control ≠ count) (hct : control ≠ tmp) (hcnt : count ≠ tmp)
    (s : IState S) (d m : ℕ) (tail tail' : List Item)
    (ht : cls tail.head? ≠ Cls.mark) (ht' : cls tail'.head? ≠ Cls.mark)
    (hc : s.G control = List.replicate d .mark ++ tail)
    (hn : s.G count = List.replicate m .mark ++ tail') (hx : s.G tmp = []) :
    IExec I Fin.elim0 (growMarks control count tmp) s
      ((s.upd control tail).upd count (List.replicate (m*2^d) .mark ++ tail')) (growMarksCost m d) := by
  induction d generalizing s m with
  | zero =>
    have hh : decide (s.cl control=Cls.mark) = false := by simp [IState.cl,hc,ht]
    have hs : s.upd control tail = s := by rw [← show s.G control=tail from by simpa using hc]; exact upd_same _ _
    have hn' : s.upd count (List.replicate m .mark ++ tail') = s := by rw [← hn]; exact upd_same _ _
    simp only [pow_zero,mul_one,hs,hn',growMarksCost]
    exact IExec.loopF hh
  | succ d ih =>
    let s0 := s.upd control (List.replicate d .mark ++ tail)
    let s1 := s0.upd count (List.replicate (2*m) .mark ++ tail')
    have hu : IExec I Fin.elim0 (.op (.unmark control)) s s0 1 :=
      IExec.op (IOp.Step.unmark (by simpa [List.replicate_succ] using hc))
    have hd := doubleMarks_exec I count tmp hcnt s0 m tail' ht'
      (by simp [s0,Ne.symm hcc,hn]) (by simp [s0,Ne.symm hct,hx])
    have hcc1 : s1.G control = List.replicate d .mark ++ tail := by simp [s1,s0,hcc]
    have hcnt1 : s1.G count = List.replicate (2*m) .mark ++ tail' := by simp [s1]
    have hx1 : s1.G tmp = [] := by simp [s1,s0,Ne.symm hcnt,Ne.symm hct,hx]
    have hh : decide (s.cl control=Cls.mark) = true := by simp [IState.cl,hc,List.replicate_succ,cls]
    have hrun := IExec.loopT hh (IExec.seq hu hd) (ih s1 (2*m) hcc1 hcnt1 hx1)
    have he : (s1.upd control tail).upd count (List.replicate (2*m*2^d) .mark ++ tail') =
        (s.upd control tail).upd count (List.replicate (m*2^(d+1)) .mark ++ tail') := by
      have hp : 2*m*2^d=m*2^(d+1) := by ring
      cases s
      simp only [s1,s0,IState.upd,hp]
      congr 1
      funext t
      by_cases ha : t=control <;> by_cases hb : t=count <;> simp_all
    rw [he] at hrun
    change IExec I Fin.elim0 (growMarks control count tmp) s _ _ at hrun
    convert hrun using 1
    simp [growMarksCost]
    omega












end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (control count tmp : Fin S) (hcc : @Ne.{1} (Fin S) control count)
  (hct : @Ne.{1} (Fin S) control tmp) (hcnt : @Ne.{1} (Fin S) count tmp) (s : NLogN.IState S) (d m : Nat)
  (tail tail' : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (ht' : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail')) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s control)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item d NLogN.Item.mark) tail))
  (hn :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) tail'))
  (hx : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s tmp) (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.growMarks S control count tmp) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s control tail) count
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d))
          NLogN.Item.mark)
        tail'))
    (KoanaKPaths.Machine.growMarksCost m d) := by
  exact @KoanaKPaths.Machine.growMarks_exec
