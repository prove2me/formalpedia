-- Prove2me | solution 1 for KoanaKPaths.Machine.duplicateTakeInts_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.803296+00:00
-- url     : https://prove2.me/submissions/109eb30d-e9d3-42e0-bf20-d80eb2305733

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

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]






















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

































lemma duplicateTakeInts_exec (I : List Sym) (count src dst tmp : Fin S)
    (hcs : count ≠ src) (hcd : count ≠ dst) (hct : count ≠ tmp)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : IState S) (xs : List ℤ) (tail ct : List Item) (ht : cls ct.head? ≠ Cls.mark)
    (hc : s.G count = List.replicate xs.length .mark ++ ct)
    (hs : s.G src = xs.map Item.int ++ tail) :
    IExec I Fin.elim0 (duplicateTakeInts count src dst tmp) s
      ((((s.upd count ct).upd src tail).upd dst (xs.reverse.map Item.int ++ s.G dst)).upd tmp
        (xs.reverse.map Item.int ++ s.G tmp)) (duplicateTakeIntsCost xs) := by
  induction xs generalizing s with
  | nil =>
    have hh : decide (s.cl count=Cls.mark) = false := by simp [IState.cl,hc,ht]
    have hcount : s.upd count ct = s := by rw [← show s.G count=ct from by simpa using hc]; exact upd_same _ _
    have hsrc : s.upd src tail = s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    simp only [List.reverse_nil,List.map_nil,List.nil_append,hcount,hsrc,upd_same,
      duplicateTakeIntsCost,List.sum_nil,zero_add]
    exact IExec.loopF hh
  | cons z xs ih =>
    let s0 := s.upd count (List.replicate xs.length .mark ++ ct)
    let s1 := s0.upd dst (.int z::s.G dst)
    let s2 := (s1.upd src (xs.map Item.int ++ tail)).upd tmp (.int z::s.G tmp)
    have hu : IExec I Fin.elim0 (.op (.unmark count)) s s0 1 := by
      exact IExec.op (IOp.Step.unmark (by simpa [List.replicate_succ] using hc))
    have hd : IExec I Fin.elim0 (.op (.dup src dst)) s0 s1 (dupCost (zsz z)+17) := by
      have hh : s0.G src = .int z::(xs.map Item.int ++ tail) := by simp [s0,Ne.symm hcs,hs]
      simpa only [s0,upd_G_ne s (Ne.symm hcd)] using
        (IExec.op (IOp.Step.dup hsd hh) : IExec I Fin.elim0 (.op (.dup src dst)) _ _ _)
    have hm : IExec I Fin.elim0 (.op (.mv src tmp)) s1 s2 (2*moveCost (zsz z)+19) := by
      have hh : s1.G src = .int z::(xs.map Item.int ++ tail) := by simp [s1,s0,hsd,Ne.symm hcs,hs]
      simpa only [s1,upd_G_ne _ (Ne.symm hdt),s0,upd_G_ne _ (Ne.symm hct)] using
        (IExec.op (IOp.Step.mv hst hh) : IExec I Fin.elim0 (.op (.mv src tmp)) _ _ _)
    have hc2 : s2.G count = List.replicate xs.length .mark ++ ct := by simp [s2,s1,s0,hcs,hcd,hct]
    have hs2 : s2.G src = xs.map Item.int ++ tail := by simp [s2,hst]
    have hh : decide (s.cl count=Cls.mark) = true := by simp [IState.cl,hc,List.replicate_succ,cls]
    have hrun := IExec.loopT hh (IExec.seq hu (IExec.seq hd hm)) (ih s2 hc2 hs2)
    have he : ((((s2.upd count ct).upd src tail).upd dst
        (xs.reverse.map Item.int ++ s2.G dst)).upd tmp (xs.reverse.map Item.int ++ s2.G tmp)) =
      ((((s.upd count ct).upd src tail).upd dst
        ((z::xs).reverse.map Item.int ++ s.G dst)).upd tmp ((z::xs).reverse.map Item.int ++ s.G tmp)) := by
      cases s
      simp only [s2,s1,s0,IState.upd]
      congr 1
      funext t
      by_cases ha : t=count <;> by_cases hb : t=src <;> by_cases hc : t=dst <;> by_cases hd : t=tmp <;>
        simp_all [List.reverse_cons,List.map_append,List.append_assoc]
    rw [he] at hrun
    change IExec I Fin.elim0 (duplicateTakeInts count src dst tmp) s _ _ at hrun
    convert hrun using 1
    simp [duplicateTakeIntsCost]
    omega








end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (count src dst tmp : Fin S) (hcs : @Ne.{1} (Fin S) count src)
  (hcd : @Ne.{1} (Fin S) count dst) (hct : @Ne.{1} (Fin S) count tmp) (hsd : @Ne.{1} (Fin S) src dst)
  (hst : @Ne.{1} (Fin S) src tmp) (hdt : @Ne.{1} (Fin S) dst tmp) (s : NLogN.IState S) (xs : List.{0} Int)
  (tail ct : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item ct)) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int xs) NLogN.Item.mark) ct))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.duplicateTakeInts S count src dst tmp) s
    (@NLogN.IState.upd S
      (@NLogN.IState.upd S (@NLogN.IState.upd S (@NLogN.IState.upd S s count ct) src tail) dst
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs)) (@NLogN.IState.G S s dst)))
      tmp
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs)) (@NLogN.IState.G S s tmp)))
    (KoanaKPaths.Machine.duplicateTakeIntsCost xs) := by
  exact @KoanaKPaths.Machine.duplicateTakeInts_exec
