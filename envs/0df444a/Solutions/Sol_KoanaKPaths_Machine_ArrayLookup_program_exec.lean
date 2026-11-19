-- Prove2me | solution 1 for KoanaKPaths.Machine.ArrayLookup.program_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:46:05.764341+00:00
-- url     : https://prove2.me/submissions/622793e8-7214-4362-bf04-d93394e63dc7

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Theorems.Thm_KoanaKPaths_Machine_ArrayLookup_backward_exec_raw
import Theorems.Thm_KoanaKPaths_Machine_ArrayLookup_forward_exec
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
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





lemma cls_int (z : ℤ) :
    cls (some (.int z)) = Cls.zero ∨ cls (some (.int z)) = Cls.pos ∨
      cls (some (.int z)) = Cls.neg := by
  by_cases hz : z=0
  · simp [cls,hz]
  · by_cases hn : z<0 <;> simp [cls,hz,hn]











lemma duplicateMoveInts_exec (I : List Sym) (src dst tmp : Fin S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : IState S) (xs : List ℤ) (tail : List Item)
    (ht : ¬ (cls tail.head? = Cls.zero ∨ cls tail.head? = Cls.pos ∨ cls tail.head? = Cls.neg))
    (hs : s.G src = xs.map Item.int ++ tail) :
    IExec I Fin.elim0 (duplicateMoveInts src dst tmp) s
      (((s.upd src tail).upd dst (xs.reverse.map Item.int ++ s.G dst)).upd tmp
        (xs.reverse.map Item.int ++ s.G tmp)) (duplicateMoveIntsCost xs) := by
  induction xs generalizing s with
  | nil =>
    have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg) = false := by
      simpa [IState.cl,hs] using ht
    have hsrc : s.upd src tail = s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    simp only [List.reverse_nil,List.map_nil,List.nil_append,hsrc,upd_same,
      duplicateMoveIntsCost,List.sum_nil,zero_add]
    exact IExec.loopF hh
  | cons z xs ih =>
    let s0 := s.upd dst (.int z::s.G dst)
    let s1 := (s0.upd src (xs.map Item.int ++ tail)).upd tmp (.int z::s.G tmp)
    have hdup : IExec I Fin.elim0 (.op (.dup src dst)) s s0 (dupCost (zsz z)+17) := by
      exact IExec.op (IOp.Step.dup hsd (by simpa using hs))
    have hmv : IExec I Fin.elim0 (.op (.mv src tmp)) s0 s1 (2*moveCost (zsz z)+19) := by
      have hsrc : s0.G src = .int z::(xs.map Item.int ++ tail) := by simp [s0,hs,hsd]
      simpa only [s0,upd_G_ne s (Ne.symm hdt)] using
        (IExec.op (IOp.Step.mv hst hsrc) : IExec I Fin.elim0 (.op (.mv src tmp)) _ _ _)
    have hs1 : s1.G src = xs.map Item.int ++ tail := by simp [s1,hst]
    have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg) = true := by
      simp only [IState.cl,hs,List.map_cons,List.cons_append,List.head?_cons,decide_eq_true_eq]
      exact cls_int z
    have hrun := IExec.loopT hh (IExec.seq hdup hmv) (ih s1 hs1)
    have hfinal : (((s1.upd src tail).upd dst (xs.reverse.map Item.int ++ s1.G dst)).upd tmp
        (xs.reverse.map Item.int ++ s1.G tmp)) =
        (((s.upd src tail).upd dst ((z::xs).reverse.map Item.int ++ s.G dst)).upd tmp
          ((z::xs).reverse.map Item.int ++ s.G tmp)) := by
      cases s
      simp only [s1,s0,IState.upd]
      congr 1
      funext t
      by_cases ha : t=src <;> by_cases hb : t=dst <;> by_cases hc : t=tmp <;>
        simp_all [List.reverse_cons,List.map_append,List.append_assoc]
    rw [hfinal] at hrun
    change IExec I Fin.elim0 (duplicateMoveInts src dst tmp) s _ _ at hrun
    convert hrun using 1
    simp [duplicateMoveIntsCost]
    omega

lemma copyReverseInts_exec (I : List Sym) (src dst tmp : Fin S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : IState S) (xs : List ℤ) (tail : List Item)
    (ht : ¬ (cls tail.head? = Cls.zero ∨ cls tail.head? = Cls.pos ∨ cls tail.head? = Cls.neg))
    (hs : s.G src = xs.map Item.int ++ tail) (hx : s.G tmp = []) :
    IExec I Fin.elim0 (copyReverseInts src dst tmp) s
      (s.upd dst (xs.reverse.map Item.int ++ s.G dst))
      (duplicateMoveIntsCost xs + moveIntsCost xs.reverse) := by
  let s1 := (((s.upd src tail).upd dst (xs.reverse.map Item.int ++ s.G dst)).upd tmp
    (xs.reverse.map Item.int ++ s.G tmp))
  have hd := duplicateMoveInts_exec I src dst tmp hsd hst hdt s xs tail ht hs
  have hm := moveInts_exec I tmp src (Ne.symm hst) s1 xs.reverse [] (by decide)
    (by simp [s1,hx])
  have hrun := IExec.seq hd hm
  have he : (s1.upd tmp []).upd src (xs.reverse.reverse.map Item.int ++ s1.G src) =
      s.upd dst (xs.reverse.map Item.int ++ s.G dst) := by
    cases s
    simp only [s1,IState.upd]
    congr 1
    funext t
    by_cases ha : t=src <;> by_cases hb : t=dst <;> by_cases hc : t=tmp <;>
      simp_all
  simpa only [he,copyReverseInts,duplicateMoveInts] using hrun






















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArrayLookup







attribute [local simp] DB Out Cache Count Back Tmp





















lemma reverseFrames_reverse (arrays : List (List ℤ)) :
    reverseFrames (arrays.reverse.map List.reverse)=frames arrays := by
  simp [reverseFrames,List.map_reverse,List.map_map,Function.comp_def]







lemma forwardCost_reverse (arrays : List (List ℤ)) :
    forwardCost (arrays.reverse.map List.reverse)=backwardCost arrays := by
  simp [forwardCost,backwardCost,List.map_map,List.map_reverse,Function.comp_def]

lemma backward_exec (I : List Sym) (s : IState NS) (arrays : List (List ℤ))
    (rest bt : List Item) (ht : cls bt.head? ≠ Cls.mark)
    (hc : s.G Back=List.replicate arrays.length .mark ++ bt)
    (hd : s.G Cache=reverseFrames arrays ++ rest) :
    IExec I Fin.elim0 backward s
      ((((s.upd Back bt).upd Count (List.replicate arrays.length .mark ++ s.G Count)).upd DB
        (frames arrays ++ s.G DB)).upd Cache rest) (backwardCost arrays) := by
  have h := backward_exec_raw I s (arrays.reverse.map List.reverse) rest bt ht
    (by simpa using hc) (by simpa only [reverseFrames] using hd)
  simpa only [List.length_map,List.length_reverse,reverseFrames_reverse,forwardCost_reverse] using h



lemma program_exec (I : List Sym) (s : IState NS) (pre : List (List ℤ)) (target : List ℤ)
    (rest ct : List Item) (ht : cls ct.head? ≠ Cls.mark)
    (hc : s.G Count=List.replicate pre.length .mark ++ ct)
    (hd : s.G DB=frames pre ++ target.map Item.int ++ .mark::rest)
    (hb : s.G Back=[]) (hx : s.G Tmp=[]) :
    IExec I Fin.elim0 program s (s.upd Out (target.reverse.map Item.int ++ s.G Out)) (lookupCost pre target) := by
  let f := (((s.upd Count ct).upd Back (List.replicate pre.length .mark ++ s.G Back)).upd Cache
    (reverseFrames pre ++ s.G Cache)).upd DB (target.map Item.int ++ .mark::rest)
  have hf : IExec I Fin.elim0 forward s f (forwardCost pre) :=
    forward_exec I s pre (target.map Item.int ++ .mark::rest) ct ht hc
      (by simpa only [List.append_assoc] using hd)
  let c := f.upd Out (target.reverse.map Item.int ++ f.G Out)
  have hcopy : IExec I Fin.elim0 (copyReverseInts DB Out Tmp) f c
      (duplicateMoveIntsCost target+moveIntsCost target.reverse) :=
    copyReverseInts_exec I DB Out Tmp (by decide) (by decide) (by decide) f target (.mark::rest)
      (by simp [cls]) (by simp [f]) (by simp [f,hx])
  have hback := backward_exec I c pre (s.G Cache) [] (by simp [cls])
    (by simp [c,f,hb]) (by simp [c,f])
  have he : ((((c.upd Back []).upd Count (List.replicate pre.length .mark ++ c.G Count)).upd DB
      (frames pre ++ c.G DB)).upd Cache (s.G Cache)) =
    s.upd Out (target.reverse.map Item.int ++ s.G Out) := by
    cases s with
    | mk G ip o =>
      have hC' : G Count=List.replicate pre.length .mark ++ ct := hc
      have hD' : G DB=frames pre ++ target.map Item.int ++ .mark::rest := hd
      have hB' : G Back=[] := hb
      simp only [Count,DB,Back] at hC' hD' hB'
      simp only [c,f,IState.upd]
      congr 1
      funext i
      by_cases hO : i=Out
      · subst i; simp [Function.update_apply]
      by_cases hC : i=Count
      · subst i; simp [Function.update_apply,hC']
      by_cases hB : i=Back
      · subst i; simp [Function.update_apply,hB']
      by_cases hD : i=DB
      · subst i; simp [Function.update_apply,hD',List.append_assoc]
      by_cases hK : i=Cache
      · subst i; simp [Function.update_apply]
      simp [Function.update_apply,hO,hC,hB,hD,hK]
  rw [he] at hback
  have hrun := IExec.seq hf (IExec.seq hcopy hback)
  change IExec I Fin.elim0 program s _ _ at hrun
  convert hrun using 1
  simp only [lookupCost]
  omega








end KoanaKPaths.Machine.ArrayLookup

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.ArrayLookup.NS) (pre : List.{0} (List.{0} Int))
  (target : List.{0} Int) (rest ct : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item ct)) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} Int) pre) NLogN.Item.mark) ct))
  (hd :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.DB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (KoanaKPaths.Machine.ArrayLookup.frames pre) (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int target))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark rest)))
  (hb :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Tmp)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.ArrayLookup.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.ArrayLookup.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.ArrayLookup.program s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Out
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int target))
        (@NLogN.IState.G KoanaKPaths.Machine.ArrayLookup.NS s KoanaKPaths.Machine.ArrayLookup.Out)))
    (KoanaKPaths.Machine.ArrayLookup.lookupCost pre target) := by
  exact @KoanaKPaths.Machine.ArrayLookup.program_exec
