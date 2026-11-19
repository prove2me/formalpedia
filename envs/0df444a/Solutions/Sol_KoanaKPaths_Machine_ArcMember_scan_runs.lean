-- Prove2me | solution 1 for KoanaKPaths.Machine.ArcMember.scan_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.438143+00:00
-- url     : https://prove2.me/submissions/64608d5f-b4c1-448c-b702-95a9f2577f8b

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_ArcMember_inspectRecord_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.Machine.Native
open NLogN
variable {S P : ℕ} {I : List Sym} {iprog : Fin P→IStmt S P} {p q : IStmt S P} {s s1 s2 : IState S} {c d : ℕ}

lemma mono (h : IRuns I iprog p s s1 c) (hc : c ≤ d) : IRuns I iprog p s s1 d := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht.trans hc,h⟩
lemma of_exec (h : IExec I iprog p s s1 c) : IRuns I iprog p s s1 c := ⟨c,le_rfl,h⟩





lemma loopT {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = true)
    (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog (.loop i f p) s1 s2 d) :
    IRuns I iprog (.loop i f p) s s2 (c+d+30) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d'+30,by omega,.loopT hf h1 h2⟩
lemma loopF {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = false) :
    IRuns I iprog (.loop i f p) s s 30 := of_exec (.loopF hf)

end KoanaKPaths.Machine.Native

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






















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S P : ℕ}








lemma itemState_ext {s t : IState S} (hG : ∀ i, s.G i=t.G i) (hip : s.ip=t.ip)
    (hout : s.out=t.out) : s=t := by
  cases s with
  | mk G ip o =>
    cases t with
    | mk H jp p =>
      have hh : G=H := funext hG
      cases hh
      cases hip
      cases hout
      rfl

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median











attribute [local simp] Records Lo Hi Mid Value Tmp Work Count Threshold Back


lemma intClass_int (x : ℤ) : intClass (cls (some (.int x)))=true := by
  rcases lt_trichotomy x 0 with h|h|h
  · simp [intClass,cls,h,h.ne]
  · subst x; simp [intClass,cls]
  · simp [intClass,cls,h.ne',not_lt.mpr h.le]











end KoanaKPaths.Machine.Median

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] DB Back QueryU QueryV Found FlagU FlagV








lemma scan_runs (I : List Sym) (s : IState NS) (ps : List (ℤ×ℤ)) (qu qv : ℤ) (f : Bool)
    (tail qtU qtV ft : List Item) (ht : Median.intClass (cls tail.head?)=false)
    (hdb : s.G DB=records ps++tail) (hqu : s.G QueryU=.int qu::qtU) (hqv : s.G QueryV=.int qv::qtV)
    (hfound : s.G Found=.int (f.toNat : ℤ)::ft) (hu : s.G FlagU=[]) (hv : s.G FlagV=[]) :
    IRuns I Fin.elim0 scan s
      (((s.upd DB tail).upd Back (records ps.reverse++s.G Back)).upd Found
        (.int ((scanFound qu qv ps f).toNat : ℤ)::ft)) (scanCost qu qv ps) := by
  induction ps generalizing s f with
  | nil =>
    have hcl : Median.intClass (s.cl DB)=false := by simpa [IState.cl,hdb,records] using ht
    have he : (((s.upd DB tail).upd Back (records ([] : List (ℤ×ℤ)).reverse++s.G Back)).upd Found
        (.int ((scanFound qu qv [] f).toNat : ℤ)::ft))=s := by
      simp only [records,List.reverse_nil,List.flatMap_nil,List.nil_append,scanFound,List.foldl_nil]
      have hd : s.G DB=tail := by simpa [records] using hdb
      rw [← hd,← hfound]
      simp
    rw [he]
    exact Native.loopF hcl
  | cons p ps ih =>
    rcases p with ⟨u,v⟩
    let nf := nextFound (decide (u=qu)) (decide (v=qv)) f
    let s1 := ((s.upd DB (records ps++tail)).upd Back (.int v::.int u::.mark::s.G Back)).upd Found
      (.int (nf.toNat : ℤ)::ft)
    have h1 : IRuns I Fin.elim0 inspectRecord s s1
        (2*recordCost u v+compareCost u qu+compareCost v qv+200) :=
      inspectRecord_runs I s u v qu qv f (records ps++tail) qtU qtV ft
        (by simpa [records] using hdb) hqu hqv hfound hu hv
    have htail := ih s1 nf (by simp [s1]) (by simp [s1,hqu]) (by simp [s1,hqv])
      (by simp [s1]) (by simp [s1,hu]) (by simp [s1,hv])
    have hcl : Median.intClass (s.cl DB)=true := by
      simp only [IState.cl,hdb,records,List.flatMap_cons,List.cons_append,List.head?_cons]
      exact Median.intClass_int v
    have h := Native.loopT hcl h1 htail
    have he : (((s1.upd DB tail).upd Back (records ps.reverse++s1.G Back)).upd Found
        (.int ((scanFound qu qv ps nf).toNat : ℤ)::ft))=
      (((s.upd DB tail).upd Back (records ((u,v)::ps).reverse++s.G Back)).upd Found
        (.int ((scanFound qu qv ((u,v)::ps) f).toNat : ℤ)::ft)) := by
      apply itemState_ext
      · intro i
        by_cases hD : i=DB
        · subst i; simp [s1]
        by_cases hB : i=Back
        · subst i; simp [s1,records,List.reverse_cons,List.flatMap_append,List.append_assoc]
        by_cases hF : i=Found
        · subst i; simp [s1,scanFound,List.foldl_cons,arcMatch,nf,nextFound]
        simp [s1,IState.upd,Function.update_apply,hD,hB,hF]
      · rfl
      · rfl
    rw [he] at h
    change IRuns I Fin.elim0 scan s _ _ at h
    apply Native.mono h
    simp only [scanCost]
    omega







end KoanaKPaths.Machine.ArcMember

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.ArcMember.NS) (ps : List.{0} (Prod.{0, 0} Int Int))
  (qu qv : Int) (f : Bool) (tail qtU qtV ft : List.{0} NLogN.Item)
  (ht : @Eq.{1} Bool (KoanaKPaths.Machine.Median.intClass (NLogN.cls (@List.head?.{0} NLogN.Item tail))) Bool.false)
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.DB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArcMember.records ps) tail))
  (hqu :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.QueryU)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int qu) qtU))
  (hqv :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.QueryV)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int qv) qtV))
  (hfound :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.Found)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (Bool.toNat f))) ft))
  (hu :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.FlagU)
      (@List.nil.{0} NLogN.Item))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.FlagV)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.ArcMember.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.ArcMember.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.ArcMember.scan s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.DB tail)
        KoanaKPaths.Machine.ArcMember.Back
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (KoanaKPaths.Machine.ArcMember.records (@List.reverse.{0} (Prod.{0, 0} Int Int) ps))
          (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.Back)))
      KoanaKPaths.Machine.ArcMember.Found
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt (Bool.toNat (KoanaKPaths.Machine.ArcMember.scanFound qu qv ps f))))
        ft))
    (KoanaKPaths.Machine.ArcMember.scanCost qu qv ps) := by
  exact @KoanaKPaths.Machine.ArcMember.scan_runs
