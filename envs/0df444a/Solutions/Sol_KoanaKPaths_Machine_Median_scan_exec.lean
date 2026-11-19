-- Prove2me | solution 1 for KoanaKPaths.Machine.Median.scan_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.471202+00:00
-- url     : https://prove2.me/submissions/2ee054b3-5cca-4b7b-b666-1ab3c09ed002

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
import Theorems.Thm_KoanaKPaths_Machine_compareLE_exec
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







lemma scan_exec (I : List Sym) (s : IState NS) (xs : List ℤ) (mid : ℤ)
    (rt mt : List Item) (ht : cls rt.head?=Cls.mark)
    (hr : s.G Records=xs.map Item.int ++ rt) (hm : s.G Mid=.int mid::mt) :
    IExec I Fin.elim0 scan s
      (((s.upd Records rt).upd Back (xs.reverse.map Item.int ++ s.G Back)).upd Count
        (List.replicate (countLE mid xs) .mark ++ s.G Count)) (scanCost mid xs) := by
  induction xs generalizing s with
  | nil =>
    have hcond : intClass (s.cl Records)=false := by simp [IState.cl,hr,ht,intClass]
    have he : (((s.upd Records rt).upd Back (([] : List ℤ).reverse.map Item.int ++ s.G Back)).upd Count
        (List.replicate (countLE mid []) .mark ++ s.G Count))=s := by
      simp only [List.reverse_nil,List.map_nil,List.nil_append,countLE,List.filter_nil,List.length_nil,
        List.replicate_zero,upd_same]
      rw [← show s.G Records=rt from by simpa using hr]
      simp only [upd_same]
    rw [he]
    exact .loopF hcond
  | cons x xs ih =>
    let s1 := (s.upd Records (xs.map Item.int ++ rt)).upd Value (.int x::s.G Value)
    let s2 := s1.upd Count (if x≤ mid then .mark::s.G Count else s.G Count)
    let s3 := (s2.upd Value (s.G Value)).upd Back (.int x::s.G Back)
    have h1 : IExec I Fin.elim0 (.op (.mv Records Value)) s s1 (2*moveCost (zsz x)+19) :=
      .op (.mv (by decide) (by simpa using hr))
    have h2 : IExec I Fin.elim0 (compareLE Value Mid Tmp Work Count) s1 s2 (compareCost x mid) := by
      have hh := compareLE_exec I Value Mid Tmp Work Count
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        s1 x mid (s.G Value) mt (by simp [s1]) (by simp [s1,hm])
      simpa [s2,s1] using hh
    have h3 : IExec I Fin.elim0 (.op (.mv Value Back)) s2 s3 (2*moveCost (zsz x)+19) := by
      have hh := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
        (IOp.Step.mv (s := s2) (i := Value) (j := Back) (a := x) (L := s.G Value)
          (by decide) (by simp [s2,s1]))
      simpa [s3,s2,s1] using hh
    have htail := ih s3 (by simp [s3,s2,s1]) (by simp [s3,s2,s1,hm])
    have hcond : intClass (s.cl Records)=true := by
      simp only [IState.cl,hr,List.map_cons,List.cons_append,List.head?_cons]
      exact intClass_int x
    have hh := IExec.loopT hcond (IExec.seq h1 (IExec.seq h2 h3)) htail
    have hcount : countLE mid (x::xs)=(if x≤ mid then 1 else 0)+countLE mid xs := by
      by_cases hx : x≤ mid <;> simp [countLE,hx,Nat.add_comm]
    have he : (((s3.upd Records rt).upd Back (xs.reverse.map Item.int ++ s3.G Back)).upd Count
        (List.replicate (countLE mid xs) .mark ++ s3.G Count))=
      (((s.upd Records rt).upd Back ((x::xs).reverse.map Item.int ++ s.G Back)).upd Count
        (List.replicate (countLE mid (x::xs)) .mark ++ s.G Count)) := by
      apply itemState_ext
      · intro i
        by_cases hR : i=Records
        · subst i; simp [s3,s2,s1]
        by_cases hB : i=Back
        · subst i; simp [s3,s2,s1,List.reverse_cons,List.map_append,List.append_assoc]
        by_cases hC : i=Count
        · subst i
          by_cases hx : x≤ mid <;>
            simp [s3,s2,s1,hcount,hx,Nat.one_add,List.replicate_succ,replicate_cons_same]
        by_cases hV : i=Value
        · subst i; simp [s3,s2,s1]
        simp [s3,s2,s1,IState.upd,Function.update_apply,hR,hB,hC,hV]
      · rfl
      · rfl
    rw [he] at hh
    change IExec I Fin.elim0 scan s _ _ at hh
    convert hh using 1 <;> simp only [scanCost] <;> omega



end KoanaKPaths.Machine.Median

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (xs : List.{0} Int) (mid : Int)
  (rt mt : List.{0} NLogN.Item) (ht : @Eq.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item rt)) NLogN.Cls.mark)
  (hr :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) rt))
  (hm :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int mid) mt)),
  @NLogN.IExec KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.scan s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records rt)
        KoanaKPaths.Machine.Median.Back
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@List.reverse.{0} Int xs))
          (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Back)))
      KoanaKPaths.Machine.Median.Count
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (KoanaKPaths.Machine.Median.countLE mid xs) NLogN.Item.mark)
        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)))
    (KoanaKPaths.Machine.Median.scanCost mid xs) := by
  exact @KoanaKPaths.Machine.Median.scan_exec
