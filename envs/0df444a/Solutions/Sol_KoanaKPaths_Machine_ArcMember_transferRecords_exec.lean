-- Prove2me | solution 1 for KoanaKPaths.Machine.ArcMember.transferRecords_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.167015+00:00
-- url     : https://prove2.me/submissions/410fefe1-f851-42d7-abbe-1dd62ec420a7

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












attribute [local simp] DB Back U V QueryU QueryV Found FlagU FlagV Tmp Work









lemma takeRecord_exec (I : List Sym) (src : Fin NS) (hu : src≠U) (hv : src≠V)
    (s : IState NS) (u v : ℤ) (tail : List Item) (hs : s.G src=.int v::.int u::.mark::tail) :
    IExec I Fin.elim0 (takeRecord src) s
      (((s.upd src tail).upd U (.int u::s.G U)).upd V (.int v::s.G V)) (recordCost u v) := by
  let s1 := (s.upd src (.int u::.mark::tail)).upd V (.int v::s.G V)
  let s2 := (s1.upd src (.mark::tail)).upd U (.int u::s.G U)
  let s3 := s2.upd src tail
  have h1 : IExec I Fin.elim0 (.op (.mv src V)) s s1 (2*moveCost (zsz v)+19) := .op (.mv hv hs)
  have h2 : IExec I Fin.elim0 (.op (.mv src U)) s1 s2 (2*moveCost (zsz u)+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s1) (i := src) (j := U) (a := u) (L := .mark::tail)
        hu (by simp [s1,hu,hv]))
    simpa [s2,s1,hu,Ne.symm hu] using h
  have h3 : IExec I Fin.elim0 (.op (.unmark src)) s2 s3 1 :=
    .op (.unmark (by simp [s2,hu]))
  have he : s3=(((s.upd src tail).upd U (.int u::s.G U)).upd V (.int v::s.G V)) := by
    apply itemState_ext
    · intro i
      by_cases hS : i=src
      · subst i; simp [s3,s2,s1,hu,hv]
      by_cases hU : i=U
      · subst i; simp [s3,s2,s1,Ne.symm hu]
      by_cases hV : i=V
      · subst i; simp [s3,s2,s1,Ne.symm hv]
      simp [s3,s2,s1,IState.upd,Function.update_apply,hS,hU,hV]
    · rfl
    · rfl
  have h := IExec.seq h1 (IExec.seq h2 h3)
  rw [he] at h
  change IExec I Fin.elim0 (takeRecord src) s _ _ at h
  convert h using 1 <;> simp only [recordCost] <;> omega

lemma pushRecord_exec (I : List Sym) (dst : Fin NS) (hu : dst≠U) (hv : dst≠V)
    (s : IState NS) (u v : ℤ) (ut vt : List Item)
    (hU : s.G U=.int u::ut) (hV : s.G V=.int v::vt) :
    IExec I Fin.elim0 (pushRecord dst) s
      (((s.upd U ut).upd V vt).upd dst (.int v::.int u::.mark::s.G dst)) (recordCost u v) := by
  let s1 := s.upd dst (.mark::s.G dst)
  let s2 := (s1.upd U ut).upd dst (.int u::.mark::s.G dst)
  let s3 := (s2.upd V vt).upd dst (.int v::.int u::.mark::s.G dst)
  have h1 : IExec I Fin.elim0 (.op (.mark dst)) s s1 1 := .op (.mark)
  have h2 : IExec I Fin.elim0 (.op (.mv U dst)) s1 s2 (2*moveCost (zsz u)+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s1) (i := U) (j := dst) (a := u) (L := ut)
        (Ne.symm hu) (by simp [s1,Ne.symm hu,hU]))
    simpa [s2,s1] using h
  have h3 : IExec I Fin.elim0 (.op (.mv V dst)) s2 s3 (2*moveCost (zsz v)+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s2) (i := V) (j := dst) (a := v) (L := vt)
        (Ne.symm hv) (by simp [s2,s1,Ne.symm hv,hV]))
    simpa [s3,s2] using h
  have he : s3=(((s.upd U ut).upd V vt).upd dst (.int v::.int u::.mark::s.G dst)) := by
    apply itemState_ext
    · intro i
      by_cases hD : i=dst
      · subst i; simp [s3,s2,s1]
      by_cases hU : i=U
      · subst i; simp [s3,s2,s1,Ne.symm hu]
      by_cases hV : i=V
      · subst i; simp [s3,s2,s1,Ne.symm hv]
      simp [s3,s2,s1,IState.upd,Function.update_apply,hD,hU,hV]
    · rfl
    · rfl
  have h := IExec.seq h1 (IExec.seq h2 h3)
  rw [he] at h
  change IExec I Fin.elim0 (pushRecord dst) s _ _ at h
  convert h using 1 <;> simp only [recordCost] <;> omega

end KoanaKPaths.Machine.ArcMember

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] U V





lemma transferRecords_exec (I : List Sym) (src dst : Fin NS)
    (hsd : src≠dst) (hsu : src≠U) (hsv : src≠V) (hdu : dst≠U) (hdv : dst≠V)
    (s : IState NS) (ps : List (ℤ×ℤ)) (tail : List Item)
    (ht : Median.intClass (cls tail.head?)=false) (hs : s.G src=records ps++tail) :
    IExec I Fin.elim0 (transferRecords src dst) s
      ((s.upd src tail).upd dst (records ps.reverse++s.G dst)) (transferCost ps) := by
  induction ps generalizing s with
  | nil =>
    have hcl : Median.intClass (s.cl src)=false := by simpa [IState.cl,hs,records] using ht
    have he : (s.upd src tail).upd dst (records ([] : List (ℤ×ℤ)).reverse++s.G dst)=s := by
      have hh : s.G src=tail := by simpa [records] using hs
      simp only [records,List.reverse_nil,List.flatMap_nil,List.nil_append]
      rw [← hh]
      simp [hsd,Ne.symm hsd]
    rw [he]
    exact .loopF hcl
  | cons p ps ih =>
    rcases p with ⟨u,v⟩
    let s1 := ((s.upd src (records ps++tail)).upd U (.int u::s.G U)).upd V (.int v::s.G V)
    let s2 := (s.upd src (records ps++tail)).upd dst (.int v::.int u::.mark::s.G dst)
    have h1 : IExec I Fin.elim0 (takeRecord src) s s1 (recordCost u v) :=
      takeRecord_exec I src hsu hsv s u v (records ps++tail) (by simpa [records] using hs)
    have h2 : IExec I Fin.elim0 (pushRecord dst) s1 s2 (recordCost u v) := by
      have h := pushRecord_exec I dst hdu hdv s1 u v (s.G U) (s.G V)
        (by simp [s1]) (by simp [s1])
      have he : (((s1.upd U (s.G U)).upd V (s.G V)).upd dst (.int v::.int u::.mark::s1.G dst))=s2 := by
        apply itemState_ext
        · intro i
          by_cases hS : i=src
          · subst i; simp [s2,s1,hsd,hsu,hsv]
          by_cases hD : i=dst
          · subst i; simp [s2,s1,Ne.symm hsd,hdu,hdv]
          by_cases hU : i=U
          · subst i; simp [s2,s1,Ne.symm hsu,Ne.symm hdu]
          by_cases hV : i=V
          · subst i; simp [s2,s1,Ne.symm hsv,Ne.symm hdv]
          simp [s2,s1,IState.upd,Function.update_apply,hS,hD,hU,hV]
        · rfl
        · rfl
      rw [he] at h
      exact h
    have htail := ih s2 (by simp [s2,hsd])
    have hcl : Median.intClass (s.cl src)=true := by
      simp only [IState.cl,hs,records,List.flatMap_cons,List.cons_append,List.head?_cons]
      exact Median.intClass_int v
    have h := IExec.loopT hcl (IExec.seq h1 h2) htail
    have he : (s2.upd src tail).upd dst (records ps.reverse++s2.G dst)=
        (s.upd src tail).upd dst (records ((u,v)::ps).reverse++s.G dst) := by
      apply itemState_ext
      · intro i
        by_cases hS : i=src
        · subst i; simp [s2,hsd]
        by_cases hD : i=dst
        · subst i; simp [s2,records,List.reverse_cons,List.flatMap_append,List.append_assoc]
        simp [s2,IState.upd,Function.update_apply,hS,hD]
      · rfl
      · rfl
    rw [he] at h
    change IExec I Fin.elim0 (transferRecords src dst) s _ _ at h
    convert h using 1 <;> simp only [transferCost] <;> omega



end KoanaKPaths.Machine.ArcMember

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (src dst : Fin KoanaKPaths.Machine.ArcMember.NS)
  (hsd : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) src dst)
  (hsu : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) src KoanaKPaths.Machine.ArcMember.U)
  (hsv : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) src KoanaKPaths.Machine.ArcMember.V)
  (hdu : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) dst KoanaKPaths.Machine.ArcMember.U)
  (hdv : @Ne.{1} (Fin KoanaKPaths.Machine.ArcMember.NS) dst KoanaKPaths.Machine.ArcMember.V)
  (s : NLogN.IState KoanaKPaths.Machine.ArcMember.NS) (ps : List.{0} (Prod.{0, 0} Int Int)) (tail : List.{0} NLogN.Item)
  (ht : @Eq.{1} Bool (KoanaKPaths.Machine.Median.intClass (NLogN.cls (@List.head?.{0} NLogN.Item tail))) Bool.false)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArcMember.records ps) tail)),
  @NLogN.IExec KoanaKPaths.Machine.ArcMember.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.ArcMember.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (KoanaKPaths.Machine.ArcMember.transferRecords src dst) s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS s src tail)
      dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArcMember.records (@List.reverse.{0} (Prod.{0, 0} Int Int) ps))
        (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s dst)))
    (KoanaKPaths.Machine.ArcMember.transferCost ps) := by
  exact @KoanaKPaths.Machine.ArcMember.transferRecords_exec
