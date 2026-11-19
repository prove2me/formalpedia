-- Prove2me | solution 1 for KoanaKPaths.Machine.ArcMember.inspectRecord_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:46:53.12604+00:00
-- url     : https://prove2.me/submissions/dfb4e97b-c991-4493-a9b7-d88b18cd4de0

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
import Theorems.Thm_KoanaKPaths_Machine_compareEq_exec
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

lemma skip (s : IState S) : IRuns I iprog .skip s s 1 := of_exec (.skip s)
lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩
lemma iteT {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = true)
    (h : IRuns I iprog p s s1 c) : IRuns I iprog (.ite i f p q) s s1 (c+25) := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t+25,by omega,.iteT hf h⟩
lemma iteF {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = false)
    (h : IRuns I iprog q s s1 c) : IRuns I iprog (.ite i f p q) s s1 (c+25) := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t+25,by omega,.iteF hf h⟩



end KoanaKPaths.Machine.Native

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S P : ℕ}



































lemma nbits_eq_bits (n : ℕ) : nbits n = Nat.bits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [nbits]
  | bit b n hn ih =>
    have hne : Nat.bit b n ≠ 0 := by
      intro hz
      cases b <;> simp_all [Nat.bit]
    rw [nbits,dif_neg hne,Nat.bit_mod_two,Nat.bit_div_two,ih,Nat.bits_append_bit n b hn]
    cases b <;> rfl

















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




















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]





































end KoanaKPaths.Machine.Wedge

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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}



lemma clearMarks_exec (I : List Sym) (src : Fin S) (s : IState S) (m : ℕ) (tail : List Item)
    (ht : cls tail.head? ≠ Cls.mark) (hs : s.G src=List.replicate m .mark ++ tail) :
    IExec I Fin.elim0 (clearMarks src) s (s.upd src tail) (31*m+30) := by
  induction m generalizing s with
  | zero =>
    have he : s.upd src tail=s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    rw [he]
    exact IExec.loopF (by simp [IState.cl,hs,ht])
  | succ m ih =>
    let s1 := s.upd src (List.replicate m .mark ++ tail)
    have h1 : IExec I Fin.elim0 (.op (.unmark src)) s s1 1 := .op (.unmark (by simpa [List.replicate_succ] using hs))
    have htail := ih s1 (by simp [s1])
    have hrun := IExec.loopT (by simp [IState.cl,hs,List.replicate_succ,cls]) h1 htail
    change IExec I Fin.elim0 (clearMarks src) s _ _ at hrun
    simpa only [s1,upd_upd,show 1+(31*m+30)+30=31*(m+1)+30 by omega] using hrun















end KoanaKPaths.Machine

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
attribute [local simp] FlagU FlagV Found







lemma markFound_runs (I : List Sym) (s : IState NS) (f : Bool) (tail : List Item)
    (hf : s.G Found=.int (f.toNat : ℤ)::tail) :
    IRuns I Fin.elim0 markFound s (s.upd Found (.int 1::tail)) 7 := by
  let s1 := s.upd Found tail
  have h1 : IExec I Fin.elim0 (.op (.drop Found)) s s1 (2*zsz (f.toNat : ℤ)+2) := .op (.drop hf)
  have h2 : IExec I Fin.elim0 (.op (.const Found 1)) s1 (s.upd Found (.int 1::tail)) 3 := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.const (s := s1) (i := Found) 1)
    simpa [s1,Wedge.zsz_eq_size] using h
  apply Native.mono (Native.seq (Native.of_exec h1) (Native.of_exec h2))
  cases f <;> simp [Wedge.zsz_eq_size]

lemma flagDecision_runs (I : List Sym) (s : IState NS) (u v f : Bool) (tail : List Item)
    (hu : s.G FlagU=flags u) (hv : s.G FlagV=flags v) (hf : s.G Found=.int (f.toNat : ℤ)::tail) :
    IRuns I Fin.elim0 flagDecision s
      (s.upd Found (.int ((nextFound u v f).toNat : ℤ)::tail)) 57 := by
  cases u with
  | false =>
    have hcl : decide (s.cl FlagU=Cls.mark)=false := by simp [IState.cl,hu,flags,cls]
    have he : s.upd Found (.int ((nextFound false v f).toNat : ℤ)::tail)=s := by
      simp only [nextFound,Bool.false_and,Bool.false_or]
      rw [← hf]; exact upd_same _ _
    rw [he]
    have h : IRuns I Fin.elim0 flagDecision s s 26 := Native.iteF hcl (Native.skip s)
    exact Native.mono h (by omega)
  | true =>
    have hcl : decide (s.cl FlagU=Cls.mark)=true := by simp [IState.cl,hu,flags,cls]
    cases v with
    | false =>
      have hclV : decide (s.cl FlagV=Cls.mark)=false := by simp [IState.cl,hv,flags,cls]
      have he : s.upd Found (.int ((nextFound true false f).toNat : ℤ)::tail)=s := by
        simp only [nextFound,Bool.and_false,Bool.false_or]
        rw [← hf]; exact upd_same _ _
      rw [he]
      have hinner : IRuns I Fin.elim0
          (.ite FlagV (fun c => decide (c=Cls.mark)) markFound .skip) s s 26 :=
        Native.iteF hclV (Native.skip s)
      have h : IRuns I Fin.elim0 flagDecision s s 51 := Native.iteT hcl hinner
      exact Native.mono h (by omega)
    | true =>
      have hclV : decide (s.cl FlagV=Cls.mark)=true := by simp [IState.cl,hv,flags,cls]
      have hm := markFound_runs I s f tail hf
      have hinner : IRuns I Fin.elim0
          (.ite FlagV (fun c => decide (c=Cls.mark)) markFound .skip) s (s.upd Found (.int 1::tail)) 32 :=
        Native.iteT hclV hm
      simpa [nextFound,flagDecision] using (Native.iteT (q := .skip) hcl hinner)



lemma mergeFlags_runs (I : List Sym) (s : IState NS) (u v f : Bool) (tail : List Item)
    (hu : s.G FlagU=flags u) (hv : s.G FlagV=flags v) (hf : s.G Found=.int (f.toNat : ℤ)::tail) :
    IRuns I Fin.elim0 mergeFlags s
      (((s.upd FlagU []).upd FlagV []).upd Found (.int ((nextFound u v f).toNat : ℤ)::tail)) 200 := by
  let s1 := s.upd Found (.int ((nextFound u v f).toNat : ℤ)::tail)
  let s2 := s1.upd FlagU []
  let s3 := s2.upd FlagV []
  have h1 := flagDecision_runs I s u v f tail hu hv hf
  have h2 : IRuns I Fin.elim0 (clearMarks FlagU) s1 s2 61 := by
    have h : IExec I Fin.elim0 (clearMarks FlagU) s1 s2 (31*u.toNat+30) :=
      clearMarks_exec I FlagU s1 u.toNat [] (by simp [cls]) (by cases u <;> simp [s1,hu,flags])
    apply Native.mono (Native.of_exec h)
    cases u <;> decide
  have h3 : IRuns I Fin.elim0 (clearMarks FlagV) s2 s3 61 := by
    have h : IExec I Fin.elim0 (clearMarks FlagV) s2 s3 (31*v.toNat+30) :=
      clearMarks_exec I FlagV s2 v.toNat [] (by simp [cls]) (by cases v <;> simp [s2,s1,hv,flags])
    apply Native.mono (Native.of_exec h)
    cases v <;> decide
  have he : s3=(((s.upd FlagU []).upd FlagV []).upd Found (.int ((nextFound u v f).toNat : ℤ)::tail)) := by
    apply itemState_ext
    · intro i
      by_cases hU : i=FlagU
      · subst i; simp [s3,s2,s1]
      by_cases hV : i=FlagV
      · subst i; simp [s3,s2,s1]
      by_cases hF : i=Found
      · subst i; simp [s3,s2,s1]
      simp [s3,s2,s1,IState.upd,Function.update_apply,hU,hV,hF]
    · rfl
    · rfl
  have h := Native.seq h1 (Native.seq h2 h3)
  rw [he] at h
  exact Native.mono h (by omega)

end KoanaKPaths.Machine.ArcMember

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] DB Back U V QueryU QueryV Found FlagU FlagV Tmp Work



lemma inspectRecord_runs (I : List Sym) (s : IState NS) (u v qu qv : ℤ) (f : Bool)
    (tail qtU qtV ft : List Item)
    (hdb : s.G DB=.int v::.int u::.mark::tail)
    (hqu : s.G QueryU=.int qu::qtU) (hqv : s.G QueryV=.int qv::qtV)
    (hfound : s.G Found=.int (f.toNat : ℤ)::ft) (hu : s.G FlagU=[]) (hv : s.G FlagV=[]) :
    IRuns I Fin.elim0 inspectRecord s
      (((s.upd DB tail).upd Back (.int v::.int u::.mark::s.G Back)).upd Found
        (.int ((nextFound (decide (u=qu)) (decide (v=qv)) f).toNat : ℤ)::ft))
      (2*recordCost u v+compareCost u qu+compareCost v qv+200) := by
  let s0 := ((s.upd DB tail).upd U (.int u::s.G U)).upd V (.int v::s.G V)
  let s1 := s0.upd FlagU (flags (decide (u=qu)))
  let s2 := s1.upd FlagV (flags (decide (v=qv)))
  let nf := nextFound (decide (u=qu)) (decide (v=qv)) f
  let s3 := ((s2.upd FlagU []).upd FlagV []).upd Found (.int (nf.toNat : ℤ)::ft)
  let s4 := ((s3.upd U (s.G U)).upd V (s.G V)).upd Back (.int v::.int u::.mark::s.G Back)
  have h0 : IExec I Fin.elim0 (takeRecord DB) s s0 (recordCost u v) :=
    takeRecord_exec I DB (by decide) (by decide) s u v tail hdb
  have h1 : IExec I Fin.elim0 (compareEq U QueryU Tmp Work FlagU) s0 s1 (compareCost u qu) := by
    have h := compareEq_exec I U QueryU Tmp Work FlagU
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      s0 u qu (s.G U) qtU (by simp [s0]) (by simp [s0,hqu])
    simpa [s1,s0,flags,hu] using h
  have h2 : IExec I Fin.elim0 (compareEq V QueryV Tmp Work FlagV) s1 s2 (compareCost v qv) := by
    have h := compareEq_exec I V QueryV Tmp Work FlagV
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      s1 v qv (s.G V) qtV (by simp [s1,s0]) (by simp [s1,s0,hqv])
    simpa [s2,s1,s0,flags,hv] using h
  have h3 : IRuns I Fin.elim0 mergeFlags s2 s3 200 :=
    mergeFlags_runs I s2 (decide (u=qu)) (decide (v=qv)) f ft
      (by simp [s2,s1]) (by simp [s2]) (by simp [s2,s1,s0,hfound])
  have h4 : IExec I Fin.elim0 (pushRecord Back) s3 s4 (recordCost u v) := by
    have h := pushRecord_exec I Back (by decide) (by decide) s3 u v (s.G U) (s.G V)
      (by simp [s3,s2,s1,s0]) (by simp [s3,s2,s1,s0])
    simpa [s4,s3,s2,s1,s0] using h
  have he : s4=(((s.upd DB tail).upd Back (.int v::.int u::.mark::s.G Back)).upd Found
        (.int (nf.toNat : ℤ)::ft)) := by
    apply itemState_ext
    · intro i
      by_cases hD : i=DB
      · subst i; simp [s4,s3,s2,s1,s0]
      by_cases hB : i=Back
      · subst i; simp [s4,s3,s2,s1,s0]
      by_cases hF : i=Found
      · subst i; simp [s4,s3,s2,s1,s0]
      by_cases hU : i=U
      · subst i; simp [s4,s3,s2,s1,s0]
      by_cases hV : i=V
      · subst i; simp [s4,s3,s2,s1,s0]
      by_cases hFU : i=FlagU
      · subst i; simp [s4,s3,s2,s1,s0,hu]
      by_cases hFV : i=FlagV
      · subst i; simp [s4,s3,s2,s1,s0,hv]
      simp [s4,s3,s2,s1,s0,IState.upd,Function.update_apply,hD,hB,hF,hU,hV,hFU,hFV]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1)
    (Native.seq (Native.of_exec h2) (Native.seq h3 (Native.of_exec h4))))
  rw [he] at h
  change IRuns I Fin.elim0 inspectRecord s _ _ at h
  apply Native.mono h
  omega



end KoanaKPaths.Machine.ArcMember

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.ArcMember.NS) (u v qu qv : Int) (f : Bool)
  (tail qtU qtV ft : List.{0} NLogN.Item)
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.DB)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int v)
        (@List.cons.{0} NLogN.Item (NLogN.Item.int u) (@List.cons.{0} NLogN.Item NLogN.Item.mark tail))))
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
    KoanaKPaths.Machine.ArcMember.inspectRecord s
    (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.DB tail)
        KoanaKPaths.Machine.ArcMember.Back
        (@List.cons.{0} NLogN.Item (NLogN.Item.int v)
          (@List.cons.{0} NLogN.Item (NLogN.Item.int u)
            (@List.cons.{0} NLogN.Item NLogN.Item.mark
              (@NLogN.IState.G KoanaKPaths.Machine.ArcMember.NS s KoanaKPaths.Machine.ArcMember.Back)))))
      KoanaKPaths.Machine.ArcMember.Found
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (Bool.toNat
              (KoanaKPaths.Machine.ArcMember.nextFound (@Decidable.decide (@Eq.{1} Int u qu) (Int.instDecidableEq u qu))
                (@Decidable.decide (@Eq.{1} Int v qv) (Int.instDecidableEq v qv)) f))))
        ft))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (KoanaKPaths.Machine.ArcMember.recordCost u v))
          (KoanaKPaths.Machine.compareCost u qu))
        (KoanaKPaths.Machine.compareCost v qv))
      (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))) := by
  exact @KoanaKPaths.Machine.ArcMember.inspectRecord_runs
