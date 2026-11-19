-- Prove2me | solution 1 for KoanaKPaths.Machine.Median.peelCount_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:26:49.603502+00:00
-- url     : https://prove2.me/submissions/a11f6052-6386-4ae3-b6c1-38060c718b4f

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


attribute [local simp] Count Threshold Saved Flag



lemma peelCount_runs (I : List Sym) (s : IState NS) (c t : ℕ)
    (hc : s.G Count=List.replicate c .mark) (ht : s.G Threshold=List.replicate t .mark) :
    IRuns I Fin.elim0 peelCount s
      (((s.upd Count []).upd Threshold (List.replicate (t-c) .mark)).upd Saved
        (List.replicate (min t c) .mark ++ s.G Saved)) (60*c+30) := by
  induction c generalizing s t with
  | zero =>
    have hcond : decide (s.cl Count=Cls.mark)=false := by simp [IState.cl,hc,cls]
    have he : (((s.upd Count []).upd Threshold (List.replicate (t-0) .mark)).upd Saved
        (List.replicate (min t 0) .mark ++ s.G Saved))=s := by
      simp only [Nat.sub_zero,Nat.min_zero,List.replicate_zero,List.nil_append]
      have hc' : s.G Count=[] := by simpa using hc
      rw [← hc',← ht]
      simp
    rw [he]
    exact Native.loopF hcond
  | succ c ih =>
    let s1 := s.upd Count (List.replicate c .mark)
    have h1 : IExec I Fin.elim0 (.op (.unmark Count)) s s1 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hc))
    have hcond : decide (s.cl Count=Cls.mark)=true := by simp [IState.cl,hc,List.replicate_succ,cls]
    cases t with
    | zero =>
      have hT : decide (s1.cl Threshold=Cls.mark)=false := by simp [IState.cl,s1,ht,cls]
      have h2 := Native.iteF (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (q := .skip) (i := Threshold) (f := fun c => decide (c=Cls.mark)) (p := .seq (.op (.unmark Threshold)) (.op (.mark Saved))) hT (Native.skip s1)
      have htail := ih s1 0 (by simp [s1]) (by simp [s1,ht])
      have hh := Native.loopT hcond (Native.seq (Native.of_exec h1) h2) htail
      have he : (((s1.upd Count []).upd Threshold (List.replicate (0-c) .mark)).upd Saved
          (List.replicate (min 0 c) .mark ++ s1.G Saved))=
        (((s.upd Count []).upd Threshold (List.replicate (0-(c+1)) .mark)).upd Saved
          (List.replicate (min 0 (c+1)) .mark ++ s.G Saved)) := by
        simp [s1]
      rw [he] at hh
      apply Native.mono hh
      omega
    | succ t =>
      let s2 := s1.upd Threshold (List.replicate t .mark)
      let s3 := s2.upd Saved (.mark::s.G Saved)
      have h21 : IExec I Fin.elim0 (.op (.unmark Threshold)) s1 s2 1 :=
        .op (.unmark (by simp [s1,ht,List.replicate_succ]))
      have h22 : IExec I Fin.elim0 (.op (.mark Saved)) s2 s3 1 := by
        simpa [s3,s2,s1] using
          (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.mark (s := s2) (i := Saved)))
      have hT : decide (s1.cl Threshold=Cls.mark)=true := by simp [IState.cl,s1,ht,List.replicate_succ,cls]
      have h2 := Native.iteT (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (i := Threshold) (f := fun c => decide (c=Cls.mark)) (q := .skip) hT (Native.seq (Native.of_exec h21) (Native.of_exec h22))
      have htail := ih s3 t (by simp [s3,s2,s1]) (by simp [s3,s2])
      have hh := Native.loopT hcond (Native.seq (Native.of_exec h1) h2) htail
      have he : (((s3.upd Count []).upd Threshold (List.replicate (t-c) .mark)).upd Saved
          (List.replicate (min t c) .mark ++ s3.G Saved))=
        (((s.upd Count []).upd Threshold (List.replicate (t+1-(c+1)) .mark)).upd Saved
          (List.replicate (min (t+1) (c+1)) .mark ++ s.G Saved)) := by
        apply itemState_ext
        · intro i
          by_cases hC : i=Count
          · subst i; simp [s3,s2,s1]
          by_cases hT : i=Threshold
          · subst i; simp [s3,s2,s1]
          by_cases hS : i=Saved
          · subst i; simp [s3,s2,s1,min_add_add_right,List.replicate_succ,replicate_cons_same]
          simp [s3,s2,s1,IState.upd,Function.update_apply,hC,hT,hS]
        · rfl
        · rfl
      rw [he] at hh
      apply Native.mono hh
      omega





end KoanaKPaths.Machine.Median

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (c t : Nat)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)
      (@List.replicate.{0} NLogN.Item c NLogN.Item.mark))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Threshold)
      (@List.replicate.{0} NLogN.Item t NLogN.Item.mark)),
  @NLogN.IRuns KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.peelCount s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count (@List.nil.{0} NLogN.Item))
        KoanaKPaths.Machine.Median.Threshold
        (@List.replicate.{0} NLogN.Item (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t c)
          NLogN.Item.mark))
      KoanaKPaths.Machine.Median.Saved
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@Min.min.{0} Nat instMinNat t c) NLogN.Item.mark)
        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) c)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Median.peelCount_runs
