-- Prove2me | solution 1 for KoanaKPaths.Machine.Median.compareCounts_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.005835+00:00
-- url     : https://prove2.me/submissions/f05828a9-2ef4-4531-badb-7900b1013a11

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
import Theorems.Thm_KoanaKPaths_Machine_Median_peelCount_runs
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
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


lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩





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


attribute [local simp] Count Threshold Saved Flag







lemma compareCounts_runs (I : List Sym) (s : IState NS) (c t : ℕ)
    (hc : s.G Count=List.replicate c .mark) (ht : s.G Threshold=List.replicate t .mark)
    (hs : s.G Saved=[]) :
    IRuns I Fin.elim0 compareCounts s
      ((s.upd Count []).upd Flag (if t≤ c then .mark::s.G Flag else s.G Flag))
      (100*c+100) := by
  let s1 := ((s.upd Count []).upd Threshold (List.replicate (t-c) .mark)).upd Saved
    (List.replicate (min t c) .mark)
  let s2 := s1.upd Flag (if t≤ c then .mark::s.G Flag else s.G Flag)
  let s3 := (s2.upd Saved []).upd Threshold
    (List.replicate (min t c) .mark ++ s2.G Threshold)
  have h1 : IRuns I Fin.elim0 peelCount s s1 (60*c+30) := by
    simpa only [hs,List.append_nil] using peelCount_runs I s c t hc ht
  have h2 : IExec I Fin.elim0
      (.ite Threshold (fun c => decide (c=Cls.mark)) .skip (.op (.mark Flag))) s1 s2 26 := by
    by_cases h : t≤ c
    · have hh : t-c=0 := by omega
      have hcl : decide (s1.cl Threshold=Cls.mark)=false := by simp [IState.cl,s1,hh,cls]
      have hm : IExec I Fin.elim0 (.op (.mark Flag)) s1 (s1.upd Flag (.mark::s1.G Flag)) 1 := .op (.mark)
      apply IExec.iteF hcl
      simpa [s2,h,s1] using hm
    · have hh : 0< t-c := by omega
      obtain ⟨u,hu⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t-c≠0)
      have hcl : decide (s1.cl Threshold=Cls.mark)=true := by
        simp [IState.cl,s1,hu,List.replicate_succ,cls]
      have he : s2=s1 := by
        have hg : s1.G Flag=s.G Flag := by simp [s1]
        dsimp [s2]; rw [if_neg h,← hg]; exact upd_same _ _
      rw [he]
      exact .iteT hcl (.skip s1)
  have h3 : IExec I Fin.elim0 (moveMarks Saved Threshold) s2 s3 (32*min t c+30) := by
    exact moveMarks_exec I Saved Threshold (by decide) s2 (min t c) [] (by simp [cls])
      (by simp [s2,s1])
  have he : s3=(s.upd Count []).upd Flag (if t≤ c then .mark::s.G Flag else s.G Flag) := by
    have hn : min t c+(t-c)=t := by omega
    apply itemState_ext
    · intro i
      by_cases hC : i=Count
      · subst i; simp [s3,s2,s1]
      by_cases hT : i=Threshold
      · subst i; simp [s3,s2,s1,← List.replicate_add,hn,ht]
      by_cases hS : i=Saved
      · subst i; simp [s3,s2,s1,hs]
      by_cases hF : i=Flag
      · subst i; simp [s3,s2,s1]
      simp [s3,s2,s1,IState.upd,Function.update_apply,hC,hT,hS,hF]
    · rfl
    · rfl
  have hh := Native.seq h1 (Native.seq (Native.of_exec h2) (Native.of_exec h3))
  change IRuns I Fin.elim0 compareCounts s _ _ at hh
  rw [he] at hh
  apply Native.mono hh
  have hh := Nat.min_le_right t c
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
      (@List.replicate.{0} NLogN.Item t NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.compareCounts s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count (@List.nil.{0} NLogN.Item))
      KoanaKPaths.Machine.Median.Flag
      (@ite.{1} (List.{0} NLogN.Item) (@LE.le.{0} Nat instLENat t c) (Nat.decLe t c)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag))
        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))) c)
      (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))) := by
  exact @KoanaKPaths.Machine.Median.compareCounts_runs
