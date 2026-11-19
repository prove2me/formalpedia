-- Prove2me | solution 1 for KoanaKPaths.Machine.SignLookup.forward_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:36.187745+00:00
-- url     : https://prove2.me/submissions/cac1d1ac-f816-460b-afd6-e9cda766187b

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
namespace KoanaKPaths.Machine.SignLookup







attribute [local simp] DB Out Cache Count Back Tmp

















lemma frames_cons (a : List ℤ) (arrays : List (List ℤ)) :
    frames (a::arrays)=a.map Item.int ++ .mark::frames arrays := by
  simp [frames,List.append_assoc]

lemma reverseFrames_cons (a : List ℤ) (arrays : List (List ℤ)) :
    reverseFrames (a::arrays)=reverseFrames arrays ++ a.reverse.map Item.int ++ [.mark] := by
  simp [reverseFrames,frames,List.reverse_cons,List.map_append,List.flatMap_append,List.append_assoc]




lemma forward_exec (I : List Sym) (s : IState NS) (arrays : List (List ℤ))
    (rest ct : List Item) (ht : cls ct.head? ≠ Cls.mark)
    (hc : s.G Count=List.replicate arrays.length .mark ++ ct)
    (hd : s.G DB=frames arrays ++ rest) :
    IExec I Fin.elim0 forward s
      ((((s.upd Count ct).upd Back (List.replicate arrays.length .mark ++ s.G Back)).upd Cache
        (reverseFrames arrays ++ s.G Cache)).upd DB rest) (forwardCost arrays) := by
  induction arrays generalizing s with
  | nil =>
    have hcond : decide (s.cl Count=Cls.mark)=false := by simp [IState.cl,hc,ht]
    have hcount : s.upd Count ct=s := by rw [← show s.G Count=ct from by simpa using hc]; exact upd_same _ _
    have hdb : s.upd DB rest=s := by rw [← show s.G DB=rest from by simpa [frames] using hd]; exact upd_same _ _
    simp only [List.length_nil,List.replicate_zero,List.nil_append,hcount,upd_same]
    simp only [reverseFrames,frames,List.reverse_nil,List.map_nil,List.flatMap_nil,List.nil_append,upd_same,hdb,
      forwardCost,List.sum_nil,zero_add]
    exact IExec.loopF hcond
  | cons a arrays ih =>
    let s1 := s.upd Count (List.replicate arrays.length .mark ++ ct)
    let s2 := s1.upd Back (.mark::s1.G Back)
    let s3 := s2.upd Cache (.mark::s2.G Cache)
    let s4 := (s3.upd DB (.mark::(frames arrays ++ rest))).upd Cache
      (a.reverse.map Item.int ++ s3.G Cache)
    let s5 := s4.upd DB (frames arrays ++ rest)
    have h1 : IExec I Fin.elim0 (.op (.unmark Count)) s s1 1 := by
      exact .op (.unmark (by simp [hc,List.replicate_succ]))
    have h2 : IExec I Fin.elim0 (.op (.mark Back)) s1 s2 1 := .op (.mark)
    have h3 : IExec I Fin.elim0 (.op (.mark Cache)) s2 s3 1 := .op (.mark)
    have h4 : IExec I Fin.elim0 (moveInts DB Cache) s3 s4 (moveIntsCost a) := by
      exact moveInts_exec I DB Cache (by decide) s3 a (.mark::(frames arrays ++ rest))
        (by simp [cls]) (by simp [s3,s2,s1,hd,frames_cons,List.append_assoc])
    have h5 : IExec I Fin.elim0 (.op (.unmark DB)) s4 s5 1 := by
      exact .op (.unmark (by simp [s4]))
    have hbody := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5 (IExec.skip s5)))))
    have hh := ih s5 (by simp [s5,s4,s3,s2,s1]) (by simp [s5])
    have hcond : decide (s.cl Count=Cls.mark)=true := by simp [IState.cl,hc,List.replicate_succ,cls]
    have hrun := IExec.loopT hcond hbody hh
    have he : ((((s5.upd Count ct).upd Back (List.replicate arrays.length .mark ++ s5.G Back)).upd Cache
        (reverseFrames arrays ++ s5.G Cache)).upd DB rest) =
      ((((s.upd Count ct).upd Back (List.replicate (a::arrays).length .mark ++ s.G Back)).upd Cache
        (reverseFrames (a::arrays) ++ s.G Cache)).upd DB rest) := by
      cases s with
      | mk G ip o =>
        simp only [s5,s4,s3,s2,s1,IState.upd]
        congr 1
        funext i
        by_cases hC : i=Count
        · subst i; simp [Function.update_apply]
        by_cases hB : i=Back
        · subst i; simp [Function.update_apply,List.replicate_succ,replicate_cons_same]
        by_cases hK : i=Cache
        · subst i; simp [Function.update_apply,reverseFrames_cons,List.append_assoc]
        by_cases hD : i=DB
        · subst i; simp [Function.update_apply]
        simp [Function.update_apply,hC,hB,hK,hD]
    rw [he] at hrun
    change IExec I Fin.elim0 forward s _ _ at hrun
    convert hrun using 1
    simp [forwardCost]
    omega



















end KoanaKPaths.Machine.SignLookup

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.SignLookup.NS) (arrays : List.{0} (List.{0} Int))
  (rest ct : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item ct)) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.SignLookup.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} Int) arrays) NLogN.Item.mark) ct))
  (hd :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.SignLookup.NS s KoanaKPaths.Machine.SignLookup.DB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.SignLookup.frames arrays) rest)),
  @NLogN.IExec KoanaKPaths.Machine.SignLookup.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.SignLookup.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.SignLookup.forward s
    (@NLogN.IState.upd KoanaKPaths.Machine.SignLookup.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.SignLookup.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.SignLookup.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.SignLookup.NS s KoanaKPaths.Machine.SignLookup.Count ct)
          KoanaKPaths.Machine.SignLookup.Back
          (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
            (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
            (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} Int) arrays) NLogN.Item.mark)
            (@NLogN.IState.G KoanaKPaths.Machine.SignLookup.NS s KoanaKPaths.Machine.SignLookup.Back)))
        KoanaKPaths.Machine.SignLookup.Cache
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (KoanaKPaths.Machine.SignLookup.reverseFrames arrays)
          (@NLogN.IState.G KoanaKPaths.Machine.SignLookup.NS s KoanaKPaths.Machine.SignLookup.Cache)))
      KoanaKPaths.Machine.SignLookup.DB rest)
    (KoanaKPaths.Machine.SignLookup.forwardCost arrays) := by
  exact @KoanaKPaths.Machine.SignLookup.forward_exec
