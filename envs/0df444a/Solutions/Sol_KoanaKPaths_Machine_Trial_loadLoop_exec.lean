-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.loadLoop_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.172053+00:00
-- url     : https://prove2.me/submissions/f8193b54-e97a-4bdf-a5a9-b21931ce7f5d

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
namespace KoanaKPaths.Machine.Trial






attribute [local simp] Coins SignDB SignLookup.DB SignTemplate SignCounter SignTmp







lemma loadLoop_exec (I : List Sym) (s : IState NS) (xs : List ℤ) (tail : List Item)
    (hc : s.G SignCounter=List.replicate xs.length .mark)
    (hs : s.G Coins=xs.map Item.int ++ tail) :
    IExec I Fin.elim0 loadLoop s
      (((s.upd SignCounter []).upd Coins tail).upd SignDB (signItems xs ++ s.G SignDB))
      (loadCost xs) := by
  induction xs generalizing s with
  | nil =>
    have hcl : decide (s.cl SignCounter=Cls.mark)=false := by simp [IState.cl,hc,cls]
    have he : (((s.upd SignCounter []).upd Coins tail).upd SignDB (signItems [] ++ s.G SignDB))=s := by
      have hC : s.G SignCounter=[] := by simpa using hc
      have hS : s.G Coins=tail := by simpa using hs
      simp only [signItems,List.reverse_nil,List.flatMap_nil,List.nil_append]
      rw [← hC,← hS]
      simp
    rw [he]
    exact .loopF hcl
  | cons x xs ih =>
    let s1 := s.upd SignCounter (List.replicate xs.length .mark)
    let s2 := s1.upd SignDB (.mark::s.G SignDB)
    let s3 := (s2.upd Coins (xs.map Item.int ++ tail)).upd SignDB (.int x::.mark::s.G SignDB)
    have h1 : IExec I Fin.elim0 (.op (.unmark SignCounter)) s s1 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hc))
    have h2 : IExec I Fin.elim0 (.op (.mark SignDB)) s1 s2 1 := by
      simpa [s2,s1] using
        (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.mark (s := s1) (i := SignDB)))
    have h3 : IExec I Fin.elim0 (.op (.mv Coins SignDB)) s2 s3 (2*moveCost (zsz x)+19) := by
      have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
        (IOp.Step.mv (s := s2) (i := Coins) (j := SignDB) (a := x)
          (L := xs.map Item.int ++ tail) (by decide) (by simp [s2,s1,hs]))
      simpa [s3,s2,s1] using h
    have htail := ih s3 (by simp [s3,s2,s1]) (by simp [s3])
    have hcl : decide (s.cl SignCounter=Cls.mark)=true := by simp [IState.cl,hc,List.replicate_succ,cls]
    have h := IExec.loopT hcl (IExec.seq h1 (IExec.seq h2 h3)) htail
    have he : (((s3.upd SignCounter []).upd Coins tail).upd SignDB (signItems xs ++ s3.G SignDB))=
        (((s.upd SignCounter []).upd Coins tail).upd SignDB (signItems (x::xs) ++ s.G SignDB)) := by
      apply itemState_ext
      · intro i
        by_cases hC : i=SignCounter
        · subst i; simp [s3,s2,s1]
        by_cases hS : i=Coins
        · subst i; simp [s3,s2,s1]
        by_cases hD : i=SignDB
        · subst i; simp [s3,s2,s1,signItems,List.reverse_cons,List.flatMap_append,List.append_assoc]
        simp [s3,s2,s1,IState.upd,Function.update_apply,hC,hS,hD]
      · rfl
      · rfl
    rw [he] at h
    change IExec I Fin.elim0 loadLoop s _ _ at h
    convert h using 1 <;> simp only [loadCost,List.map_cons,List.sum_cons] <;> omega







end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (xs : List.{0} Int)
  (tail : List.{0} NLogN.Item)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignCounter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} Int xs) NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) tail)),
  @NLogN.IExec KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Trial.loadLoop s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignCounter
          (@List.nil.{0} NLogN.Item))
        KoanaKPaths.Machine.Trial.Coins tail)
      KoanaKPaths.Machine.Trial.SignDB
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems xs)
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)))
    (KoanaKPaths.Machine.Trial.loadCost xs) := by
  exact @KoanaKPaths.Machine.Trial.loadLoop_exec
