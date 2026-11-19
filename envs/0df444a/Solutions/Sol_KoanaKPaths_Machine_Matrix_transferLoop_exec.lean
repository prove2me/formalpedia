-- Prove2me | solution 1 for KoanaKPaths.Machine.Matrix.transferLoop_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:45:54.055945+00:00
-- url     : https://prove2.me/submissions/c05620a2-298f-48fd-a53e-58d096e38699

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
import Theorems.Thm_KoanaKPaths_Machine_transferArray_exec
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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArrayLookup







attribute [local simp] DB Out Cache Count Back Tmp

















lemma frames_cons (a : List ℤ) (arrays : List (List ℤ)) :
    frames (a::arrays)=a.map Item.int ++ .mark::frames arrays := by
  simp [frames,List.append_assoc]


























end KoanaKPaths.Machine.ArrayLookup

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Matrix







attribute [local simp] Prev ArrayLookup.DB Current Tmp Template Counter CopyTmp





lemma transferLoop_exec (I : List Sym) (s : IState NS) (arrays : List (List ℤ)) (tail : List Item)
    (hc : s.G Counter=List.replicate arrays.length .mark)
    (hs : s.G Current=ArrayLookup.frames arrays++tail) :
    IExec I Fin.elim0 transferLoop s
      (((s.upd Counter []).upd Current tail).upd Prev (ArrayLookup.frames arrays.reverse++s.G Prev))
      (transferCost arrays) := by
  induction arrays generalizing s with
  | nil =>
    have hcl : decide (s.cl Counter=Cls.mark)=false := by simp [IState.cl,hc,cls]
    have he : (((s.upd Counter []).upd Current tail).upd Prev
        (ArrayLookup.frames ([] : List (List ℤ)).reverse++s.G Prev))=s := by
      have hC : s.G Counter=[] := by simpa using hc
      have hS : s.G Current=tail := by simpa [ArrayLookup.frames] using hs
      simp only [List.reverse_nil,ArrayLookup.frames,List.flatMap_nil,List.nil_append]
      rw [← hC,← hS]
      simp
    rw [he]
    exact .loopF hcl
  | cons a arrays ih =>
    let s1 := s.upd Counter (List.replicate arrays.length .mark)
    let s2 := (s1.upd Current (ArrayLookup.frames arrays++tail)).upd Prev
      (a.map Item.int ++ .mark::s.G Prev)
    have h1 : IExec I Fin.elim0 (.op (.unmark Counter)) s s1 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hc))
    have h2 : IExec I Fin.elim0 (transferArray Current Prev Tmp) s1 s2 (2*moveIntsCost a+4) := by
      have h := transferArray_exec I Current Prev Tmp (by decide) (by decide) (by decide)
        s1 a (ArrayLookup.frames arrays++tail) (by simpa [s1,ArrayLookup.frames_cons,List.append_assoc] using hs)
      simpa [s2,s1] using h
    have htail := ih s2 (by simp [s2,s1]) (by simp [s2])
    have hcl : decide (s.cl Counter=Cls.mark)=true := by simp [IState.cl,hc,List.replicate_succ,cls]
    have h := IExec.loopT hcl (IExec.seq h1 h2) htail
    have he : (((s2.upd Counter []).upd Current tail).upd Prev
        (ArrayLookup.frames arrays.reverse++s2.G Prev))=
      (((s.upd Counter []).upd Current tail).upd Prev
        (ArrayLookup.frames (a::arrays).reverse++s.G Prev)) := by
      apply itemState_ext
      · intro i
        by_cases hC : i=Counter
        · subst i; simp [s2,s1]
        by_cases hS : i=Current
        · subst i; simp [s2,s1]
        by_cases hP : i=Prev
        · subst i; simp [s2,s1,ArrayLookup.frames,List.reverse_cons,List.flatMap_append,List.append_assoc]
        simp [s2,s1,IState.upd,Function.update_apply,hC,hS,hP]
      · rfl
      · rfl
    rw [he] at h
    change IExec I Fin.elim0 transferLoop s _ _ at h
    convert h using 1 <;> simp only [transferCost] <;> omega







end KoanaKPaths.Machine.Matrix

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Matrix.NS) (arrays : List.{0} (List.{0} Int))
  (tail : List.{0} NLogN.Item)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Matrix.NS s KoanaKPaths.Machine.Matrix.Counter)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (List.{0} Int) arrays) NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Matrix.NS s KoanaKPaths.Machine.Matrix.Current)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames arrays) tail)),
  @NLogN.IExec KoanaKPaths.Machine.Matrix.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Matrix.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Matrix.transferLoop s
    (@NLogN.IState.upd KoanaKPaths.Machine.Matrix.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Matrix.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Matrix.NS s KoanaKPaths.Machine.Matrix.Counter
          (@List.nil.{0} NLogN.Item))
        KoanaKPaths.Machine.Matrix.Current tail)
      KoanaKPaths.Machine.Matrix.Prev
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames (@List.reverse.{0} (List.{0} Int) arrays))
        (@NLogN.IState.G KoanaKPaths.Machine.Matrix.NS s KoanaKPaths.Machine.Matrix.Prev)))
    (KoanaKPaths.Machine.Matrix.transferCost arrays) := by
  exact @KoanaKPaths.Machine.Matrix.transferLoop_exec
