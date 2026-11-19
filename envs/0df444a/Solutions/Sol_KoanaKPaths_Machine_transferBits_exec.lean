-- Prove2me | solution 1 for KoanaKPaths.Machine.transferBits_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:42:43.420013+00:00
-- url     : https://prove2.me/submissions/da39a4d1-81ab-4835-bdb0-8c6633c82649

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
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


















@[simp] lemma set_same (σ : St S) (i : Fin S) : σ.set i (σ.stk i) = σ := by
  apply St.ext
  · funext j
    simp [St.set]
  · rfl
  · rfl

lemma transferBits_exec (I : List Sym) (prog : Fin P → Stmt S P)
    (src dst : Fin S) (hne : src ≠ dst) (σ : St S)
    (A : List Bool) (tail : List Sym) (ht : bitOf tail.head? = none)
    (hs : σ.stk src = A.map codeBit ++ tail) :
    Exec I prog (transferBits src dst) σ
      ((σ.set src tail).set dst (A.reverse.map codeBit ++ σ.stk dst)) (4*A.length+1) := by
  induction A generalizing σ with
  | nil =>
    have hh : isBitT (σ.top src) = false := by simp [St.top,hs,isBitT,ht]
    have hsrc : σ.set src tail = σ := by rw [← show σ.stk src = tail from by simpa using hs]; exact set_same _ _
    unfold transferBits
    simp only [List.reverse_nil,List.map_nil,List.nil_append,List.length_nil,mul_zero,zero_add,hsrc,set_same]
    exact Exec.loopF hh
  | cons b A ih =>
    let σ1 := (σ.pop src).push dst (codeBit b)
    have hbody : Exec I prog
        (.ite src (fun o => decide (o=some 0))
          (.seq (.pop src) (.push dst 0)) (.seq (.pop src) (.push dst 1))) σ σ1 3 := by
      cases b
      · apply Exec.iteT
        · simp [St.top,hs,codeBit]
        · exact Exec.seq (Exec.pop _ _) (Exec.push _ _ _)
      · apply Exec.iteF
        · simp [St.top,hs,codeBit]
        · exact Exec.seq (Exec.pop _ _) (Exec.push _ _ _)
    have hsrc1 : σ1.stk src = A.map codeBit ++ tail := by
      simp [σ1,St.push,St.pop,hs,hne]
    have hloop : isBitT (σ.top src) = true := by cases b <;> simp [St.top,hs,isBitT,codeBit,bitOf]
    have hrun := Exec.loopT hloop hbody (ih σ1 hsrc1)
    have hfinal : ((σ1.set src tail).set dst (A.reverse.map codeBit ++ σ1.stk dst)) =
        ((σ.set src tail).set dst ((b::A).reverse.map codeBit ++ σ.stk dst)) := by
      apply St.ext
      · funext t
        by_cases hs : t=src <;> by_cases hd : t=dst <;>
          simp_all [σ1,St.set,St.push,St.pop,List.reverse_cons,List.map_append,List.append_assoc]
      · rfl
      · rfl
    rw [hfinal] at hrun
    convert hrun using 1 <;> simp [transferBits] <;> omega
































end KoanaKPaths.Machine

end

theorem solution :
∀ {S P : Nat} (I : List.{0} NLogN.Sym) (prog : Fin P → NLogN.Stmt S P) (src dst : Fin S) (hne : @Ne.{1} (Fin S) src dst)
  (σ : NLogN.St S) (A : List.{0} Bool) (tail : List.{0} NLogN.Sym)
  (ht : @Eq.{1} (Option.{0} Bool) (NLogN.bitOf (@List.head?.{0} NLogN.Sym tail)) (@Option.none.{0} Bool))
  (hs :
    @Eq.{1} (List.{0} NLogN.Sym) (@NLogN.St.stk S σ src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Sym) (List.{0} NLogN.Sym) (List.{0} NLogN.Sym)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Sym) (@List.instAppend.{0} NLogN.Sym))
        (@List.map.{0, 0} Bool NLogN.Sym NLogN.codeBit A) tail)),
  @NLogN.Exec S P I prog (@KoanaKPaths.Machine.transferBits S P src dst) σ
    (@NLogN.St.set S (@NLogN.St.set S σ src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Sym) (List.{0} NLogN.Sym) (List.{0} NLogN.Sym)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Sym) (@List.instAppend.{0} NLogN.Sym))
        (@List.map.{0, 0} Bool NLogN.Sym NLogN.codeBit (@List.reverse.{0} Bool A)) (@NLogN.St.stk S σ dst)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Bool A))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by
  exact @KoanaKPaths.Machine.transferBits_exec
