-- Prove2me | solution 1 for KoanaKPaths.Machine.transferArray_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:31:19.955087+00:00
-- url     : https://prove2.me/submissions/9ce9814a-339a-4bc7-8aba-0137f3296d7c

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
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

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]























end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

lemma moveIntsCost_reverse (xs : List ℤ) : moveIntsCost xs.reverse=moveIntsCost xs := by
  simp [moveIntsCost,List.map_reverse]



lemma transferArray_exec (I : List Sym) (src dst tmp : Fin S)
    (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp) (s : IState S) (xs : List ℤ) (tail : List Item)
    (hs : s.G src=xs.map Item.int ++ .mark::tail) :
    IExec I Fin.elim0 (transferArray src dst tmp) s
      ((s.upd src tail).upd dst (xs.map Item.int ++ .mark::s.G dst)) (2*moveIntsCost xs+4) := by
  let s1 := s.upd tmp (.mark::s.G tmp)
  let s2 := (s1.upd src (.mark::tail)).upd tmp (xs.reverse.map Item.int ++ s1.G tmp)
  let s3 := s2.upd src tail
  let s4 := s3.upd dst (.mark::s3.G dst)
  let s5 := (s4.upd tmp (.mark::s.G tmp)).upd dst (xs.reverse.reverse.map Item.int ++ s4.G dst)
  let s6 := s5.upd tmp (s.G tmp)
  have h1 : IExec I Fin.elim0 (.op (.mark tmp)) s s1 1 := .op (.mark)
  have h2 : IExec I Fin.elim0 (moveInts src tmp) s1 s2 (moveIntsCost xs) :=
    moveInts_exec I src tmp hst s1 xs (.mark::tail) (by simp [cls]) (by simp [s1,hst,hs])
  have h3 : IExec I Fin.elim0 (.op (.unmark src)) s2 s3 1 := by exact .op (.unmark (by simp [s2,hst]))
  have h4 : IExec I Fin.elim0 (.op (.mark dst)) s3 s4 1 := .op (.mark)
  have h5 : IExec I Fin.elim0 (moveInts tmp dst) s4 s5 (moveIntsCost xs.reverse) :=
    moveInts_exec I tmp dst (Ne.symm hdt) s4 xs.reverse (.mark::s.G tmp) (by simp [cls])
      (by simp [s4,s3,s2,s1,Ne.symm hdt,Ne.symm hst])
  have h6 : IExec I Fin.elim0 (.op (.unmark tmp)) s5 s6 1 := by
    exact .op (.unmark (by simp [s5,Ne.symm hdt]))
  have he : s6=(s.upd src tail).upd dst (xs.map Item.int ++ .mark::s.G dst) := by
    cases s
    simp only [s6,s5,s4,s3,s2,s1,IState.upd]
    congr 1
    funext i
    by_cases hS : i=src <;> by_cases hD : i=dst <;> by_cases hT : i=tmp <;> simp_all
  have hrun := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5 h6))))
  change IExec I Fin.elim0 (transferArray src dst tmp) s _ _ at hrun
  rw [he] at hrun
  convert hrun using 1 <;> rw [moveIntsCost_reverse] <;> omega

end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (src dst tmp : Fin S) (hsd : @Ne.{1} (Fin S) src dst)
  (hst : @Ne.{1} (Fin S) src tmp) (hdt : @Ne.{1} (Fin S) dst tmp) (s : NLogN.IState S) (xs : List.{0} Int)
  (tail : List.{0} NLogN.Item)
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s src)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark tail))),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.transferArray S src dst tmp) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s src tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs)
        (@List.cons.{0} NLogN.Item NLogN.Item.mark (@NLogN.IState.G S s dst))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (KoanaKPaths.Machine.moveIntsCost xs))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) := by
  exact @KoanaKPaths.Machine.transferArray_exec
