-- Prove2me | solution 1 for KoanaKPaths.Machine.repeatInts_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:37.677192+00:00
-- url     : https://prove2.me/submissions/487827a2-7f2b-4aa9-a9e1-51ae29b0a849

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
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
variable {S : ℕ}



lemma repeatInts_exec (I : List Sym) (count dst : Fin S) (hne : count ≠ dst) (z : ℤ)
    (s : IState S) (m : ℕ) (tail : List Item) (ht : cls tail.head? ≠ Cls.mark)
    (hc : s.G count=List.replicate m .mark ++ tail) :
    IExec I Fin.elim0 (repeatInts count dst z) s
      ((s.upd count tail).upd dst (List.replicate m (.int z) ++ s.G dst))
      ((zsz z+33)*m+30) := by
  induction m generalizing s with
  | zero =>
    have hcond : decide (s.cl count=Cls.mark)=false := by simp [IState.cl,hc,ht]
    have hs : s.upd count tail=s := by rw [← show s.G count=tail from by simpa using hc]; exact upd_same _ _
    simp only [List.replicate_zero,List.nil_append,hs,upd_same,mul_zero,zero_add]
    exact IExec.loopF hcond
  | succ m ih =>
    let s1 := s.upd count (List.replicate m .mark ++ tail)
    let s2 := s1.upd dst (.int z::s.G dst)
    have h1 : IExec I Fin.elim0 (.op (.unmark count)) s s1 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hc))
    have h2 : IExec I Fin.elim0 (.op (.const dst z)) s1 s2 (zsz z+2) := by
      simpa only [s1,upd_G_ne s (Ne.symm hne)] using
        (IExec.op (IOp.Step.const (s := s1) (i := dst) z) : IExec I Fin.elim0 _ _ _ _)
    have hcond : decide (s.cl count=Cls.mark)=true := by simp [IState.cl,hc,List.replicate_succ,cls]
    have hrun := IExec.loopT hcond (IExec.seq h1 h2) (ih s2 (by simp [s2,s1,hne]))
    have he : (s2.upd count tail).upd dst (List.replicate m (.int z) ++ s2.G dst) =
        (s.upd count tail).upd dst (List.replicate (m+1) (.int z) ++ s.G dst) := by
      cases s
      simp only [s2,s1,IState.upd]
      congr 1
      funext i
      by_cases ha : i=count <;> by_cases hb : i=dst <;>
        simp_all [List.replicate_succ,replicate_cons_same]
    rw [he] at hrun
    change IExec I Fin.elim0 (repeatInts count dst z) s _ _ at hrun
    convert hrun using 1 <;> simp only [Nat.mul_add,Nat.mul_one] <;> omega

end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (count dst : Fin S) (hne : @Ne.{1} (Fin S) count dst) (z : Int)
  (s : NLogN.IState S) (m : Nat) (tail : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s count)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m NLogN.Item.mark) tail)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.repeatInts S count dst z) s
    (@NLogN.IState.upd S (@NLogN.IState.upd S s count tail) dst
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item m (NLogN.Item.int z)) (@NLogN.IState.G S s dst)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (NLogN.zsz z)
          (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))))
        m)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.repeatInts_exec
