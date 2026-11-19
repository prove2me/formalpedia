-- Prove2me | solution 1 for KoanaKPaths.Machine.powerMarks_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:45:46.284682+00:00
-- url     : https://prove2.me/submissions/14af2304-fe31-4244-b4f2-e9376b584d05

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_growMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
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





















lemma copyMarks_exec (I : List Sym) (src dst tmp : Fin S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (s : IState S) (m : ℕ) (tail : List Item) (ht : cls tail.head? ≠ Cls.mark)
    (hs : s.G src = List.replicate m .mark ++ tail) (hx : s.G tmp = []) :
    IExec I Fin.elim0 (copyMarks src dst tmp) s
      (s.upd dst (List.replicate m .mark ++ s.G dst)) (65*m+60) := by
  let s1 := (((s.upd src tail).upd dst (List.replicate m .mark ++ s.G dst)).upd tmp
    (List.replicate m .mark ++ s.G tmp))
  have hd := copyMoveMarks_exec I src dst tmp hsd hst hdt s m tail ht hs
  have hm := moveMarks_exec I tmp src (Ne.symm hst) s1 m [] (by decide) (by simp [s1,hx])
  have he : (s1.upd tmp []).upd src (List.replicate m .mark ++ s1.G src) =
      s.upd dst (List.replicate m .mark ++ s.G dst) := by
    cases s
    simp only [s1,IState.upd]
    congr 1
    funext t
    by_cases ha : t=src <;> by_cases hb : t=dst <;> by_cases hc : t=tmp <;> simp_all
  have hrun := IExec.seq hd hm
  rw [he] at hrun
  change IExec I Fin.elim0 (copyMarks src dst tmp) s _ ((33*m+30)+(32*m+30)) at hrun
  convert hrun using 1 <;> omega

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}














lemma powerMarks_exec (I : List Sym) (depth count control tmp : Fin S)
    (hdc : depth ≠ count) (hdn : depth ≠ control) (hdt : depth ≠ tmp)
    (hcn : count ≠ control) (hct : count ≠ tmp) (hnt : control ≠ tmp)
    (s : IState S) (d : ℕ) (tail : List Item) (ht : cls tail.head? ≠ Cls.mark)
    (hd : s.G depth = List.replicate d .mark ++ tail)
    (hc : s.G count = []) (hn : s.G control = []) (hx : s.G tmp = []) :
    IExec I Fin.elim0 (powerMarks depth count control tmp) s
      (s.upd count (List.replicate (2^d) .mark)) (1+(65*d+60)+growMarksCost 1 d) := by
  let s0 := s.upd count [.mark]
  let s1 := s0.upd control (List.replicate d .mark)
  have hm : IExec I Fin.elim0 (.op (.mark count)) s s0 1 := by
    simpa only [hc] using (IExec.op (IOp.Step.mark (s := s) (i := count)) : IExec I Fin.elim0 _ _ _ _)
  have hcopy := copyMarks_exec I depth control tmp hdn hdt hnt s0 d tail ht
    (by simp [s0,hdc,hd]) (by simp [s0,Ne.symm hct,hx])
  have hcopy' : IExec I Fin.elim0 (copyMarks depth control tmp) s0 s1 (65*d+60) := by
    simpa only [s1,s0,upd_G_ne s (Ne.symm hcn),hn,List.append_nil] using hcopy
  have hg := growMarks_exec I control count tmp (Ne.symm hcn) hnt hct s1 d 1 [] [] (by decide) (by decide)
    (by simp [s1]) (by simp [s1,s0,hcn]) (by simp [s1,s0,Ne.symm hnt,Ne.symm hct,hx])
  have he : (s1.upd control []).upd count (List.replicate (1*2^d) .mark ++ []) =
      s.upd count (List.replicate (2^d) .mark) := by
    cases s
    simp only [s1,s0,IState.upd]
    congr 1
    funext t
    by_cases ha : t=count <;> by_cases hb : t=control <;> simp_all
  rw [he] at hg
  have hh := IExec.seq hm (IExec.seq hcopy' hg)
  change IExec I Fin.elim0 (powerMarks depth count control tmp) s _ _ at hh
  convert hh using 1 <;> omega



end KoanaKPaths.Machine

end

theorem solution :
∀ {S : Nat} (I : List.{0} NLogN.Sym) (depth count control tmp : Fin S) (hdc : @Ne.{1} (Fin S) depth count)
  (hdn : @Ne.{1} (Fin S) depth control) (hdt : @Ne.{1} (Fin S) depth tmp) (hcn : @Ne.{1} (Fin S) count control)
  (hct : @Ne.{1} (Fin S) count tmp) (hnt : @Ne.{1} (Fin S) control tmp) (s : NLogN.IState S) (d : Nat)
  (tail : List.{0} NLogN.Item) (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item tail)) NLogN.Cls.mark)
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s depth)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item d NLogN.Item.mark) tail))
  (hc : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s count) (@List.nil.{0} NLogN.Item))
  (hn : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s control) (@List.nil.{0} NLogN.Item))
  (hx : @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G S s tmp) (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1} (NLogN.IStmt S (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.powerMarks S depth count control tmp) s
    (@NLogN.IState.upd S s count
      (@List.replicate.{0} NLogN.Item
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)
        NLogN.Item.mark))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65))) d)
          (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))))
      (KoanaKPaths.Machine.growMarksCost (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d)) := by
  exact @KoanaKPaths.Machine.powerMarks_exec
