-- Prove2me | solution 1 for KoanaKPaths.Machine.Wedge.initializeUnit_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:37.725378+00:00
-- url     : https://prove2.me/submissions/e19b66bf-f672-4177-bbca-8fcdcabecc04

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
import Theorems.Thm_KoanaKPaths_Machine_powerMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_repeatInts_exec
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
attribute [local simp] A D HC DC Aux



lemma initializeUnit_exec (I : List Sym) (s : IState NS) (d : ℕ) (td : List Item)
    (ht : cls td.head? ≠ Cls.mark) (hd : s.G D=List.replicate d .mark ++ td)
    (hc : s.G HC=[]) (hn : s.G DC=[]) (hx : s.G Aux=[]) :
    IExec I Fin.elim0 initializeUnit s
      (s.upd A (.int 1::(List.replicate (2^d-1) (.int 0) ++ .mark::s.G A)))
      ((1+(65*d+60)+growMarksCost 1 d)+33*(2^d-1)+35) := by
  let s1 := s.upd A (.mark::s.G A)
  let s2 := s1.upd HC (List.replicate (2^d) .mark)
  let s3 := s2.upd HC (List.replicate (2^d-1) .mark)
  let s4 := (s3.upd HC []).upd A (List.replicate (2^d-1) (.int 0) ++ s3.G A)
  let s5 := s4.upd A (.int 1::s4.G A)
  have hp : 0<2^d := by positivity
  have h1 : IExec I Fin.elim0 (.op (.mark A)) s s1 1 := .op (.mark)
  have h2 : IExec I Fin.elim0 (powerMarks D HC DC Aux) s1 s2
      (1+(65*d+60)+growMarksCost 1 d) :=
    powerMarks_exec I D HC DC Aux (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) s1 d td ht (by simp [s1,hd]) (by simp [s1,hc]) (by simp [s1,hn]) (by simp [s1,hx])
  have h3 : IExec I Fin.elim0 (.op (.unmark HC)) s2 s3 1 := by
    have he : List.replicate (2^d) Item.mark = .mark::List.replicate (2^d-1) .mark := by
      calc
        _ = List.replicate ((2^d-1)+1) Item.mark := by congr 1; omega
        _ = _ := List.replicate_succ
    simpa only [s3,s2,upd_upd] using
      (IExec.op (IOp.Step.unmark (s := s2) (i := HC) (by simp [s2,he])) : IExec I Fin.elim0 _ _ _ 1)
  have h4 : IExec I Fin.elim0 (repeatInts HC A 0) s3 s4 (33*(2^d-1)+30) := by
    have hh := repeatInts_exec I HC A (by decide) 0 s3 (2^d-1) [] (by simp [cls]) (by simp [s3])
    simpa only [show zsz 0=0 from by simp [zsz,zbits,nbits_eq_bits],zero_add,List.append_nil] using hh
  have h5 : IExec I Fin.elim0 (.op (.const A 1)) s4 s5 3 := by
    simpa only [show zsz 1=1 from by simp [zsz,zbits,nbits_eq_bits]] using
      (IExec.op (IOp.Step.const (s := s4) (i := A) 1) : IExec I Fin.elim0 _ _ _ _)
  have he : s5=s.upd A (.int 1::(List.replicate (2^d-1) (.int 0) ++ .mark::s.G A)) := by
    cases s with
    | mk G ip o =>
      have hc' : G HC=[] := hc
      simp only [HC] at hc'
      simp only [s5,s4,s3,s2,s1,IState.upd]
      congr 1
      funext i
      by_cases hA : i=A
      · subst i; simp [Function.update_apply]
      by_cases hH : i=HC
      · subst i; simp [Function.update_apply,hc']
      simp [Function.update_apply,hA,hH]
  have hrun := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 h5)))
  change IExec I Fin.elim0 initializeUnit s _ _ at hrun
  rw [he] at hrun
  convert hrun using 1 <;> omega



end KoanaKPaths.Machine.Wedge

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Wedge.NS) (d : Nat) (td : List.{0} NLogN.Item)
  (ht : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item td)) NLogN.Cls.mark)
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.D)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item d NLogN.Item.mark) td))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.HC)
      (@List.nil.{0} NLogN.Item))
  (hn :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.DC)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.Aux)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Wedge.initializeUnit s
    (@NLogN.IState.upd KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.replicate.{0} NLogN.Item
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))))
          (@List.cons.{0} NLogN.Item NLogN.Item.mark
            (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s KoanaKPaths.Machine.Wedge.A)))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65))) d)
              (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))))
          (KoanaKPaths.Machine.growMarksCost (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) d))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 35) (instOfNatNat (nat_lit 35)))) := by
  exact @KoanaKPaths.Machine.Wedge.initializeUnit_exec
