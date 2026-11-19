-- Prove2me | solution 1 for KoanaKPaths.Machine.Median.initialize_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.149743+00:00
-- url     : https://prove2.me/submissions/fec71d23-363f-4410-b6f5-f009ebf50415

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_MedianOfMeans
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Mathlib
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
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
@[simp] lemma upd_same (s : IState S) (i : Fin S) : s.upd i (s.G i) = s := by
  cases s
  simp [IState.upd]

@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]


















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
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]





































end KoanaKPaths.Machine.Wedge

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



attribute [local simp] Template CopyTmp Output Fuel Hi Ruler Work Lo



lemma shiftLoop_exec (I : List Sym) (s : IState NS) (L p : ℕ) (ht rt : List Item)
    (hf : s.G Fuel=List.replicate L .mark) (hh : s.G Hi=.int ((2 : ℤ)^p)::ht)
    (hr : s.G Ruler=.int 2::rt) :
    IExec I Fin.elim0 shiftLoop s
      ((s.upd Fuel []).upd Hi (.int ((2 : ℤ)^(p+L))::ht)) ((shlCost 1+31)*L+30) := by
  induction L generalizing s p with
  | zero =>
    have hcl : decide (s.cl Fuel=Cls.mark)=false := by simp [IState.cl,hf,cls]
    have he : (s.upd Fuel []).upd Hi (.int ((2 : ℤ)^(p+0))::ht)=s := by
      have hf' : s.G Fuel=[] := by simpa using hf
      simp only [Nat.add_zero]
      rw [← hf',← hh]
      simp
    rw [he]
    exact .loopF hcl
  | succ L ih =>
    let s1 := s.upd Fuel (List.replicate L .mark)
    let s2 := s1.upd Hi (.int ((2 : ℤ)^(p+1))::ht)
    have h1 : IExec I Fin.elim0 (.op (.unmark Fuel)) s s1 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hf))
    have h2 : IExec I Fin.elim0 (.op (.shl Hi Ruler)) s1 s2 (shlCost 1) := by
      have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
        (IOp.Step.shl (s := s1) (i := Hi) (j := Ruler) (a := (2 : ℤ)^p) (m := 1)
          (Li := ht) (Lj := rt) (by decide) (by simp [s1,hh]) (by simpa [s1] using hr))
      simpa [s2,pow_succ] using h
    have htail := ih s2 (p+1) (by simp [s2,s1]) (by simp [s2]) (by simp [s2,s1,hr])
    have hcl : decide (s.cl Fuel=Cls.mark)=true := by simp [IState.cl,hf,List.replicate_succ,cls]
    have h := IExec.loopT hcl (IExec.seq h1 h2) htail
    have he : (s2.upd Fuel []).upd Hi (.int ((2 : ℤ)^(p+1+L))::ht)=
      (s.upd Fuel []).upd Hi (.int ((2 : ℤ)^(p+(L+1)))::ht) := by
      apply itemState_ext
      · intro i
        by_cases hF : i=Fuel
        · subst i; simp [s2,s1]
        by_cases hH : i=Hi
        · subst i; simp [s2,s1,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        simp [s2,s1,IState.upd,Function.update_apply,hF,hH]
      · rfl
      · rfl
    rw [he] at h
    change IExec I Fin.elim0 shiftLoop s _ _ at h
    convert h using 1 <;> ring



lemma initialize_exec (I : List Sym) (s : IState NS) (L : ℕ)
    (ht : s.G Template=List.replicate L .mark) (hf : s.G Fuel=[]) (hx : s.G CopyTmp=[]) :
    IExec I Fin.elim0 initializeInterval s
      ((((s.upd Ruler (.int 2::s.G Ruler)).upd Hi
        (.int ((2^L-1 : ℕ) : ℤ)::s.G Hi)).upd Lo (.int 0::s.G Lo)).upd Fuel
          (List.replicate L .mark))
      ((shlCost 1+161)*L+addIntCost (zsz ((2 : ℤ)^L)+1)+162) := by
  let s0 := s.upd Ruler (.int 2::s.G Ruler)
  let s1 := s0.upd Hi (.int 1::s.G Hi)
  let s2 := s1.upd Lo (.int 0::s.G Lo)
  let s3 := s2.upd Fuel (List.replicate L .mark)
  let s4 := (s3.upd Fuel []).upd Hi (.int ((2 : ℤ)^L)::s.G Hi)
  let s5 := s4.upd Work (.int (-1)::s.G Work)
  let sa := (s5.upd Hi (s.G Hi)).upd Work (s.G Work)
  let s6 := sa.upd Hi (.int ((2^L-1 : ℕ) : ℤ)::s.G Hi)
  let s7 := s6.upd Fuel (List.replicate L .mark)
  have hz2 : zsz (2 : ℤ)=2 := by
    have h := Nat.size_pow (n := 1)
    simpa [Wedge.zsz_eq_size] using h
  have h0 : IExec I Fin.elim0 (.op (.const Ruler 2)) s s0 4 := by
    simpa only [hz2] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s) (i := Ruler) 2))
  have h1 : IExec I Fin.elim0 (.op (.const Hi 1)) s0 s1 3 := by
    simpa [s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s0) (i := Hi) 1))
  have h2 : IExec I Fin.elim0 (.op (.const Lo 0)) s1 s2 2 := by
    simpa [s2,s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s1) (i := Lo) 0))
  have h3 : IExec I Fin.elim0 (copyMarks Template Fuel CopyTmp) s2 s3 (65*L+60) := by
    have h := copyMarks_exec I Template Fuel CopyTmp (by decide) (by decide) (by decide)
      s2 L [] (by simp [cls]) (by simp [s2,s1,s0,ht]) (by simp [s2,s1,s0,hx])
    simpa [s3,s2,s1,s0,hf] using h
  have h4 : IExec I Fin.elim0 shiftLoop s3 s4 ((shlCost 1+31)*L+30) := by
    have h := shiftLoop_exec I s3 L 0 (s.G Hi) (s.G Ruler)
      (by simp [s3]) (by simp [s3,s2,s1]) (by simp [s3,s2,s1,s0])
    simpa [s4] using h
  have h5 : IExec I Fin.elim0 (.op (.const Work (-1))) s4 s5 3 := by
    simpa [s5,s4,s3,s2,s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s4) (i := Work) (-1)))
  have hcast : (2 : ℤ)^L+ -1=((2^L-1 : ℕ) : ℤ) := by
    have hp : 1≤(2 : ℕ)^L := by
      have hpos : 0<(2 : ℕ)^L := by positivity
      omega
    have h := congrArg (fun x : ℕ => (x : ℤ)) (Nat.sub_add_cancel hp)
    push_cast at h
    omega
  have h6 : IExec I Fin.elim0 (.op (.add Hi Work Hi)) s5 s6
      (addIntCost (zsz ((2 : ℤ)^L)+1)) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.add (s := s5) (i := Hi) (j := Work) (k := Hi)
        (a := (2 : ℤ)^L) (b := -1) (Li := s.G Hi) (Lj := s.G Work)
        (by decide) (by simp [s5,s4]) (by simp [s5]))
    simpa [s6,sa,hcast,Wedge.zsz_eq_size] using h
  have h7 : IExec I Fin.elim0 (copyMarks Template Fuel CopyTmp) s6 s7 (65*L+60) := by
    have h := copyMarks_exec I Template Fuel CopyTmp (by decide) (by decide) (by decide)
      s6 L [] (by simp [cls]) (by simp [s6,sa,s5,s4,s3,s2,s1,s0,ht])
      (by simp [s6,sa,s5,s4,s3,s2,s1,s0,hx])
    simpa [s7,s6,sa,s5,s4] using h
  have he : s7=((((s.upd Ruler (.int 2::s.G Ruler)).upd Hi
        (.int ((2^L-1 : ℕ) : ℤ)::s.G Hi)).upd Lo (.int 0::s.G Lo)).upd Fuel
          (List.replicate L .mark)) := by
    apply itemState_ext
    · intro i
      by_cases hR : i=Ruler
      · subst i; simp [s7,s6,sa,s5,s4,s3,s2,s1,s0]
      by_cases hH : i=Hi
      · subst i; simp [s7,s6,sa,s5,s4,s3,s2,s1,s0]
      by_cases hL : i=Lo
      · subst i; simp [s7,s6,sa,s5,s4,s3,s2,s1,s0]
      by_cases hF : i=Fuel
      · subst i; simp [s7,s6,sa,s5,s4,s3,s2,s1,s0]
      by_cases hW : i=Work
      · subst i; simp [s7,s6,sa,s5,s4,s3,s2,s1,s0]
      simp [s7,s6,sa,s5,s4,s3,s2,s1,s0,IState.upd,Function.update_apply,hR,hH,hL,hF,hW]
    · rfl
    · rfl
  have h := IExec.seq h0 (IExec.seq h1 (IExec.seq h2 (IExec.seq h3
    (IExec.seq h4 (IExec.seq h5 (IExec.seq h6 h7))))))
  rw [he] at h
  change IExec I Fin.elim0 initializeInterval s _ _ at h
  convert h using 1 <;> ring



end KoanaKPaths.Machine.Median

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (L : Nat)
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Template)
      (@List.replicate.{0} NLogN.Item L NLogN.Item.mark))
  (hf :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Fuel)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.CopyTmp)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IExec KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.initializeInterval s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
          (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Ruler
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))
              (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Ruler)))
          KoanaKPaths.Machine.Median.Hi
          (@List.cons.{0} NLogN.Item
            (NLogN.Item.int
              (@Nat.cast.{0} Int instNatCastInt
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Hi)))
        KoanaKPaths.Machine.Median.Lo
        (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
          (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Lo)))
      KoanaKPaths.Machine.Median.Fuel (@List.replicate.{0} NLogN.Item L NLogN.Item.mark))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (NLogN.shlCost (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 161) (instOfNatNat (nat_lit 161))))
          L)
        (NLogN.addIntCost
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (NLogN.zsz
              (@HPow.hPow.{0, 0, 0} Int Nat Int
                (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) L))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))) := by
  exact @KoanaKPaths.Machine.Median.initialize_exec
