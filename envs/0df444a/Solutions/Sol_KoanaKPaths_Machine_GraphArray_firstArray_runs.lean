-- Prove2me | solution 1 for KoanaKPaths.Machine.GraphArray.firstArray_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:26:49.639293+00:00
-- url     : https://prove2.me/submissions/7cd5a10c-a4ce-4b69-b8b4-38127e3fce57

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
import Theorems.Thm_KoanaKPaths_Machine_Wedge_call_exec
import Theorems.Thm_KoanaKPaths_Machine_Wedge_initializeUnit_exec
import Theorems.Thm_KoanaKPaths_Machine_Wedge_negate_exec
import Theorems.Thm_KoanaKPaths_Machine_Wedge_wedgeCost_bound
import Theorems.Thm_KoanaKPaths_Machine_Wedge_wedgeReverse_width
import Theorems.Thm_KoanaKPaths_Machine_transferArray_exec
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




















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}









lemma moveIntsCost_le (xs : List ℤ) (w : ℕ) (hw : ∀ z ∈ xs, zsz z ≤ w) :
    moveIntsCost xs ≤ (76*w+131)*xs.length+30 := by
  unfold moveIntsCost
  have h : (xs.map (fun z => 2*moveCost (zsz z)+49)).sum ≤ (76*w+131)*xs.length := by
    induction xs with
    | nil => simp
    | cons z xs ih =>
      have hz := hw z (by simp)
      have hr := ih (fun x hx => hw x (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      unfold moveCost at *
      nlinarith
  omega




























lemma zsz_neg (z : ℤ) : zsz (-z)=zsz z := by simp [zsz,zbits]



end KoanaKPaths.Machine

end

section

namespace KoanaKPaths.Machine
open NLogN
variable {S P : ℕ}



lemma liftClosed_exec (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IExec I Fin.elim0 p s s' c) : IExec I prog (liftClosed p) s s' c := by
  induction h with
  | skip s => exact .skip s
  | op h => exact .op h
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | iteT h _ ih => exact .iteT h ih
  | iteF h _ ih => exact .iteF h ih
  | loopT h _ _ ih1 ih2 => exact .loopT h ih1 ih2
  | loopF h => exact .loopF h
  | call => exact Fin.elim0 ‹Fin 0›



end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}







lemma growMarksCost_identity (m d : ℕ) :
    growMarksCost m d+97*m=97*m*2^d+91*d+30 := by
  induction d generalizing m with
  | zero => simp [growMarksCost]; omega
  | succ d ih =>
    simp only [growMarksCost]
    have hh := ih (2*m)
    rw [pow_succ]
    nlinarith

lemma growMarksCost_le (m d : ℕ) : growMarksCost m d ≤ (97*m+121)*2^d := by
  have h := growMarksCost_identity m d
  have hd : d ≤ 2^d := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hp : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
  nlinarith






lemma powerMarks_cost (d : ℕ) : 1+(65*d+60)+growMarksCost 1 d ≤ 400*2^d := by
  have hg := growMarksCost_le 1 d
  have hd : d ≤ 2^d := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hp : 1 ≤ 2^d := Nat.one_le_pow d 2 (by omega)
  nlinarith

end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
namespace KoanaKPaths.ExteriorCoordinates







lemma wedgeReverse_length (vs A : List ℤ) (h : A.length=2^vs.length) :
    (wedgeReverse vs A).length=2^vs.length := by
  induction vs generalizing A with
  | nil => rfl
  | cons z vs ih =>
    have hp : 2^vs.length ≤ A.length := by rw [h,List.length_cons,pow_succ]; omega
    have ha : (A.take (2^vs.length)).length=2^vs.length := by simp [List.length_take,Nat.min_eq_left hp]
    have hb : (A.drop (2^vs.length)).length=2^vs.length := by simp [List.length_drop,h,pow_succ]; omega
    simp only [wedgeReverse,List.length_append,List.length_zipWith,ih _ ha,ih _ hb,ha,Nat.min_self,
      List.length_cons,pow_succ]
    omega

end KoanaKPaths.ExteriorCoordinates

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]















lemma moveIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤w) :
    moveIntsCost xs ≤ 200*(w+1)*(xs.length+1) := by
  have hh := moveIntsCost_le xs w h
  nlinarith





















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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
attribute [local simp] A D HC DC Aux





lemma initializeUnit_cost (d : ℕ) :
    (1+(65*d+60)+growMarksCost 1 d)+33*(2^d-1)+35 ≤ 500*2^d := by
  have hp := powerMarks_cost d
  have hd : 1≤2^d := Nat.one_le_pow d 2 (by omega)
  omega

end KoanaKPaths.Machine.Wedge

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
open Wedge



lemma signedList_eq_scale (z : ℤ) (hz : z=1 ∨ z = -1) (xs : List ℤ) :
    signedList z xs=xs.map (fun x => z*x) := by
  rcases hz with rfl|rfl <;> simp [signedList]

lemma scaleBySign_exec (I : List Sym) (sign src : Fin Wedge.NS) (hne : sign≠src) (hnz : src≠Z)
    (s : IState Wedge.NS) (z : ℤ) (xs : List ℤ) (st xt : List Item) (hz : z=1 ∨ z = -1)
    (hs : s.G sign=.int z::st) (hx : s.G src=xs.map Item.int ++ .mark::xt) :
    IExec I prog (scaleBySign sign src) s
      ((s.upd src ((xs.map (fun x => z*x)).map Item.int ++ .mark::xt)).upd sign st)
      ((if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+29) := by
  let s1 := s.upd src ((signedList z xs).map Item.int ++ .mark::xt)
  have h1 : IExec I prog (.ite sign (fun c => decide (c=Cls.neg)) (negate src) .skip) s s1
      ((if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+25) := by
    by_cases hn : z<0
    · have hcond : decide (s.cl sign=Cls.neg)=true := by
        have hz0 : z≠0 := ne_of_lt hn
        simp [IState.cl,hs,cls,hn,hz0]
      have hh := negate_exec I src hnz s xs xt hx
      simpa only [s1,signedList,if_pos hn,List.map_map,Function.comp_def] using IExec.iteT hcond hh
    · have hcond : decide (s.cl sign=Cls.neg)=false := by
        by_cases hz0 : z=0 <;> simp [IState.cl,hs,cls,hn,hz0]
      have he : s1=s := by
        dsimp only [s1,signedList]
        rw [if_neg hn,← hx]
        exact upd_same _ _
      rw [he,if_neg hn]
      exact IExec.iteF hcond (.skip s)
  have h2 : IExec I prog (.op (.drop sign)) s1 (s1.upd sign st) 4 := by
    have hzsz : zsz z=1 := by rcases hz with rfl|rfl <;> simp [zsz,zbits,nbits_eq_bits]
    simpa only [hzsz] using
      (IExec.op (IOp.Step.drop (I := I) (s := s1) (i := sign) (a := z) (L := st)
        (by simp [s1,hne,hs])) : IExec I prog _ _ _ _)
  have hrun := IExec.seq h1 h2
  change IExec I prog (scaleBySign sign src) s _ _ at hrun
  simpa only [s1,signedList_eq_scale z hz,show (if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+25+4=
    (if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+29 by omega] using hrun

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.GraphArray
open KoanaKPaths.ExteriorCoordinates




attribute [local simp] Current Tmp Sign Wedge.A Wedge.R Wedge.D Wedge.V Wedge.HC Wedge.DC Wedge.Aux





lemma unitArray_length (d : ℕ) : (unitArray d).length=2^d := by
  have hp : 0<2^d := by positivity
  simp only [unitArray,List.length_cons,List.length_replicate]
  omega

lemma unitArray_width (d : ℕ) : ∀ x∈unitArray d, zsz x≤1 := by
  intro x hx
  simp only [unitArray,List.mem_cons] at hx
  rcases hx with rfl|hx
  · simp [Wedge.zsz_eq_size]
  · have he : x=0 := List.eq_of_mem_replicate hx
    subst x; simp [Wedge.zsz_eq_size]

lemma firstArray_runs (I : List Sym) (s : IState NS) (vs : List ℤ) (z : ℤ)
    (td tv st : List Item) (hdt : cls td.head?≠Cls.mark)
    (hd : s.G Wedge.D=List.replicate vs.length .mark ++ td)
    (hv : s.G Wedge.V=vs.map Item.int ++ tv)
    (hsgn : ∀ x∈vs, x=1 ∨ x= -1) (hz : z=1 ∨ z= -1)
    (hs : s.G Sign=.int z::st) (hc : s.G Wedge.HC=[])
    (hdc : s.G Wedge.DC=[]) (ha : s.G Wedge.Aux=[]) :
    IRuns I Wedge.prog firstArray s
      ((s.upd Sign st).upd Current
        (((wedgeReverse vs (unitArray vs.length)).map (fun x => z*x)).map Item.int ++ .mark::s.G Current))
      (1000000*(vs.length+2)^2*2^vs.length) := by
  let d := vs.length
  let xs := unitArray d
  let next := wedgeReverse vs xs
  let scaled := next.map (fun x => z*x)
  let s0 := s.upd Wedge.A (xs.map Item.int ++ .mark::s.G Wedge.A)
  let s1 := (s0.upd Wedge.A (s.G Wedge.A)).upd Wedge.R (next.map Item.int ++ .mark::s.G Wedge.R)
  let s2 := (s1.upd Wedge.R (scaled.map Item.int ++ .mark::s.G Wedge.R)).upd Sign st
  let s3 := (s2.upd Wedge.R (s.G Wedge.R)).upd Current (scaled.map Item.int ++ .mark::s.G Current)
  have h0 : IExec I Wedge.prog (liftClosed Wedge.initializeUnit) s s0
      ((1+(65*d+60)+growMarksCost 1 d)+33*(2^d-1)+35) := by
    have h := liftClosed_exec I Wedge.prog (Wedge.initializeUnit_exec I s d td hdt hd hc hdc ha)
    simpa [s0,xs,unitArray,List.map_replicate] using h
  have h1 : IExec I Wedge.prog (.call 0) s0 s1 (Wedge.wedgeCost vs xs) := by
    have h := Wedge.call_exec I vs s0 xs (s.G Wedge.A) td tv (unitArray_length d) hsgn hdt
      (by simp [s0]) (by simp [s0,hd]) (by simp [s0,hv])
      (by simp [s0,hc]) (by simp [s0,hdc]) (by simp [s0,ha])
    simpa [s1,s0,next] using h
  have h2 : IExec I Wedge.prog (scaleBySign Sign Wedge.R) s1 s2
      ((if z<0 then 2*moveIntsCost next+20*next.length+3 else 1)+29) := by
    have h := scaleBySign_exec I Sign Wedge.R (by decide) (by decide) s1 z next st (s.G Wedge.R) hz
      (by simp [s1,s0,hs]) (by simp [s1])
    simpa [s2,s1,scaled] using h
  have h3 : IExec I Wedge.prog (liftClosed (transferArray Wedge.R Current Tmp)) s2 s3 (2*moveIntsCost scaled+4) := by
    have h := liftClosed_exec I Wedge.prog (transferArray_exec I Wedge.R Current Tmp
      (by decide) (by decide) (by decide) s2 scaled (s.G Wedge.R) (by simp [s2]))
    simpa [s3,s2,s1,s0] using h
  have he : s3=(s.upd Sign st).upd Current (scaled.map Item.int ++ .mark::s.G Current) := by
    apply itemState_ext
    · intro i
      by_cases hA : i=Wedge.A
      · subst i; simp [s3,s2,s1,s0]
      by_cases hR : i=Wedge.R
      · subst i; simp [s3,s2,s1,s0]
      by_cases hS : i=Sign
      · subst i; simp [s3,s2,s1,s0]
      by_cases hC : i=Current
      · subst i; simp [s3,s2,s1,s0]
      simp [s3,s2,s1,s0,IState.upd,Function.update_apply,hA,hR,hS,hC]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1)
    (Native.seq (Native.of_exec h2) (Native.of_exec h3)))
  rw [he] at h
  change IRuns I Wedge.prog firstArray s _ _ at h
  apply Native.mono h
  have hu := Wedge.initializeUnit_cost d
  have hw := Wedge.wedgeCost_bound vs xs 1 (unitArray_length d) hsgn (unitArray_width d)
  have hnlen : next.length=2^d := wedgeReverse_length vs xs (unitArray_length d)
  have hnw : ∀ x∈next, zsz x≤ d+1 := by
    have h := Wedge.wedgeReverse_width vs xs 1 hsgn (unitArray_width d)
    simpa [d,Nat.add_comm] using h
  have hsw : ∀ x∈scaled, zsz x≤ d+1 := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    rcases hz with rfl|rfl <;> simpa [zsz_neg] using hnw a ha
  have hnmove := Wedge.moveIntsCost_bound next (d+1) hnw
  have hsmove := Wedge.moveIntsCost_bound scaled (d+1) hsw
  have hslen : scaled.length=2^d := by simpa [scaled] using hnlen
  rw [hnlen] at hnmove
  rw [hslen] at hsmove
  have hp : 1≤2^d := Nat.one_le_pow d 2 (by omega)
  split_ifs <;> (try simp only [hnlen]) <;> dsimp only [d] at * <;> nlinarith

end KoanaKPaths.Machine.GraphArray

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.GraphArray.NS) (vs : List.{0} Int) (z : Int)
  (td tv st : List.{0} NLogN.Item) (hdt : @Ne.{1} NLogN.Cls (NLogN.cls (@List.head?.{0} NLogN.Item td)) NLogN.Cls.mark)
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.D)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.replicate.{0} NLogN.Item (@List.length.{0} Int vs) NLogN.Item.mark) td))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.V)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int vs) tv))
  (hsgn :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) vs x →
        Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int x (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hz :
    Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Sign)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int z) st))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.HC)
      (@List.nil.{0} NLogN.Item))
  (hdc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.DC)
      (@List.nil.{0} NLogN.Item))
  (ha :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.Aux)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.GraphArray.firstArray s
    (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Sign st)
      KoanaKPaths.Machine.GraphArray.Current
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0} Int Int
            (fun (x : Int) => @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) z x)
            (KoanaKPaths.ExteriorCoordinates.wedgeReverse vs
              (KoanaKPaths.Machine.GraphArray.unitArray (@List.length.{0} Int vs)))))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark
          (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Current))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 1000000) (instOfNatNat (nat_lit 1000000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int vs)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Int vs))) := by
  exact @KoanaKPaths.Machine.GraphArray.firstArray_runs
