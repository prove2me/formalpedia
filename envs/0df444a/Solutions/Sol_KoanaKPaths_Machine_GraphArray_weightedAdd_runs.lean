-- Prove2me | solution 1 for KoanaKPaths.Machine.GraphArray.weightedAdd_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:44:12.89814+00:00
-- url     : https://prove2.me/submissions/fca4e6f1-ed03-4548-94b0-330094bb1305

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
import Theorems.Thm_KoanaKPaths_Machine_Wedge_negate_exec
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
import Theorems.Thm_KoanaKPaths_Machine_zipAddInts_exec
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
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]

lemma zsz_add_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x+y)≤w+1 := by
  apply (zsz_le_iff _ _).mpr
  have hx' := (zsz_le_iff x w).mp hx
  have hy' := (zsz_le_iff y w).mp hy
  have ha := Int.natAbs_add_le x y
  rw [pow_succ]
  omega





lemma zipWith_all {α β γ : Type} (f : α → β → γ) (P : γ → Prop) (xs : List α) (ys : List β)
    (h : ∀ x∈xs, ∀ y∈ys, P (f x y)) : ∀ z∈List.zipWith f xs ys, P z := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      intro z hz
      simp only [List.zipWith_cons_cons,List.mem_cons] at hz
      rcases hz with rfl|hz
      · exact h x (by simp) y (by simp)
      · exact ih ys (fun a ha b hb => h a (by simp [ha]) b (by simp [hb])) z hz



lemma sum_map_le_mul {α : Type} (f : α → ℕ) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs, f x≤C) : (xs.map f).sum ≤ C*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hh := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

lemma moveIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤w) :
    moveIntsCost xs ≤ 200*(w+1)*(xs.length+1) := by
  have hh := moveIntsCost_le xs w h
  nlinarith



lemma addIntCost_formula (L : ℕ) : addIntCost L=297*L+393 := by
  simp only [addIntCost,addMagCost,subMagCost,zipCost,moveCost]
  ring

lemma zipAddIntsCost_bound (xs ys : List ℤ) (w : ℕ)
    (hx : ∀ z∈xs, zsz z≤w) (hy : ∀ z∈ys, zsz z≤w) :
    zipAddIntsCost xs ys ≤ 1000*(w+1)*(xs.length+1) := by
  have ha : ∀ z∈List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys,
      z≤594*w+423 := by
    apply zipWith_all
    intro x hxm y hym
    rw [addIntCost_formula]
    have hx' := hx x hxm
    have hy' := hy y hym
    omega
  have hs := sum_map_le_mul id
    (List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys) (594*w+423) ha
  simp only [List.map_id_fun,id_eq,List.map_id] at hs
  have hl : (List.zipWith (fun x y => addIntCost (zsz x+zsz y)+30) xs ys).length≤xs.length := by
    simp [List.length_zipWith]
  unfold zipAddIntsCost
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

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}

lemma moveIntsCost_reverse (xs : List ℤ) : moveIntsCost xs.reverse=moveIntsCost xs := by
  simp [moveIntsCost,List.map_reverse]





end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Accumulate




attribute [local simp] Src Acc Tmp Wedge.A



lemma program_exec (I : List Sym) (s : IState NS) (xs ys : List ℤ) (st atail : List Item)
    (hlen : xs.length=ys.length)
    (hs : s.G Src=xs.map Item.int ++ .mark::st) (ha : s.G Acc=ys.map Item.int ++ .mark::atail) :
    IExec I Fin.elim0 program s
      ((s.upd Src st).upd Acc ((List.zipWith (·+·) xs ys).map Item.int ++ .mark::atail))
      (zipAddIntsCost xs ys+moveIntsCost (List.zipWith (·+·) xs ys)+5) := by
  let sum := List.zipWith (·+·) xs ys
  let s1 := s.upd Tmp (.mark::s.G Tmp)
  let s2 := ((s1.upd Src (.mark::st)).upd Acc (.mark::atail)).upd Tmp (sum.reverse.map Item.int ++ s1.G Tmp)
  let s3 := s2.upd Src st
  let s4 := s3.upd Acc atail
  let s5 := s4.upd Acc (.mark::atail)
  let s6 := (s5.upd Tmp (.mark::s.G Tmp)).upd Acc (sum.reverse.reverse.map Item.int ++ s5.G Acc)
  let s7 := s6.upd Tmp (s.G Tmp)
  have h1 : IExec I Fin.elim0 (.op (.mark Tmp)) s s1 1 := .op (.mark)
  have h2 : IExec I Fin.elim0 (zipAddInts Src Acc Tmp) s1 s2 (zipAddIntsCost xs ys) :=
    zipAddInts_exec I Src Acc Tmp (by decide) (by decide) (by decide) s1 xs ys (.mark::st) (.mark::atail)
      (by simp [cls]) hlen (by simp [s1,hs]) (by simp [s1,ha])
  have h3 : IExec I Fin.elim0 (.op (.unmark Src)) s2 s3 1 := by exact .op (.unmark (by simp [s2]))
  have h4 : IExec I Fin.elim0 (.op (.unmark Acc)) s3 s4 1 := by exact .op (.unmark (by simp [s3,s2]))
  have h5 : IExec I Fin.elim0 (.op (.mark Acc)) s4 s5 1 := by
    simpa only [s5,s4,upd_G_self,upd_upd] using
      (IExec.op (IOp.Step.mark (s := s4) (i := Acc)) : IExec I Fin.elim0 _ _ _ 1)
  have h6 : IExec I Fin.elim0 (moveInts Tmp Acc) s5 s6 (moveIntsCost sum.reverse) :=
    moveInts_exec I Tmp Acc (by decide) s5 sum.reverse (.mark::s.G Tmp) (by simp [cls])
      (by simp [s5,s4,s3,s2,s1])
  have h7 : IExec I Fin.elim0 (.op (.unmark Tmp)) s6 s7 1 := by exact .op (.unmark (by simp [s6]))
  have he : s7=(s.upd Src st).upd Acc (sum.map Item.int ++ .mark::atail) := by
    cases s
    simp only [s7,s6,s5,s4,s3,s2,s1,IState.upd]
    congr 1
    funext i
    by_cases hS : i=Src <;> by_cases hA : i=Acc <;> by_cases hT : i=Tmp <;> simp_all
  have hrun := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 (IExec.seq h4 (IExec.seq h5 (IExec.seq h6 h7)))))
  change IExec I Fin.elim0 program s _ _ at hrun
  rw [he] at hrun
  convert hrun using 1
  rw [moveIntsCost_reverse]
  dsimp only [sum]
  omega

end KoanaKPaths.Machine.Accumulate

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.GraphArray
open KoanaKPaths.ExteriorCoordinates
attribute [local simp] Sign Wedge.A Accumulate.Src Accumulate.Acc



lemma weightedAdd_runs (I : List Sym) (s : IState NS) (z : ℤ) (xs ys : List ℤ)
    (st atail sigtail : List Item) (hz : z=1 ∨ z= -1) (hlen : xs.length=ys.length)
    (hsign : s.G Sign=.int z::sigtail)
    (hsrc : s.G Wedge.A=xs.map Item.int ++ .mark::st)
    (hacc : s.G Accumulate.Acc=ys.map Item.int ++ .mark::atail) (w : ℕ)
    (hx : ∀ x∈xs, zsz x≤ w) (hy : ∀ y∈ys, zsz y≤ w) :
    IRuns I Wedge.prog weightedAdd s
      (((s.upd Wedge.A st).upd Sign sigtail).upd Accumulate.Acc
        ((List.zipWith (·+·) (xs.map (fun x => z*x)) ys).map Item.int ++ .mark::atail))
      (10000*(w+2)*(xs.length+1)) := by
  let scaled := xs.map (fun x => z*x)
  let sum := List.zipWith (·+·) scaled ys
  let s0 := (s.upd Wedge.A (scaled.map Item.int ++ .mark::st)).upd Sign sigtail
  let s1 := (s0.upd Wedge.A st).upd Accumulate.Acc (sum.map Item.int ++ .mark::atail)
  have h0 : IExec I Wedge.prog (scaleBySign Sign Wedge.A) s s0
      ((if z<0 then 2*moveIntsCost xs+20*xs.length+3 else 1)+29) :=
    scaleBySign_exec I Sign Wedge.A (by decide) (by decide) s z xs sigtail st hz hsign hsrc
  have hlen' : scaled.length=ys.length := by simpa [scaled] using hlen
  have h1 : IExec I Wedge.prog (liftClosed Accumulate.program) s0 s1
      (zipAddIntsCost scaled ys+moveIntsCost sum+5) := by
    have h := liftClosed_exec I Wedge.prog (Accumulate.program_exec I s0 scaled ys st atail hlen'
      (by simp [s0]) (by simp [s0,hacc]))
    exact h
  have he : s1=((s.upd Wedge.A st).upd Sign sigtail).upd Accumulate.Acc (sum.map Item.int ++ .mark::atail) := by
    apply itemState_ext
    · intro i
      by_cases hA : i=Wedge.A
      · subst i; simp [s1,s0]
      by_cases hS : i=Sign
      · subst i; simp [s1,s0]
      by_cases hC : i=Accumulate.Acc
      · subst i; simp [s1,s0]
      simp [s1,s0,IState.upd,Function.update_apply,hA,hS,hC]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.of_exec h1)
  rw [he] at h
  change IRuns I Wedge.prog weightedAdd s _ _ at h
  apply Native.mono h
  have hsw : ∀ x∈scaled, zsz x≤ w := by
    intro x hx'
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx'
    rcases hz with rfl|rfl <;> simpa [zsz_neg] using hx a ha
  have hsum : ∀ x∈sum, zsz x≤ w+1 := by
    apply Wedge.zipWith_all (·+·) (fun x => zsz x≤ w+1) scaled ys
    intro a ha b hb
    exact Wedge.zsz_add_le a b w (hsw a ha) (hy b hb)
  have hscale := Wedge.moveIntsCost_bound xs w hx
  have hzip := Wedge.zipAddIntsCost_bound scaled ys w hsw hy
  have hmove := Wedge.moveIntsCost_bound sum (w+1) hsum
  have hscaled : scaled.length=xs.length := by simp [scaled]
  have hsumlen : sum.length=xs.length := by simp [sum,List.length_zipWith,hscaled,← hlen]
  rw [hsumlen] at hmove
  rw [hscaled] at hzip
  split_ifs <;> nlinarith

end KoanaKPaths.Machine.GraphArray

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.GraphArray.NS) (z : Int) (xs ys : List.{0} Int)
  (st atail sigtail : List.{0} NLogN.Item)
  (hz :
    Or (@Eq.{1} Int z (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
      (@Eq.{1} Int z (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))))
  (hlen : @Eq.{1} Nat (@List.length.{0} Int xs) (@List.length.{0} Int ys))
  (hsign :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.GraphArray.Sign)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int z) sigtail))
  (hsrc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.A)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark st)))
  (hacc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Accumulate.Acc)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int ys) (@List.cons.{0} NLogN.Item NLogN.Item.mark atail)))
  (w : Nat)
  (hx :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w)
  (hy :
    ∀ (y : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) ys y →
        @LE.le.{0} Nat instLENat (NLogN.zsz y) w),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.GraphArray.weightedAdd s
    (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS
        (@NLogN.IState.upd KoanaKPaths.Machine.GraphArray.NS s KoanaKPaths.Machine.Wedge.A st)
        KoanaKPaths.Machine.GraphArray.Sign sigtail)
      KoanaKPaths.Machine.Accumulate.Acc
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.zipWith.{0, 0, 0} Int Int Int
            (fun (x1 x2 : Int) => @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) x1 x2)
            (@List.map.{0, 0} Int Int
              (fun (x : Int) => @HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul) z x) xs)
            ys))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark atail)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int xs)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @KoanaKPaths.Machine.GraphArray.weightedAdd_runs
