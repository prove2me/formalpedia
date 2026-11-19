-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.readSign_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.067072+00:00
-- url     : https://prove2.me/submissions/a1b17607-584c-4f22-b653-ea702d66a5fe

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
import Theorems.Thm_KoanaKPaths_Machine_Trial_querySign_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_signAddress_runs
import Theorems.Thm_NLogN_smul_runs
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
































end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Wedge
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]







lemma zsz_sign (z : ℤ) (hz : z=1 ∨ z = -1) : zsz z=1 := by
  rcases hz with rfl|rfl <;> simp [zsz_eq_size]





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





















end KoanaKPaths.Machine.Wedge

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArrayLookup

lemma forwardCost_bound (pre : List (List ℤ)) (P w : ℕ)
    (hlen : ∀ a∈pre, a.length≤P) (hw : ∀ a∈pre, ∀ x∈a, zsz x≤w) :
    forwardCost pre ≤ (200*(w+1)*(P+1)+35)*pre.length+30 := by
  have hs := Wedge.sum_map_le_mul (fun a => moveIntsCost a+35) pre (200*(w+1)*(P+1)+35) (by
    intro a ha
    have h := Wedge.moveIntsCost_bound a w (hw a ha)
    have hl := hlen a ha
    nlinarith)
  unfold forwardCost
  omega

lemma backwardCost_bound (pre : List (List ℤ)) (P w : ℕ)
    (hlen : ∀ a∈pre, a.length≤P) (hw : ∀ a∈pre, ∀ x∈a, zsz x≤w) :
    backwardCost pre ≤ (200*(w+1)*(P+1)+35)*pre.length+30 := by
  have hs := Wedge.sum_map_le_mul (fun a => moveIntsCost a.reverse+35) pre (200*(w+1)*(P+1)+35) (by
    intro a ha
    have h := Wedge.moveIntsCost_bound a.reverse w (by simpa using hw a ha)
    simp only [List.length_reverse] at h
    have hl := hlen a ha
    nlinarith)
  unfold backwardCost
  omega

lemma duplicateMoveIntsCost_bound (xs : List ℤ) (w : ℕ) (hw : ∀ x∈xs, zsz x≤w) :
    duplicateMoveIntsCost xs ≤ 400*(w+1)*(xs.length+1) := by
  have hs := Wedge.sum_map_le_mul
    (fun z => dupCost (zsz z)+17+(2*moveCost (zsz z)+19)+30) xs (211*w+313) (by
      intro z hz
      have h := hw z hz
      simp only [dupCost,zipCost,moveCost]
      nlinarith)
  unfold duplicateMoveIntsCost
  nlinarith

lemma lookupCost_bound (pre : List (List ℤ)) (target : List ℤ) (P w : ℕ)
    (hlen : ∀ a∈pre, a.length≤P) (hw : ∀ a∈pre, ∀ x∈a, zsz x≤w)
    (htlen : target.length≤P) (htw : ∀ x∈target, zsz x≤w) :
    lookupCost pre target ≤ 2000*(w+1)*(P+1)*(pre.length+1) := by
  have hf := forwardCost_bound pre P w hlen hw
  have hb := backwardCost_bound pre P w hlen hw
  have hc := duplicateMoveIntsCost_bound target w htw
  have hm := Wedge.moveIntsCost_bound target.reverse w (by simpa using htw)
  simp only [List.length_reverse] at hm
  unfold lookupCost
  nlinarith [Nat.zero_le (w*P),Nat.zero_le (w*P*pre.length),Nat.zero_le (w*pre.length),
    Nat.zero_le (P*pre.length)]



end KoanaKPaths.Machine.ArrayLookup

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
attribute [local simp] SignDB SignLookup.DB SignLookup.Out SignLookup.Count SignLookup.Back SignLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp







lemma signLookupCost_eq (pre : List (List ℤ)) (target : List ℤ) :
    SignLookup.lookupCost pre target=ArrayLookup.lookupCost pre target := rfl

lemma querySign_cost (xs : List ℤ) (i : Fin xs.length) (hx : ∀ x∈xs, x=1 ∨ x= -1) :
    1100*(i.val+1)+SignLookup.lookupCost
      ((xs.reverse.map (fun x => [x])).take i.val) [xs.reverse[i.val]'(by simpa using i.isLt)]≤
        10000*(xs.length+1) := by
  have hwidth : ∀ z∈xs.reverse, zsz z≤1 := by
    intro z hz
    exact Nat.le_of_eq (Wedge.zsz_sign z (hx z (by simpa using hz)))
  have hw : ∀ a∈(xs.reverse.map (fun x => [x])).take i.val, a.length≤1 ∧ ∀ z∈a, zsz z≤1 := by
    intro a ha
    obtain ⟨x,hx',rfl⟩ := List.mem_map.mp (List.mem_of_mem_take ha)
    exact ⟨by simp,by simpa using hwidth x hx'⟩
  have hz := hwidth (xs.reverse[i.val]'(by simpa using i.isLt)) (List.getElem_mem _)
  rw [signLookupCost_eq]
  have hb := ArrayLookup.lookupCost_bound
    ((xs.reverse.map (fun x => [x])).take i.val) [xs.reverse[i.val]'(by simpa using i.isLt)] 1 1
    (fun a ha => (hw a ha).1) (fun a ha => (hw a ha).2) (by simp) (by simpa using hz)
  have hl : ((xs.reverse.map (fun x => [x])).take i.val).length≤ i.val := List.length_take_le _ _
  nlinarith [i.isLt]

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square
attribute [local simp] SignDB SignLookup.DB SignLookup.Out SignLookup.Count SignLookup.Back SignLookup.Tmp
  BitCounter.Source BitCounter.Count BitCounter.Tmp Total
variable {v : ℕ}



lemma readSign_runs (I : List Sym) (reg : Fin v→Fin NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (xs : List ℤ) (w : ℕ) (hw : 1≤ w)
    (he : e.width values≤ w) (hT : zsz (xs.length : ℤ)≤ w) (hj : e.eval values< xs.length)
    (s : IState NS) (tt rest : List Item) (hTotal : s.G Total=.int (xs.length : ℤ)::tt)
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail)
    (hc : s.G BitCounter.Count=[]) (ht : s.G BitCounter.Tmp=[])
    (hindex : s.G SignLookup.Count=[]) (hback : s.G SignLookup.Back=[])
    (htmp : s.G SignLookup.Tmp=[]) (hdb : s.G SignDB=signItems xs++rest)
    (hxs : ∀ x∈xs, x=1 ∨ x= -1) :
    IRuns I Fin.elim0 (readSign reg e) s
      (s.upd SignLookup.Out (.int (xs[e.eval values]'hj)::s.G SignLookup.Out))
      (30000*(e.size+2)*(w+1)^2+10000*(xs.length+1)) := by
  let j := e.eval values
  let idx : Fin xs.length := ⟨xs.length-1-j,by dsimp [j]; omega⟩
  let s1 := s.upd BitCounter.Source (.int (idx.val : ℤ)::s.G BitCounter.Source)
  have h0 : IRuns I Fin.elim0 (signAddress reg e) s s1 (30000*(e.size+2)*(w+1)^2) :=
    signAddress_runs I reg hreg values e xs.length w hw he hT hj s tt hTotal hv
  have h1 := querySign_runs I s1 xs idx (s.G BitCounter.Source) rest
    (by simp [s1]) (by simp [s1,hc]) (by simp [s1,ht]) (by simp [s1,hindex])
    (by simp [s1,hback]) (by simp [s1,htmp]) (by simp [s1,hdb])
  have hread : xs.reverse[idx.val]'(by simpa using idx.isLt)=xs[j]'hj := by
    rw [List.getElem_reverse]
    congr 1
    dsimp [idx,j]
    omega
  have hpost : (s1.upd BitCounter.Source (s.G BitCounter.Source)).upd SignLookup.Out
      (.int (xs.reverse[idx.val]'(by simpa using idx.isLt))::s1.G SignLookup.Out)=
      s.upd SignLookup.Out (.int (xs[j]'hj)::s.G SignLookup.Out) := by
    simp [s1,hread]
  rw [hpost] at h1
  have h := Native.seq h0 h1
  apply Native.mono h
  have hc := querySign_cost xs idx hxs
  omega

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ {v : Nat} (I : List.{0} NLogN.Sym) (reg : Fin v → Fin KoanaKPaths.Machine.Trial.NS)
  (hreg : ∀ (i : Fin v), @Ne.{1} (Fin KoanaKPaths.Machine.Trial.NS) (reg i) KoanaKPaths.Machine.Square.Eval)
  (values : Fin v → Nat) (e : KoanaKPaths.Machine.Arithmetic.Expr v) (xs : List.{0} Int) (w : Nat)
  (hw : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w)
  (he : @LE.le.{0} Nat instLENat (@KoanaKPaths.Machine.Arithmetic.Expr.width v values e) w)
  (hT : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) w)
  (hj : @LT.lt.{0} Nat instLTNat (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e) (@List.length.{0} Int xs))
  (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) (tt rest : List.{0} NLogN.Item)
  (hTotal :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@List.length.{0} Int xs))) tt))
  (hv :
    ∀ (i : Fin v),
      @Exists.{1} (List.{0} NLogN.Item) fun (tail : List.{0} NLogN.Item) =>
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s (reg i))
          (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (values i))) tail))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@List.nil.{0} NLogN.Item))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hindex :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hback :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (htmp :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems xs) rest))
  (hxs :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        Or (@Eq.{1} Int x (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Eq.{1} Int x
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))),
  @NLogN.IRuns KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Trial.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (@KoanaKPaths.Machine.Trial.readSign v reg e) s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Out
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@GetElem.getElem.{0, 0, 0} (List.{0} Int) Nat Int
            (fun (as : List.{0} Int) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Int as))
            (@List.instGetElemNatLtLength.{0} Int) xs (@KoanaKPaths.Machine.Arithmetic.Expr.eval v values e) hj))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Out)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 30000) (instOfNatNat (nat_lit 30000)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@KoanaKPaths.Machine.Arithmetic.Expr.size v e)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int xs)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  exact @KoanaKPaths.Machine.Trial.readSign_runs
