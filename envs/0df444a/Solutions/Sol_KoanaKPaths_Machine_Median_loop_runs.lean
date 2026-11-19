-- Prove2me | solution 1 for KoanaKPaths.Machine.Median.loop_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.429081+00:00
-- url     : https://prove2.me/submissions/fe2416b8-f044-4934-b790-ae0a73d5a719

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
import Theorems.Thm_KoanaKPaths_Machine_Median_round_runs
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
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


lemma loopT {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = true)
    (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog (.loop i f p) s1 s2 d) :
    IRuns I iprog (.loop i f p) s s2 (c+d+30) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d'+30,by omega,.loopT hf h1 h2⟩
lemma loopF {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = false) :
    IRuns I iprog (.loop i f p) s s 30 := of_exec (.loopF hf)

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
attribute [local simp] Records Lo Hi Mid Ruler Rem Count Threshold Saved Flag





lemma midpoint_width (lo hi w : ℕ) (hl : zsz (lo : ℤ)≤ w) (hh : zsz (hi : ℤ)≤ w) :
    zsz (((lo+hi)/2 : ℕ) : ℤ)≤ w := by
  apply (Wedge.zsz_le_iff _ _).mpr
  have hl' := (Wedge.zsz_le_iff (lo : ℤ) w).mp hl
  have hh' := (Wedge.zsz_le_iff (hi : ℤ) w).mp hh
  simp only [Int.natAbs_natCast] at hl' hh' ⊢
  omega

lemma nextBounds_width (xs : List ℤ) (t lo hi w : ℕ) (hw : 1≤ w)
    (hl : zsz (lo : ℤ)≤ w) (hh : zsz (hi : ℤ)≤ w) :
    zsz ((nextBounds xs t lo hi).1 : ℤ)≤ w+1 ∧
      zsz ((nextBounds xs t lo hi).2 : ℤ)≤ w+1 := by
  have hm := midpoint_width lo hi w hl hh
  have hinc : zsz ((((lo+hi)/2+1 : ℕ)) : ℤ)≤ w+1 := by
    have h1 : zsz (1 : ℤ)≤ w := by simpa [Wedge.zsz_eq_size] using hw
    simpa only [Nat.cast_add,Nat.cast_one] using Wedge.zsz_add_le (((lo+hi)/2 : ℕ) : ℤ) 1 w hm h1
  unfold nextBounds
  split_ifs <;> simp only [Prod.fst,Prod.snd] <;> omega



end KoanaKPaths.Machine.Median

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median

attribute [local simp] Fuel Records Lo Hi Mid Ruler Count Threshold Saved Flag





lemma searchBounds_next (xs : List ℤ) (t L lo hi : ℕ) :
    searchBounds (fun mid => t≤ countLE (mid : ℤ) xs) (L+1) lo hi=
      searchBounds (fun mid => t≤ countLE (mid : ℤ) xs) L
        (nextBounds xs t lo hi).1 (nextBounds xs t lo hi).2 := by
  rw [searchBounds]
  unfold nextBounds
  split_ifs <;> rfl

lemma loop_runs (I : List Sym) (L : ℕ) : ∀ (s : IState NS) (xs : List ℤ) (t lo hi w : ℕ)
    (rt lt ht rult : List Item),
    s.G Fuel=List.replicate L .mark → s.G Records=xs.map Item.int ++ .mark::rt →
    s.G Lo=.int (lo : ℤ)::lt → s.G Hi=.int (hi : ℤ)::ht →
    s.G Ruler=.int 2::rult → s.G Mid=[] → s.G Count=[] →
    s.G Threshold=List.replicate t .mark → s.G Saved=[] → s.G Flag=[] →
    1≤ w → zsz (lo : ℤ)≤ w → zsz (hi : ℤ)≤ w →
    (∀ x∈xs, zsz x≤ w) →
    IRuns I Fin.elim0 loop s
      (boundsState s 0 (searchBounds (fun mid => t≤ countLE (mid : ℤ) xs) L lo hi) lt ht)
      (10000*(w+L+1)*(xs.length+1)*L+30) := by
  induction L with
  | zero =>
    intro s xs t lo hi w rt lt ht rult hFuel hrec hl hh hrul hmid hc hthr hs hf hw hlo hhi hx
    have hcl : decide (s.cl Fuel=Cls.mark)=false := by simp [IState.cl,hFuel,cls]
    have he : boundsState s 0 (searchBounds (fun mid => t≤ countLE (mid : ℤ) xs) 0 lo hi) lt ht=s := by
      unfold boundsState searchBounds
      simp only [Prod.fst,Prod.snd,List.replicate_zero]
      have hF : s.G Fuel=[] := by simpa using hFuel
      rw [← hF,← hl,← hh]
      simp
    rw [he]
    exact Native.loopF hcl
  | succ L ih =>
    intro s xs t lo hi w rt lt ht rult hFuel hrec hl hh hrul hmid hc hthr hs hf hw hlo hhi hx
    let s0 := s.upd Fuel (List.replicate L .mark)
    let nb := nextBounds xs t lo hi
    let s1 := (s0.upd Lo (.int (nb.1 : ℤ)::lt)).upd Hi (.int (nb.2 : ℤ)::ht)
    have h0 : IExec I Fin.elim0 (.op (.unmark Fuel)) s s0 1 :=
      .op (.unmark (by simpa [List.replicate_succ] using hFuel))
    have h1 : IRuns I Fin.elim0 round s0 s1 (8000*(w+1)*(xs.length+1)) := by
      exact round_runs I s0 xs t lo hi w rt lt ht rult
        (by simp [s0,hrec]) (by simp [s0,hl]) (by simp [s0,hh])
        (by simp [s0,hrul]) (by simp [s0,hmid]) (by simp [s0,hc])
        (by simp [s0,hthr]) (by simp [s0,hs]) (by simp [s0,hf]) hlo hhi hx
    have hn := nextBounds_width xs t lo hi w hw hlo hhi
    have htail := ih s1 xs t nb.1 nb.2 (w+1) rt lt ht rult
      (by simp [s1,s0]) (by simp [s1,s0,hrec]) (by simp [s1]) (by simp [s1])
      (by simp [s1,s0,hrul]) (by simp [s1,s0,hmid]) (by simp [s1,s0,hc])
      (by simp [s1,s0,hthr]) (by simp [s1,s0,hs]) (by simp [s1,s0,hf])
      (by omega) hn.1 hn.2 (by intro x hx'; have := hx x hx'; omega)
    have hcl : decide (s.cl Fuel=Cls.mark)=true := by simp [IState.cl,hFuel,List.replicate_succ,cls]
    have hr := Native.loopT hcl (Native.seq (Native.of_exec h0) h1) htail
    have he : boundsState s1 0
        (searchBounds (fun mid => t≤ countLE (mid : ℤ) xs) L nb.1 nb.2) lt ht=
      boundsState s 0 (searchBounds (fun mid => t≤ countLE (mid : ℤ) xs) (L+1) lo hi) lt ht := by
      rw [searchBounds_next]
      apply itemState_ext
      · intro i
        by_cases hF : i=Fuel
        · subst i; simp [boundsState,s1,s0,nb]
        by_cases hL : i=Lo
        · subst i; simp [boundsState,s1,s0,nb]
        by_cases hH : i=Hi
        · subst i; simp [boundsState,s1,s0,nb]
        simp [boundsState,s1,s0,nb,IState.upd,Function.update_apply,hF,hL,hH]
      · rfl
      · rfl
    rw [he] at hr
    change IRuns I Fin.elim0 loop s _ _ at hr
    apply Native.mono hr
    ring_nf
    omega

end KoanaKPaths.Machine.Median

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (L : Nat) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (xs : List.{0} Int)
  (t lo hi w : Nat) (rt lt ht rult : List.{0} NLogN.Item),
  @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Fuel)
      (@List.replicate.{0} NLogN.Item L NLogN.Item.mark) →
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records)
        (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
          (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
          (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark rt)) →
      @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Lo)
          (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt lo)) lt) →
        @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Hi)
            (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt hi)) ht) →
          @Eq.{1} (List.{0} NLogN.Item)
              (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Ruler)
              (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))
                rult) →
            @Eq.{1} (List.{0} NLogN.Item)
                (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid)
                (@List.nil.{0} NLogN.Item) →
              @Eq.{1} (List.{0} NLogN.Item)
                  (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)
                  (@List.nil.{0} NLogN.Item) →
                @Eq.{1} (List.{0} NLogN.Item)
                    (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Threshold)
                    (@List.replicate.{0} NLogN.Item t NLogN.Item.mark) →
                  @Eq.{1} (List.{0} NLogN.Item)
                      (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)
                      (@List.nil.{0} NLogN.Item) →
                    @Eq.{1} (List.{0} NLogN.Item)
                        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag)
                        (@List.nil.{0} NLogN.Item) →
                      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) w →
                        @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt lo)) w →
                          @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt hi)) w →
                            (∀ (x : Int),
                                @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
                                  @LE.le.{0} Nat instLENat (NLogN.zsz x) w) →
                              @NLogN.IRuns KoanaKPaths.Machine.Median.NS
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
                                (@Fin.elim0.{1}
                                  (NLogN.IStmt KoanaKPaths.Machine.Median.NS
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                KoanaKPaths.Machine.Median.loop s
                                (KoanaKPaths.Machine.Median.boundsState s
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                  (@KoanaKPaths.Machine.Median.searchBounds
                                    (fun (mid : Nat) =>
                                      @LE.le.{0} Nat instLENat t
                                        (KoanaKPaths.Machine.Median.countLE (@Nat.cast.{0} Int instNatCastInt mid) xs))
                                    (fun (a : Nat) =>
                                      Nat.decLe t
                                        (KoanaKPaths.Machine.Median.countLE (@Nat.cast.{0} Int instNatCastInt a) xs))
                                    L lo hi)
                                  lt ht)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 10000) (instOfNatNat (nat_lit 10000)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w L)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@List.length.{0} Int xs)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    L)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Median.loop_runs
