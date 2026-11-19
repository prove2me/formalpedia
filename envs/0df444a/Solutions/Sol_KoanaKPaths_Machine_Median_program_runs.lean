-- Prove2me | solution 1 for KoanaKPaths.Machine.Median.program_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:46:16.267502+00:00
-- url     : https://prove2.me/submissions/fcefc6a3-a067-4fa2-b91f-0f1badbedb9e

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
import Theorems.Thm_KoanaKPaths_Machine_Median_initialize_exec
import Theorems.Thm_KoanaKPaths_Machine_Median_loop_runs
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
open KoanaKPaths.ExteriorCoordinates

lemma zsz_eq_size (z : ℤ) : zsz z=z.natAbs.size := by
  simp [zsz,zbits,nbits_eq_bits,Nat.size_eq_bits_len]

lemma zsz_le_iff (z : ℤ) (w : ℕ) : zsz z ≤ w ↔ z.natAbs<2^w := by
  rw [zsz_eq_size,Nat.size_le]

















lemma addIntCost_formula (L : ℕ) : addIntCost L=297*L+393 := by
  simp only [addIntCost,addMagCost,subMagCost,zipCost,moveCost]
  ring

















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
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates







lemma sum_finRange {A : Type} [AddCommMonoid A] (n : ℕ) (f : Fin n→A) :
    ((List.finRange n).map f).sum=∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]














end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Sampling

lemma median_le_iff_count {α : Type} [LinearOrder α] [Inhabited α] (b : ℕ)
    (x : Fin (2*b+1)→α) (t : α) :
    median b x≤ t ↔ b+1≤(Finset.univ.filter (fun i => x i≤ t)).card := by
  classical
  let good := Finset.univ.filter (fun i => x i≤ t)
  let bad := Finset.univ.filter (fun i => t< x i)
  have hc : good.card+bad.card=2*b+1 := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin (2*b+1) => x i≤ t)
    simpa only [good,bad,not_le,Finset.card_univ,Fintype.card_fin] using h
  constructor
  · intro hm
    by_contra hn
    have hb : b+1≤ bad.card := by change ¬b+1≤ good.card at hn; omega
    obtain ⟨s,hsbad,hsc⟩ := Finset.exists_subset_card_eq hb
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    have hsel : t< selectedMin s x := by
      rw [selectedMin,dif_pos hne,Finset.lt_inf'_iff]
      intro i hi
      exact (Finset.mem_filter.mp (hsbad hi)).2
    have hs : s∈Finset.univ.powersetCard (b+1) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s,hsc⟩
    have hlow : selectedMin s x≤ median b x := Finset.le_sup' (fun s => selectedMin s x) hs
    exact (not_lt_of_ge hm) (hsel.trans_le hlow)
  · intro hg
    change b+1≤ good.card at hg
    apply Finset.sup'_le
    intro s hs
    have hsc := (Finset.mem_powersetCard.mp hs).2
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i,hi⟩ := Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.subset_univ s) (Finset.subset_univ good) (by
        simp only [Finset.card_univ,Fintype.card_fin]; omega)
    obtain ⟨his,hig⟩ := Finset.mem_inter.mp hi
    rw [selectedMin,dif_pos hne]
    exact (Finset.inf'_le x his).trans (Finset.mem_filter.mp hig).2







end KoanaKPaths.Sampling

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Machine.Median



lemma searchBounds_correct (test : ℕ→Prop) [DecidablePred test] (m L lo hi : ℕ)
    (ht : ∀ t, test t ↔ m≤ t) (hlo : lo≤ m) (hhi : m≤ hi) (hw : hi-lo<2^L) :
    searchBounds test L lo hi=(m,m) := by
  induction L generalizing lo hi with
  | zero => simp only [searchBounds]; norm_num at hw; congr <;> omega
  | succ L ih =>
    simp only [searchBounds]
    split_ifs with h
    · have hm := (ht _).mp h
      apply ih _ _ hlo hm
      rw [pow_succ] at hw
      omega
    · have hm : (lo+hi)/2< m := by have := (ht _).not.mp h; omega
      apply ih _ _ (by omega) hhi
      rw [pow_succ] at hw
      omega

lemma countLE_eq_sum (mid : ℤ) (xs : List ℤ) :
    countLE mid xs=(xs.map (fun x => if x≤ mid then 1 else 0)).sum := by
  induction xs with
  | nil => simp [countLE]
  | cons x xs ih =>
    by_cases h : x≤ mid <;> simp [countLE,h] at ih ⊢ <;> omega

lemma countLE_finRange (b : ℕ) (f : Fin (2*b+1)→ℕ) (mid : ℕ) :
    countLE (mid : ℤ) ((List.finRange (2*b+1)).map (fun i => (f i : ℤ)))=
      (Finset.univ.filter (fun i => f i≤ mid)).card := by
  rw [countLE_eq_sum]
  simp only [List.map_map,Function.comp_def]
  rw [KoanaKPaths.Main.sum_finRange]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  have h : ((f i : ℤ)≤ (mid : ℤ)) ↔ f i≤ mid := by omega
  simp only [h]

lemma searchBounds_median (b L : ℕ) (f : Fin (2*b+1)→ℕ) (hf : ∀ i, f i<2^L) :
    searchBounds (fun mid => b+1≤ countLE (mid : ℤ)
      ((List.finRange (2*b+1)).map (fun i => (f i : ℤ)))) L 0 (2^L-1)=
      (KoanaKPaths.Sampling.median b f,KoanaKPaths.Sampling.median b f) := by
  apply searchBounds_correct
  · intro t
    rw [countLE_finRange]
    exact (KoanaKPaths.Sampling.median_le_iff_count b f t).symm
  · omega
  · apply (KoanaKPaths.Sampling.median_le_iff_count b f _).mpr
    have hg : Finset.univ.filter (fun i => f i≤ 2^L-1)=Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      have := hf i
      omega
    rw [hg]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  · have hp : 0<2^L := by positivity
    omega

end KoanaKPaths.Machine.Median

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median



attribute [local simp] Template CopyTmp Output Fuel Hi Ruler Work Lo









lemma initializeCost_bound (L : ℕ) :
    (shlCost 1+161)*L+addIntCost (zsz ((2 : ℤ)^L)+1)+162≤2000*(L+1) := by
  have hz : zsz ((2 : ℤ)^L)=L+1 := by
    simpa [Wedge.zsz_eq_size,Int.natAbs_pow] using (Nat.size_pow (n := L))
  rw [hz,Wedge.addIntCost_formula]
  norm_num [shlCost,moveCost,zipCost]
  omega

end KoanaKPaths.Machine.Median

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Lo Hi Ruler Output



lemma finishMedian_exec (I : List Sym) (s : IState NS) (m : ℕ) (lt ht rt : List Item)
    (hl : s.G Lo=.int (m : ℤ)::lt) (hh : s.G Hi=.int (m : ℤ)::ht)
    (hr : s.G Ruler=.int 2::rt) :
    IExec I Fin.elim0 finishMedian s
      ((((s.upd Hi ht).upd Lo lt).upd Output (.int (m : ℤ)::s.G Output)).upd Ruler rt)
      (2*zsz (m : ℤ)+2*moveCost (zsz (m : ℤ))+27) := by
  let s1 := s.upd Hi ht
  let s2 := (s1.upd Lo lt).upd Output (.int (m : ℤ)::s.G Output)
  let s3 := s2.upd Ruler rt
  have h1 : IExec I Fin.elim0 (.op (.drop Hi)) s s1 (2*zsz (m : ℤ)+2) := .op (.drop hh)
  have h2 : IExec I Fin.elim0 (.op (.mv Lo Output)) s1 s2 (2*moveCost (zsz (m : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s1) (i := Lo) (j := Output) (a := (m : ℤ)) (L := lt)
        (by decide) (by simp [s1,hl]))
    simpa [s2,s1] using h
  have h3 : IExec I Fin.elim0 (.op (.drop Ruler)) s2 s3 6 := by
    have hz : zsz (2 : ℤ)=2 := by simpa [Wedge.zsz_eq_size] using (Nat.size_pow (n := 1))
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.drop (s := s2) (i := Ruler) (a := 2) (L := rt) (by simp [s2,s1,hr]))
    simpa only [hz] using h
  have h := IExec.seq h1 (IExec.seq h2 h3)
  change IExec I Fin.elim0 finishMedian s _ _ at h
  convert h using 1 <;> omega

lemma finishMedian_cost (m w : ℕ) (hm : zsz (m : ℤ)≤ w) :
    2*zsz (m : ℤ)+2*moveCost (zsz (m : ℤ))+27≤1000*(w+1) := by
  unfold moveCost
  omega

end KoanaKPaths.Machine.Median

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Template CopyTmp Output Fuel Records Lo Hi Mid Ruler Count Threshold Saved Flag



lemma median_bound (b L : ℕ) (f : Fin (2*b+1)→ℕ) (hf : ∀ i, f i<2^L) :
    KoanaKPaths.Sampling.median b f<2^L := by
  have h : KoanaKPaths.Sampling.median b f≤2^L-1 := by
    apply (KoanaKPaths.Sampling.median_le_iff_count b f _).mpr
    have hg : Finset.univ.filter (fun i => f i≤2^L-1)=Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      have := hf i
      omega
    rw [hg]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  have hp : 0<2^L := by positivity
  omega

/-- An exact median machine with linear dependence on the number of groups. -/
lemma program_runs (I : List Sym) (s : IState NS) (b L : ℕ) (f : Fin (2*b+1)→ℕ)
    (rt : List Item) (hL : 1≤ L)
    (hrec : s.G Records=((List.finRange (2*b+1)).map (fun i => (f i : ℤ))).map Item.int ++ .mark::rt)
    (ht : s.G Template=List.replicate L .mark) (hFuel : s.G Fuel=[])
    (hcopy : s.G CopyTmp=[]) (hmid : s.G Mid=[]) (hc : s.G Count=[])
    (hthr : s.G Threshold=List.replicate (b+1) .mark) (hs : s.G Saved=[]) (hf : s.G Flag=[])
    (hval : ∀ i, f i<2^L) :
    IRuns I Fin.elim0 program s
      (s.upd Output (.int ((KoanaKPaths.Sampling.median b f : ℕ) : ℤ)::s.G Output))
      (30000*(L+1)^2*(2*b+2)) := by
  let xs := (List.finRange (2*b+1)).map (fun i => (f i : ℤ))
  let m := KoanaKPaths.Sampling.median b f
  let s0 := ((((s.upd Ruler (.int 2::s.G Ruler)).upd Hi
    (.int ((2^L-1 : ℕ) : ℤ)::s.G Hi)).upd Lo (.int 0::s.G Lo)).upd Fuel (List.replicate L .mark))
  let s1 := boundsState s0 0 (m,m) (s.G Lo) (s.G Hi)
  have h0 : IExec I Fin.elim0 initializeInterval s s0
      ((shlCost 1+161)*L+addIntCost (zsz ((2 : ℤ)^L)+1)+162) := initialize_exec I s L ht hFuel hcopy
  have hxs : ∀ x∈xs, zsz x≤ L := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    apply (Wedge.zsz_le_iff _ _).mpr
    simpa only [Int.natAbs_natCast] using hval i
  have hlo : zsz (0 : ℤ)≤ L := by simp [Wedge.zsz_eq_size]
  have hhi : zsz ((2^L-1 : ℕ) : ℤ)≤ L := by
    apply (Wedge.zsz_le_iff _ _).mpr
    simp only [Int.natAbs_natCast]
    have hp : 0<2^L := by positivity
    omega
  have h1 : IRuns I Fin.elim0 loop s0 s1 (10000*(L+L+1)*(xs.length+1)*L+30) := by
    have h := loop_runs I L s0 xs (b+1) 0 (2^L-1) L rt (s.G Lo) (s.G Hi) (s.G Ruler)
      (by simp [s0]) (by simp [s0,hrec,xs]) (by simp [s0]) (by simp [s0])
      (by simp [s0]) (by simp [s0,hmid]) (by simp [s0,hc])
      (by simp [s0,hthr]) (by simp [s0,hs]) (by simp [s0,hf]) hL hlo hhi hxs
    rw [show searchBounds (fun mid => b+1≤ countLE (mid : ℤ) xs) L 0 (2^L-1)=(m,m) from
      searchBounds_median b L f hval] at h
    exact h
  have h2 := finishMedian_exec I s1 m (s.G Lo) (s.G Hi) (s.G Ruler)
    (by simp [s1,boundsState]) (by simp [s1,boundsState]) (by simp [s1,boundsState,s0])
  have he : ((((s1.upd Hi (s.G Hi)).upd Lo (s.G Lo)).upd Output
      (.int (m : ℤ)::s1.G Output)).upd Ruler (s.G Ruler))=
      s.upd Output (.int (m : ℤ)::s.G Output) := by
    apply itemState_ext
    · intro i
      by_cases hR : i=Ruler
      · subst i; simp [s1,boundsState,s0]
      by_cases hH : i=Hi
      · subst i; simp [s1,boundsState,s0]
      by_cases hL : i=Lo
      · subst i; simp [s1,boundsState,s0]
      by_cases hF : i=Fuel
      · subst i; simp [s1,boundsState,s0,hFuel]
      by_cases hO : i=Output
      · subst i; simp [s1,boundsState,s0]
      simp [s1,boundsState,s0,IState.upd,Function.update_apply,hR,hH,hL,hF,hO]
    · rfl
    · rfl
  rw [he] at h2
  have h := Native.seq (Native.of_exec h0) (Native.seq h1 (Native.of_exec h2))
  change IRuns I Fin.elim0 program s _ _ at h
  apply Native.mono h
  have hi := initializeCost_bound L
  have hm : zsz (m : ℤ)≤ L := by
    apply (Wedge.zsz_le_iff _ _).mpr
    simpa only [Int.natAbs_natCast] using median_bound b L f hval
  have hfin := finishMedian_cost m L hm
  have hlen : xs.length=2*b+1 := by simp [xs]
  rw [hlen]
  nlinarith [Nat.zero_le (L*L*b)]

end KoanaKPaths.Machine.Median

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (b L : Nat)
  (f :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Nat)
  (rt : List.{0} NLogN.Item)
  (hL : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) L)
  (hrec :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.map.{0, 0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            Int
            (fun
                (i :
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
              @Nat.cast.{0} Int instNatCastInt (f i))
            (List.finRange
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark rt)))
  (ht :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Template)
      (@List.replicate.{0} NLogN.Item L NLogN.Item.mark))
  (hFuel :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Fuel)
      (@List.nil.{0} NLogN.Item))
  (hcopy :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.CopyTmp)
      (@List.nil.{0} NLogN.Item))
  (hmid :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid)
      (@List.nil.{0} NLogN.Item))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)
      (@List.nil.{0} NLogN.Item))
  (hthr :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Threshold)
      (@List.replicate.{0} NLogN.Item
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)
      (@List.nil.{0} NLogN.Item))
  (hf :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag)
      (@List.nil.{0} NLogN.Item))
  (hval :
    ∀
      (i :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @LT.lt.{0} Nat instLTNat (f i)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) L)),
  @NLogN.IRuns KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.program s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Output
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@KoanaKPaths.Sampling.median Nat Nat.instLinearOrder instInhabitedNat b f)))
        (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Output)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 30000) (instOfNatNat (nat_lit 30000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) L
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by
  exact @KoanaKPaths.Machine.Median.program_runs
