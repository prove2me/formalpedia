-- Prove2me | solution 1 for KoanaKPaths.Machine.Median.round_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:15.590018+00:00
-- url     : https://prove2.me/submissions/ff3b8bc7-bdae-473d-914b-207469a2eb5e

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
import Theorems.Thm_KoanaKPaths_Machine_Median_compareCounts_runs
import Theorems.Thm_KoanaKPaths_Machine_Median_midpoint_exec
import Theorems.Thm_KoanaKPaths_Machine_Median_scan_exec
import Theorems.Thm_KoanaKPaths_Machine_moveInts_exec
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

lemma zsz_sub_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x-y)≤w+1 := by
  simpa only [sub_eq_add_neg] using zsz_add_le x (-y) w hx (by simpa [zsz_neg] using hy)









lemma moveIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ z∈xs, zsz z≤w) :
    moveIntsCost xs ≤ 200*(w+1)*(xs.length+1) := by
  have hh := moveIntsCost_le xs w h
  nlinarith



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

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}







lemma compareCost_bound (x y : ℤ) (w : ℕ) (hx : zsz x≤ w) (hy : zsz y≤ w) :
    compareCost x y≤ 2000*(w+1) := by
  have hd := Wedge.zsz_sub_le x y w hx hy
  have hn : zsz (-y)=zsz y := by simp [Wedge.zsz_eq_size]
  unfold compareCost dupCost zipCost moveCost
  rw [hn,Wedge.addIntCost_formula]
  nlinarith

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median











attribute [local simp] Records Lo Hi Mid Value Tmp Work Count Threshold Back












lemma scanCost_bound (xs : List ℤ) (mid : ℤ) (w : ℕ)
    (hm : zsz mid≤ w) (hx : ∀ x∈xs, zsz x≤ w) :
    scanCost mid xs≤2500*(w+1)*xs.length+30 := by
  induction xs with
  | nil => simp [scanCost]
  | cons x xs ih =>
    have hw := hx x (by simp)
    have ht := ih (fun z hz => hx z (by simp [hz]))
    have hc := compareCost_bound x mid w hw hm
    simp only [scanCost,List.length_cons]
    unfold moveCost
    nlinarith

end KoanaKPaths.Machine.Median

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Records Mid Value Tmp Work Count Threshold Back Saved Flag



lemma countRecords_exec (I : List Sym) (s : IState NS) (xs : List ℤ) (mid : ℤ)
    (rt mt : List Item) (hr : s.G Records=xs.map Item.int ++ .mark::rt)
    (hm : s.G Mid=.int mid::mt) :
    IExec I Fin.elim0 countRecords s
      (s.upd Count (List.replicate (countLE mid xs) .mark ++ s.G Count))
      (scanCost mid xs+moveIntsCost xs.reverse+2) := by
  let s1 := s.upd Back (.mark::s.G Back)
  let s2 := ((s1.upd Records (.mark::rt)).upd Back
    (xs.reverse.map Item.int ++ s1.G Back)).upd Count
      (List.replicate (countLE mid xs) .mark ++ s1.G Count)
  let s3 := (s2.upd Back (.mark::s.G Back)).upd Records
    (xs.map Item.int ++ .mark::rt)
  let s4 := s3.upd Back (s.G Back)
  have h1 : IExec I Fin.elim0 (.op (.mark Back)) s s1 1 := .op (.mark)
  have h2 : IExec I Fin.elim0 scan s1 s2 (scanCost mid xs) :=
    scan_exec I s1 xs mid (.mark::rt) mt (by simp [cls]) (by simp [s1,hr]) (by simp [s1,hm])
  have h3 : IExec I Fin.elim0 (moveInts Back Records) s2 s3 (moveIntsCost xs.reverse) := by
    have hh := moveInts_exec I Back Records (by decide) s2 xs.reverse (.mark::s.G Back)
      (by simp [cls]) (by simp [s2,s1])
    simpa [s3,s2,s1] using hh
  have h4 : IExec I Fin.elim0 (.op (.unmark Back)) s3 s4 1 :=
    .op (.unmark (by simp [s3]))
  have he : s4=s.upd Count (List.replicate (countLE mid xs) .mark ++ s.G Count) := by
    apply itemState_ext
    · intro i
      by_cases hR : i=Records
      · subst i; simp [s4,s3,s2,s1,hr]
      by_cases hB : i=Back
      · subst i; simp [s4,s3,s2,s1]
      by_cases hC : i=Count
      · subst i; simp [s4,s3,s2,s1]
      simp [s4,s3,s2,s1,IState.upd,Function.update_apply,hR,hB,hC]
    · rfl
    · rfl
  have hh := IExec.seq h1 (IExec.seq h2 (IExec.seq h3 h4))
  rw [he] at hh
  change IExec I Fin.elim0 countRecords s _ _ at hh
  convert hh using 1 <;> omega

lemma countRecords_cost_bound (xs : List ℤ) (mid : ℤ) (w : ℕ)
    (hm : zsz mid≤ w) (hx : ∀ x∈xs, zsz x≤ w) :
    scanCost mid xs+moveIntsCost xs.reverse+2≤3000*(w+1)*(xs.length+1) := by
  have hs := scanCost_bound xs mid w hm hx
  have ht := Wedge.moveIntsCost_bound xs.reverse w (by simpa using hx)
  simp only [List.length_reverse] at ht
  nlinarith



lemma quantileTest_runs (I : List Sym) (s : IState NS) (xs : List ℤ) (mid : ℤ)
    (rt mt : List Item) (t w : ℕ)
    (hr : s.G Records=xs.map Item.int ++ .mark::rt) (hm : s.G Mid=.int mid::mt)
    (hc : s.G Count=[]) (ht : s.G Threshold=List.replicate t .mark) (hs : s.G Saved=[])
    (hmid : zsz mid≤ w) (hx : ∀ x∈xs, zsz x≤ w) :
    IRuns I Fin.elim0 quantileTest s
      (s.upd Flag (if t≤ countLE mid xs then .mark::s.G Flag else s.G Flag))
      (4000*(w+1)*(xs.length+1)) := by
  let s1 := s.upd Count (List.replicate (countLE mid xs) .mark)
  have h1 : IExec I Fin.elim0 countRecords s s1 (scanCost mid xs+moveIntsCost xs.reverse+2) := by
    simpa only [hc,List.append_nil] using countRecords_exec I s xs mid rt mt hr hm
  have h2 := compareCounts_runs I s1 (countLE mid xs) t (by simp [s1]) (by simp [s1,ht]) (by simp [s1,hs])
  have hh := Native.seq (Native.of_exec h1) h2
  have he : (s1.upd Count []).upd Flag
      (if t≤ countLE mid xs then .mark::s1.G Flag else s1.G Flag)=
      s.upd Flag (if t≤ countLE mid xs then .mark::s.G Flag else s.G Flag) := by
    simp [s1,← hc]
  rw [he] at hh
  change IRuns I Fin.elim0 quantileTest s _ _ at hh
  apply Native.mono hh
  have hb := countRecords_cost_bound xs mid w hmid hx
  have hn : countLE mid xs≤ xs.length := List.length_filter_le _ _
  nlinarith

end KoanaKPaths.Machine.Median

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median


attribute [local simp] Lo Hi Mid Tmp Work Ruler Rem







lemma midpointCost_bound (lo hi w : ℕ) (hl : zsz (lo : ℤ)≤ w) (hh : zsz (hi : ℤ)≤ w) :
    midpointCost lo hi≤2000*(w+1) := by
  have hm : zsz (((lo+hi)%2 : ℕ) : ℤ)≤ 1 := by
    apply (Wedge.zsz_le_iff _ _).mpr
    simpa only [Int.natAbs_natCast,pow_one] using Nat.mod_lt (lo+hi) (by decide : 0<2)
  unfold midpointCost dupCost zipCost moveCost
  rw [Wedge.addIntCost_formula]
  nlinarith

end KoanaKPaths.Machine.Median

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Median
attribute [local simp] Lo Hi Mid Work Flag



lemma updateUpper_exec (I : List Sym) (s : IState NS) (hi mid : ℕ)
    (ht mt ft : List Item) (hh : s.G Hi=.int (hi : ℤ)::ht)
    (hm : s.G Mid=.int (mid : ℤ)::mt) (hf : s.G Flag=.mark::ft) :
    IExec I Fin.elim0 updateInterval s
      (((s.upd Flag ft).upd Mid mt).upd Hi (.int (mid : ℤ)::ht))
      (2*zsz (hi : ℤ)+2*moveCost (zsz (mid : ℤ))+47) := by
  let s1 := s.upd Flag ft
  let s2 := s1.upd Hi ht
  let s3 := (s2.upd Mid mt).upd Hi (.int (mid : ℤ)::ht)
  have h1 : IExec I Fin.elim0 (.op (.unmark Flag)) s s1 1 := .op (.unmark hf)
  have h2 : IExec I Fin.elim0 (.op (.drop Hi)) s1 s2 (2*zsz (hi : ℤ)+2) :=
    .op (.drop (by simp [s1,hh]))
  have h3 : IExec I Fin.elim0 (.op (.mv Mid Hi)) s2 s3 (2*moveCost (zsz (mid : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.mv (s := s2) (i := Mid) (j := Hi) (a := (mid : ℤ)) (L := mt)
        (by decide) (by simp [s2,s1,hm]))
    simpa [s3,s2] using h
  have hcl : decide (s.cl Flag=Cls.mark)=true := by simp [IState.cl,hf,cls]
  have h : IExec I Fin.elim0 updateInterval s s3
      (1+(2*zsz (hi : ℤ)+2+(2*moveCost (zsz (mid : ℤ))+19))+25) :=
    .iteT hcl (IExec.seq h1 (IExec.seq h2 h3))
  have he : s3=((s.upd Flag ft).upd Mid mt).upd Hi (.int (mid : ℤ)::ht) := by
    apply itemState_ext
    · intro i
      by_cases hF : i=Flag <;> by_cases hM : i=Mid <;> by_cases hH : i=Hi <;>
        simp_all [s3,s2,s1,IState.upd,Function.update_apply]
    · rfl
    · rfl
  rw [he] at h
  convert h using 1 <;> omega

lemma updateLower_exec (I : List Sym) (s : IState NS) (lo mid : ℕ)
    (lt mt : List Item) (hl : s.G Lo=.int (lo : ℤ)::lt)
    (hm : s.G Mid=.int (mid : ℤ)::mt) (hf : s.G Flag=[]) :
    IExec I Fin.elim0 updateInterval s
      ((s.upd Mid mt).upd Lo (.int ((mid+1 : ℕ) : ℤ)::lt))
      (2*zsz (lo : ℤ)+addIntCost (zsz (mid : ℤ)+1)+30) := by
  let s1 := s.upd Lo lt
  let s2 := s1.upd Work (.int 1::s.G Work)
  let sa := (s2.upd Mid mt).upd Work (s.G Work)
  let s3 := sa.upd Lo (.int ((mid+1 : ℕ) : ℤ)::lt)
  have h1 : IExec I Fin.elim0 (.op (.drop Lo)) s s1 (2*zsz (lo : ℤ)+2) := .op (.drop hl)
  have h2 : IExec I Fin.elim0 (.op (.const Work 1)) s1 s2 3 := by
    simpa [s2,s1,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s1) (i := Work) 1))
  have h3 : IExec I Fin.elim0 (.op (.add Mid Work Lo)) s2 s3 (addIntCost (zsz (mid : ℤ)+1)) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0))
      (IOp.Step.add (s := s2) (i := Mid) (j := Work) (k := Lo)
        (a := (mid : ℤ)) (b := 1) (Li := mt) (Lj := s.G Work)
        (by decide) (by simp [s2,s1,hm]) (by simp [s2]))
    simpa [s3,sa,s2,s1,Nat.cast_add,Wedge.zsz_eq_size] using h
  have hcl : decide (s.cl Flag=Cls.mark)=false := by simp [IState.cl,hf,cls]
  have h : IExec I Fin.elim0 updateInterval s s3
      ((2*zsz (lo : ℤ)+2)+(3+addIntCost (zsz (mid : ℤ)+1))+25) :=
    .iteF hcl (IExec.seq h1 (IExec.seq h2 h3))
  have he : s3=(s.upd Mid mt).upd Lo (.int ((mid+1 : ℕ) : ℤ)::lt) := by
    apply itemState_ext
    · intro i
      by_cases hM : i=Mid <;> by_cases hL : i=Lo <;> by_cases hW : i=Work <;>
        simp_all [s3,sa,s2,s1,IState.upd,Function.update_apply]
    · rfl
    · rfl
  rw [he] at h
  convert h using 1 <;> omega

lemma updateUpper_cost (hi mid w : ℕ) (hh : zsz (hi : ℤ)≤ w) (hm : zsz (mid : ℤ)≤ w) :
    2*zsz (hi : ℤ)+2*moveCost (zsz (mid : ℤ))+47≤1000*(w+1) := by
  unfold moveCost
  omega

lemma updateLower_cost (lo mid w : ℕ) (hl : zsz (lo : ℤ)≤ w) (hm : zsz (mid : ℤ)≤ w) :
    2*zsz (lo : ℤ)+addIntCost (zsz (mid : ℤ)+1)+30≤1000*(w+1) := by
  rw [Wedge.addIntCost_formula]
  omega

end KoanaKPaths.Machine.Median

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



lemma round_runs (I : List Sym) (s : IState NS) (xs : List ℤ) (t lo hi w : ℕ)
    (rt lt ht rult : List Item)
    (hrec : s.G Records=xs.map Item.int ++ .mark::rt)
    (hl : s.G Lo=.int (lo : ℤ)::lt) (hh : s.G Hi=.int (hi : ℤ)::ht)
    (hrul : s.G Ruler=.int 2::rult) (hmid : s.G Mid=[])
    (hc : s.G Count=[]) (hthr : s.G Threshold=List.replicate t .mark)
    (hs : s.G Saved=[]) (hf : s.G Flag=[])
    (hlo : zsz (lo : ℤ)≤ w) (hhi : zsz (hi : ℤ)≤ w)
    (hx : ∀ x∈xs, zsz x≤ w) :
    IRuns I Fin.elim0 round s
      ((s.upd Lo (.int ((nextBounds xs t lo hi).1 : ℤ)::lt)).upd Hi
        (.int ((nextBounds xs t lo hi).2 : ℤ)::ht))
      (8000*(w+1)*(xs.length+1)) := by
  let mid := (lo+hi)/2
  let s1 := s.upd Mid [.int (mid : ℤ)]
  let s2 := s1.upd Flag (if t≤ countLE (mid : ℤ) xs then [.mark] else [])
  have h1 : IExec I Fin.elim0 midpoint s s1 (midpointCost lo hi) := by
    simpa only [hmid] using midpoint_exec I s lo hi lt ht rult hl hh hrul
  have hm := midpoint_width lo hi w hlo hhi
  have h2 : IRuns I Fin.elim0 quantileTest s1 s2 (4000*(w+1)*(xs.length+1)) := by
    have h := quantileTest_runs I s1 xs (mid : ℤ) rt [] t w
      (by simp [s1,hrec]) (by simp [s1]) (by simp [s1,hc])
      (by simp [s1,hthr]) (by simp [s1,hs]) hm hx
    simpa [s2,s1,hf] using h
  have hbound := midpointCost_bound lo hi w hlo hhi
  by_cases htest : t≤ countLE (mid : ℤ) xs
  · have h3 := updateUpper_exec I s2 hi mid ht [] []
      (by simp [s2,s1,hh]) (by simp [s2,s1]) (by simp [s2,htest])
    have h := Native.seq (Native.of_exec h1) (Native.seq h2 (Native.of_exec h3))
    have he : ((s2.upd Flag []).upd Mid []).upd Hi (.int (mid : ℤ)::ht)=
        (s.upd Lo (.int ((nextBounds xs t lo hi).1 : ℤ)::lt)).upd Hi
          (.int ((nextBounds xs t lo hi).2 : ℤ)::ht) := by
      simp only [nextBounds,show (lo+hi)/2=mid from rfl,if_pos htest,Prod.fst,Prod.snd]
      apply itemState_ext
      · intro i
        by_cases hL : i=Lo
        · subst i; simp [s2,s1,hl]
        by_cases hH : i=Hi
        · subst i; simp [s2,s1]
        by_cases hM : i=Mid
        · subst i; simp [s2,s1,hmid]
        by_cases hF : i=Flag
        · subst i; simp [s2,s1,hf]
        simp [s2,s1,IState.upd,Function.update_apply,hL,hH,hM,hF]
      · rfl
      · rfl
    rw [he] at h
    change IRuns I Fin.elim0 round s _ _ at h
    apply Native.mono h
    have hb := updateUpper_cost hi mid w hhi hm
    nlinarith
  · have h3 := updateLower_exec I s2 lo mid lt []
      (by simp [s2,s1,hl]) (by simp [s2,s1]) (by simp [s2,htest])
    have h := Native.seq (Native.of_exec h1) (Native.seq h2 (Native.of_exec h3))
    have he : (s2.upd Mid []).upd Lo (.int ((mid+1 : ℕ) : ℤ)::lt)=
        (s.upd Lo (.int ((nextBounds xs t lo hi).1 : ℤ)::lt)).upd Hi
          (.int ((nextBounds xs t lo hi).2 : ℤ)::ht) := by
      simp only [nextBounds,show (lo+hi)/2=mid from rfl,if_neg htest,Prod.fst,Prod.snd]
      apply itemState_ext
      · intro i
        by_cases hL : i=Lo
        · subst i; simp [s2,s1]
        by_cases hH : i=Hi
        · subst i; simp [s2,s1,hh]
        by_cases hM : i=Mid
        · subst i; simp [s2,s1,hmid]
        by_cases hF : i=Flag
        · subst i; simp [s2,s1,hf,htest]
        simp [s2,s1,IState.upd,Function.update_apply,hL,hH,hM,hF]
      · rfl
      · rfl
    rw [he] at h
    change IRuns I Fin.elim0 round s _ _ at h
    apply Native.mono h
    have hb := updateLower_cost lo mid w hlo hm
    nlinarith

end KoanaKPaths.Machine.Median

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Median.NS) (xs : List.{0} Int) (t lo hi w : Nat)
  (rt lt ht rult : List.{0} NLogN.Item)
  (hrec :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Records)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int xs) (@List.cons.{0} NLogN.Item NLogN.Item.mark rt)))
  (hl :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Lo)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt lo)) lt))
  (hh :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Hi)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt hi)) ht))
  (hrul :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Ruler)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))) rult))
  (hmid :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Mid)
      (@List.nil.{0} NLogN.Item))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Count)
      (@List.nil.{0} NLogN.Item))
  (hthr :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Threshold)
      (@List.replicate.{0} NLogN.Item t NLogN.Item.mark))
  (hs :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Saved)
      (@List.nil.{0} NLogN.Item))
  (hf :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Flag)
      (@List.nil.{0} NLogN.Item))
  (hlo : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt lo)) w)
  (hhi : @LE.le.{0} Nat instLENat (NLogN.zsz (@Nat.cast.{0} Int instNatCastInt hi)) w)
  (hx :
    ∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) xs x →
        @LE.le.{0} Nat instLENat (NLogN.zsz x) w),
  @NLogN.IRuns KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) I
    (@Fin.elim0.{1}
      (NLogN.IStmt KoanaKPaths.Machine.Median.NS (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    KoanaKPaths.Machine.Median.round s
    (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Median.NS s KoanaKPaths.Machine.Median.Lo
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@Prod.fst.{0, 0} Nat Nat (KoanaKPaths.Machine.Median.nextBounds xs t lo hi))))
          lt))
      KoanaKPaths.Machine.Median.Hi
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@Prod.snd.{0, 0} Nat Nat (KoanaKPaths.Machine.Median.nextBounds xs t lo hi))))
        ht))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 8000) (instOfNatNat (nat_lit 8000)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) w
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Int xs)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @KoanaKPaths.Machine.Median.round_runs
