-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.predecessorVertex_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:15.444666+00:00
-- url     : https://prove2.me/submissions/ae65bd59-f297-42fe-a609-fdc0517e39ee

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_ArcMember_scan_runs
import Theorems.Thm_KoanaKPaths_Machine_ArcMember_transferRecords_exec
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_predecessorRow_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
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

lemma liftClosed_runs (I : List Sym) (prog : Fin P → IStmt S P)
    {p : IStmt S 0} {s s' : IState S} {c : ℕ}
    (h : IRuns I Fin.elim0 p s s' c) : IRuns I prog (liftClosed p) s s' c := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t,ht,liftClosed_exec I prog h⟩

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
namespace KoanaKPaths.Machine.Controls







lemma zsz_nat_le (n : ℕ) : zsz (n : ℤ)≤ n := by
  rw [Wedge.zsz_eq_size,Int.natAbs_natCast]
  exact Nat.size_le.mpr Nat.lt_two_pow_self








end KoanaKPaths.Machine.Controls

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main



lemma wordWidth_pos (n k : ℕ) : 1≤ wordWidth n k := by
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]





lemma row_word_width (n k r : ℕ) (hr : r≤ k) : zsz (r : ℤ)≤ wordWidth n k := by
  have hz := Controls.zsz_nat_le r
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]





end KoanaKPaths.Machine.Trial

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
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] DB Back U V QueryU QueryV Found FlagU FlagV Tmp Work





lemma inspectRecord_cost (u v qu qv : ℤ) (w : ℕ)
    (hu : zsz u≤ w) (hv : zsz v≤ w) (hqu : zsz qu≤ w) (hqv : zsz qv≤ w) :
    2*recordCost u v+compareCost u qu+compareCost v qv+200≤5000*(w+1) := by
  have h1 := compareCost_bound u qu w hu hqu
  have h2 := compareCost_bound v qv w hv hqv
  unfold recordCost moveCost
  nlinarith

end KoanaKPaths.Machine.ArcMember

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] U V







lemma transferCost_bound (ps : List (ℤ×ℤ)) (w : ℕ)
    (hw : ∀ p∈ps, zsz p.1≤ w ∧ zsz p.2≤ w) :
    transferCost ps≤1000*(w+1)*(ps.length+1) := by
  induction ps with
  | nil => simp [transferCost]; omega
  | cons p ps ih =>
    rcases p with ⟨u,v⟩
    have h := hw (u,v) (by simp)
    have ht := ih (fun p hp => hw p (by simp [hp]))
    simp only [transferCost,List.length_cons]
    unfold recordCost moveCost
    nlinarith

end KoanaKPaths.Machine.ArcMember

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] DB Back QueryU QueryV Found FlagU FlagV










lemma scanCost_bound (ps : List (ℤ×ℤ)) (qu qv : ℤ) (w : ℕ)
    (hqu : zsz qu≤ w) (hqv : zsz qv≤ w) (hw : ∀ p∈ps, zsz p.1≤ w ∧ zsz p.2≤ w) :
    scanCost qu qv ps≤5100*(w+1)*(ps.length+1) := by
  induction ps with
  | nil => simp [scanCost]; omega
  | cons p ps ih =>
    rcases p with ⟨u,v⟩
    have h := hw (u,v) (by simp)
    have ht := ih (fun p hp => hw p (by simp [hp]))
    have hc := inspectRecord_cost u v qu qv w h.1 h.2 hqu hqv
    simp only [scanCost,List.length_cons]
    nlinarith

lemma scanFound_any (qu qv : ℤ) (ps : List (ℤ×ℤ)) (f : Bool) :
    scanFound qu qv ps f=(ps.any (arcMatch qu qv) || f) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change scanFound qu qv ps (arcMatch qu qv p || f)=_
    rw [ih]
    simp [List.any_cons,Bool.or_assoc,Bool.or_left_comm]

lemma matches_mem (qu qv : ℤ) (ps : List (ℤ×ℤ)) :
    ps.any (arcMatch qu qv)=decide ((qu,qv)∈ps) := by
  by_cases hmem : (qu,qv)∈ps
  · have htrue : ps.any (arcMatch qu qv)=true := List.any_eq_true.mpr
      ⟨(qu,qv),hmem,by simp [arcMatch]⟩
    simp [htrue,hmem]
  · cases hbool : ps.any (arcMatch qu qv) with
    | false => simp [hbool,hmem]
    | true =>
      obtain ⟨⟨u,v⟩,hp,hmatch⟩ := List.any_eq_true.mp hbool
      have he : (u,v)=(qu,qv) := by
        simp only [arcMatch,Bool.and_eq_true,decide_eq_true_eq] at hmatch
        exact Prod.ext hmatch.1 hmatch.2
      exact False.elim (hmem (he ▸ hp))

end KoanaKPaths.Machine.ArcMember

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.ArcMember
attribute [local simp] DB Back QueryU QueryV Found FlagU FlagV



lemma queryArc_runs (I : List Sym) (s : IState NS) (ps : List (ℤ×ℤ)) (qu qv : ℤ)
    (qtU qtV : List Item) (w : ℕ)
    (hdb : s.G DB=records ps) (hback : s.G Back=[])
    (hqu : s.G QueryU=.int qu::qtU) (hqv : s.G QueryV=.int qv::qtV)
    (hu : s.G FlagU=[]) (hv : s.G FlagV=[])
    (hwu : zsz qu≤ w) (hwv : zsz qv≤ w) (hw : ∀ p∈ps, zsz p.1≤ w ∧ zsz p.2≤ w) :
    IRuns I Fin.elim0 queryArc s
      (s.upd Found (.int ((decide ((qu,qv)∈ps)).toNat : ℤ)::s.G Found))
      (7000*(w+1)*(ps.length+1)) := by
  let s0 := s.upd Found (.int 0::s.G Found)
  let f := scanFound qu qv ps false
  let s1 := ((s0.upd DB []).upd Back (records ps.reverse)).upd Found (.int (f.toNat : ℤ)::s.G Found)
  let s2 := (s1.upd Back []).upd DB (records ps)
  have h0 : IExec I Fin.elim0 (.op (.const Found 0)) s s0 2 := by
    simpa [Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s) (i := Found) 0))
  have h1 : IRuns I Fin.elim0 scan s0 s1 (scanCost qu qv ps) := by
    have h := scan_runs I s0 ps qu qv false [] qtU qtV (s.G Found) (by simp [Median.intClass,cls])
      (by simp [s0,hdb]) (by simp [s0,hqu]) (by simp [s0,hqv])
      (by simp [s0]) (by simp [s0,hu]) (by simp [s0,hv])
    simpa [s1,s0,hback] using h
  have h2 : IExec I Fin.elim0 (transferRecords Back DB) s1 s2 (transferCost ps.reverse) := by
    have h := transferRecords_exec I Back DB (by decide) (by decide) (by decide) (by decide) (by decide)
      s1 ps.reverse [] (by simp [Median.intClass,cls]) (by simp [s1])
    simpa [s2,s1,s0] using h
  have hf : f=decide ((qu,qv)∈ps) := by
    simp [f,scanFound_any,matches_mem]
  have he : s2=s.upd Found (.int ((decide ((qu,qv)∈ps)).toNat : ℤ)::s.G Found) := by
    apply itemState_ext
    · intro i
      by_cases hD : i=DB
      · subst i; simp [s2,s1,s0,hdb]
      by_cases hB : i=Back
      · subst i; simp [s2,s1,s0,hback]
      by_cases hF : i=Found
      · subst i; simp [s2,s1,s0,hf]
      simp [s2,s1,s0,IState.upd,Function.update_apply,hD,hB,hF]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq h1 (Native.of_exec h2))
  rw [he] at h
  change IRuns I Fin.elim0 queryArc s _ _ at h
  apply Native.mono h
  have hc := scanCost_bound ps qu qv w hwu hwv hw
  have ht := transferCost_bound ps.reverse w (by simpa using hw)
  simp only [List.length_reverse] at ht
  nlinarith

lemma arcItems_records (ps : List (ℕ×ℕ)) : Input.arcItems ps=
    records (ps.reverse.map (fun p => ((p.1 : ℤ),(p.2 : ℤ)))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨u,v⟩
    simp [Input.arcItems,ih,records,List.reverse_cons,List.map_append,List.flatMap_append]



lemma arcItems_ofArcs {n : ℕ} (arcs : List (Fin n × Fin n)) :
    Input.arcItems (Input.arcValues arcs)=records (ofArcs arcs) := by
  rw [arcItems_records]
  simp [ofArcs,Input.arcValues,List.map_map,Function.comp_def]

lemma ofArcs_mem {n : ℕ} (arcs : List (Fin n × Fin n)) (u v : Fin n) :
    ((u.val : ℤ),(v.val : ℤ))∈ofArcs arcs ↔ (u,v)∈arcs.toFinset := by
  simp only [ofArcs,List.mem_map,List.mem_reverse,List.mem_toFinset]
  constructor
  · rintro ⟨⟨u',v'⟩,hp,he⟩
    have hU : u'=u := by
      apply Fin.ext
      have h := congrArg Prod.fst he
      change (u'.val : ℤ)=(u.val : ℤ) at h
      exact_mod_cast h
    have hV : v'=v := by
      apply Fin.ext
      have h := congrArg Prod.snd he
      change (v'.val : ℤ)=(v.val : ℤ) at h
      exact_mod_cast h
    simpa only [hU,hV] using hp
  · intro hp
    exact ⟨(u,v),hp,rfl⟩

end KoanaKPaths.Machine.ArcMember

namespace KoanaKPaths.Machine.ArcMember
open NLogN
lemma graph_query_runs (I : List Sym) (s : IState NS) {n : ℕ}
    (arcs : List (Fin n × Fin n)) (u v : Fin n) (qtU qtV : List Item)
    (hdb : s.G DB=Input.arcItems (Input.arcValues arcs)) (hback : s.G Back=[])
    (hqu : s.G QueryU=.int (u.val : ℤ)::qtU) (hqv : s.G QueryV=.int (v.val : ℤ)::qtV)
    (hu : s.G FlagU=[]) (hv : s.G FlagV=[]) :
    IRuns I Fin.elim0 queryArc s
      (s.upd Found (.int ((decide ((u,v)∈arcs.toFinset)).toNat : ℤ)::s.G Found))
      (7000*(n+1)*(arcs.length+1)) := by
  have hz : ∀ x : Fin n, zsz (x.val : ℤ)≤ n := by
    intro x
    apply (Wedge.zsz_le_iff _ _).mpr
    simp only [Int.natAbs_natCast]
    exact x.isLt.trans Nat.lt_two_pow_self
  have hp : ∀ p∈ofArcs arcs, zsz p.1≤ n ∧ zsz p.2≤ n := by
    intro p hp
    obtain ⟨⟨u',v'⟩,_,rfl⟩ := List.mem_map.mp hp
    exact ⟨hz u',hz v'⟩
  have h := queryArc_runs I s (ofArcs arcs) (u.val : ℤ) (v.val : ℤ) qtU qtV n
    (by simpa only [arcItems_ofArcs] using hdb) hback hqu hqv hu hv (hz u) (hz v) hp
  simp only [ofArcs_mem] at h
  simpa only [ofArcs,List.length_map,List.length_reverse] using h
end KoanaKPaths.Machine.ArcMember

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main






lemma Core.upd {n k : ℕ} {s : IState NS} {ω : Fin (trialBits n k)→Bool}
    {arcs : List (Fin n × Fin n)} {p : ℕ} (h : Core s ω arcs p) (j : Fin NS)
    (hj : j∉coreRegisters) (xs : List Item) : Core (s.upd j xs) ω arcs p := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr

lemma Core.at {n k : ℕ} {s : IState NS} {ω : Fin (trialBits n k)→Bool}
    {arcs : List (Fin n × Fin n)} {p : ℕ} (h : Core s ω arcs p) (j : Fin NS)
    (hj : j∈coreRegisters) : s.G j=coreStack ω arcs p j := h j hj

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates




lemma predSet_next {n k : ℕ} (u : Fin n) : predSet n k u.val k=predSet n k (u.val+1) 0 := by
  ext q
  simp only [predSet,Finset.mem_filter,Finset.mem_univ,true_and]
  have h := q.2.isLt
  omega







lemma predSum_next {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v u : Fin n) :
    predSum arcs σ R p i a v u.val k=predSum arcs σ R p i a v (u.val+1) 0 := by
  rw [predSum,predSum,predSet_next]



end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates
attribute [local simp] PreviousCounter PreviousState Accumulate.Acc Vertex StateIndex LayerIndex Predecessor Found
  Wedge.D LabelTmp ArcMember.Found ArcMember.DB ArcMember.Back ArcMember.FlagU ArcMember.FlagV





lemma predecessorVertex_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n))
    (p : ℕ) (hp : p≤ k) (i : Fin (k-1)) (a : Fin k) (v u : Fin n)
    (vt atail it ut accTail : List Item)
    (hCore : Core s ω arcs p)
    (hV : s.G Vertex=.int (v.val : ℤ)::vt) (hA : s.G StateIndex=.int (a.val : ℤ)::atail)
    (hI : s.G LayerIndex=.int (i.val : ℤ)::it) (hU : s.G Predecessor=.int (u.val : ℤ)::ut)
    (hCount : s.G PreviousCounter=[])
    (hAcc : s.G Accumulate.Acc=(coefficientList
      (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val 0)).map Item.int ++ .mark::accTail) :
    IRuns I Wedge.prog predecessorVertex s
      ((s.upd Predecessor (.int ((u.val+1 : ℕ) : ℤ)::ut)).upd Accumulate.Acc
        ((coefficientList (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v (u.val+1) 0)).map Item.int ++ .mark::accTail))
      (predecessorVertexCost n k arcs.length) := by
  let f : ℤ := (decide ((u,v)∈arcs.toFinset)).toNat
  let s0 := s.upd Found (.int f::s.G Found)
  let s1 := s0.upd PreviousState (.int 0::s.G PreviousState)
  let s2 := s1.upd PreviousCounter (List.replicate k .mark)
  let s3 := predecessorRowState s2 ω arcs p i a v u k (s.G PreviousState) accTail
  let s4 := s3.upd PreviousState (s.G PreviousState)
  let s5 := s4.upd Found (s.G Found)
  let s6 := s5.upd Predecessor (.int ((u.val+1 : ℕ) : ℤ)::ut)
  have h0 : IRuns I Wedge.prog (liftClosed ArcMember.queryArc) s s0 (7000*(n+1)*(arcs.length+1)) := by
    exact liftClosed_runs I Wedge.prog (ArcMember.graph_query_runs I s arcs u v ut vt
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 30 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 67 (by decide)) hU hV
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 108 (by decide))
      (by simpa [coreStack,NS,Wedge.NS] using hCore.at 109 (by decide)))
  have h1 : IExec I Wedge.prog (.op (.const PreviousState 0)) s0 s1 2 := by
    simpa [s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := Wedge.prog) (IOp.Step.const (s := s0) (i := PreviousState) 0))
  have h2 : IExec I Wedge.prog (liftClosed (copyMarks Wedge.D PreviousCounter LabelTmp)) s1 s2 (65*k+60) := by
    have h := liftClosed_exec I Wedge.prog (copyMarks_exec I Wedge.D PreviousCounter LabelTmp
      (by decide) (by decide) (by decide) s1 k [] (by simp [cls])
      (by simpa [s1,s0,coreStack,NS,Wedge.NS] using hCore.at 3 (by decide))
      (by simpa [s1,s0,coreStack,NS,Wedge.NS] using hCore.at 89 (by decide)))
    simpa [s2,s1,s0,hCount] using h
  have hCP : Core s2 ω arcs p := ((hCore.upd Found (by decide) _).upd PreviousState (by decide) _).upd PreviousCounter (by decide) _
  have h3 : IRuns I Wedge.prog predecessorRow s2 s3
      ((predecessorCellCost (n*k) (trialBits n k) k (wordWidth n k)+56)*k+30) := by
    exact predecessorRow_runs I s2 ω arcs p hp i a v u vt atail it ut (s.G PreviousState) accTail (s.G Found) hCP
      (by simp [s2,s1,s0,hV]) (by simp [s2,s1,s0,hA]) (by simp [s2,s1,s0,hI])
      (by simp [s2,s1,s0,hU]) (by simp [s2,s1,s0]) (by simp [s2])
      (by simp [s2,s1,s0,f]) (by simp [s2,s1,s0,hAcc])
  have h4 : IExec I Wedge.prog (.op (.drop PreviousState)) s3 s4 (2*zsz (k : ℤ)+2) :=
    .op (.drop (by simp [s3,predecessorRowState]))
  have h5 : IExec I Wedge.prog (.op (.drop Found)) s4 s5 (2*zsz f+2) :=
    .op (.drop (by simp [s4,s3,predecessorRowState,s2,s1,s0]))
  have h6 : IRuns I Wedge.prog (liftClosed (Square.increment Predecessor)) s5 s6
      (13000*(wordWidth n k+1)^2) :=
    liftClosed_runs I Wedge.prog (Square.increment_runs I Predecessor (by decide) s5 u.val (wordWidth n k) ut
      (by simp [s5,s4,s3,predecessorRowState,s2,s1,s0,hU]) (wordWidth_pos n k) (by
        have hu := Controls.zsz_nat_le u.val
        unfold wordWidth; nlinarith [u.isLt,Nat.zero_le (n*n),Nat.zero_le (k*k)]))
  have hpost : s6=(s.upd Predecessor (.int ((u.val+1 : ℕ) : ℤ)::ut)).upd Accumulate.Acc
      ((coefficientList (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v (u.val+1) 0)).map Item.int ++ .mark::accTail) := by
    apply itemState_ext
    · intro r
      by_cases h80 : r=80
      · subst r; simp [s6,s5,s4,s3,predecessorRowState,s2,s1,s0,IState.upd]
      by_cases h85 : r=85
      · subst r; simp [s6,s5,s4,s3,predecessorRowState,s2,s1,s0,IState.upd]
      by_cases h86 : r=86
      · subst r; simp [s6,s5,s4,s3,predecessorRowState,s2,s1,s0,IState.upd]
      by_cases h92 : r=92
      · subst r; simp [s6,s5,s4,s3,predecessorRowState,s2,s1,s0,IState.upd,hCount]
      by_cases h20 : r=20
      · subst r; simp [s6,s5,s4,s3,predecessorRowState,s2,s1,s0,IState.upd,predSum_next]
      simp [s6,s5,s4,s3,predecessorRowState,s2,s1,s0,IState.upd,Function.update_apply,h80,h85,h86,h92,h20]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq h3 (Native.seq (Native.of_exec h4) (Native.seq (Native.of_exec h5) h6)))))
  rw [hpost] at h
  change IRuns I Wedge.prog predecessorVertex s _ _ at h
  apply Native.mono h
  have hkW := row_word_width n k k le_rfl
  have hfW : zsz f≤1 := by by_cases h : (u,v)∈arcs.toFinset <;> simp [f,h,Wedge.zsz_eq_size]
  unfold predecessorVertexCost
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (p : Nat)
  (hp : @LE.le.{0} Nat instLENat p k)
  (i :
    Fin
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (a : Fin k) (v u : Fin n) (vt atail it ut accTail : List.{0} NLogN.Item)
  (hCore : @KoanaKPaths.Machine.Trial.Core n k s ω arcs p)
  (hV :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val n v))) vt))
  (hA :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val k a))) atail))
  (hI :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LayerIndex)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@Fin.val
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              i)))
        it))
  (hU :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Predecessor)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val n u))) ut))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousCounter)
      (@List.nil.{0} NLogN.Item))
  (hAcc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Accumulate.Acc)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@KoanaKPaths.ExteriorCoordinates.coefficientList k
            (@KoanaKPaths.Main.predSum n k arcs
              (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              p i a v (@Fin.val n u) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark accTail))),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.predecessorVertex s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Predecessor
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n u)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          ut))
      KoanaKPaths.Machine.Accumulate.Acc
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@KoanaKPaths.ExteriorCoordinates.coefficientList k
            (@KoanaKPaths.Main.predSum n k arcs
              (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                    Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                    (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                    (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                      (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                  (KoanaKPaths.Main.trialEquiv n k) ω))
              p i a v
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n u)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
        (@List.cons.{0} NLogN.Item NLogN.Item.mark accTail)))
    (KoanaKPaths.Machine.Trial.predecessorVertexCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)) := by
  exact @KoanaKPaths.Machine.Trial.predecessorVertex_runs
