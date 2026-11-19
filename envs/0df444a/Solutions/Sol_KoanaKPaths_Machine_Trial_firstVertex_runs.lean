-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.firstVertex_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:15.405191+00:00
-- url     : https://prove2.me/submissions/cc9610bd-0720-46d1-8e8d-e5ae989e02b5

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
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
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_width_le
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_firstRow_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_loadVector_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
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
namespace KoanaKPaths.Machine
variable {S : ℕ}





lemma cls_int (z : ℤ) :
    cls (some (.int z)) = Cls.zero ∨ cls (some (.int z)) = Cls.pos ∨
      cls (some (.int z)) = Cls.neg := by
  by_cases hz : z=0
  · simp [cls,hz]
  · by_cases hn : z<0 <;> simp [cls,hz,hn]




































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
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}











lemma Expr.root_width (e : Expr v) (values : Fin v→ℕ) :
    zsz (e.eval values : ℤ)≤ e.width values := by
  cases e <;> exact le_max_left _ _



end KoanaKPaths.Machine.Arithmetic

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}









lemma clearInts_exec (I : List Sym) (src : Fin S) (s : IState S) (xs : List ℤ) (tail : List Item)
    (ht : ¬ (cls tail.head?=Cls.zero ∨ cls tail.head?=Cls.pos ∨ cls tail.head?=Cls.neg))
    (hs : s.G src=xs.map Item.int ++ tail) :
    IExec I Fin.elim0 (clearInts src) s (s.upd src tail) (clearIntsCost xs) := by
  induction xs generalizing s with
  | nil =>
    have he : s.upd src tail=s := by rw [← show s.G src=tail from by simpa using hs]; exact upd_same _ _
    rw [he]
    exact IExec.loopF (by simpa [IState.cl,hs] using ht)
  | cons x xs ih =>
    let s1 := s.upd src (xs.map Item.int ++ tail)
    have h1 : IExec I Fin.elim0 (.op (.drop src)) s s1 (2*zsz x+2) := .op (.drop (by simpa using hs))
    have hh : decide (s.cl src=Cls.zero ∨ s.cl src=Cls.pos ∨ s.cl src=Cls.neg)=true := by
      simp only [IState.cl,hs,List.map_cons,List.cons_append,List.head?_cons,decide_eq_true_eq]
      exact cls_int x
    have hrun := IExec.loopT hh h1 (ih s1 (by simp [s1]))
    change IExec I Fin.elim0 (clearInts src) s _ _ at hrun
    simp only [s1,upd_upd] at hrun
    convert hrun using 1
    simp only [clearIntsCost,List.map_cons,List.sum_cons]
    omega









end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Main

lemma trialEquiv_label {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (v : Fin n) (r : Fin k) :
    (trialEquiv n k ω).1 v r=ω (trialIndexEquiv n k (.inl (v,r))) := rfl





lemma trialIndex_label {n k : ℕ} (v : Fin n) (r : Fin k) :
    (trialIndexEquiv n k (.inl (v,r))).val=v.val*k+r.val := by
  change r.val+k*v.val=v.val*k+r.val
  ring









end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main





lemma signsOf_values {n k : ℕ} (ω : Fin (trialBits n k)→Bool) :
    ∀ x∈signsOf ω, x=1 ∨ x= -1 := by
  intro x hx
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
  rw [← hi]
  cases h : ω i <;> simp [sgn,h]

lemma signsOf_get {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (j : Fin (trialBits n k)) :
    (signsOf ω).getD j.val 1=sgn (ω j) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [signsOf,List.length_ofFn] using j.isLt)]
  simp only [signsOf,List.getElem_ofFn]

lemma labelBlock_ofFn (xs : List ℤ) (k v r m : ℕ) :
    labelBlock xs k v r m=List.ofFn (fun i : Fin m => xs.getD (v*k+(r+i.val)) 1) := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih =>
    rw [labelBlock,List.ofFn_succ]
    congr 1
    rw [ih]
    apply congrArg List.ofFn
    funext i
    congr 1
    simp only [Fin.val_succ]
    omega

lemma labelBlock_decodes {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (v : Fin n) :
    labelBlock (signsOf ω) k v.val 0 k=labelList (trialEquiv n k ω).1 v := by
  rw [labelBlock_ofFn]
  unfold labelList
  rw [← List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext r
  have h := signsOf_get ω (trialIndexEquiv n k (.inl (v,r)))
  rw [trialIndex_label] at h
  simpa only [Nat.zero_add,trialEquiv_label] using h



end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main















end KoanaKPaths.Main

namespace KoanaKPaths.Machine.Norm
lemma clearIntsCost_bound (xs : List ℤ) (w : ℕ) (h : ∀ x∈xs, zsz x≤ w) :
    clearIntsCost xs≤(2*w+32)*xs.length+30 := by
  unfold clearIntsCost
  have hh : (xs.map (fun x => 2*zsz x+32)).sum≤(2*w+32)*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  omega



end KoanaKPaths.Machine.Norm

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic




























lemma exprTrial_eval (n k a b m : ℕ) : exprTrial.eval (inputValues n k a b m)=KoanaKPaths.Main.trialBits n k := rfl















end KoanaKPaths.Machine.Controls

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

lemma label_word_width {n k : ℕ} (v : Fin n) (r : ℕ) (hr : r< k) :
    labelExpr.width (labelValues k v.val r)≤ wordWidth n k := by
  have hk := Controls.zsz_nat_le k
  have hv := Controls.zsz_nat_le v.val
  have hR := Controls.zsz_nat_le r
  have ha : labelExpr.atomWidth (labelValues k v.val r)≤1+n+k := by
    change max (max (zsz (v.val : ℤ)) (zsz (k : ℤ))) (zsz (r : ℤ))≤1+n+k
    omega
  have hw := labelExpr.width_le (labelValues k v.val r) (1+n+k) ha
  have hs : labelExpr.size=5 := rfl
  rw [hs] at hw
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]

lemma trial_word_width (n k a b m : ℕ) :
    zsz (trialBits n k : ℤ)≤ wordWidth n k := by
  have hn := Controls.zsz_nat_le n
  have hk := Controls.zsz_nat_le k
  have hkm := Controls.zsz_nat_le (k-1)
  have ha : Controls.exprTrial.atomWidth (Controls.inputValues n k a b m)≤1+n+k := by
    simp only [Controls.exprTrial,Controls.exprN,Controls.exprK,Controls.exprKMinus,Expr.atomWidth]
    change max (max (zsz (n : ℤ)) (zsz (k : ℤ)))
      (max (max (zsz (k : ℤ)) (zsz (n : ℤ)))
        (max (zsz ((k-1 : ℕ) : ℤ)) (max (zsz (k : ℤ)) (max (zsz (k : ℤ)) (zsz (n : ℤ))))))≤1+n+k
    omega
  have hw := Controls.exprTrial.width_le (Controls.inputValues n k a b m) (1+n+k) ha
  have hroot := Controls.exprTrial.root_width (Controls.inputValues n k a b m)
  rw [Controls.exprTrial_eval] at hroot
  have hs : Controls.exprTrial.size=15 := rfl
  rw [hs] at hw
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]

lemma row_word_width (n k r : ℕ) (hr : r≤ k) : zsz (r : ℤ)≤ wordWidth n k := by
  have hz := Controls.zsz_nat_le r
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]

lemma label_index_valid {n k : ℕ} (v : Fin n) (r : ℕ) (hr : r< k) : v.val*k+r< trialBits n k := by
  have hp := (finProdFinEquiv (v,⟨r,hr⟩)).isLt
  change r+k*v.val< n*k at hp
  have hT : n*k≤ trialBits n k := by unfold trialBits; omega
  nlinarith



end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] LabelCounter LabelTmp StateIndex Vertex GraphArray.Current Wedge.V Wedge.D Wedge.HC Wedge.DC Wedge.Aux
  Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp





lemma firstVertex_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (v : Fin n)
    (nt kt vt tt dbtail : List Item)
    (hn : s.G 53=.int (n : ℤ)::nt) (hk : s.G 54=.int (k : ℤ)::kt)
    (hv : s.G Vertex=.int (v.val : ℤ)::vt) (hT : s.G Total=.int (trialBits n k : ℤ)::tt)
    (hdb : s.G SignDB=signItems (signsOf ω)++dbtail)
    (hbc : s.G BitCounter.Count=[]) (hbt : s.G BitCounter.Tmp=[])
    (hsc : s.G SignLookup.Count=[]) (hsb : s.G SignLookup.Back=[]) (hst : s.G SignLookup.Tmp=[])
    (hd : s.G Wedge.D=List.replicate k .mark) (hCounter : s.G LabelCounter=[]) (hTmp : s.G LabelTmp=[])
    (hHC : s.G Wedge.HC=[]) (hDC : s.G Wedge.DC=[]) (hAux : s.G Wedge.Aux=[]) :
    IRuns I Wedge.prog firstVertex s
      ((s.upd Vertex (.int ((v.val+1 : ℕ) : ℤ)::vt)).upd GraphArray.Current
        (ArrayLookup.frames (List.ofFn (fun a => denseLayer arcs (trialEquiv n k ω).1
          (trialEquiv n k ω).2 1 v a)).reverse ++ s.G GraphArray.Current))
      (firstVertexCost n k) := by
  let w := wordWidth n k
  let xs := signsOf ω
  let ds := (labelBlock xs k v.val 0 k).reverse
  let F : Fin k→List ℤ := fun a => denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1 v a
  let s0 := s.upd Wedge.V (ds.map Item.int ++ .mark::s.G Wedge.V)
  let s1 := s0.upd StateIndex (.int 0::s.G StateIndex)
  let s2 := s1.upd LabelCounter (List.replicate k .mark)
  let s3 := firstRowState s2 F k (s.G StateIndex)
  let s4 := s3.upd StateIndex (s.G StateIndex)
  let s5 := s4.upd Wedge.V (.mark::s.G Wedge.V)
  let s6 := s5.upd Wedge.V (s.G Wedge.V)
  let s7 := s6.upd Vertex (.int ((v.val+1 : ℕ) : ℤ)::vt)
  have h0 : IRuns I Wedge.prog (liftClosed loadVector) s s0
      (labelIterationCost xs w*k+65*k+2*zsz (k : ℤ)+95) := by
    exact liftClosed_runs I Wedge.prog (loadVector_runs I s xs k v.val w kt vt tt dbtail
      (wordWidth_pos n k) hk hv (by simpa only [xs,signsOf_length] using hT) hdb hd hCounter hTmp hbc hbt hsc hsb hst
      (signsOf_values ω) (fun row hr => label_word_width v row hr)
      (by simpa only [xs,signsOf_length,w] using trial_word_width n k 0 0 0) (row_word_width n k) (fun row hr => by simpa only [xs,signsOf_length] using label_index_valid v row hr))
  have h1 : IExec I Wedge.prog (.op (.const StateIndex 0)) s0 s1 2 := by
    simpa [s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := Wedge.prog) (IOp.Step.const (s := s0) (i := StateIndex) 0))
  have h2 : IExec I Wedge.prog (liftClosed (copyMarks Wedge.D LabelCounter LabelTmp)) s1 s2 (65*k+60) := by
    have h := liftClosed_exec I Wedge.prog (copyMarks_exec I Wedge.D LabelCounter LabelTmp
      (by decide) (by decide) (by decide) s1 k [] (by simp [cls]) (by simp [s1,s0,hd]) (by simp [s1,s0,hTmp]))
    simpa [s2,s1,s0,hCounter] using h
  have h3 : IRuns I Wedge.prog firstRow s2 s3 ((firstCellCost n k+31)*k+30) := by
    exact firstRow_runs I s2 ω arcs v nt kt vt (s.G StateIndex) tt dbtail (.mark::s.G Wedge.V)
      (by simp [s2,s1,s0,hn]) (by simp [s2,s1,s0,hk]) (by simp [s2,s1,s0,hv])
      (by simp [s2,s1]) (by simp [s2]) (by simp [s2,s1,s0,hT]) (by simp [s2,s1,s0,hdb])
      (by simp [s2,s1,s0,hbc]) (by simp [s2,s1,s0,hbt]) (by simp [s2,s1,s0,hsc])
      (by simp [s2,s1,s0,hsb]) (by simp [s2,s1,s0,hst]) (by simp [s2,s1,s0,hd])
      (by simp [s2,s1,s0,ds,xs]) (by simp [s2,s1,s0,hHC]) (by simp [s2,s1,s0,hDC]) (by simp [s2,s1,s0,hAux])
  have h4 : IExec I Wedge.prog (.op (.drop StateIndex)) s3 s4 (2*zsz (k : ℤ)+2) :=
    .op (.drop (by simp [s3,firstRowState]))
  have h5 : IExec I Wedge.prog (liftClosed (clearInts Wedge.V)) s4 s5 (clearIntsCost ds) := by
    exact liftClosed_exec I Wedge.prog (clearInts_exec I Wedge.V s4 ds (.mark::s.G Wedge.V)
      (by simp [cls]) (by simp [s4,s3,firstRowState,s2,s1,s0]))
  have h6 : IExec I Wedge.prog (.op (.unmark Wedge.V)) s5 s6 1 := .op (.unmark (by simp [s5]))
  have hvw : zsz (v.val : ℤ)≤ w := by
    have hh := Controls.zsz_nat_le v.val
    unfold w wordWidth
    have hvn := v.isLt
    nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
  have h7 : IRuns I Wedge.prog (liftClosed (Square.increment Vertex)) s6 s7 (13000*(w+1)^2) :=
    liftClosed_runs I Wedge.prog (Square.increment_runs I Vertex (by decide) s6 v.val w vt
      (by simp [s6,s5,s4,s3,firstRowState,s2,s1,s0,hv]) (wordWidth_pos n k) hvw)
  have htake : (List.ofFn F).take k=List.ofFn F := List.take_of_length_le (by simp)
  have hpost : s7=(s.upd Vertex (.int ((v.val+1 : ℕ) : ℤ)::vt)).upd GraphArray.Current
      (ArrayLookup.frames (List.ofFn F).reverse ++ s.G GraphArray.Current) := by
    apply itemState_ext
    · intro i
      by_cases hV : i=Vertex
      · subst i; simp [s7,s6,s5,s4,s3,firstRowState,s2,s1,s0]
      by_cases hC : i=GraphArray.Current
      · subst i; simp [s7,s6,s5,s4,s3,firstRowState,s2,s1,s0,htake]
      by_cases hA : i=StateIndex
      · subst i; simp [s7,s6,s5,s4,s3,firstRowState,s2,s1,s0]
      by_cases hVec : i=Wedge.V
      · subst i; simp [s7,s6,s5,s4,s3,firstRowState,s2,s1,s0]
      by_cases hCount : i=LabelCounter
      · subst i; simp [s7,s6,s5,s4,s3,firstRowState,s2,s1,s0,hCounter]
      simp [s7,s6,s5,s4,s3,firstRowState,s2,s1,s0,IState.upd,Function.update_apply,hV,hC,hA,hVec,hCount]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq h3 (Native.seq (Native.of_exec h4) (Native.seq (Native.of_exec h5)
      (Native.seq (Native.of_exec h6) h7))))))
  rw [hpost] at h
  change IRuns I Wedge.prog firstVertex s _ _ at h
  apply Native.mono h
  have hlen : ds.length=k := by simp [ds,xs,labelBlock_decodes,labelList]
  have hsig : ∀ x∈ds, zsz x≤1 := by
    intro x hx
    have hh : x∈labelList (trialEquiv n k ω).1 v := by simpa [ds,xs,labelBlock_decodes] using hx
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hh
    cases h : (trialEquiv n k ω).1 v r <;> simp [sgn,Wedge.zsz_eq_size]
  have hclear := Norm.clearIntsCost_bound ds 1 hsig
  rw [hlen] at hclear
  have hkw := row_word_width n k k le_rfl
  unfold firstVertexCost labelIterationCost
  simp only [xs,signsOf_length]
  dsimp only [w] at *
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (v : Fin n)
  (nt kt vt tt dbtail : List.{0} NLogN.Item)
  (hn :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
        (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 53)
          (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 53))))
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt n)) nt))
  (hk :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s
        (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Trial.NS) (nat_lit 54)
          (@Fin.instOfNat KoanaKPaths.Machine.Trial.NS
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 54))))
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt k)) kt))
  (hv :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (@Fin.val n v))) vt))
  (hT :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Total)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@Nat.cast.{0} Int instNatCastInt (KoanaKPaths.Main.trialBits n k)))
        tt))
  (hdb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.SignDB)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.Trial.signItems (@KoanaKPaths.Machine.Trial.signsOf n k ω)) dbtail))
  (hbc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Count)
      (@List.nil.{0} NLogN.Item))
  (hbt :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.BitCounter.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hsc :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Count)
      (@List.nil.{0} NLogN.Item))
  (hsb :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Back)
      (@List.nil.{0} NLogN.Item))
  (hst :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.SignLookup.Tmp)
      (@List.nil.{0} NLogN.Item))
  (hd :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.D)
      (@List.replicate.{0} NLogN.Item k NLogN.Item.mark))
  (hCounter :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelCounter)
      (@List.nil.{0} NLogN.Item))
  (hTmp :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelTmp)
      (@List.nil.{0} NLogN.Item))
  (hHC :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.HC)
      (@List.nil.{0} NLogN.Item))
  (hDC :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.DC)
      (@List.nil.{0} NLogN.Item))
  (hAux :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.Aux)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.firstVertex s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Vertex
        (@List.cons.{0} NLogN.Item
          (NLogN.Item.int
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val n v)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          vt))
      KoanaKPaths.Machine.GraphArray.Current
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames
          (@List.reverse.{0} (List.{0} Int)
            (@List.ofFn.{0} (List.{0} Int) k fun (a : Fin k) =>
              @KoanaKPaths.Main.denseLayer n k k arcs
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
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) v a)))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.GraphArray.Current)))
    (KoanaKPaths.Machine.Trial.firstVertexCost n k) := by
  exact @KoanaKPaths.Machine.Trial.firstVertex_runs
