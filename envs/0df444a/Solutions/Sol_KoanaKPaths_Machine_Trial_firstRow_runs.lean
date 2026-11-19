-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.firstRow_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.391434+00:00
-- url     : https://prove2.me/submissions/525b85da-63a1-42bd-a00c-2b876726d1bd

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
import Theorems.Thm_KoanaKPaths_Machine_Native_invariant_loop
import Theorems.Thm_KoanaKPaths_Machine_Trial_firstCell_runs
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






















end KoanaKPaths.Machine

end

section

set_option maxHeartbeats 1000000
namespace KoanaKPaths.ExteriorCoordinates



lemma wedgeList_congr_vector (d : ℕ) (A v w : List ℤ)
    (h : ∀ j<d, v.getD j 0 = w.getD j 0) : wedgeList d A v = wedgeList d A w := by
  induction d generalizing A with
  | zero => rfl
  | succ d ih =>
    simp only [wedgeList]
    rw [ih _ (fun j hj => h j (by omega)),ih _ (fun j hj => h j (by omega)),h d (by omega)]

lemma wedgeReverse_eq_wedgeList (vs A : List ℤ) :
    wedgeReverse vs A = wedgeList vs.length A vs.reverse := by
  induction vs generalizing A with
  | nil => rfl
  | cons z vs ih =>
    simp only [wedgeReverse,List.length_cons,wedgeList,List.reverse_cons]
    have hg : ∀ j<vs.length, (vs.reverse++[z]).getD j 0 = vs.reverse.getD j 0 := by
      intro j hj
      exact List.getD_append _ _ _ _ (by simpa using hj)
    rw [wedgeList_congr_vector vs.length _ _ _ hg,wedgeList_congr_vector vs.length _ _ _ hg]
    rw [← ih,← ih]
    have hl : (vs.reverse++[z]).getD vs.length 0 = z := by
      rw [List.getD_append_right _ _ _ _ (by simp),List.length_reverse,Nat.sub_self]
      rfl
    rw [hl]



end KoanaKPaths.ExteriorCoordinates

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
namespace KoanaKPaths.Machine.ArrayLookup







attribute [local simp] DB Out Cache Count Back Tmp

















lemma frames_cons (a : List ℤ) (arrays : List (List ℤ)) :
    frames (a::arrays)=a.map Item.int ++ .mark::frames arrays := by
  simp [frames,List.append_assoc]


























end KoanaKPaths.Machine.ArrayLookup

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Main

lemma trialEquiv_label {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (v : Fin n) (r : Fin k) :
    (trialEquiv n k ω).1 v r=ω (trialIndexEquiv n k (.inl (v,r))) := rfl

lemma trialEquiv_first {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (a : Fin k) (v : Fin n) :
    (trialEquiv n k ω).2.1 a v=ω (trialIndexEquiv n k (.inr (.inl (a,v)))) := rfl



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

lemma first_array_decodes {n k : ℕ} (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (v : Fin n) (a : Fin k) :
    ((KoanaKPaths.ExteriorCoordinates.wedgeReverse
      (labelBlock (signsOf ω) k v.val 0 k).reverse (GraphArray.unitArray k)).map
        (fun x => sgn ((trialEquiv n k ω).2.1 a v)*x))=
      denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1 v a := by
  rw [labelBlock_decodes,KoanaKPaths.ExteriorCoordinates.wedgeReverse_eq_wedgeList]
  have hlen : (labelList (trialEquiv n k ω).1 v).length=k := by simp [labelList]
  simp only [List.length_reverse,hlen,List.reverse_reverse,GraphArray.unitArray,denseLayer]

end KoanaKPaths.Machine.Trial

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





end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main

lemma first_word_width {n k : ℕ} (v : Fin n) (a : Fin k) :
    firstExpr.width (firstValues n k v.val a.val)≤ wordWidth n k := by
  have hn := Controls.zsz_nat_le n
  have hk := Controls.zsz_nat_le k
  have hv := Controls.zsz_nat_le v.val
  have ha := Controls.zsz_nat_le a.val
  have hatom : firstExpr.atomWidth (firstValues n k v.val a.val)≤1+n+k := by
    change max (max (zsz (n : ℤ)) (zsz (k : ℤ)))
      (max (max (zsz (a.val : ℤ)) (zsz (n : ℤ))) (zsz (v.val : ℤ)))≤1+n+k
    omega
  have h := firstExpr.width_le (firstValues n k v.val a.val) (1+n+k) hatom
  have hs : firstExpr.size=9 := rfl
  rw [hs] at h
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]

lemma signsOf_first {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (a : Fin k) (v : Fin n) :
    (signsOf ω)[n*k+a.val*n+v.val]'(by
      rw [signsOf_length]
      simpa only [trialIndex_first] using (trialIndexEquiv n k (.inr (.inl (a,v)))).isLt)=
      sgn ((trialEquiv n k ω).2.1 a v) := by
  have h := signsOf_get ω (trialIndexEquiv n k (.inr (.inl (a,v))))
  rw [trialIndex_first] at h
  rw [List.getD_eq_getElem _ _ (by
    rw [signsOf_length]
    simpa only [trialIndex_first] using (trialIndexEquiv n k (.inr (.inl (a,v)))).isLt)] at h
  simpa only [trialEquiv_first] using h

lemma firstCell_decoded (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (v : Fin n) (a : Fin k)
    (nt kt vt atail tt dbtail vtail : List Item)
    (hn : s.G 53=.int (n : ℤ)::nt) (hk : s.G 54=.int (k : ℤ)::kt)
    (hv : s.G Vertex=.int (v.val : ℤ)::vt) (ha : s.G StateIndex=.int (a.val : ℤ)::atail)
    (hT : s.G Total=.int (trialBits n k : ℤ)::tt)
    (hdb : s.G SignDB=signItems (signsOf ω)++dbtail)
    (hbc : s.G BitCounter.Count=[]) (hbt : s.G BitCounter.Tmp=[])
    (hsc : s.G SignLookup.Count=[]) (hsb : s.G SignLookup.Back=[]) (hst : s.G SignLookup.Tmp=[])
    (hd : s.G Wedge.D=List.replicate k .mark)
    (hvec : s.G Wedge.V=(labelBlock (signsOf ω) k v.val 0 k).reverse.map Item.int ++ vtail)
    (hHC : s.G Wedge.HC=[]) (hDC : s.G Wedge.DC=[]) (hAux : s.G Wedge.Aux=[]) :
    IRuns I Wedge.prog firstCell s
      ((s.upd StateIndex (.int ((a.val+1 : ℕ) : ℤ)::atail)).upd GraphArray.Current
        ((denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1 v a).map Item.int ++ .mark::s.G GraphArray.Current))
      (10000000*(wordWidth n k+k+2)^2*2^k+10000*(trialBits n k+1)) := by
  let vs := (labelBlock (signsOf ω) k v.val 0 k).reverse
  have hlen : vs.length=k := by simp [vs,labelBlock_decodes,labelList]
  have hsgn : ∀ x∈vs, x=1 ∨ x= -1 := by
    intro x hx
    have hh : x∈labelList (trialEquiv n k ω).1 v := by simpa [vs,labelBlock_decodes] using hx
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hh
    cases h : (trialEquiv n k ω).1 v r <;> simp [sgn,h]
  have hj : n*k+a.val*n+v.val<(signsOf ω).length := by
    rw [signsOf_length]
    simpa only [trialIndex_first] using (trialIndexEquiv n k (.inr (.inl (a,v)))).isLt
  have h := firstCell_runs I s (signsOf ω) vs n k v.val a.val (wordWidth n k)
    nt kt vt atail tt dbtail vtail (wordWidth_pos n k) hn hk hv ha
    (by simpa only [signsOf_length] using hT) hdb hbc hbt hsc hsb hst (signsOf_values ω)
    (first_word_width v a) (by rw [signsOf_length]; exact trial_word_width n k 0 0 0)
    (row_word_width n k a.val (Nat.le_of_lt a.isLt)) hj hlen hd hvec hsgn hHC hDC hAux
  have harr : (KoanaKPaths.ExteriorCoordinates.wedgeReverse vs (GraphArray.unitArray k)).map
      (fun x => (signsOf ω)[n*k+a.val*n+v.val]'hj*x)=
      denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1 v a := by
    rw [signsOf_first]
    exact first_array_decodes ω arcs v a
  rw [harr,signsOf_length] at h
  exact h

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Machine

lemma framePrefix_succ (arrays : List (List ℤ)) (i : ℕ) (hi : i< arrays.length) :
    ArrayLookup.frames (arrays.take (i+1)).reverse=
      arrays[i].map NLogN.Item.int ++ .mark::ArrayLookup.frames (arrays.take i).reverse := by
  rw [List.take_succ_eq_append_getElem hi,List.reverse_append]
  simp only [List.reverse_singleton,List.singleton_append,ArrayLookup.frames_cons]

lemma framePrefix_ofFn_succ {k : ℕ} (F : Fin k→List ℤ) (i : ℕ) (hi : i< k) :
    ArrayLookup.frames ((List.ofFn F).take (i+1)).reverse=
      (F ⟨i,hi⟩).map NLogN.Item.int ++ .mark::ArrayLookup.frames ((List.ofFn F).take i).reverse := by
  have h := framePrefix_succ (List.ofFn F) i (by simpa only [List.length_ofFn] using hi)
  simpa only [List.getElem_ofFn] using h



end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] LabelCounter StateIndex GraphArray.Current Vertex Wedge.D Wedge.V
  Wedge.HC Wedge.DC Wedge.Aux Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp
  BitCounter.Count BitCounter.Tmp







lemma firstRow_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (v : Fin n)
    (nt kt vt atail tt dbtail vtail : List Item)
    (hn : s.G 53=.int (n : ℤ)::nt) (hk : s.G 54=.int (k : ℤ)::kt)
    (hv : s.G Vertex=.int (v.val : ℤ)::vt) (ha : s.G StateIndex=.int 0::atail)
    (hCounter : s.G LabelCounter=List.replicate k .mark)
    (hT : s.G Total=.int (trialBits n k : ℤ)::tt)
    (hdb : s.G SignDB=signItems (signsOf ω)++dbtail)
    (hbc : s.G BitCounter.Count=[]) (hbt : s.G BitCounter.Tmp=[])
    (hsc : s.G SignLookup.Count=[]) (hsb : s.G SignLookup.Back=[]) (hst : s.G SignLookup.Tmp=[])
    (hd : s.G Wedge.D=List.replicate k .mark)
    (hvec : s.G Wedge.V=(labelBlock (signsOf ω) k v.val 0 k).reverse.map Item.int ++ vtail)
    (hHC : s.G Wedge.HC=[]) (hDC : s.G Wedge.DC=[]) (hAux : s.G Wedge.Aux=[]) :
    IRuns I Wedge.prog firstRow s
      (firstRowState s (fun a => denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1 v a) k atail)
      ((firstCellCost n k+31)*k+30) := by
  let F : Fin k→List ℤ := fun a => denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1 v a
  let Inv : ℕ→IState NS→Prop := fun i st => st=firstRowState s F i atail
  have hcounter : ∀ i≤ k, ∀ st, Inv i st → st.G LabelCounter=List.replicate (k-i) .mark ++ [] := by
    intro i hi st hst
    rw [hst]
    simp [firstRowState]
  have hstep : ∀ i< k, ∀ st, Inv i st → ∃ st',
      IRuns I Wedge.prog (.seq (.op (.unmark LabelCounter)) firstCell) st st' (firstCellCost n k+1) ∧ Inv (i+1) st' := by
    intro i hi st hInv
    rw [hInv]
    let cur := firstRowState s F i atail
    let popped := cur.upd LabelCounter (List.replicate (k-(i+1)) .mark)
    let ai : Fin k := ⟨i,hi⟩
    let next := (popped.upd StateIndex (.int ((i+1 : ℕ) : ℤ)::atail)).upd GraphArray.Current
      ((F ai).map Item.int ++ .mark::popped.G GraphArray.Current)
    have hlen : k-i=(k-(i+1))+1 := by omega
    have h0 : IExec I Wedge.prog (.op (.unmark LabelCounter)) cur popped 1 :=
      .op (.unmark (by simp [cur,firstRowState,hlen,List.replicate_succ]))
    have h1 : IRuns I Wedge.prog firstCell popped next (firstCellCost n k) := by
      exact firstCell_decoded I popped ω arcs v ai nt kt vt atail tt dbtail vtail
        (by simp [popped,cur,firstRowState,hn]) (by simp [popped,cur,firstRowState,hk])
        (by simp [popped,cur,firstRowState,hv]) (by simp [popped,cur,firstRowState,ai])
        (by simp [popped,cur,firstRowState,hT]) (by simp [popped,cur,firstRowState,hdb])
        (by simp [popped,cur,firstRowState,hbc]) (by simp [popped,cur,firstRowState,hbt])
        (by simp [popped,cur,firstRowState,hsc]) (by simp [popped,cur,firstRowState,hsb])
        (by simp [popped,cur,firstRowState,hst]) (by simp [popped,cur,firstRowState,hd])
        (by simp [popped,cur,firstRowState,hvec]) (by simp [popped,cur,firstRowState,hHC])
        (by simp [popped,cur,firstRowState,hDC]) (by simp [popped,cur,firstRowState,hAux])
    have hpost : next=firstRowState s F (i+1) atail := by
      apply itemState_ext
      · intro r
        by_cases hC : r=LabelCounter
        · subst r; simp [next,popped,cur,firstRowState]
        by_cases hA : r=StateIndex
        · subst r; simp [next,popped,cur,firstRowState]
        by_cases hO : r=GraphArray.Current
        · subst r
          simp [next,popped,cur,firstRowState,framePrefix_ofFn_succ F i hi,List.append_assoc,ai]
        simp [next,popped,cur,firstRowState,IState.upd,Function.update_apply,hC,hA,hO]
      · rfl
      · rfl
    refine ⟨next,?_,hpost⟩
    exact Native.mono (Native.seq (Native.of_exec h0) h1) (by omega)
  have hinit : Inv 0 s := by
    unfold Inv firstRowState
    simp only [Nat.sub_zero,List.take_zero,List.reverse_nil,ArrayLookup.frames,List.flatMap_nil,List.nil_append,Nat.cast_zero]
    rw [← hCounter,← ha]
    simp
  obtain ⟨st',hrun,hend⟩ := Native.invariant_loop I Wedge.prog LabelCounter
    (.seq (.op (.unmark LabelCounter)) firstCell) Inv k (firstCellCost n k+1) [] (by simp [cls]) hcounter hstep s hinit
  rw [hend] at hrun
  simpa only [firstRow,F,Nat.add_assoc,show (1+30 : ℕ)=31 from rfl] using hrun

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (v : Fin n)
  (nt kt vt atail tt dbtail vtail : List.{0} NLogN.Item)
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
  (ha :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.StateIndex)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) atail))
  (hCounter :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.LabelCounter)
      (@List.replicate.{0} NLogN.Item k NLogN.Item.mark))
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
  (hvec :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Wedge.V)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.reverse.{0} Int
            (KoanaKPaths.Machine.Trial.labelBlock (@KoanaKPaths.Machine.Trial.signsOf n k ω) k (@Fin.val n v)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)))
        vtail))
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
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.firstRow s
    (@KoanaKPaths.Machine.Trial.firstRowState k s
      (fun (a : Fin k) =>
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
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) v a)
      k atail)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (KoanaKPaths.Machine.Trial.firstCellCost n k)
          (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
        k)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Trial.firstRow_runs
