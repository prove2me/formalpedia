-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.firstLayer_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.236426+00:00
-- url     : https://prove2.me/submissions/e27e9c11-2cee-4d98-8ea1-070aa6c7877c

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
import Theorems.Thm_KoanaKPaths_Machine_Matrix_transferLoop_exec
import Theorems.Thm_KoanaKPaths_Machine_Trial_firstVertices_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
import Theorems.Thm_KoanaKPaths_Main_graphLayer_natAbs
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

set_option maxHeartbeats 400000
open scoped BigOperators
namespace KoanaKPaths.ExteriorCoordinates


























lemma subsetOrder_length (k : ℕ) : (subsetOrder k).length = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [subsetOrder,ih,pow_succ]; omega







lemma coefficientList_length {k : ℕ} (A : Coordinates k) : (coefficientList A).length = 2^k := by
  simp [coefficientList,subsetOrder_length]

































end KoanaKPaths.ExteriorCoordinates

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
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates














lemma denseLayer_length {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (p : ℕ) (v : Fin n) (a : Fin ℓ) :
    (denseLayer arcs σ R p v a).length=2^k := by
  rw [denseLayer_correct]
  exact coefficientList_length _







end KoanaKPaths.Main

end

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates














lemma layerRadius_le_exp (n k ℓ : ℕ) : layerRadius n k ℓ≤2^(n+k+ℓ+3) := by
  have hp : layerRadius n k ℓ≤(n+1)*(k+1)*(ℓ+1) := by
    unfold layerRadius
    nlinarith [Nat.zero_le (n*k),Nat.zero_le (n*ℓ),Nat.zero_le (k*ℓ)]
  have hn : n+1≤2^(n+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hk : k+1≤2^(k+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hl : ℓ+1≤2^(ℓ+1) := Nat.le_of_lt Nat.lt_two_pow_self
  calc
    _ ≤ (n+1)*(k+1)*(ℓ+1) := hp
    _ ≤ 2^(n+1)*2^(k+1)*2^(ℓ+1) := Nat.mul_le_mul (Nat.mul_le_mul hn hk) hl
    _ = _ := by rw [← pow_add,← pow_add]; congr 1; omega

lemma graphLayer_width {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (p : ℕ) (v : Fin n) (a : Fin ℓ) (S : Finset (Fin k)) :
    NLogN.zsz (graphLayer arcs σ R p v a S)≤(n+k+ℓ+3)*p+1 := by
  apply (Machine.Wedge.zsz_le_iff _ _).mpr
  have hr := Nat.pow_le_pow_left (layerRadius_le_exp n k ℓ) p
  rw [← pow_mul] at hr
  have h := (graphLayer_natAbs arcs σ R p v a S).trans hr
  have hp : 0<2^((n+k+ℓ+3)*p) := by positivity
  rw [pow_succ]
  omega



end KoanaKPaths.Main

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
namespace KoanaKPaths.Main



lemma matrixArrays_length {n k : ℕ} (F : Fin n→Fin k→List ℤ) :
    (matrixArrays F).length=n*k := by simp [matrixArrays]



lemma matrixArrays_nested {n k : ℕ} (F : Fin n→Fin k→List ℤ) :
    matrixArrays F=(List.ofFn (fun v : Fin n => List.ofFn (F v))).flatten := by
  rw [matrixArrays,List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val*k+j.val< n*k := by
    have hm := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hm
    omega
  have he : (⟨i.val*k+j.val,hij⟩ : Fin (n*k))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*k+j.val=j.val+k*i.val
    ring
  simp only [he,Equiv.symm_apply_apply]

lemma matrixArrays_bounds {n k : ℕ} (F : Fin n→Fin k→List ℤ) (P w : ℕ)
    (hl : ∀ v a, (F v a).length≤ P) (hw : ∀ v a, ∀ x∈F v a, NLogN.zsz x≤ w) :
    (∀ A∈matrixArrays F, A.length≤ P) ∧
      (∀ A∈matrixArrays F, ∀ x∈A, NLogN.zsz x≤ w) := by
  constructor
  · intro A hA
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hA
    rw [← hi]
    exact hl _ _
  · intro A hA
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hA
    rw [← hi]
    exact hw _ _

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Matrix







attribute [local simp] Prev ArrayLookup.DB Current Tmp Template Counter CopyTmp









lemma transfer_exec (I : List Sym) (s : IState NS) (arrays : List (List ℤ)) (tail : List Item)
    (ht : s.G Template=List.replicate arrays.length .mark)
    (hc : s.G Counter=[]) (hx : s.G CopyTmp=[])
    (hs : s.G Current=ArrayLookup.frames arrays++tail) :
    IExec I Fin.elim0 transfer s
      ((s.upd Current tail).upd Prev (ArrayLookup.frames arrays.reverse++s.G Prev))
      (65*arrays.length+60+transferCost arrays) := by
  let s1 := s.upd Counter (List.replicate arrays.length .mark)
  have h1 : IExec I Fin.elim0 (copyMarks Template Counter CopyTmp) s s1 (65*arrays.length+60) := by
    simpa [s1,hc] using copyMarks_exec I Template Counter CopyTmp (by decide) (by decide) (by decide)
      s arrays.length [] (by simp [cls]) (by simpa using ht) hx
  have h2 := transferLoop_exec I s1 arrays tail (by simp [s1]) (by simp [s1,hs])
  have he : (((s1.upd Counter []).upd Current tail).upd Prev
      (ArrayLookup.frames arrays.reverse++s1.G Prev))=
      (s.upd Current tail).upd Prev (ArrayLookup.frames arrays.reverse++s.G Prev) := by
    simp [s1,← hc]
  rw [he] at h2
  exact IExec.seq h1 h2

lemma transferCost_bound (arrays : List (List ℤ)) (k w : ℕ)
    (hl : ∀ a∈arrays, a.length≤2^k) (hw : ∀ a∈arrays, ∀ x∈a, zsz x≤ w) :
    65*arrays.length+60+transferCost arrays≤2000*(w+1)*2^k*(arrays.length+1) := by
  have hbase : transferCost arrays≤1000*(w+1)*2^k*arrays.length+30 := by
    induction arrays with
    | nil => simp [transferCost]
    | cons a arrays ih =>
      have hlen := hl a (by simp)
      have ha := Wedge.moveIntsCost_bound a w (hw a (by simp))
      have ht := ih (fun a ha => hl a (by simp [ha])) (fun a ha => hw a (by simp [ha]))
      have hp : 1≤2^k := by
        have h : 0<2^k := by positivity
        omega
      simp only [transferCost,List.length_cons]
      nlinarith
  have hp : 1≤2^k := by
    have h : 0<2^k := by positivity
    omega
  have hPW : 1≤(w+1)*2^k := Nat.mul_le_mul (by omega : 1≤ w+1) hp
  have hm : arrays.length≤(w+1)*2^k*arrays.length := by
    simpa using Nat.mul_le_mul_right arrays.length hPW
  nlinarith

end KoanaKPaths.Machine.Matrix

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates

lemma denseLayer_word_width {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (hp : p≤ k+1) (v : Fin n) (a : Fin k) :
    ∀ x∈denseLayer arcs σ R p v a, zsz x≤ wordWidth n k := by
  intro x hx
  rw [denseLayer_correct] at hx
  obtain ⟨S,_,rfl⟩ := List.mem_map.mp hx
  have h := graphLayer_width arcs σ R p v a S
  have hmul := Nat.mul_le_mul_left (n+k+k+3) hp
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k),Nat.zero_le (k*k)]

lemma denseMatrix_word_bounds {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (hp : p≤ k+1) :
    (∀ A∈matrixArrays (denseLayer arcs σ R p), A.length≤2^k) ∧
    (∀ A∈matrixArrays (denseLayer arcs σ R p), ∀ x∈A, zsz x≤ wordWidth n k) := by
  exact matrixArrays_bounds (denseLayer arcs σ R p) (2^k) (wordWidth n k)
    (fun v a => Nat.le_of_eq (denseLayer_length arcs σ R p v a)) (denseLayer_word_width arcs σ R p hp)

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] VerticesCounter VerticesTemplate Vertex LabelCounter LabelTmp GraphArray.Current
  Matrix.Current Matrix.Prev Matrix.Template Matrix.Counter Matrix.CopyTmp
  Wedge.D Wedge.HC Wedge.DC Wedge.Aux Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back
  SignLookup.Tmp BitCounter.Count BitCounter.Tmp ArrayLookup.DB





lemma firstLayer_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (nt kt tt dbtail : List Item)
    (hn : s.G 53=.int (n : ℤ)::nt) (hk : s.G 54=.int (k : ℤ)::kt)
    (hN : s.G VerticesTemplate=List.replicate n .mark) (hOuter : s.G VerticesCounter=[])
    (hT : s.G Total=.int (trialBits n k : ℤ)::tt) (hdb : s.G SignDB=signItems (signsOf ω)++dbtail)
    (hbc : s.G BitCounter.Count=[]) (hbt : s.G BitCounter.Tmp=[])
    (hsc : s.G SignLookup.Count=[]) (hsb : s.G SignLookup.Back=[]) (hst : s.G SignLookup.Tmp=[])
    (hd : s.G Wedge.D=List.replicate k .mark) (hCounter : s.G LabelCounter=[]) (hTmp : s.G LabelTmp=[])
    (hHC : s.G Wedge.HC=[]) (hDC : s.G Wedge.DC=[]) (hAux : s.G Wedge.Aux=[])
    (hMatrix : s.G Matrix.Template=List.replicate (n*k) .mark)
    (hMC : s.G Matrix.Counter=[]) (hMT : s.G Matrix.CopyTmp=[]) :
    IRuns I Wedge.prog firstLayer s
      (s.upd Matrix.Prev (ArrayLookup.frames (matrixArrays
        (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1)) ++ s.G Matrix.Prev))
      (firstLayerCost n k) := by
  let F : Fin n→Fin k→List ℤ := denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1
  let arrays := matrixArrays F
  let s0 := s.upd Vertex (.int 0::s.G Vertex)
  let s1 := s0.upd VerticesCounter (List.replicate n .mark)
  let s2 := firstVerticesState s1 F n (s.G Vertex)
  let s3 := s2.upd Vertex (s.G Vertex)
  let s4 := (s3.upd Matrix.Current (s.G Matrix.Current)).upd Matrix.Prev
    (ArrayLookup.frames arrays++s.G Matrix.Prev)
  have h0 : IExec I Wedge.prog (.op (.const Vertex 0)) s s0 2 := by
    simpa [Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := Wedge.prog) (IOp.Step.const (s := s) (i := Vertex) 0))
  have h1 : IExec I Wedge.prog (liftClosed (copyMarks VerticesTemplate VerticesCounter LabelTmp)) s0 s1 (65*n+60) := by
    have h := liftClosed_exec I Wedge.prog (copyMarks_exec I VerticesTemplate VerticesCounter LabelTmp
      (by decide) (by decide) (by decide) s0 n [] (by simp [cls]) (by simp [s0,hN]) (by simp [s0,hTmp]))
    simpa [s1,s0,hOuter] using h
  have h2 : IRuns I Wedge.prog firstVertices s1 s2 ((firstVertexCost n k+31)*n+30) := by
    exact firstVertices_runs I s1 ω arcs nt kt (s.G Vertex) tt dbtail
      (by simp [s1,s0,hn]) (by simp [s1,s0,hk]) (by simp [s1,s0]) (by simp [s1])
      (by simp [s1,s0,hT]) (by simp [s1,s0,hdb]) (by simp [s1,s0,hbc]) (by simp [s1,s0,hbt])
      (by simp [s1,s0,hsc]) (by simp [s1,s0,hsb]) (by simp [s1,s0,hst]) (by simp [s1,s0,hd])
      (by simp [s1,s0,hCounter]) (by simp [s1,s0,hTmp]) (by simp [s1,s0,hHC])
      (by simp [s1,s0,hDC]) (by simp [s1,s0,hAux])
  have h3 : IExec I Wedge.prog (.op (.drop Vertex)) s2 s3 (2*zsz (n : ℤ)+2) :=
    .op (.drop (by simp [s2,firstVerticesState]))
  have htake : (List.ofFn (fun v => List.ofFn (F v))).take n=List.ofFn (fun v => List.ofFn (F v)) :=
    List.take_of_length_le (by simp)
  have hCurr : s3.G Matrix.Current=ArrayLookup.frames arrays.reverse++s.G Matrix.Current := by
    simp [s3,s2,firstVerticesState,s1,s0,htake,arrays,matrixArrays_nested]
  have h4 : IExec I Wedge.prog (liftClosed Matrix.transfer) s3 s4
      (65*arrays.reverse.length+60+Matrix.transferCost arrays.reverse) := by
    have h := liftClosed_exec I Wedge.prog (Matrix.transfer_exec I s3 arrays.reverse (s.G Matrix.Current)
      (by simp [s3,s2,firstVerticesState,s1,s0,arrays,matrixArrays_length,hMatrix])
      (by simp [s3,s2,firstVerticesState,s1,s0,hMC])
      (by simp [s3,s2,firstVerticesState,s1,s0,hMT]) hCurr)
    simpa [s4,s3,s2,firstVerticesState,s1,s0,IState.upd] using h
  have hpost : s4=s.upd Matrix.Prev (ArrayLookup.frames arrays++s.G Matrix.Prev) := by
    apply itemState_ext
    · intro i
      by_cases hP : i=Matrix.Prev
      · subst i; simp [s4,s3,s2,firstVerticesState,s1,s0,IState.upd]
      by_cases hC : i=Matrix.Current
      · subst i; simp [s4,s3,s2,firstVerticesState,s1,s0,IState.upd]
      by_cases hV : i=Vertex
      · subst i; simp [s4,s3,s2,firstVerticesState,s1,s0,IState.upd]
      by_cases hO : i=VerticesCounter
      · subst i; simp [s4,s3,s2,firstVerticesState,s1,s0,IState.upd,hOuter]
      simp [s4,s3,s2,firstVerticesState,s1,s0,IState.upd,Function.update_apply,hP,hC,hV,hO]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1)
    (Native.seq h2 (Native.seq (Native.of_exec h3) (Native.of_exec h4))))
  rw [hpost] at h
  change IRuns I Wedge.prog firstLayer s _ _ at h
  apply Native.mono h
  have hbounds := denseMatrix_word_bounds arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1 (by omega)
  have htransfer := Matrix.transferCost_bound arrays.reverse k (wordWidth n k)
    (by simpa [arrays,F] using hbounds.1) (by simpa [arrays,F] using hbounds.2)
  have hnw : zsz (n : ℤ)≤ wordWidth n k := by
    have hh := Controls.zsz_nat_le n
    unfold wordWidth
    nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
  simp only [List.length_reverse,arrays,matrixArrays_length] at htransfer
  unfold firstLayerCost
  simp only [List.length_reverse,arrays,matrixArrays_length]
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (nt kt tt dbtail : List.{0} NLogN.Item)
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
  (hN :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.VerticesTemplate)
      (@List.replicate.{0} NLogN.Item n NLogN.Item.mark))
  (hOuter :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.VerticesCounter)
      (@List.nil.{0} NLogN.Item))
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
      (@List.nil.{0} NLogN.Item))
  (hMatrix :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Matrix.Template)
      (@List.replicate.{0} NLogN.Item (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n k)
        NLogN.Item.mark))
  (hMC :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Matrix.Counter)
      (@List.nil.{0} NLogN.Item))
  (hMT :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Matrix.CopyTmp)
      (@List.nil.{0} NLogN.Item)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.firstLayer s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Matrix.Prev
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (KoanaKPaths.Machine.ArrayLookup.frames
          (@KoanaKPaths.Main.matrixArrays n k
            (@KoanaKPaths.Main.denseLayer n k k arcs
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
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Matrix.Prev)))
    (KoanaKPaths.Machine.Trial.firstLayerCost n k) := by
  exact @KoanaKPaths.Machine.Trial.firstLayer_runs
