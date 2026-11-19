-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.nativeTrial_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:38.045242+00:00
-- url     : https://prove2.me/submissions/9c3d4023-92a0-4bd4-b19f-6adac7fe9c5c

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
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_compile_runs
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_width_le
import Theorems.Thm_KoanaKPaths_Machine_Trial_graphLayers_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_loadLoop_exec
import Theorems.Thm_KoanaKPaths_Machine_Trial_normDriver_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
import Theorems.Thm_KoanaKPaths_Main_graphLayer_natAbs
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





lemma zsz_sign (z : ℤ) (hz : z=1 ∨ z = -1) : zsz z=1 := by
  rcases hz with rfl|rfl <;> simp [zsz_eq_size]





























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
namespace KoanaKPaths.Machine.Trial






attribute [local simp] Coins SignDB SignLookup.DB SignTemplate SignCounter SignTmp











lemma loadSigns_exec (I : List Sym) (s : IState NS) (xs : List ℤ) (tail : List Item)
    (ht : s.G SignTemplate=List.replicate xs.length .mark)
    (hc : s.G SignCounter=[]) (hx : s.G SignTmp=[])
    (hs : s.G Coins=xs.map Item.int ++ tail) :
    IExec I Fin.elim0 loadSigns s
      ((s.upd Coins tail).upd SignDB (signItems xs ++ s.G SignDB))
      (65*xs.length+60+loadCost xs) := by
  let s1 := s.upd SignCounter (List.replicate xs.length .mark)
  have h1 : IExec I Fin.elim0 (copyMarks SignTemplate SignCounter SignTmp) s s1 (65*xs.length+60) := by
    simpa [s1,hc] using copyMarks_exec I SignTemplate SignCounter SignTmp (by decide) (by decide)
      (by decide) s xs.length [] (by simp [cls]) (by simpa using ht) hx
  have h2 := loadLoop_exec I s1 xs tail (by simp [s1]) (by simp [s1,hs])
  have he : (((s1.upd SignCounter []).upd Coins tail).upd SignDB (signItems xs ++ s1.G SignDB))=
      (s.upd Coins tail).upd SignDB (signItems xs ++ s.G SignDB) := by
    simp [s1,← hc]
  rw [he] at h2
  exact IExec.seq h1 h2

lemma loadSigns_cost (xs : List ℤ) (hx : ∀ x∈xs, x=1 ∨ x= -1) :
    65*xs.length+60+loadCost xs≤300*(xs.length+1) := by
  have hs : loadCost xs=209*xs.length+30 := by
    unfold loadCost
    have h : (xs.map (fun x => 2*moveCost (zsz x)+51)).sum=209*xs.length := by
      induction xs with
      | nil => simp
      | cons x xs ih =>
        have hw := Wedge.zsz_sign x (hx x (by simp))
        have ht := ih (fun z hz => hx z (by simp [hz]))
        simp only [List.map_cons,List.sum_cons,List.length_cons,hw,ht]
        norm_num [moveCost]
        omega
    rw [h]
  rw [hs]
  omega

end KoanaKPaths.Machine.Trial

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

















lemma clearItems_exec (I : List Sym) (src : Fin S) (s : IState S) :
    IExec I Fin.elim0 (clearItems src) s (s.upd src []) (clearItemsCost (s.G src)) := by
  suffices ∀ xs : List Item, ∀ s : IState S, s.G src=xs →
      IExec I Fin.elim0 (clearItems src) s (s.upd src []) (clearItemsCost xs) from this _ s rfl
  intro xs
  induction xs with
  | nil =>
    intro s hs
    have he : s.upd src []=s := by rw [← hs]; exact upd_same _ _
    rw [he]
    exact IExec.loopF (by simp [IState.cl,hs,cls])
  | cons x xs ih =>
    intro s hs
    let s1 := s.upd src xs
    have hc : decide (s.cl src≠Cls.none)=true := by
      cases x <;> simp [IState.cl,hs,cls]
      split_ifs <;> simp
    have hbody : IExec I Fin.elim0
        (.ite src (fun c => decide (c=Cls.mark)) (.op (.unmark src)) (.op (.drop src))) s s1
        (itemClearCost x-30) := by
      cases x with
      | mark =>
        exact IExec.iteT (by simp [IState.cl,hs,cls]) (IExec.op (IOp.Step.unmark hs))
      | int z =>
        have hh : decide (s.cl src=Cls.mark)=false := by simp [IState.cl,hs,cls]; split_ifs <;> simp
        have h := IExec.iteF (i := src) (f := fun c => decide (c=Cls.mark)) (p := .op (.unmark src)) hh (IExec.op (IOp.Step.drop hs) : IExec I Fin.elim0 _ _ _ (2*zsz z+2))
        convert h using 1 <;> simp [itemClearCost] <;> omega
    have hrun := IExec.loopT hc hbody (ih s1 (by simp [s1]))
    have hpos : 30≤ itemClearCost x := by cases x <;> simp [itemClearCost]
    change IExec I Fin.elim0 (clearItems src) s _ _ at hrun
    simp only [s1,upd_upd] at hrun
    convert hrun using 1
    simp only [clearItemsCost,List.map_cons,List.sum_cons]
    omega

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









end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}
attribute [local simp] Square.Eval Square.Value BitCounter.Source BitCounter.Count BitCounter.Tmp



lemma storeExpr_runs (I : List Sym) (reg : Fin v→Fin Square.NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (w : ℕ) (hw : e.width values≤ w)
    (dst : Fin Square.NS) (hd : dst≠Eval) (s : IState Square.NS)
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail) :
    IRuns I Fin.elim0 (storeExpr reg e dst) s
      (s.upd dst (.int (e.eval values : ℤ)::s.G dst)) (11000*(e.size+1)*(w+1)^2) := by
  let s1 := s.upd Eval (.int (e.eval values : ℤ)::s.G Eval)
  let s2 := (s1.upd Eval (s.G Eval)).upd dst (.int (e.eval values : ℤ)::s.G dst)
  have h1 := e.compile_runs I reg hreg values w hw s hv
  have h2 : IExec I Fin.elim0 (.op (.mv Eval dst)) s1 s2 (2*moveCost (zsz (e.eval values : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt Square.NS 0))
      (IOp.Step.mv (s := s1) (i := Eval) (j := dst) (a := (e.eval values : ℤ)) (L := s.G Eval)
        (Ne.symm hd) (by simp [s1]))
    simpa [s2,s1,hd] using h
  have he : s2=s.upd dst (.int (e.eval values : ℤ)::s.G dst) := by simp [s2,s1]
  have h := Native.seq h1 (Native.of_exec h2)
  rw [he] at h
  change IRuns I Fin.elim0 (storeExpr reg e dst) s _ _ at h
  apply Native.mono h
  have hx := (e.root_width values).trans hw
  unfold moveCost
  nlinarith [Nat.zero_le (e.size*w*w)]





end KoanaKPaths.Machine.Arithmetic

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







end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace KoanaKPaths.Main



lemma matrixArrays_length {n k : ℕ} (F : Fin n→Fin k→List ℤ) :
    (matrixArrays F).length=n*k := by simp [matrixArrays]





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
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

lemma clearItemsCost_bound (xs : List Item) (w : ℕ)
    (hw : ∀ x∈xs, itemClearCost x≤2*w+57) :
    clearItemsCost xs≤(2*w+57)*xs.length+30 := by
  have hh : (xs.map itemClearCost).sum≤(2*w+57)*xs.length := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := hw x (by simp)
      have ht := ih (fun y hy => hw y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  exact Nat.add_le_add_right hh 30

lemma frames_length (arrays : List (List ℤ)) (k : ℕ) (hl : ∀ a∈arrays, a.length≤2^k) :
    (ArrayLookup.frames arrays).length≤(2^k+1)*arrays.length := by
  induction arrays with
  | nil => simp [ArrayLookup.frames]
  | cons a arrays ih =>
    have ha := hl a (by simp)
    have ht := ih (fun b hb => hl b (by simp [hb]))
    simp only [ArrayLookup.frames,List.flatMap_cons,List.length_append,List.length_map,List.length_singleton,List.length_cons,List.length_nil] at *
    nlinarith

lemma clearFrames_bound (arrays : List (List ℤ)) (k w : ℕ)
    (hl : ∀ a∈arrays, a.length≤2^k) (hw : ∀ a∈arrays, ∀ x∈a, zsz x≤ w) :
    clearItemsCost (ArrayLookup.frames arrays)≤(2*w+57)*(2^k+1)*arrays.length+30 := by
  have h := clearItemsCost_bound (ArrayLookup.frames arrays) w (by
    intro x hx
    obtain ⟨a,ha,hx⟩ := List.mem_flatMap.mp hx
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hx
    rcases hx with ⟨z,hz,rfl⟩|rfl
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hw a ha z hz)) 57
    · simp [itemClearCost])
  exact h.trans (Nat.add_le_add_right (by
    have hmul := Nat.mul_le_mul_left (2*w+57) (frames_length arrays k hl)
    simpa only [Nat.mul_assoc] using hmul) 30)

end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main







lemma Ready.at {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)}
    (h : Ready (k := k) s arcs) (j : Fin NS) (hj : j∈readyRegisters) : s.G j=readyStack n k arcs j := h j hj

lemma Ready.upd {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)} (h : Ready (k := k) s arcs)
    (j : Fin NS) (hj : j∉readyRegisters) (xs : List Item) : Ready (k := k) (s.upd j xs) arcs := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr

lemma Ready.core {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)}
    (h : Ready (k := k) s arcs) (ω : Fin (trialBits n k)→Bool) (p : ℕ) :
    Core (((s.upd 63 [.int (trialBits n k : ℤ)]).upd 24 (signItems (signsOf ω))).upd 14
      (ArrayLookup.frames (matrixArrays (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p)))) ω arcs p := by
  intro j hj
  simp only [coreRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (try simp [IState.upd,coreStack,NS,Wedge.NS])
  all_goals exact h.at _ (by decide)

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main







lemma totalExpr_eval (n k : ℕ) : totalExpr.eval (totalValues n k)=trialBits n k := rfl

lemma total_word_width (n k : ℕ) : totalExpr.width (totalValues n k)≤ wordWidth n k := by
  have hn := Controls.zsz_nat_le n
  have hk := Controls.zsz_nat_le k
  have hkm := Controls.zsz_nat_le (k-1)
  have ha : totalExpr.atomWidth (totalValues n k)≤1+n+k := by
    change max (max (zsz (n : ℤ)) (zsz (k : ℤ)))
      (max (max (zsz (k : ℤ)) (zsz (n : ℤ)))
        (max (zsz ((k-1 : ℕ) : ℤ)) (max (zsz (k : ℤ)) (max (zsz (k : ℤ)) (zsz (n : ℤ))))))≤1+n+k
    omega
  have h := totalExpr.width_le (totalValues n k) (1+n+k) ha
  have hs : totalExpr.size=15 := rfl
  rw [hs] at h
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]

lemma storeTotal_runs (I : List Sym) (s : IState NS) {n k : ℕ} (arcs : List (Fin n × Fin n))
    (hr : Ready (k := k) s arcs) : IRuns I Fin.elim0 storeTotal s
      (s.upd Total [.int (trialBits n k : ℤ)]) (176000*(wordWidth n k+1)^2) := by
  have h := storeExpr_runs I totalRegs (by intro j; fin_cases j <;> decide) (totalValues n k)
    totalExpr (wordWidth n k) (total_word_width n k) Total (by decide) s (by
      intro j; fin_cases j
      · exact ⟨[],by simpa [totalRegs,totalValues,readyStack,NS,Wedge.NS] using hr.at 53 (by decide)⟩
      · exact ⟨[],by simpa [totalRegs,totalValues,readyStack,NS,Wedge.NS] using hr.at 54 (by decide)⟩
      · exact ⟨[],by simpa [totalRegs,totalValues,readyStack,NS,Wedge.NS] using hr.at 66 (by decide)⟩)
  have ht : s.G Total=[] := by simpa [Total,readyStack,NS,Wedge.NS] using hr.at 63 (by decide)
  simpa [storeTotal,totalExpr_eval,ht,show totalExpr.size=15 from rfl] using h

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial

lemma signItems_clear_cost (xs : List ℤ) (hx : ∀ x∈xs, x=1 ∨ x= -1) :
    clearItemsCost (signItems xs)≤120*(xs.length+1) := by
  let arrays := xs.reverse.map (fun x => [x])
  have hf : signItems xs=ArrayLookup.frames arrays := by
    dsimp only [arrays,signItems,ArrayLookup.frames]
    rw [List.flatMap_map]
    rfl
  rw [hf]
  have h := clearFrames_bound arrays 0 1 (by
    intro a ha; obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha; simp) (by
    intro a ha x hxa
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    have he : x=z := by simpa using hxa
    subst x
    have hs := hx z (by simpa using hz)
    exact Nat.le_of_eq (Wedge.zsz_sign z hs))
  simp only [arrays,List.length_map,List.length_reverse] at h
  norm_num at h
  dsimp only [arrays] at *
  simp only [List.map_reverse] at *
  omega

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine
variable {S : ℕ}
lemma item_upd_comm (s : IState S) (i j : Fin S) (hi : i≠j) (xs ys : List Item) :
    (s.upd i xs).upd j ys=(s.upd j ys).upd i xs := by
  apply itemState_ext
  · intro r
    by_cases hI : r=i <;> by_cases hJ : r=j <;> simp_all [IState.upd,Function.update_apply]
  · rfl
  · rfl
end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] SignLookup.DB Coins SignDB SignTemplate SignCounter SignTmp Total Matrix.Prev ArrayLookup.DB Norm.Sum
  LabelCounter PredecessorCounter





lemma nativeTrial_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n))
    (coinTail : List Item) (hk : 1≤ k) (hr : Ready (k := k) s arcs)
    (hCoins : s.G Coins=(signsOf ω).map Item.int ++ coinTail) :
    IRuns I Wedge.prog nativeTrial s
      ((s.upd Coins coinTail).upd Norm.Sum
        (.int (trialNumerator (walkTensor n arcs k) (trialEquiv n k ω) : ℤ)::s.G Norm.Sum))
      (nativeTrialCost n k arcs.length) := by
  let base := s.upd Coins coinTail
  let s0 := s.upd Total [.int (trialBits n k : ℤ)]
  let s1 := labeledState base ω
  let s2 := s1.upd Matrix.Prev (ArrayLookup.frames (matrixArrays
    (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k)))
  let s3 := s2.upd Norm.Sum
    (.int (trialNumerator (walkTensor n arcs k) (trialEquiv n k ω) : ℤ)::s.G Norm.Sum)
  let s4 := s3.upd Matrix.Prev []
  let s5 := s4.upd SignDB []
  let s6 := s5.upd Total []
  have hrbase : Ready (k := k) base arcs := hr.upd Coins (by decide) _
  have h0 : IRuns I Wedge.prog (liftClosed storeTotal) s s0 (176000*(wordWidth n k+1)^2) :=
    liftClosed_runs I Wedge.prog (storeTotal_runs I s arcs hr)
  have h1 : IRuns I Wedge.prog (liftClosed loadSigns) s0 s1 (300*(trialBits n k+1)) := by
    have h := liftClosed_exec I Wedge.prog (loadSigns_exec I s0 (signsOf ω) coinTail
      (by simpa [s0,readyStack,NS,Wedge.NS,signsOf_length] using hr.at 44 (by decide))
      (by simpa [s0,readyStack,NS,Wedge.NS] using hr.at 67 (by decide))
      (by simpa [s0,readyStack,NS,Wedge.NS] using hr.at 68 (by decide))
      (by simp [s0,hCoins]))
    have hdb : s.G SignDB=[] := by simpa [readyStack,NS,Wedge.NS] using hr.at 24 (by decide)
    have he : (s0.upd Coins coinTail).upd SignDB (signItems (signsOf ω)++s0.G SignDB)=s1 := by
      simp only [s0,s1,labeledState,base,upd_G_ne _ (by decide : SignDB≠Total),hdb,List.append_nil]
      rw [item_upd_comm s Total Coins (by decide)]
    rw [he] at h
    exact Native.mono (Native.of_exec h) (by simpa only [signsOf_length] using loadSigns_cost (signsOf ω) (signsOf_values ω))
  have h2 : IRuns I Wedge.prog graphLayers s1 s2 (firstLayerCost n k+layerDriverCost n k arcs.length) :=
    graphLayers_runs I base ω arcs hk hrbase
  have hCore : Core s2 ω arcs k := hrbase.core ω k
  have h3 : IRuns I Wedge.prog normDriver s2 s3 (normDriverCost n k) := by
    have h := normDriver_runs I s2 ω arcs hk hCore
      (by simpa [s2,s1,labeledState,base,readyStack,NS,Wedge.NS] using hr.at 88 (by decide))
      (by simpa [s2,s1,labeledState,base,readyStack,NS,Wedge.NS] using hr.at 91 (by decide))
    simpa [s3,s2,s1,labeledState,base] using h
  have h4 : IRuns I Wedge.prog (liftClosed (clearItems Matrix.Prev)) s3 s4
      ((2*wordWidth n k+57)*(2^k+1)*(n*k)+30) := by
    have h := liftClosed_exec I Wedge.prog (clearItems_exec I Matrix.Prev s3)
    have hb := denseMatrix_word_bounds arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k (by omega)
    have hh := clearFrames_bound (matrixArrays (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k))
      k (wordWidth n k) hb.1 hb.2
    rw [matrixArrays_length] at hh
    apply Native.mono (Native.of_exec h)
    simpa [s3,s2] using hh
  have h5 : IRuns I Wedge.prog (liftClosed (clearItems SignDB)) s4 s5 (120*(trialBits n k+1)) := by
    have h := liftClosed_exec I Wedge.prog (clearItems_exec I SignDB s4)
    apply Native.mono (Native.of_exec h)
    have hh := signItems_clear_cost (signsOf ω) (signsOf_values ω)
    simpa [s4,s3,s2,s1,labeledState,signsOf_length] using hh
  have h6 : IExec I Wedge.prog (.op (.drop Total)) s5 s6 (2*zsz (trialBits n k : ℤ)+2) :=
    .op (.drop (by simp [s5,s4,s3,s2,s1,labeledState]))
  have hprev : s.G Matrix.Prev=[] := by simpa [readyStack,NS,Wedge.NS] using hr.at 14 (by decide)
  have hsign : s.G SignDB=[] := by simpa [readyStack,NS,Wedge.NS] using hr.at 24 (by decide)
  have htotal : s.G Total=[] := by simpa [readyStack,NS,Wedge.NS] using hr.at 63 (by decide)
  have hpost : s6=(s.upd Coins coinTail).upd Norm.Sum
        (.int (trialNumerator (walkTensor n arcs k) (trialEquiv n k ω) : ℤ)::s.G Norm.Sum) := by
    apply itemState_ext
    · intro r
      by_cases h52 : r=52 <;> by_cases h79 : r=79 <;> by_cases h14 : r=14 <;> by_cases h24 : r=24 <;> by_cases h63 : r=63 <;>
        simp [s6,s5,s4,s3,s2,s1,labeledState,base,IState.upd,Function.update_apply,h52,h79,h14,h24,h63,hprev,hsign,htotal]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq h1 (Native.seq h2 (Native.seq h3 (Native.seq h4 (Native.seq h5 (Native.of_exec h6))))))
  rw [hpost] at h
  change IRuns I Wedge.prog nativeTrial s _ _ at h
  apply Native.mono h
  have hTw := trial_word_width n k 0 0 0
  unfold nativeTrialCost
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (coinTail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k s arcs)
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int (@KoanaKPaths.Machine.Trial.signsOf n k ω)) coinTail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.nativeTrial s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins coinTail)
      KoanaKPaths.Machine.Norm.Sum
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (@KoanaKPaths.Main.trialNumerator n k (KoanaKPaths.Main.walkTensor n arcs k)
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
                (KoanaKPaths.Main.trialEquiv n k) ω))))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Norm.Sum)))
    (KoanaKPaths.Machine.Trial.nativeTrialCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)) := by
  exact @KoanaKPaths.Machine.Trial.nativeTrial_runs
