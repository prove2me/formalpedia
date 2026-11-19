-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.predecessorRow_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:22:16.441771+00:00
-- url     : https://prove2.me/submissions/d0dfcbbe-2792-4a4f-a528-ba09bced712b

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
import Theorems.Thm_KoanaKPaths_Machine_Arithmetic_Expr_width_le
import Theorems.Thm_KoanaKPaths_Machine_Native_invariant_loop
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_predecessorCell_runs
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
lemma iteT {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = true)
    (h : IRuns I iprog p s s1 c) : IRuns I iprog (.ite i f p q) s s1 (c+25) := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t+25,by omega,.iteT hf h⟩
lemma iteF {i : Fin S} {f : Cls → Bool} (hf : f (s.cl i) = false)
    (h : IRuns I iprog q s s1 c) : IRuns I iprog (.ite i f p q) s s1 (c+25) := by
  obtain ⟨t,ht,h⟩ := h
  exact ⟨t+25,by omega,.iteF hf h⟩



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



lemma zipWith_same_map {α β γ δ : Type} (L : List α) (f : α → β) (g : α → γ) (h : β → γ → δ) :
    List.zipWith h (L.map f) (L.map g) = L.map (fun x => h (f x) (g x)) := by
  induction L <;> simp_all

















lemma coefficientList_add {k : ℕ} (A B : Coordinates k) :
    coefficientList (A+B) = List.zipWith (·+·) (coefficientList A) (coefficientList B) := by
  simp only [coefficientList,zipWith_same_map]
  rfl

lemma coefficientList_smul {k : ℕ} (z : ℤ) (A : Coordinates k) :
    coefficientList (z • A) = (coefficientList A).map (z*·) := by
  simp [coefficientList,List.map_map,Function.comp_def]









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

lemma signsOf_get {n k : ℕ} (ω : Fin (trialBits n k)→Bool) (j : Fin (trialBits n k)) :
    (signsOf ω).getD j.val 1=sgn (ω j) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [signsOf,List.length_ofFn] using j.isLt)]
  simp only [signsOf,List.getElem_ofFn]







end KoanaKPaths.Machine.Trial

end

section

set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates

lemma natAbs_sum_le {α : Type} (s : Finset α) (f : α→ℤ) :
    (∑ x∈s, f x).natAbs ≤ ∑ x∈s, (f x).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma sgn_natAbs (b : Bool) : (sgn b).natAbs=1 := by cases b <;> norm_num [sgn]










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
namespace KoanaKPaths.Main



lemma matrixArrays_length {n k : ℕ} (F : Fin n→Fin k→List ℤ) :
    (matrixArrays F).length=n*k := by simp [matrixArrays]

lemma matrixArrays_get {n k : ℕ} (F : Fin n→Fin k→List ℤ) (v : Fin n) (a : Fin k) :
    (matrixArrays F)[(finProdFinEquiv (v,a)).val]'(by simp [matrixArrays]; exact (finProdFinEquiv (v,a)).isLt)=F v a := by
  unfold matrixArrays
  rw [List.getElem_ofFn]
  change F (finProdFinEquiv.symm (finProdFinEquiv (v,a))).1
    (finProdFinEquiv.symm (finProdFinEquiv (v,a))).2=F v a
  rw [Equiv.symm_apply_apply]



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



lemma predecessorTerm_natAbs {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (q : Fin n × Fin k) (S : Finset (Fin k)) :
    (predecessorTerm arcs σ R p i a v q S).natAbs≤(layerRadius n k k)^p := by
  unfold predecessorTerm
  split_ifs
  · simpa only [Pi.smul_apply,smul_eq_mul,Int.natAbs_mul,sgn_natAbs,one_mul] using
      graphLayer_natAbs arcs σ R p q.1 q.2 S
  · simp

lemma predecessorSum_natAbs {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (Q : Finset (Fin n × Fin k)) (S : Finset (Fin k)) :
    ((∑ q∈Q, predecessorTerm arcs σ R p i a v q) S).natAbs≤ n*k*(layerRadius n k k)^p := by
  classical
  simp only [Finset.sum_apply]
  calc
    _ ≤ ∑ q∈Q, (predecessorTerm arcs σ R p i a v q S).natAbs := natAbs_sum_le Q _
    _ ≤ ∑ _q∈Q, (layerRadius n k k)^p := Finset.sum_le_sum
      (fun q _ => predecessorTerm_natAbs arcs σ R p i a v q S)
    _ = Q.card*(layerRadius n k k)^p := by simp
    _ ≤ n*k*(layerRadius n k k)^p := Nat.mul_le_mul_right _ (by
      simpa only [Fintype.card_prod,Fintype.card_fin] using Q.card_le_univ)

lemma predecessorSum_width {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (Q : Finset (Fin n × Fin k)) (S : Finset (Fin k)) :
    NLogN.zsz ((∑ q∈Q, predecessorTerm arcs σ R p i a v q) S)≤
      n+k+(n+k+k+3)*p+1 := by
  have hr := Nat.pow_le_pow_left (layerRadius_le_exp n k k) p
  rw [← pow_mul] at hr
  have hn : n≤2^n := Nat.le_of_lt Nat.lt_two_pow_self
  have hk : k≤2^k := Nat.le_of_lt Nat.lt_two_pow_self
  have hnk := Nat.mul_le_mul hn hk
  rw [← pow_add] at hnk
  have h := (predecessorSum_natAbs arcs σ R p i a v Q S).trans (Nat.mul_le_mul hnk hr)
  rw [← pow_add] at h
  apply (Machine.Wedge.zsz_le_iff _ _).mpr
  rw [pow_succ]
  have hp : 0<2^(n+k+(n+k+k+3)*p) := by positivity
  omega

lemma predecessorSum_width_polynomial {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (hp : p≤ k) (i : Fin (k-1)) (a : Fin k) (v : Fin n)
    (Q : Finset (Fin n × Fin k)) (S : Finset (Fin k)) :
    NLogN.zsz ((∑ q∈Q, predecessorTerm arcs σ R p i a v q) S)≤100*(1+n+k)^2 := by
  have h := predecessorSum_width arcs σ R p i a v Q S
  have hmul := Nat.mul_le_mul_left (n+k+k+3) hp
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k),Nat.zero_le (k*k)]

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace KoanaKPaths.Main
open ExteriorCoordinates





lemma predSet_succ {n k : ℕ} (u : Fin n) (b : Fin k) :
    predSet n k u.val (b.val+1)=insert (u,b) (predSet n k u.val b.val) := by
  ext q
  simp only [predSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  have he : q=(u,b) ↔ q.1.val=u.val ∧ q.2.val=b.val := by
    constructor
    · intro h; subst q; exact ⟨rfl,rfl⟩
    · rintro ⟨h1,h2⟩; exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  rw [he]
  omega
lemma predSet_notMem {n k : ℕ} (u : Fin n) (b : Fin k) : (u,b)∉predSet n k u.val b.val := by
  simp [predSet]






lemma predSum_succ {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (i : Fin (k-1)) (a : Fin k) (v u : Fin n) (b : Fin k) :
    predSum arcs σ R p i a v u.val (b.val+1)=
      predecessorTerm arcs σ R p i a v (u,b)+predSum arcs σ R p i a v u.val b.val := by
  simp only [predSum,predSet_succ,Finset.sum_insert (predSet_notMem u b)]
lemma predSum_width {n k : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k k) (p : ℕ) (hp : p≤ k) (i : Fin (k-1)) (a : Fin k) (v : Fin n) (u b : ℕ) :
    ∀ x∈coefficientList (predSum arcs σ R p i a v u b), NLogN.zsz x≤100*(1+n+k)^2 := by
  intro x hx
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hx
  exact predecessorSum_width_polynomial arcs σ R p hp i a v _ S

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates

lemma pred_word_width {n k : ℕ} (u : Fin n) (b : Fin k) :
    predExpr.width (predValues k u.val b.val)≤ wordWidth n k := by
  have hk := Controls.zsz_nat_le k
  have hu := Controls.zsz_nat_le u.val
  have hb := Controls.zsz_nat_le b.val
  have hatom : predExpr.atomWidth (predValues k u.val b.val)≤1+n+k := by
    change max (max (zsz (u.val : ℤ)) (zsz (k : ℤ))) (zsz (b.val : ℤ))≤1+n+k
    omega
  have h := predExpr.width_le (predValues k u.val b.val) (1+n+k) hatom
  have hs : predExpr.size=5 := rfl
  rw [hs] at h
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]

lemma later_word_width {n k : ℕ} (v : Fin n) (a b : Fin k) (i : Fin (k-1)) :
    laterExpr.width (laterValues n k v.val a.val i.val b.val)≤ wordWidth n k := by
  have hn := Controls.zsz_nat_le n
  have hk := Controls.zsz_nat_le k
  have hv := Controls.zsz_nat_le v.val
  have ha := Controls.zsz_nat_le a.val
  have hb := Controls.zsz_nat_le b.val
  have hi := Controls.zsz_nat_le i.val
  have hatom : laterExpr.atomWidth (laterValues n k v.val a.val i.val b.val)≤1+n+k := by
    change max (max (zsz (n : ℤ)) (zsz (k : ℤ)))
      (max (max (zsz (k : ℤ)) (zsz (n : ℤ)))
        (max (max (zsz (i.val : ℤ)) (max (zsz (k : ℤ)) (max (zsz (k : ℤ)) (zsz (n : ℤ)))))
          (max (max (zsz (a.val : ℤ)) (max (zsz (k : ℤ)) (zsz (n : ℤ))))
            (max (max (zsz (b.val : ℤ)) (zsz (n : ℤ))) (zsz (v.val : ℤ))))))≤1+n+k
    omega
  have h := laterExpr.width_le (laterValues n k v.val a.val i.val b.val) (1+n+k) hatom
  have hs : laterExpr.size=27 := rfl
  rw [hs] at h
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]

lemma signsOf_later {n k : ℕ} (ω : Fin (trialBits n k)→Bool)
    (i : Fin (k-1)) (a b : Fin k) (v : Fin n) :
    (signsOf ω)[laterIndex n k v.val a.val i.val b.val]'(by
      rw [signsOf_length]
      simpa only [trialIndex_later,laterIndex] using
        (trialIndexEquiv n k (.inr (.inr (i,a,(b,v))))).isLt)=
      sgn ((trialEquiv n k ω).2.2 i a (b,v)) := by
  have h := signsOf_get ω (trialIndexEquiv n k (.inr (.inr (i,a,(b,v)))))
  rw [trialIndex_later] at h
  rw [List.getD_eq_getElem _ _ (by
    rw [signsOf_length]
    simpa only [trialIndex_later] using
      (trialIndexEquiv n k (.inr (.inr (i,a,(b,v))))).isLt)] at h
  exact h

lemma predecessorCell_decoded (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n))
    (p : ℕ) (hp : p≤ k) (i : Fin (k-1)) (a b : Fin k) (v u : Fin n)
    (C : Coordinates k) (cw : ∀ x∈coefficientList C, zsz x≤ wordWidth n k)
    (vt atail it ut bt accTail : List Item)
    (hCore : Core s ω arcs p)
    (hV : s.G Vertex=.int (v.val : ℤ)::vt) (hA : s.G StateIndex=.int (a.val : ℤ)::atail)
    (hI : s.G LayerIndex=.int (i.val : ℤ)::it) (hU : s.G Predecessor=.int (u.val : ℤ)::ut)
    (hB : s.G PreviousState=.int (b.val : ℤ)::bt)
    (hAcc : s.G Accumulate.Acc=(coefficientList C).map Item.int ++ .mark::accTail) :
    IRuns I Wedge.prog predecessorCell s
      ((s.upd PreviousState (.int ((b.val+1 : ℕ) : ℤ)::bt)).upd Accumulate.Acc
        ((coefficientList (sgn ((trialEquiv n k ω).2.2 i a (b,v)) •
          graphLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p u b+C)).map Item.int ++ .mark::accTail))
      (predecessorCellCost (n*k) (trialBits n k) k (wordWidth n k)) := by
  let arrays := matrixArrays (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p)
  have hj : u.val*k+b.val< arrays.length := by
    rw [matrixArrays_length]
    have hh := (finProdFinEquiv (u,b)).isLt
    change b.val+k*u.val< n*k at hh
    nlinarith
  have hzj : laterIndex n k v.val a.val i.val b.val<(signsOf ω).length := by
    rw [signsOf_length]
    simpa only [trialIndex_later,laterIndex] using
      (trialIndexEquiv n k (.inr (.inr (i,a,(b,v))))).isLt
  have hbnd := denseMatrix_word_bounds arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p (by omega)
  have h := predecessorCell_runs I s arrays (signsOf ω) (coefficientList C)
    n k v.val a.val i.val u.val b.val (wordWidth n k) [] [] vt atail it ut bt [] [] [] accTail
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 53 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 54 (by decide)) hV hA hI hU hB
    (by simpa [coreStack,NS,Wedge.NS,signsOf_length] using hCore.at 63 (by decide))
    (by simpa [arrays,coreStack,NS,Wedge.NS] using hCore.at 14 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 24 (by decide)) hAcc
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 40 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 41 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 17 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 18 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 19 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 27 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 28 (by decide))
    (by simpa [coreStack,NS,Wedge.NS] using hCore.at 29 (by decide))
    (signsOf_values ω) (wordWidth_pos n k) (pred_word_width u b) (later_word_width v a b i)
    (by rw [signsOf_length]; exact trial_word_width n k 0 0 0)
    (row_word_width n k b.val (by omega))
    (by intro xs hx; obtain ⟨j,hj⟩ := List.mem_ofFn.mp hx; rw [←hj]; exact denseLayer_length _ _ _ _ _ _)
    hbnd.2 (coefficientList_length C) cw hj hzj
  have harr : arrays[u.val*k+b.val]'hj=coefficientList
      (graphLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p u b) := by
    have hh := matrixArrays_get (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p) u b
    have hidx : (finProdFinEquiv (u,b)).val=u.val*k+b.val := by change b.val+k*u.val=_; ring
    simpa only [hidx] using hh.trans (denseLayer_correct _ _ _ _ _ _)
  rw [harr,signsOf_later,←coefficientList_smul,←coefficientList_add,signsOf_length,matrixArrays_length] at h
  exact h

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic Square KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates

attribute [local simp] Found PreviousState Accumulate.Acc



lemma predecessorStep_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n))
    (p : ℕ) (hp : p≤ k) (i : Fin (k-1)) (a b : Fin k) (v u : Fin n)
    (vt atail it ut bt accTail ft : List Item)
    (hCore : Core s ω arcs p)
    (hV : s.G Vertex=.int (v.val : ℤ)::vt) (hA : s.G StateIndex=.int (a.val : ℤ)::atail)
    (hI : s.G LayerIndex=.int (i.val : ℤ)::it) (hU : s.G Predecessor=.int (u.val : ℤ)::ut)
    (hB : s.G PreviousState=.int (b.val : ℤ)::bt)
    (hF : s.G Found=.int ((decide ((u,v)∈arcs.toFinset)).toNat : ℤ)::ft)
    (hAcc : s.G Accumulate.Acc=(coefficientList
      (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val b.val)).map Item.int ++ .mark::accTail) :
    IRuns I Wedge.prog predecessorStep s
      ((s.upd PreviousState (.int ((b.val+1 : ℕ) : ℤ)::bt)).upd Accumulate.Acc
        ((coefficientList (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val (b.val+1))).map Item.int ++ .mark::accTail))
      (predecessorCellCost (n*k) (trialBits n k) k (wordWidth n k)+25) := by
  have hsum := predSum_succ arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u b
  by_cases harc : (u,v)∈arcs.toFinset
  · have hc := predecessorCell_decoded I s ω arcs p hp i a b v u _
      (predSum_width arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p hp i a v u.val b.val)
      vt atail it ut bt accTail hCore hV hA hI hU hB hAcc
    have hs : predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val (b.val+1)=
        sgn ((trialEquiv n k ω).2.2 i a (b,v)) •
          graphLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p u b+
            predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val b.val := by
      simpa [predecessorTerm,harc] using hsum
    rw [←hs] at hc
    exact Native.iteT (by simp [IState.cl,hF,harc,cls]) hc
  · have hs : predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val (b.val+1)=
        predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val b.val := by
      simpa [predecessorTerm,harc] using hsum
    have hc := liftClosed_runs I Wedge.prog (increment_runs I PreviousState (by decide) s b.val
      (wordWidth n k) bt hB (wordWidth_pos n k) (row_word_width n k b.val (by omega)))
    have he : (s.upd PreviousState (.int ((b.val+1 : ℕ) : ℤ)::bt)).upd Accumulate.Acc
        ((coefficientList (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val (b.val+1))).map Item.int ++ .mark::accTail)=
        s.upd PreviousState (.int ((b.val+1 : ℕ) : ℤ)::bt) := by
      rw [hs,←hAcc]
      simp [IState.upd]
    rw [he]
    apply Native.mono (Native.iteF (p := predecessorCell) (by simp [IState.cl,hF,harc,cls]) hc)
    unfold predecessorCellCost
    omega

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main KoanaKPaths.ExteriorCoordinates

attribute [local simp] PreviousCounter PreviousState Accumulate.Acc Vertex StateIndex LayerIndex Predecessor Found





lemma predecessorRow_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n))
    (p : ℕ) (hp : p≤ k) (i : Fin (k-1)) (a : Fin k) (v u : Fin n)
    (vt atail it ut bt accTail ft : List Item)
    (hCore : Core s ω arcs p)
    (hV : s.G Vertex=.int (v.val : ℤ)::vt) (hA : s.G StateIndex=.int (a.val : ℤ)::atail)
    (hI : s.G LayerIndex=.int (i.val : ℤ)::it) (hU : s.G Predecessor=.int (u.val : ℤ)::ut)
    (hB : s.G PreviousState=.int 0::bt) (hCount : s.G PreviousCounter=List.replicate k .mark)
    (hF : s.G Found=.int ((decide ((u,v)∈arcs.toFinset)).toNat : ℤ)::ft)
    (hAcc : s.G Accumulate.Acc=(coefficientList
      (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val 0)).map Item.int ++ .mark::accTail) :
    IRuns I Wedge.prog predecessorRow s
      (predecessorRowState s ω arcs p i a v u k bt accTail)
      ((predecessorCellCost (n*k) (trialBits n k) k (wordWidth n k)+56)*k+30) := by
  let C := predecessorCellCost (n*k) (trialBits n k) k (wordWidth n k)
  let Inv : ℕ→IState NS→Prop := fun b st => st=predecessorRowState s ω arcs p i a v u b bt accTail
  have hcounter : ∀ b≤ k, ∀ st, Inv b st → st.G PreviousCounter=List.replicate (k-b) .mark ++ [] := by
    intro b hb st hs; rw [hs]; simp [predecessorRowState]
  have hstep : ∀ b< k, ∀ st, Inv b st → ∃ st',
      IRuns I Wedge.prog (.seq (.op (.unmark PreviousCounter)) predecessorStep) st st' (C+26) ∧ Inv (b+1) st' := by
    intro b hb st hs; rw [hs]
    let cur := predecessorRowState s ω arcs p i a v u b bt accTail
    let popped := cur.upd PreviousCounter (List.replicate (k-(b+1)) .mark)
    let bi : Fin k := ⟨b,hb⟩
    let next := (popped.upd PreviousState (.int ((b+1 : ℕ) : ℤ)::bt)).upd Accumulate.Acc
      ((coefficientList (predSum arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p i a v u.val (b+1))).map Item.int ++ .mark::accTail)
    have hlen : k-b=(k-(b+1))+1 := by omega
    have h0 : IExec I Wedge.prog (.op (.unmark PreviousCounter)) cur popped 1 :=
      .op (.unmark (by simp [cur,predecessorRowState,hlen,List.replicate_succ]))
    have hCP : Core popped ω arcs p :=
      (((hCore.upd PreviousCounter (by decide) _).upd PreviousState (by decide) _).upd Accumulate.Acc (by decide) _).upd PreviousCounter (by decide) _
    have h1 : IRuns I Wedge.prog predecessorStep popped next (C+25) := by
      exact predecessorStep_runs I popped ω arcs p hp i a bi v u vt atail it ut bt accTail ft hCP
        (by simp [popped,cur,predecessorRowState,hV]) (by simp [popped,cur,predecessorRowState,hA])
        (by simp [popped,cur,predecessorRowState,hI]) (by simp [popped,cur,predecessorRowState,hU])
        (by simp [popped,cur,predecessorRowState,bi]) (by simp [popped,cur,predecessorRowState,hF])
        (by simp [popped,cur,predecessorRowState,bi])
    have hpost : next=predecessorRowState s ω arcs p i a v u (b+1) bt accTail := by
      apply itemState_ext
      · intro r
        by_cases hC : r=PreviousCounter
        · subst r; simp [next,popped,cur,predecessorRowState]
        by_cases hB : r=PreviousState
        · subst r; simp [next,popped,cur,predecessorRowState]
        by_cases hA : r=Accumulate.Acc
        · subst r; simp [next,popped,cur,predecessorRowState]
        simp [next,popped,cur,predecessorRowState,IState.upd,Function.update_apply,hC,hB,hA]
      · rfl
      · rfl
    exact ⟨next,Native.mono (Native.seq (Native.of_exec h0) h1) (by omega),hpost⟩
  have hinit : Inv 0 s := by
    unfold Inv predecessorRowState
    simp only [Nat.sub_zero,Nat.cast_zero]
    rw [←hCount,←hB,←hAcc]
    simp
  obtain ⟨st,hrun,hend⟩ := Native.invariant_loop I Wedge.prog PreviousCounter
    (.seq (.op (.unmark PreviousCounter)) predecessorStep) Inv k (C+26) [] (by simp [cls]) hcounter hstep s hinit
  rw [hend] at hrun
  simpa only [predecessorRow,C,Nat.add_assoc,show (26+30 : ℕ)=56 from rfl] using hrun

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
  (a : Fin k) (v u : Fin n) (vt atail it ut bt accTail ft : List.{0} NLogN.Item)
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
  (hB :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousState)
      (@List.cons.{0} NLogN.Item (NLogN.Item.int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) bt))
  (hCount :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.PreviousCounter)
      (@List.replicate.{0} NLogN.Item k NLogN.Item.mark))
  (hF :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Found)
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@Nat.cast.{0} Int instNatCastInt
            (Bool.toNat
              (@Decidable.decide
                (@Membership.mem.{0, 0} (Prod.{0, 0} (Fin n) (Fin n)) (Finset.{0} (Prod.{0, 0} (Fin n) (Fin n)))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Prod.{0, 0} (Fin n) (Fin n)))
                    (Prod.{0, 0} (Fin n) (Fin n)) (@Finset.instSetLike.{0} (Prod.{0, 0} (Fin n) (Fin n))))
                  (@List.toFinset.{0} (Prod.{0, 0} (Fin n) (Fin n))
                    (fun (a b : Prod.{0, 0} (Fin n) (Fin n)) =>
                      @instDecidableEqProd.{0, 0} (Fin n) (Fin n) (instDecidableEqFin n) (instDecidableEqFin n) a b)
                    arcs)
                  (@Prod.mk.{0, 0} (Fin n) (Fin n) u v))
                (@Finset.decidableMem.{0} (Prod.{0, 0} (Fin n) (Fin n))
                  (fun (a b : Prod.{0, 0} (Fin n) (Fin n)) =>
                    @instDecidableEqProd.{0, 0} (Fin n) (Fin n) (instDecidableEqFin n) (instDecidableEqFin n) a b)
                  (@Prod.mk.{0, 0} (Fin n) (Fin n) u v)
                  (@List.toFinset.{0} (Prod.{0, 0} (Fin n) (Fin n))
                    (fun (a b : Prod.{0, 0} (Fin n) (Fin n)) =>
                      @instDecidableEqProd.{0, 0} (Fin n) (Fin n) (instDecidableEqFin n) (instDecidableEqFin n) a b)
                    arcs))))))
        ft))
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
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.predecessorRow s
    (@KoanaKPaths.Machine.Trial.predecessorRowState n k s ω arcs p i a v u k bt accTail)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (KoanaKPaths.Machine.Trial.predecessorCellCost
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n k) (KoanaKPaths.Main.trialBits n k) k
            (KoanaKPaths.Machine.Trial.wordWidth n k))
          (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        k)
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) := by
  exact @KoanaKPaths.Machine.Trial.predecessorRow_runs
