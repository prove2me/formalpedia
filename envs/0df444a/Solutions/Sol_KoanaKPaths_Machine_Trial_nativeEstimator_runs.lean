-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.nativeEstimator_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:48:47.210375+00:00
-- url     : https://prove2.me/submissions/aadfe631-2fa6-420d-ac11-151699b565f1

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_MedianOfMeans
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
import Theorems.Thm_KoanaKPaths_Machine_Median_program_runs
import Theorems.Thm_KoanaKPaths_Machine_Native_invariant_loop
import Theorems.Thm_KoanaKPaths_Machine_Square_increment_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_groupDriver_runs
import Theorems.Thm_KoanaKPaths_Machine_copyMoveMarks_exec
import Theorems.Thm_KoanaKPaths_Machine_moveMarks_exec
import Theorems.Thm_KoanaKPaths_Main_denseLayer_correct
import Theorems.Thm_KoanaKPaths_Main_graphNorm_width
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











lemma zipWith_same_map {α β γ δ : Type} (L : List α) (f : α → β) (g : α → γ) (h : β → γ → δ) :
    List.zipWith h (L.map f) (L.map g) = L.map (fun x => h (f x) (g x)) := by
  induction L <;> simp_all













lemma subsetOrder_last (k : ℕ) : (subsetOrder k).getLast? = some Finset.univ := by
  induction k with
  | zero => simp [subsetOrder]
  | succ k ih =>
    have hu : upperSet (Finset.univ : Finset (Fin k)) = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro r
      refine Fin.lastCases ?_ (fun x => ?_) r
      · simp [upperSet]
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_map.mpr ⟨x,Finset.mem_univ x,rfl⟩
    have hn : (subsetOrder k).map upperSet ≠ [] := by
      have hl := subsetOrder_length k
      intro he
      have := congrArg List.length he
      simp only [List.length_map,List.length_nil] at this
      have hp : 0 < 2^k := by positivity
      omega
    rw [subsetOrder,List.getLast?_append_of_ne_nil _ hn,List.getLast?_map,ih]
    simp [hu]

lemma coefficientList_last {k : ℕ} (A : Coordinates k) :
    (coefficientList A).getLast? = some (A Finset.univ) := by
  simp [coefficientList,List.getLast?_map,subsetOrder_last]

lemma coefficientList_add {k : ℕ} (A B : Coordinates k) :
    coefficientList (A+B) = List.zipWith (·+·) (coefficientList A) (coefficientList B) := by
  simp only [coefficientList,zipWith_same_map]
  rfl



lemma coefficientList_zero (k : ℕ) : coefficientList (0 : Coordinates k) = List.replicate (2^k) 0 := by
  change (subsetOrder k).map (fun _ => (0 : ℤ)) = _
  simp [List.map_const,subsetOrder_length]







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

lemma arrayFold_coeff {k : ℕ} (as : List (Coordinates k)) (a : Coordinates k) :
    (as.map coefficientList).foldl (List.zipWith (·+·)) (coefficientList a) =
      coefficientList (a+as.sum) := by
  induction as generalizing a with
  | nil => simp
  | cons b as ih =>
    simp only [List.map_cons,List.foldl_cons,List.sum_cons]
    rw [← coefficientList_add,ih]
    congr 1
    exact add_assoc _ _ _

lemma arraySum_coeff {k : ℕ} (as : List (Coordinates k)) :
    arraySum k (as.map coefficientList)=coefficientList as.sum := by
  unfold arraySum
  rw [← coefficientList_zero,arrayFold_coeff,zero_add]



lemma sum_finRange {A : Type} [AddCommMonoid A] (n : ℕ) (f : Fin n→A) :
    ((List.finRange n).map f).sum=∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n),List.toFinset_finRange]








lemma denseOutput_correct {n k ℓ : ℕ} (arcs : List (Fin n × Fin n)) (σ : Labels n k)
    (R : SketchSigns n k ℓ) (a : Fin ℓ) :
    denseOutput arcs σ R a=coefficientList (graphOutput arcs σ R a) := by
  unfold denseOutput
  simp only [denseLayer_correct]
  have hm : (List.finRange n).map (fun v => coefficientList (graphLayer arcs σ R k v a)) =
      ((List.finRange n).map (fun v => graphLayer arcs σ R k v a)).map coefficientList := by
    simp only [List.map_map,Function.comp_def]
  rw [hm,arraySum_coeff,sum_finRange]
  rfl

lemma denseTrial_correct {n k ℓ : ℕ} (hk : 1≤k) (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    denseTrial arcs σ R=(sketchFrobSq (walkTensor n arcs k) σ R k).toNat := by
  unfold denseTrial
  simp only [denseOutput_correct,coefficientList_last,Option.getD_some]
  rw [sum_finRange,graph_dp_sketch hk]

lemma denseTrial_eq_trialNumerator {n k : ℕ} (hk : 1≤k) (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k k) :
    denseTrial arcs σ R=trialNumerator (walkTensor n arcs k) (σ,R) :=
  denseTrial_correct hk arcs σ R

end KoanaKPaths.Main

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

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main





lemma graphNorm_nonneg {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    0≤ ∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2 :=
  Finset.sum_nonneg (fun a _ => sq_nonneg _)



lemma denseTrial_cast {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    (denseTrial arcs σ R : ℤ)=∑ a : Fin ℓ, (graphOutput arcs σ R a Finset.univ)^2 := by
  unfold denseTrial
  simp only [denseOutput_correct,ExteriorCoordinates.coefficientList_last,Option.getD_some]
  rw [sum_finRange]
  exact Int.toNat_of_nonneg (graphNorm_nonneg arcs σ R)

lemma denseTrial_width {n k ℓ : ℕ} (arcs : List (Fin n × Fin n))
    (σ : Labels n k) (R : SketchSigns n k ℓ) :
    zsz (denseTrial arcs σ R : ℤ)≤ trialWidth n k ℓ := by
  rw [denseTrial_cast]
  exact graphNorm_width arcs σ R

lemma trialWidth_polynomial (n k : ℕ) : trialWidth n k k≤20*(1+n+k)^2 := by
  unfold trialWidth outputExponent
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k)]

end KoanaKPaths.Main

namespace KoanaKPaths.Machine.Norm




end KoanaKPaths.Machine.Norm

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Main



lemma groupTrials_le_exp (k a : ℕ) : groupTrials k a≤2^(10+3*k+2*a) := by
  have hk : k≤2^k := Nat.le_of_lt Nat.lt_two_pow_self
  have hk3 := Nat.pow_le_pow_left hk 3
  calc
    groupTrials k a = 2^10*k^3*4^a := by unfold groupTrials; norm_num
    _ ≤ 2^10*(2^k)^3*4^a := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk3)
    _ = _ := by
      rw [← pow_mul,show 4=2^2 from rfl,← pow_mul,← pow_add,← pow_add]
      congr 1
      omega

lemma groupSum_le_exp {n k a : ℕ} (arcs : List (Fin n × Fin n))
    (w : Fin (groupTrials k a)→Labels n k × SketchSigns n k k) :
    (∑ j, denseTrial arcs (w j).1 (w j).2)≤
      2^(10+3*k+2*a+trialWidth n k k) := by
  have hf : ∀ j, denseTrial arcs (w j).1 (w j).2≤2^(trialWidth n k k) := by
    intro j
    have h := (Machine.Wedge.zsz_le_iff _ _).mp (denseTrial_width arcs (w j).1 (w j).2)
    simp only [Int.natAbs_natCast] at h
    omega
  calc
    _ ≤ ∑ _j : Fin (groupTrials k a), 2^(trialWidth n k k) := Finset.sum_le_sum (fun j _ => hf j)
    _ = groupTrials k a*2^(trialWidth n k k) := by simp
    _ ≤ 2^(10+3*k+2*a)*2^(trialWidth n k k) := Nat.mul_le_mul_right _ (groupTrials_le_exp k a)
    _ = _ := (pow_add _ _ _).symm

lemma groupSum_lt_medianWidth {n k a : ℕ} (arcs : List (Fin n × Fin n))
    (w : Fin (groupTrials k a)→Labels n k × SketchSigns n k k) :
    (∑ j, denseTrial arcs (w j).1 (w j).2)<2^(medianWidth n k a) := by
  have hs := groupSum_le_exp arcs w
  have hw := trialWidth_polynomial n k
  have he : 10+3*k+2*a+trialWidth n k k< medianWidth n k a := by
    unfold medianWidth
    nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k),Nat.zero_le (k*k)]
  exact lt_of_le_of_lt hs (Nat.pow_lt_pow_right (by decide) he)







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
open NLogN
namespace KoanaKPaths.Machine.Trial
open Arithmetic KoanaKPaths.Main



lemma wordWidth_pos (n k : ℕ) : 1≤ wordWidth n k := by
  unfold wordWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]











end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main







lemma Ready.at {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)}
    (h : Ready (k := k) s arcs) (j : Fin NS) (hj : j∈readyRegisters) : s.G j=readyStack n k arcs j := h j hj





end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main

lemma numerators_ofFn {n k m : ℕ} (arcs : List (Fin n × Fin n))
    (os : Fin m→Fin (trialBits n k)→Bool) :
    numerators arcs (List.ofFn os)=List.ofFn
      (fun j => (trialNumerator (walkTensor n arcs k) (trialEquiv n k (os j)) : ℤ)) := by
  simp [numerators,List.map_ofFn,Function.comp_def]

lemma numerators_sum_ofFn {n k m : ℕ} (arcs : List (Fin n × Fin n))
    (os : Fin m→Fin (trialBits n k)→Bool) :
    (numerators arcs (List.ofFn os)).sum=
      ((∑ j, trialNumerator (walkTensor n arcs k) (trialEquiv n k (os j)) : ℕ) : ℤ) := by
  rw [numerators_ofFn,List.sum_ofFn]
  simp only [Nat.cast_sum]

lemma groupSums_ofFn {n k q m : ℕ} (arcs : List (Fin n × Fin n))
    (os : Fin q→Fin m→Fin (trialBits n k)→Bool) :
    groupSums arcs (List.ofFn (fun i => List.ofFn (os i)))=
      List.ofFn (fun i => ((∑ j, trialNumerator (walkTensor n arcs k) (trialEquiv n k (os i j)) : ℕ) : ℤ)) := by
  simp only [groupSums,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact numerators_sum_ofFn arcs (os i)

lemma numeratorGroup_lt {n k a : ℕ} (arcs : List (Fin n × Fin n)) (hk : 1≤ k)
    (os : Fin (groupTrials k a)→Fin (trialBits n k)→Bool) :
    (∑ j, trialNumerator (walkTensor n arcs k) (trialEquiv n k (os j)))<2^(medianWidth n k a) := by
  have h := groupSum_lt_medianWidth arcs (fun j => trialEquiv n k (os j))
  simpa only [denseTrial_eq_trialNumerator hk] using h

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main






lemma EstimatorReady.at {n : ℕ} {s : IState NS} {k a b : ℕ} {arcs : List (Fin n × Fin n)}
    (h : EstimatorReady s k a b arcs) (j : Fin NS) (hj : j∈estimatorRegisters) :
    s.G j=estimatorStack n k a b arcs.length j := h.2 j hj

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] GroupTemplate GroupCounter TrialTemplate TrialCounter GroupCopyTmp OuterCopyTmp Coins Balanced.Records Balanced.Restore
  Median.Records Median.Template Median.CopyTmp Median.Output Median.Fuel Median.Mid Median.Count Median.Threshold Median.Saved Median.Flag





lemma nativeNumerator_runs (I : List Sym) (s : IState NS) {n k a b : ℕ}
    (arcs : List (Fin n × Fin n))
    (os : Fin (2*b+1)→Fin (groupTrials k a)→Fin (trialBits n k)→Bool)
    (tail : List Item) (hk : 1≤ k) (hr : EstimatorReady s k a b arcs)
    (hCoins : s.G Coins=groupsStream (List.ofFn (fun i => List.ofFn (os i)))++tail) :
    IRuns I Wedge.prog nativeNumerator s
      ((((s.upd Coins tail).upd Balanced.Records
        ((List.ofFn (fun i => ((∑ j, trialNumerator (walkTensor n arcs k) (trialEquiv n k (os i j)) : ℕ) : ℤ))).map Item.int ++ .mark::s.G Balanced.Records))).upd Median.Output
          [.int ((KoanaKPaths.Sampling.median b (fun i => ∑ j,
            trialNumerator (walkTensor n arcs k) (trialEquiv n k (os i j))) : ℕ) : ℤ)])
      (numeratorCost n k a b arcs.length) := by
  let oss := List.ofFn (fun i => List.ofFn (os i))
  let f : Fin (2*b+1)→ℕ := fun i => ∑ j, trialNumerator (walkTensor n arcs k) (trialEquiv n k (os i j))
  let s1 := (s.upd Coins tail).upd Balanced.Records
    ((List.ofFn (fun i => (f i : ℤ))).map Item.int ++ .mark::s.G Balanced.Records)
  have h0 : IRuns I Wedge.prog groupDriver s s1
      (groupDriverCost n k arcs.length (groupTrials k a) (2*b+1)) := by
    have h := groupDriver_runs I s arcs oss (groupTrials k a) tail hk hr.1
      (by intro xs hxs; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs; simp)
      (by simpa [oss,estimatorStack,NS,Wedge.NS] using hr.at 43 (by decide))
      (by simpa [estimatorStack,NS,Wedge.NS] using hr.at 100 (by decide))
      (by simpa [estimatorStack,NS,Wedge.NS] using hr.at 42 (by decide))
      (by simpa [estimatorStack,NS,Wedge.NS] using hr.at 101 (by decide))
      (by simpa [estimatorStack,NS,Wedge.NS] using hr.at 61 (by decide))
      (by simpa [estimatorStack,NS,Wedge.NS] using hr.at 62 (by decide))
      (by simpa [estimatorStack,NS,Wedge.NS] using hr.at 105 (by decide)) hCoins
    simpa only [oss,groupSums_ofFn,List.length_ofFn] using h
  have h1 : IRuns I Wedge.prog (liftClosed Median.program) s1
      (s1.upd Median.Output [.int ((KoanaKPaths.Sampling.median b f : ℕ) : ℤ)])
      (30000*(medianWidth n k a+1)^2*(2*b+2)) := by
    have h := liftClosed_runs I Wedge.prog (Median.program_runs I s1 b (medianWidth n k a) f
      (s.G Balanced.Records) (by have hh := wordWidth_pos n k; unfold medianWidth wordWidth at *; omega)
      (by simpa only [s1,Median.Records,Balanced.Records,upd_G_self,List.ofFn_eq_map])
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 124 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 123 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 125 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 110 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 114 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 115 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 117 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 119 (by decide))
      (fun i => numeratorGroup_lt arcs hk (os i)))
    have ho : s1.G Median.Output=[] := by
      simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 126 (by decide)
    simpa only [ho] using h
  exact Native.seq h0 h1

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Main

lemma trialDenominator_le_exp (k : ℕ) : trialDenominator k≤2^(2*k*k) := by
  have hk : k≤2^k := Nat.le_of_lt Nat.lt_two_pow_self
  have hpow := Nat.pow_le_pow_left hk k
  rw [← pow_mul] at hpow
  calc
    trialDenominator k = k^k*k.factorial := rfl
    _ ≤ k^k*k^k := Nat.mul_le_mul_left _ (Nat.factorial_le_pow k)
    _ ≤ 2^(k*k)*2^(k*k) := Nat.mul_le_mul hpow hpow
    _ = _ := by rw [← pow_add]; congr 1; ring

lemma estimateDenominator_le_exp (k a : ℕ) :
    groupTrials k a*trialDenominator k≤2^(10+3*k+2*a+2*k*k) := by
  calc
    _ ≤ 2^(10+3*k+2*a)*2^(2*k*k) :=
      Nat.mul_le_mul (groupTrials_le_exp k a) (trialDenominator_le_exp k)
    _ = _ := (pow_add _ _ _).symm

lemma estimateDenominator_width (n k a : ℕ) :
    zsz ((groupTrials k a*trialDenominator k : ℕ) : ℤ)≤ medianWidth n k a := by
  apply (Machine.Wedge.zsz_le_iff _ _).mpr
  simp only [Int.natAbs_natCast]
  have h := estimateDenominator_le_exp k a
  have he : 10+3*k+2*a+2*k*k< medianWidth n k a := by
    unfold medianWidth
    nlinarith [Nat.zero_le (n*n),Nat.zero_le (n*k),Nat.zero_le (k*k)]
  exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by decide) he)



end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Main


lemma partialDenominator_zero (k a : ℕ) : partialDenominator k a 0=groupTrials k a := by simp [partialDenominator]
lemma partialDenominator_succ (k a i : ℕ) :
    partialDenominator k a (i+1)=partialDenominator k a i*k*(i+1) := by
  simp only [partialDenominator,pow_succ,Nat.factorial_succ]
  ring
lemma partialDenominator_full (k a : ℕ) : partialDenominator k a k=groupTrials k a*trialDenominator k := by
  unfold partialDenominator trialDenominator
  ring
lemma partialDenominator_le {k a i : ℕ} (hk : 1≤ k) (hi : i≤ k) :
    partialDenominator k a i≤ groupTrials k a*trialDenominator k := by
  have hp : k^i≤ k^k := Nat.pow_le_pow_right hk hi
  have hf : i.factorial≤ k.factorial := Nat.factorial_le hi
  simpa [partialDenominator,trialDenominator,Nat.mul_assoc] using
    Nat.mul_le_mul (Nat.mul_le_mul_left (groupTrials k a) hp) hf
lemma partialDenominator_width {n k a i : ℕ} (hk : 1≤ k) (hi : i≤ k) :
    zsz (partialDenominator k a i : ℤ)≤ medianWidth n k a := by
  apply (Machine.Wedge.zsz_le_iff _ _).mpr
  simp only [Int.natAbs_natCast]
  have h := (Machine.Wedge.zsz_le_iff _ _).mp (estimateDenominator_width n k a)
  simp only [Int.natAbs_natCast] at h
  exact (partialDenominator_le hk hi).trans_lt h
lemma medianWidth_pos (n k a : ℕ) : 1≤ medianWidth n k a := by
  unfold medianWidth
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
lemma medianWidth_controls (n k a : ℕ) :
    zsz (k : ℤ)≤ medianWidth n k a ∧ zsz ((4^a : ℕ) : ℤ)≤ medianWidth n k a ∧
      zsz (1024 : ℤ)≤ medianWidth n k a := by
  constructor
  · have h := Machine.Controls.zsz_nat_le k
    unfold medianWidth
    nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
  constructor
  · apply (Machine.Wedge.zsz_le_iff _ _).mpr
    simp only [Int.natAbs_natCast]
    have he : (4 : ℕ)^a=2^(2*a) := by rw [show (4 : ℕ)=2^2 from rfl,←pow_mul]
    rw [he]
    apply Nat.pow_lt_pow_right (by decide)
    unfold medianWidth
    nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
  · have he : zsz (1024 : ℤ)=11 := by rw [Machine.Wedge.zsz_eq_size]; decide
    rw [he]
    unfold medianWidth
    nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Arithmetic
open Square
variable {v : ℕ}
attribute [local simp] Eval Value



lemma replaceExpr_runs (I : List Sym) (reg : Fin v→Fin Square.NS) (hreg : ∀ i, reg i≠Eval)
    (values : Fin v→ℕ) (e : Expr v) (w : ℕ) (hw : e.width values≤ w)
    (dst : Fin Square.NS) (hd : dst≠Eval) (s : IState Square.NS) (old : ℤ) (tail : List Item)
    (hs : s.G dst=.int old::tail) (hold : zsz old≤ w)
    (hv : ∀ i, ∃ tail, s.G (reg i)=.int (values i : ℤ)::tail) :
    IRuns I Fin.elim0 (replaceExpr reg e dst) s
      (s.upd dst (.int (e.eval values : ℤ)::tail)) (12000*(e.size+1)*(w+1)^2) := by
  have hd70 : dst≠70 := hd
  let s0 := s.upd Eval (.int (e.eval values : ℤ)::s.G Eval)
  let s1 := s0.upd dst tail
  let s2 := (s1.upd Eval (s.G Eval)).upd dst (.int (e.eval values : ℤ)::tail)
  have h0 := e.compile_runs I reg hreg values w hw s hv
  have h1 : IExec I Fin.elim0 (.op (.drop dst)) s0 s1 (2*zsz old+2) :=
    .op (.drop (by simp [s0,hd,hs]))
  have h2 : IExec I Fin.elim0 (.op (.mv Eval dst)) s1 s2 (2*moveCost (zsz (e.eval values : ℤ))+19) := by
    have h := IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt Square.NS 0))
      (IOp.Step.mv (s := s1) (i := Eval) (j := dst) (a := (e.eval values : ℤ))
        (L := s.G Eval) (Ne.symm hd) (by simp [s1,s0,hd70,Ne.symm hd70]))
    simpa [s2,s1,s0,hd] using h
  have he : s2=s.upd dst (.int (e.eval values : ℤ)::tail) := by
    apply itemState_ext
    · intro r
      by_cases h70 : r=70 <;> by_cases hD : r=dst <;> simp_all [s2,s1,s0,IState.upd,Function.update_apply]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq (Native.of_exec h1) (Native.of_exec h2))
  rw [he] at h
  change IRuns I Fin.elim0 (replaceExpr reg e dst) s _ _ at h
  apply Native.mono h
  have hroot := (e.root_width values).trans hw
  unfold moveCost
  nlinarith [Nat.zero_le (e.size*w*w)]

end KoanaKPaths.Machine.Arithmetic

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Denominator
open Arithmetic KoanaKPaths.Main



attribute [local simp] Den Index Trial.StateIndex






lemma expr_eval (k a j : ℕ) : expr.eval (values k a j)=partialDenominator k a (j+1) :=
  (partialDenominator_succ k a j).symm

lemma step_runs (I : List Sym) (s : IState NS) (n k a j : ℕ) (hk : 1≤ k) (hj : j< k)
    (kt dt jt : List Item)
    (hK : s.G 54=.int (k : ℤ)::kt)
    (hD : s.G Den=.int (partialDenominator k a j : ℤ)::dt)
    (hJ : s.G Index=.int (j : ℤ)::jt) :
    IRuns I Fin.elim0 step s
      ((s.upd Den (.int (partialDenominator k a (j+1) : ℤ)::dt)).upd Index (.int ((j+1 : ℕ) : ℤ)::jt))
      (10000000*(medianWidth n k a+1)^2) := by
  let L := medianWidth n k a
  have hdw : zsz (partialDenominator k a j : ℤ)≤ L := partialDenominator_width hk (by omega)
  have hkw : zsz (k : ℤ)≤ L := (medianWidth_controls n k a).1
  have hjw : zsz (j : ℤ)≤ L := by
    apply (Wedge.zsz_le_iff _ _).mpr
    have hh := (Wedge.zsz_le_iff _ _).mp hkw
    simp only [Int.natAbs_natCast] at *
    omega
  have hL : 1≤ L := medianWidth_pos n k a
  have hatom : expr.atomWidth (values k a j)≤ L := by
    change max (max (zsz (partialDenominator k a j : ℤ)) (zsz (k : ℤ)))
      (max (zsz (j : ℤ)) (zsz (1 : ℤ)))≤ L
    have h1 : zsz (1 : ℤ)=1 := by rw [Wedge.zsz_eq_size]; decide
    rw [h1]
    omega
  have hwidth : expr.width (values k a j)≤7*(L+1) :=
    expr.width_le (values k a j) L hatom
  let s0 := s.upd Den (.int (partialDenominator k a (j+1) : ℤ)::dt)
  have h0 : IRuns I Fin.elim0 (replaceExpr regs expr Den) s s0 (96000*(7*(L+1)+1)^2) := by
    have h := replaceExpr_runs I regs (by intro r; fin_cases r <;> decide) (values k a j)
      expr (7*(L+1)) hwidth Den (by decide) s (partialDenominator k a j : ℤ) dt hD (by omega)
      (by intro r; fin_cases r
          · exact ⟨dt,hD⟩
          · exact ⟨kt,hK⟩
          · exact ⟨jt,hJ⟩)
    simpa only [expr_eval,show expr.size=7 from rfl,show (12000*(7+1) : ℕ)=96000 from rfl] using h
  have h1 : IRuns I Fin.elim0 (Square.increment Index) s0
      (s0.upd Index (.int ((j+1 : ℕ) : ℤ)::jt)) (13000*(L+1)^2) :=
    Square.increment_runs I Index (by decide) s0 j L jt (by simp [s0,hJ]) hL hjw
  have h := Native.seq h0 h1
  exact Native.mono h (by dsimp only [L]; nlinarith)

end KoanaKPaths.Machine.Denominator

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Denominator
open Arithmetic KoanaKPaths.Main






lemma initExpr_eval (k a : ℕ) : initExpr.eval (initValues k a)=partialDenominator k a 0 := by
  rw [partialDenominator_zero]
  change 1024*(k*k*k)*4^a=1024*k^3*4^a
  ring

lemma initDen_runs (I : List Sym) (s : IState NS) (n k a : ℕ) (kt atail : List Item)
    (hK : s.G 54=.int (k : ℤ)::kt) (hA : s.G 60=.int ((4^a : ℕ) : ℤ)::atail) (hD : s.G Den=[]) :
    IRuns I Fin.elim0 initDen s
      (s.upd Den [.int (partialDenominator k a 0 : ℤ)])
      (20000000*(medianWidth n k a+1)^2) := by
  let L := medianWidth n k a
  have hbounds := medianWidth_controls n k a
  have hatom : initExpr.atomWidth (initValues k a)≤ L := by
    change max (max (zsz (1024 : ℤ))
      (max (max (zsz (k : ℤ)) (zsz (k : ℤ))) (zsz (k : ℤ)))) (zsz ((4^a : ℕ) : ℤ))≤ L
    dsimp only [L]
    omega
  have hwidth : initExpr.width (initValues k a)≤9*(L+1) :=
    initExpr.width_le (initValues k a) L hatom
  have hv : ∀ r, ∃ tail, s.G (initRegs r)=.int (initValues k a r : ℤ)::tail := by
    intro r
    fin_cases r
    · exact ⟨kt,hK⟩
    · exact ⟨atail,hA⟩
  have h := storeExpr_runs I initRegs (by intro r; fin_cases r <;> decide) (initValues k a)
    initExpr (9*(L+1)) hwidth Den (by decide) s hv
  have hh : IRuns I Fin.elim0 initDen s (s.upd Den [.int (partialDenominator k a 0 : ℤ)])
      (110000*(9*(L+1)+1)^2) := by
    simpa only [initDen,initExpr_eval,hD,show initExpr.size=9 from rfl,show (11000*(9+1) : ℕ)=110000 from rfl] using h
  exact Native.mono hh (by dsimp only [L]; nlinarith)

end KoanaKPaths.Machine.Denominator

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Denominator
open KoanaKPaths.Main

attribute [local simp] Counter Trial.LabelCounter Den Index Trial.StateIndex




lemma loop_runs (I : List Sym) (s : IState NS) (n k a : ℕ) (kt dt jt : List Item)
    (hk : 1≤ k) (hK : s.G 54=.int (k : ℤ)::kt)
    (hD : s.G Den=.int (partialDenominator k a 0 : ℤ)::dt)
    (hJ : s.G Index=.int 0::jt) (hC : s.G Counter=List.replicate k .mark) :
    IRuns I Fin.elim0 loop s (loopState s k a k dt jt)
      ((10000000*(medianWidth n k a+1)^2+31)*k+30) := by
  let C := 10000000*(medianWidth n k a+1)^2
  let Inv : ℕ→IState NS→Prop := fun j st => st=loopState s k a j dt jt
  have hcounter : ∀ j≤ k, ∀ st, Inv j st → st.G Counter=List.replicate (k-j) .mark ++ [] := by
    intro j hj st hs; rw [hs]; simp [loopState]
  have hstep : ∀ j< k, ∀ st, Inv j st → ∃ st',
      IRuns I Fin.elim0 (.seq (.op (.unmark Counter)) step) st st' (C+1) ∧ Inv (j+1) st' := by
    intro j hj st hs; rw [hs]
    let cur := loopState s k a j dt jt
    let popped := cur.upd Counter (List.replicate (k-(j+1)) .mark)
    let next := (popped.upd Den (.int (partialDenominator k a (j+1) : ℤ)::dt)).upd Index
      (.int ((j+1 : ℕ) : ℤ)::jt)
    have hlen : k-j=(k-(j+1))+1 := by omega
    have h0 : IExec I Fin.elim0 (.op (.unmark Counter)) cur popped 1 :=
      .op (.unmark (by simp [cur,loopState,hlen,List.replicate_succ]))
    have h1 : IRuns I Fin.elim0 step popped next C :=
      step_runs I popped n k a j hk hj kt dt jt (by simp [popped,cur,loopState,hK])
        (by simp [popped,cur,loopState]) (by simp [popped,cur,loopState])
    have he : next=loopState s k a (j+1) dt jt := by
      apply itemState_ext
      · intro r
        by_cases h88 : r=88 <;> by_cases h83 : r=83 <;> by_cases h127 : r=127 <;>
          simp [next,popped,cur,loopState,IState.upd,Function.update_apply,h88,h83,h127]
      · rfl
      · rfl
    exact ⟨next,Native.mono (Native.seq (Native.of_exec h0) h1) (by omega),he⟩
  have hinit : Inv 0 s := by
    unfold Inv loopState
    simp only [Nat.sub_zero,Nat.cast_zero]
    rw [←hC,←hD,←hJ]
    simp
  obtain ⟨st,hrun,hend⟩ := Native.invariant_loop I Fin.elim0 Counter
    (.seq (.op (.unmark Counter)) step) Inv k (C+1) [] (by simp [cls]) hcounter hstep s hinit
  rw [hend] at hrun
  simpa only [loop,C,Nat.add_assoc,show (1+30 : ℕ)=31 from rfl] using hrun

end KoanaKPaths.Machine.Denominator

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Denominator
open KoanaKPaths.Main
attribute [local simp] Den Index Counter Trial.StateIndex Trial.LabelCounter Trial.LabelTmp Wedge.D





lemma program_runs (I : List Sym) (s : IState NS) (n k a : ℕ) (kt atail : List Item)
    (hk : 1≤ k) (hK : s.G 54=.int (k : ℤ)::kt) (hA : s.G 60=.int ((4^a : ℕ) : ℤ)::atail)
    (hD : s.G Den=[]) (hTemplate : s.G Wedge.D=List.replicate k .mark)
    (hCounter : s.G Counter=[]) (hTmp : s.G Trial.LabelTmp=[]) :
    IRuns I Fin.elim0 program s
      (s.upd Den [.int ((groupTrials k a*trialDenominator k : ℕ) : ℤ)])
      (driverCost n k a) := by
  let s0 := s.upd Den [.int (partialDenominator k a 0 : ℤ)]
  let s1 := s0.upd Index (.int 0::s.G Index)
  let s2 := s1.upd Counter (List.replicate k .mark)
  let s3 := loopState s2 k a k [] (s.G Index)
  let s4 := s3.upd Index (s.G Index)
  have h0 : IRuns I Fin.elim0 initDen s s0 (20000000*(medianWidth n k a+1)^2) :=
    initDen_runs I s n k a kt atail hK hA hD
  have h1 : IExec I Fin.elim0 (.op (.const Index 0)) s0 s1 2 := by
    simpa [s1,s0,Wedge.zsz_eq_size] using
      (IExec.op (I := I) (iprog := (Fin.elim0 : Fin 0→IStmt NS 0)) (IOp.Step.const (s := s0) (i := Index) 0))
  have h2 : IExec I Fin.elim0 (copyMarks Wedge.D Counter Trial.LabelTmp) s1 s2 (65*k+60) := by
    have h := copyMarks_exec I Wedge.D Counter Trial.LabelTmp (by decide) (by decide) (by decide)
      s1 k [] (by simp [cls]) (by simp [s1,s0,hTemplate]) (by simp [s1,s0,hTmp])
    simpa [s2,s1,s0,hCounter] using h
  have h3 : IRuns I Fin.elim0 loop s2 s3 ((10000000*(medianWidth n k a+1)^2+31)*k+30) :=
    loop_runs I s2 n k a kt [] (s.G Index) hk (by simp [s2,s1,s0,hK])
      (by simp [s2,s1,s0]) (by simp [s2,s1]) (by simp [s2])
  have h4 : IExec I Fin.elim0 (.op (.drop Index)) s3 s4 (2*zsz (k : ℤ)+2) :=
    .op (.drop (by simp [s3,loopState]))
  have he : s4=s.upd Den [.int ((groupTrials k a*trialDenominator k : ℕ) : ℤ)] := by
    apply itemState_ext
    · intro r
      by_cases h127 : r=127 <;> by_cases h83 : r=83 <;> by_cases h88 : r=88 <;>
        simp [s4,s3,loopState,s2,s1,s0,IState.upd,Function.update_apply,h127,h83,h88,hCounter,partialDenominator_full]
    · rfl
    · rfl
  have h := Native.seq h0 (Native.seq (Native.of_exec h1) (Native.seq (Native.of_exec h2)
    (Native.seq h3 (Native.of_exec h4))))
  rw [he] at h
  change IRuns I Fin.elim0 program s _ _ at h
  apply Native.mono h
  have hkw := (medianWidth_controls n k a).1
  have hL := medianWidth_pos n k a
  unfold driverCost
  nlinarith [Nat.zero_le (k*(medianWidth n k a)^2)]

end KoanaKPaths.Machine.Denominator

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main





lemma ofFn_prod_flatten {α : Type} {m n : ℕ} (f : Fin m→Fin n→α) :
    List.ofFn (fun t : Fin (m*n) => f (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)=
      (List.ofFn (fun i => List.ofFn (f i))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hij : i.val*n+j.val< m*n := by
    have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at hm
    omega
  have he : (⟨i.val*n+j.val,hij⟩ : Fin (m*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val=j.val+n*i.val
    ring
  simp only [he,Equiv.symm_apply_apply]

lemma trialStream_ofFn {n k m : ℕ} (os : Fin m→Fin (trialBits n k)→Bool) :
    trialStream (List.ofFn os)=
      (List.ofFn (fun t : Fin (m*trialBits n k) => sgn (os (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2))).map Item.int := by
  unfold trialStream signsOf
  congr 1
  have hflat {α β : Type} (xs : List α) (f : α→List β) : xs.flatMap f=(xs.map f).flatten := by
    induction xs <;> simp_all
  rw [hflat,List.map_ofFn]
  exact (ofFn_prod_flatten (fun i j => sgn (os i j))).symm

lemma groupsStream_flatten {n k : ℕ} (oss : List (List (Fin (trialBits n k)→Bool))) :
    groupsStream oss=trialStream oss.flatten := by
  induction oss with
  | nil => rfl
  | cons os oss ih =>
    simpa [groupsStream,trialStream,List.map_append,List.flatMap_append] using
      congrArg (fun xs => trialStream os++xs) ih

lemma sampleTrials_stream {n k a b : ℕ} (ω : Fin (sampleBits n k a b)→Bool) :
    groupsStream (List.ofFn (fun i => List.ofFn (sampleTrials ω i)))=
      (List.ofFn (fun t => sgn (ω t))).map Item.int := by
  rw [groupsStream_flatten,←ofFn_prod_flatten (sampleTrials ω),trialStream_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext t
  change sgn (ω (finProdFinEquiv
    (finProdFinEquiv (finProdFinEquiv.symm ((finProdFinEquiv.symm t).1)),
      (finProdFinEquiv.symm t).2)))=sgn (ω t)
  rw [Equiv.apply_symm_apply]
  exact congrArg (fun t => sgn (ω t)) (finProdFinEquiv.apply_symm_apply t)


end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
open scoped BigOperators
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] Coins Balanced.Records Median.Output Denominator.Den Denominator.Index Denominator.Counter
  StateIndex LabelCounter LabelTmp Wedge.D




lemma nativeEstimator_runs (I : List Sym) (s : IState NS) {n k a b : ℕ}
    (arcs : List (Fin n × Fin n)) (ω : Fin (sampleBits n k a b)→Bool) (tail : List Item)
    (hk : 1≤ k) (hr : EstimatorReady s k a b arcs)
    (hCoins : s.G Coins=(List.ofFn (fun j => sgn (ω j))).map Item.int ++ tail) :
    ∃ s', IRuns I Wedge.prog nativeEstimator s s' (estimatorCost n k a b arcs.length) ∧
      s'.G 126=[.int ((estimateFraction (walkTensor n arcs k) a b (samplesEquiv n k a b ω)).num : ℤ)] ∧
      s'.G 127=[.int ((estimateFraction (walkTensor n arcs k) a b (samplesEquiv n k a b ω)).den : ℤ)] ∧
      s'.ip=s.ip ∧ s'.out=s.out := by
  let os := sampleTrials ω
  let f : Fin (2*b+1)→ℕ := fun i => ∑ j, trialNumerator (walkTensor n arcs k) (trialEquiv n k (os i j))
  let s1 := (((s.upd Coins tail).upd Balanced.Records
    ((List.ofFn (fun i => (f i : ℤ))).map Item.int ++ .mark::s.G Balanced.Records))).upd Median.Output
      [.int ((KoanaKPaths.Sampling.median b f : ℕ) : ℤ)]
  let s2 := s1.upd Denominator.Den [.int ((groupTrials k a*trialDenominator k : ℕ) : ℤ)]
  have h0 : IRuns I Wedge.prog nativeNumerator s s1 (numeratorCost n k a b arcs.length) :=
    nativeNumerator_runs I s arcs os tail hk hr (by simpa only [os,sampleTrials_stream] using hCoins)
  have h1 : IRuns I Wedge.prog (liftClosed Denominator.program) s1 s2 (Denominator.driverCost n k a) := by
    exact liftClosed_runs I Wedge.prog (Denominator.program_runs I s1 n k a [] [] hk
      (by simpa [s1,readyStack,NS,Wedge.NS] using hr.1.at 54 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 60 (by decide))
      (by simpa [s1,estimatorStack,NS,Wedge.NS] using hr.at 127 (by decide))
      (by simpa [s1,readyStack,NS,Wedge.NS] using hr.1.at 3 (by decide))
      (by simpa [s1,readyStack,NS,Wedge.NS] using hr.1.at 88 (by decide))
      (by simpa [s1,readyStack,NS,Wedge.NS] using hr.1.at 89 (by decide)))
  have hnum : (KoanaKPaths.Sampling.median b f : ℕ)=
      (estimateFraction (walkTensor n arcs k) a b (samplesEquiv n k a b ω)).num := by
    rfl
  refine ⟨s2,Native.seq h0 h1,?_,?_,rfl,rfl⟩
  · simpa [s2,s1] using congrArg (fun x : ℕ => [Item.int (x : ℤ)]) hnum
  · rfl

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k a b : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (ω : Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
  (tail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.EstimatorReady n s k a b arcs)
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@List.map.{0, 0} Int NLogN.Item NLogN.Item.int
          (@List.ofFn.{0} Int (KoanaKPaths.Main.sampleBits n k a b)
            fun (j : Fin (KoanaKPaths.Main.sampleBits n k a b)) => KoanaKPaths.Main.sgn (ω j)))
        tail)),
  @Exists.{1} (NLogN.IState KoanaKPaths.Machine.Wedge.NS) fun (s' : NLogN.IState KoanaKPaths.Machine.Wedge.NS) =>
    And
      (@NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
        KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.nativeEstimator s s'
        (KoanaKPaths.Machine.Trial.estimatorCost n k a b (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)))
      (And
        (@Eq.{1} (List.{0} NLogN.Item)
          (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s'
            (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Wedge.NS) (nat_lit 126)
              (@Fin.instOfNat KoanaKPaths.Machine.Wedge.NS
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))) (nat_lit 126))))
          (@List.cons.{0} NLogN.Item
            (NLogN.Item.int
              (@Nat.cast.{0} Int instNatCastInt
                (HypergraphUnreliability.FPRAS.Frac.num
                  (@KoanaKPaths.Main.estimateFraction n k (KoanaKPaths.Main.walkTensor n arcs k) a b
                    (@DFunLike.coe.{1, 1, 1}
                      (Equiv.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                        (Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          Fin (KoanaKPaths.Main.groupTrials k a) →
                            Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                      (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                      (fun (x : Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool) =>
                        Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          Fin (KoanaKPaths.Main.groupTrials k a) →
                            Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                        (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                        (Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          Fin (KoanaKPaths.Main.groupTrials k a) →
                            Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                        (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                      (KoanaKPaths.Main.samplesEquiv n k a b) ω)))))
            (@List.nil.{0} NLogN.Item)))
        (And
          (@Eq.{1} (List.{0} NLogN.Item)
            (@NLogN.IState.G KoanaKPaths.Machine.Wedge.NS s'
              (@OfNat.ofNat.{0} (Fin KoanaKPaths.Machine.Wedge.NS) (nat_lit 127)
                (@Fin.instOfNat KoanaKPaths.Machine.Wedge.NS
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127))))
                  (nat_lit 127))))
            (@List.cons.{0} NLogN.Item
              (NLogN.Item.int
                (@Nat.cast.{0} Int instNatCastInt
                  (HypergraphUnreliability.FPRAS.Frac.den
                    (@KoanaKPaths.Main.estimateFraction n k (KoanaKPaths.Main.walkTensor n arcs k) a b
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                        (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                        (fun (x : Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool) =>
                          Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                            (Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                              Fin (KoanaKPaths.Main.groupTrials k a) →
                                Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                          (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                          (Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                            Fin (KoanaKPaths.Main.groupTrials k a) →
                              Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                          (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.sampleBits n k a b) → Bool)
                            (Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                              Fin (KoanaKPaths.Main.groupTrials k a) →
                                Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                        (KoanaKPaths.Main.samplesEquiv n k a b) ω)))))
              (@List.nil.{0} NLogN.Item)))
          (And
            (@Eq.{1} Nat (@NLogN.IState.ip KoanaKPaths.Machine.Wedge.NS s')
              (@NLogN.IState.ip KoanaKPaths.Machine.Trial.NS s))
            (@Eq.{1} (List.{0} Bool) (@NLogN.IState.out KoanaKPaths.Machine.Wedge.NS s')
              (@NLogN.IState.out KoanaKPaths.Machine.Trial.NS s))))) := by
  exact @KoanaKPaths.Machine.Trial.nativeEstimator_runs
