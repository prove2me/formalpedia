-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.groupNative_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:49:13.137454+00:00
-- url     : https://prove2.me/submissions/05cc2ec1-e57f-47cc-8aae-ea16377ef8b6

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
import Theorems.Thm_KoanaKPaths_Machine_Balanced_finishGroup_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_trialFold_runs
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

lemma zsz_add_le (x y : ℤ) (w : ℕ) (hx : zsz x≤w) (hy : zsz y≤w) : zsz (x+y)≤w+1 := by
  apply (zsz_le_iff _ _).mpr
  have hx' := (zsz_le_iff x w).mp hx
  have hy' := (zsz_le_iff y w).mp hy
  have ha := Int.natAbs_add_le x y
  rw [pow_succ]
  omega















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
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main









lemma Ready.upd {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)} (h : Ready (k := k) s arcs)
    (j : Fin NS) (hj : j∉readyRegisters) (xs : List Item) : Ready (k := k) (s.upd j xs) arcs := by
  intro r hr
  have hne : r≠j := by rintro rfl; exact hj hr
  simpa [IState.upd,hne] using h r hr



end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
lemma trialNumerator_word_width {n k : ℕ} (ω : Fin (trialBits n k)→Bool)
    (arcs : List (Fin n × Fin n)) (hk : 1≤ k) :
    zsz (trialNumerator (walkTensor n arcs k) (trialEquiv n k ω) : ℤ)≤ wordWidth n k := by
  rw [←denseTrial_eq_trialNumerator hk]
  have h := denseTrial_width arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2
  have hp := trialWidth_polynomial n k
  unfold wordWidth
  omega
end KoanaKPaths.Machine.Trial

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Balanced









lemma potential_cons (w l : ℕ) (x : ℤ) (cs : List Chunk) :
    potential w ((l,x)::cs)=5000*(w+l+2)+potential w cs := by simp [potential]; ring

lemma carryInsert_width (w l : ℕ) (x : ℤ) (cs : List Chunk)
    (hx : zsz x≤ w+l) (hc : ∀ c∈cs, zsz c.2≤ w+c.1) :
    ∀ c∈carryInsert l x cs, zsz c.2≤ w+c.1 := by
  induction cs generalizing l x with
  | nil => simpa only [carryInsert,List.mem_singleton,forall_eq] using hx
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    have hy := hc (j,y) (by simp)
    change zsz y ≤ w+j at hy
    have htail : ∀ c∈cs, zsz c.2≤ w+c.1 := fun c hm => hc c (by simp [hm])
    simp only [carryInsert]
    split_ifs with h
    · subst j
      apply ih
      · simpa only [Nat.add_assoc] using Wedge.zsz_add_le x y (w+l) hx hy
      · exact htail
    · intro c hm
      simp only [List.mem_cons] at hm
      rcases hm with rfl|hm
      · exact hx
      · exact hc c (by simpa only [List.mem_cons] using hm)

lemma carryCharge_amortized (w l : ℕ) (x : ℤ) (cs : List Chunk)
    (hx : zsz x≤ w+l) (hc : ∀ c∈cs, zsz c.2≤ w+c.1) :
    carryCharge l x cs+potential w (carryInsert l x cs) ≤ potential w cs+6000*(w+l+2) := by
  induction cs generalizing l x with
  | nil =>
    simp only [carryCharge,carryInsert,potential,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,mul_zero]
    unfold moveCost
    nlinarith
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    have hy := hc (j,y) (by simp)
    change zsz y ≤ w+j at hy
    have htail : ∀ c∈cs, zsz c.2≤ w+c.1 := fun c hm => hc c (by simp [hm])
    simp only [carryCharge,carryInsert]
    split_ifs with h
    · subst j
      have hxy : zsz (x+y)≤ w+(l+1) := by
        simpa only [Nat.add_assoc] using Wedge.zsz_add_le x y (w+l) hx hy
      have hrec := ih (l+1) (x+y) hxy htail
      rw [potential_cons]
      have hadd : addIntCost (zsz x+zsz y)+68≤594*(w+l)+461 := by
        rw [Wedge.addIntCost_formula]
        omega
      nlinarith
    · rw [potential_cons,potential_cons]
      unfold moveCost
      nlinarith











lemma accumulate_amortized (w : ℕ) (cs : List Chunk) (xs : List ℤ)
    (hc : ∀ c∈cs, zsz c.2≤ w+c.1) (hx : ∀ x∈xs, zsz x≤ w) :
    accumulateCharge cs xs+potential w (accumulate cs xs) ≤ potential w cs+6000*(w+2)*xs.length := by
  induction xs generalizing cs with
  | nil => simp [accumulate,accumulateCharge]
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have hstep := carryCharge_amortized w 0 x cs (by simpa using hxx) hc
    have hnext := carryInsert_width w 0 x cs (by simpa using hxx) hc
    have hrec := ih (carryInsert 0 x cs) hnext (fun y hm => hx y (by simp [hm]))
    simp only [accumulate,accumulateCharge,List.length_cons]
    nlinarith






lemma carryInsert_order (l : ℕ) (x : ℤ) (cs : List Chunk)
    (hcs : cs.Pairwise (fun a b => a.1<b.1)) (hl : ∀ c∈cs, l≤ c.1) :
    (carryInsert l x cs).Pairwise (fun a b => a.1<b.1) ∧ ∀ c∈carryInsert l x cs, l≤ c.1 := by
  induction cs generalizing l x with
  | nil => simp [carryInsert]
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hcs
    have hj : l≤ j := hl (j,y) (by simp)
    simp only [carryInsert]
    split_ifs with he
    · subst j
      have hnext : ∀ c∈cs, l+1≤ c.1 := by intro c hc; have hh := hhead c hc; omega
      have hh := ih (l+1) (x+y) htail hnext
      exact ⟨hh.1,fun c hc => (by have := hh.2 c hc; omega)⟩
    · constructor
      · apply List.Pairwise.cons
        · intro c hc
          have hh : j≤ c.1 := by
            simp only [List.mem_cons] at hc
            rcases hc with rfl|hc
            · exact le_rfl
            · exact Nat.le_of_lt (hhead c hc)
          omega
        · exact hcs
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl|hc
        · exact le_rfl
        · exact hl c (by simpa only [List.mem_cons] using hc)



lemma foldCharge_bound (w l : ℕ) (x : ℤ) (cs : List Chunk)
    (hx : zsz x≤ w+l) (hs : cs.Pairwise (fun a b => a.1<b.1))
    (hl : ∀ c∈cs, l≤ c.1) (hc : ∀ c∈cs, zsz c.2≤ w+c.1) :
    foldCharge x cs≤ potential w cs+30 := by
  induction cs generalizing l x with
  | nil => simp [foldCharge,potential]
  | cons c cs ih =>
    rcases c with ⟨j,y⟩
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    have hj := hl (j,y) (by simp)
    change l≤ j at hj
    have hx' : zsz x≤ w+j := by omega
    have hy := hc (j,y) (by simp)
    change zsz y≤ w+j at hy
    have hxy : zsz (x+y)≤ w+(j+1) := by
      simpa only [Nat.add_assoc] using Wedge.zsz_add_le x y (w+j) hx' hy
    have hnext : ∀ c∈cs, j+1≤ c.1 := by intro c hc; have hh := hhead c hc; omega
    have hr := ih (j+1) (x+y) hxy htail hnext (fun c hm => hc c (by simp [hm]))
    simp only [foldCharge,potential_cons]
    rw [Wedge.addIntCost_formula]
    omega

lemma accumulate_order (cs : List Chunk) (xs : List ℤ) (hs : cs.Pairwise (fun a b => a.1<b.1)) :
    (accumulate cs xs).Pairwise (fun a b => a.1<b.1) := by
  induction xs generalizing cs with
  | nil => exact hs
  | cons x xs ih =>
    exact ih _ ((carryInsert_order 0 x cs hs (by intro c hc; omega)).1)

lemma accumulate_width (w : ℕ) (cs : List Chunk) (xs : List ℤ)
    (hc : ∀ c∈cs, zsz c.2≤ w+c.1) (hx : ∀ x∈xs, zsz x≤ w) :
    ∀ c∈accumulate cs xs, zsz c.2≤ w+c.1 := by
  induction xs generalizing cs with
  | nil => exact hc
  | cons x xs ih =>
    have hh := carryInsert_width w 0 x cs (by simpa using hx x (by simp)) hc
    exact ih _ hh (fun y hm => hx y (by simp [hm]))

/-- All merges and the final fold cost linearly in the number of input bits, independent of
how many binary carry levels the final sum occupies. -/
theorem balanced_total (w : ℕ) (xs : List ℤ) (hx : ∀ x∈xs, zsz x≤ w) :
    accumulateCharge [] xs+foldCharge 0 (accumulate [] xs)≤6000*(w+2)*xs.length+30 := by
  have h0 : ∀ c∈([] : List Chunk), zsz c.2≤ w+c.1 := by simp
  have ha := accumulate_amortized w [] xs h0 hx
  have hs := accumulate_order [] xs (by simp)
  have hw := accumulate_width w [] xs h0 hx
  have hf := foldCharge_bound w 0 0 (accumulate [] xs)
    (by simp [Wedge.zsz_eq_size]) hs (by intro c hc; omega) hw
  rw [show potential w []=0 from by simp [potential]] at ha
  omega

end KoanaKPaths.Machine.Balanced

end

section

set_option autoImplicit false
set_option maxHeartbeats 3000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main


attribute [local simp] TrialCounter TrialTemplate GroupCopyTmp Coins Balanced.Partials Balanced.Bits Balanced.Restore Balanced.Records





lemma groupNative_runs (I : List Sym) (s : IState NS) {n k : ℕ}
    (arcs : List (Fin n × Fin n)) (os : List (Fin (trialBits n k)→Bool)) (tail : List Item)
    (hk : 1≤ k) (hr : Ready (k := k) s arcs)
    (ht : s.G TrialTemplate=List.replicate os.length .mark) (hc : s.G TrialCounter=[])
    (hx : s.G GroupCopyTmp=[]) (hRestore : s.G Balanced.Restore=[])
    (hCoins : s.G Coins=trialStream os++tail) :
    IRuns I Wedge.prog groupNative s
      ((s.upd Coins tail).upd Balanced.Records (.int (numerators arcs os).sum::s.G Balanced.Records))
      (groupNativeCost n k arcs.length os.length) := by
  let xs := numerators arcs os
  let cs := Balanced.accumulate [] xs
  let s0 := s.upd Balanced.Partials (.mark::s.G Balanced.Partials)
  let s1 := s0.upd Balanced.Bits (.mark::s.G Balanced.Bits)
  let s2 := s1.upd TrialCounter (List.replicate os.length .mark)
  let s3 := trialFoldState s2 arcs os [] tail (s.G Balanced.Bits) (.mark::s.G Balanced.Partials)
  let s4 := ((s3.upd Balanced.Partials (s.G Balanced.Partials)).upd Balanced.Bits (s.G Balanced.Bits)).upd Balanced.Records
    (.int xs.sum::s.G Balanced.Records)
  have h0 : IExec I Wedge.prog (.op (.mark Balanced.Partials)) s s0 1 := .op (.mark)
  have h1 : IExec I Wedge.prog (.op (.mark Balanced.Bits)) s0 s1 1 := by
    simpa [s1,s0] using (IExec.op (I := I) (iprog := Wedge.prog) (IOp.Step.mark (s := s0) (i := Balanced.Bits)))
  have h2 : IExec I Wedge.prog (liftClosed (copyMarks TrialTemplate TrialCounter GroupCopyTmp)) s1 s2
      (65*os.length+60) := by
    have h := liftClosed_exec I Wedge.prog (copyMarks_exec I TrialTemplate TrialCounter GroupCopyTmp
      (by decide) (by decide) (by decide) s1 os.length [] (by simp [cls]) (by simp [s1,s0,ht]) (by simp [s1,s0,hx]))
    simpa [s2,s1,s0,hc] using h
  have hr2 : Ready (k := k) s2 arcs :=
    ((hr.upd Balanced.Partials (by decide) _).upd Balanced.Bits (by decide) _).upd TrialCounter (by decide) _
  have h3 : IRuns I Wedge.prog trialFold s2 s3
      (trialFoldBaseCost n k arcs.length*os.length+Balanced.accumulateCharge [] xs+30) :=
    trialFold_runs I s2 arcs os [] tail (s.G Balanced.Bits) (.mark::s.G Balanced.Partials) hk hr2
      (by simp [s2]) (by simp [s2,s1,s0,hCoins]) (by simp [s2,s1,Balanced.counterCode])
      (by simp [s2,s1,s0]) (by simp [s2,s1,s0,hRestore]) (by simp)
  have hw : ∀ x∈xs, zsz x≤ wordWidth n k := by
    intro x hx
    obtain ⟨ω,hω,rfl⟩ := List.mem_map.mp hx
    exact trialNumerator_word_width ω arcs hk
  have h4 : IRuns I Wedge.prog (liftClosed Balanced.finishGroup) s3 s4
      (Balanced.foldCharge 0 cs+34*xs.length+1000*(wordWidth n k+xs.length+1)) := by
    have h := liftClosed_runs I Wedge.prog (Balanced.finishGroup_runs I s3 xs
      (s.G Balanced.Partials) (s.G Balanced.Bits)
      (by simp [s3,trialFoldState,xs]) (by simp [s3,trialFoldState,xs]) (wordWidth n k) hw)
    simpa [s4,s3,trialFoldState,s2,s1,s0,cs,xs] using h
  have hpost : s4=(s.upd Coins tail).upd Balanced.Records (.int xs.sum::s.G Balanced.Records) := by
    apply itemState_ext
    · intro r
      by_cases h102 : r=102 <;> by_cases h103 : r=103 <;> by_cases h101 : r=101 <;> by_cases h52 : r=52 <;> by_cases h107 : r=107 <;>
        simp [s4,s3,trialFoldState,s2,s1,s0,IState.upd,Function.update_apply,h102,h103,h101,h52,h107,hc]
    · rfl
    · rfl
  have h := Native.seq (Native.of_exec h0) (Native.seq (Native.of_exec h1)
    (Native.seq (Native.of_exec h2) (Native.seq h3 h4)))
  rw [hpost] at h
  change IRuns I Wedge.prog groupNative s _ _ at h
  apply Native.mono h
  have hb := Balanced.balanced_total (wordWidth n k) xs hw
  have hlen : xs.length=os.length := by simp [xs,numerators]
  rw [hlen] at hb ⊢
  unfold groupNativeCost
  dsimp only [cs] at *
  nlinarith

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (s : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (os : List.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool))
  (tail : List.{0} NLogN.Item)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k s arcs)
  (ht :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialTemplate)
      (@List.replicate.{0} NLogN.Item (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os)
        NLogN.Item.mark))
  (hc :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.TrialCounter)
      (@List.nil.{0} NLogN.Item))
  (hx :
    @Eq.{1} (List.{0} NLogN.Item)
      (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.GroupCopyTmp)
      (@List.nil.{0} NLogN.Item))
  (hRestore :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Restore)
      (@List.nil.{0} NLogN.Item))
  (hCoins :
    @Eq.{1} (List.{0} NLogN.Item) (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins)
      (@HAppend.hAppend.{0, 0, 0} (List.{0} NLogN.Item) (List.{0} NLogN.Item) (List.{0} NLogN.Item)
        (@instHAppendOfAppend.{0} (List.{0} NLogN.Item) (@List.instAppend.{0} NLogN.Item))
        (@KoanaKPaths.Machine.Trial.trialStream n k os) tail)),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.groupNative s
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS
      (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Trial.Coins tail)
      KoanaKPaths.Machine.Balanced.Records
      (@List.cons.{0} NLogN.Item
        (NLogN.Item.int
          (@List.sum.{0} Int Int.instAdd
            (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring))
            (@KoanaKPaths.Machine.Trial.numerators n k arcs os)))
        (@NLogN.IState.G KoanaKPaths.Machine.Trial.NS s KoanaKPaths.Machine.Balanced.Records)))
    (KoanaKPaths.Machine.Trial.groupNativeCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs)
      (@List.length.{0} (Fin (KoanaKPaths.Main.trialBits n k) → Bool) os)) := by
  exact @KoanaKPaths.Machine.Trial.groupNative_runs
