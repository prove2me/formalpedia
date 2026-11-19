-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.wholeCost_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:43:13.152738+00:00
-- url     : https://prove2.me/submissions/d899f822-2e0b-46c4-a5cf-dc2325a31453

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
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Trial_cost_sum_bound
import Theorems.Thm_KoanaKPaths_Machine_Trial_estimatorCost_polynomial
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



lemma accuracy_square_bound (a : ℕ) : (a+1)^2≤4^a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    calc
      (a+1+1)^2≤4*(a+1)^2 := by nlinarith [Nat.zero_le (a*a)]
      _ ≤ 4*4^a := Nat.mul_le_mul_left 4 ih
      _ = 4^(a+1) := by rw [pow_succ]; ring

lemma medianWidth_cost (n k a : ℕ) :
    (medianWidth n k a+1)^2≤11000*(1+n+k)^4*4^a := by
  have ha := accuracy_square_bound a
  have hp : 1≤(1+n+k)^2 := by nlinarith [Nat.zero_le (n*n),Nat.zero_le (k*k)]
  have hlin : medianWidth n k a+1≤103*(1+n+k)^2*(a+1) := by
    unfold medianWidth
    nlinarith
  have hs := Nat.pow_le_pow_left hlin 2
  calc
    _ ≤ (103*(1+n+k)^2*(a+1))^2 := hs
    _ = 10609*(1+n+k)^4*(a+1)^2 := by ring
    _ ≤ 11000*(1+n+k)^4*4^a := by nlinarith [Nat.mul_le_mul_left (10609*(1+n+k)^4) ha]

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic

























lemma exprM_eval (n k a b m : ℕ) : exprM.eval (inputValues n k a b m)=KoanaKPaths.Main.groupTrials k a := by
  simp [exprM,exprK,exprPower,Expr.eval,inputValues,KoanaKPaths.Main.groupTrials,pow_succ] <;> ring

lemma exprQ_eval (n k a b m : ℕ) : exprQ.eval (inputValues n k a b m)=2*b+1 := rfl
lemma exprTrial_eval (n k a b m : ℕ) : exprTrial.eval (inputValues n k a b m)=KoanaKPaths.Main.trialBits n k := rfl
lemma exprNK_eval (n k a b m : ℕ) : exprNK.eval (inputValues n k a b m)=n*k := rfl
lemma exprWidth_eval (n k a b m : ℕ) : exprWidth.eval (inputValues n k a b m)=KoanaKPaths.Main.medianWidth n k a := by
  simp [exprWidth,exprN,exprK,exprA,Expr.eval,inputValues,KoanaKPaths.Main.medianWidth] <;> ring
lemma exprSample_eval (n k a b m : ℕ) : exprSample.eval (inputValues n k a b m)=KoanaKPaths.Main.sampleBits n k a b := by
  simp only [exprSample,Expr.eval,exprM_eval,exprQ_eval,exprTrial_eval]
  rfl
lemma exprThreshold_eval (n k a b m : ℕ) : exprThreshold.eval (inputValues n k a b m)=b+1 := rfl











end KoanaKPaths.Machine.Controls

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls



lemma nat_square_le_exp (t : ℕ) : t^2≤2^(t+1) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    by_cases ht : t≤2
    · interval_cases t <;> norm_num
    · have h3 : 3≤ t := by omega
      have hprod : 3*t≤t*t := Nat.mul_le_mul_right t h3
      have hs : (t+1)^2≤2*t^2 := by nlinarith
      calc
        (t+1)^2≤2*t^2 := hs
        _ ≤ 2*2^(t+1) := Nat.mul_le_mul_left 2 ih
        _ = 2^(t+1+1) := by rw [pow_succ]; ring

lemma size_square_le (b : ℕ) : b.size^2≤4*b := by
  by_cases hz : b.size=0
  · simp [hz]
  · have he : b.size+1=(b.size-1)+2 := by omega
    have hb : 2^(b.size-1)≤b := Nat.lt_size.mp (by omega)
    calc
      _ ≤ 2^(b.size+1) := nat_square_le_exp b.size
      _ = 4*2^(b.size-1) := by rw [he,pow_add]; norm_num; ring
      _ ≤ 4*b := Nat.mul_le_mul_left 4 hb

lemma zsz_nat_le (n : ℕ) : zsz (n : ℤ)≤ n := by
  rw [Wedge.zsz_eq_size,Int.natAbs_natCast]
  exact Nat.size_le.mpr Nat.lt_two_pow_self






lemma controlWidth_square (n k a b m : ℕ) :
    (controlWidth n k a b m+1)^2≤1000*(1+n+k+m)^2*4^a*(b+1) := by
  let H := 1+n+k+m
  have hH : 1≤H := by dsimp [H]; omega
  have ha := KoanaKPaths.Main.accuracy_square_bound a
  have hb := size_square_le b
  have he : controlWidth n k a b m+1≤12*H+2*a+b.size := by unfold controlWidth; dsimp [H]; omega
  have hs := Nat.pow_le_pow_left he 2
  have hrough : (12*H+2*a+b.size)^2≤500*H^2+20*(a+1)^2+4*b.size^2 := by
    nlinarith [two_mul_le_add_sq (12*H) (2*a),two_mul_le_add_sq (12*H) b.size,
      two_mul_le_add_sq (2*a) b.size]
  have hp : 1≤4^a := by
    have h : 0<4^a := by positivity
    omega
  have hH2 : 1≤H^2 := by nlinarith
  have h1 : 500*H^2≤500*H^2*4^a*(b+1) := by nlinarith [Nat.mul_le_mul_left (500*H^2) hp]
  have h2 : 20*(a+1)^2≤20*H^2*4^a*(b+1) := by
    have h := Nat.mul_le_mul_left 20 ha
    nlinarith [Nat.mul_le_mul_right (20*4^a) hH2]
  have h3 : 4*b.size^2≤16*H^2*4^a*(b+1) := by
    have h := Nat.mul_le_mul_left 4 hb
    nlinarith [Nat.mul_le_mul_right (16*(b+1)) (Nat.mul_le_mul hH2 hp)]
  change _≤1000*H^2*4^a*(b+1)
  nlinarith

end KoanaKPaths.Machine.Controls

end

section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
open NLogN
namespace KoanaKPaths.Machine.Input
attribute [local simp] VertexField PathField AccuracyField ConfidenceField ArcCountField Counter DB
attribute [local simp] BitCounter.Count BitCounter.Tmp
variable {P : ℕ}



lemma arcSymbols_values {n : ℕ} (arcs : List (Fin n × Fin n)) :
    arcSymbols (arcValues arcs)=(arcs.flatMap (fun p => HypergraphUnreliability.FPRAS.natCode p.1.val ++
      HypergraphUnreliability.FPRAS.natCode p.2.val)).map codeBit := by
  induction arcs with
  | nil => rfl
  | cons p arcs ih =>
    have h := congrArg (fun L => (HypergraphUnreliability.FPRAS.natCode p.1.val).map codeBit ++
      (HypergraphUnreliability.FPRAS.natCode p.2.val).map codeBit ++ L) ih
    simpa [arcValues,arcSymbols,List.map_append,List.append_assoc] using h

lemma graphInput_symbols (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool) :
    logicalInput (KoanaKPaths.Main.graphInputControls n arcs k a b) tape =
      fieldSymbols (headerFields n k a b arcs.length) ++ arcSymbols (arcValues arcs) ++ codeSep::tape.map codeBit := by
  simp [logicalInput,KoanaKPaths.Main.graphInputControls,HypergraphUnreliability.FPRAS.listCode,
    fieldSymbols,headerFields,arcSymbols_values,List.map_append,List.append_assoc]

lemma graphInput_length (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    (KoanaKPaths.Main.graphInputControls n arcs k a b).length =
      (fieldSymbols (headerFields n k a b arcs.length)).length+(arcSymbols (arcValues arcs)).length := by
  have h := congrArg List.length (graphInput_symbols n arcs k a b [])
  simp only [logicalInput,List.length_append,List.length_map,List.length_cons,List.length_nil] at h
  omega











end KoanaKPaths.Machine.Input

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



end KoanaKPaths.Machine.Median

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
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main HypergraphUnreliability.FPRAS

lemma fraction_num_width {n k a b : ℕ} (arcs : List (Fin n × Fin n)) (hk : 1≤ k)
    (w : Fin (2*b+1)→Fin (groupTrials k a)→Labels n k × SketchSigns n k k) :
    zsz ((estimateFraction (walkTensor n arcs k) a b w).num : ℤ)≤ medianWidth n k a := by
  apply (Wedge.zsz_le_iff _ _).mpr
  simp only [Int.natAbs_natCast]
  apply Median.median_bound
  intro i
  have h := groupSum_lt_medianWidth arcs (w i)
  simpa only [denseTrial_eq_trialNumerator hk] using h

lemma fraction_bits_bounds {n k a b : ℕ} (arcs : List (Fin n × Fin n)) (hk : 1≤ k)
    (w : Fin (2*b+1)→Fin (groupTrials k a)→Labels n k × SketchSigns n k k) :
    (Nat.bits (estimateFraction (walkTensor n arcs k) a b w).num).length≤ medianWidth n k a ∧
    (Nat.bits (estimateFraction (walkTensor n arcs k) a b w).den).length≤ medianWidth n k a := by
  constructor
  · simpa only [Wedge.zsz_eq_size,Int.natAbs_natCast,Nat.size_eq_bits_len] using fraction_num_width arcs hk w
  · simpa only [Wedge.zsz_eq_size,Int.natAbs_natCast,Nat.size_eq_bits_len,estimateFraction] using estimateDenominator_width n k a

lemma fraction_writtenCost {n k a b : ℕ} (arcs : List (Fin n × Fin n)) (hk : 1≤ k)
    (w : Fin (2*b+1)→Fin (groupTrials k a)→Labels n k × SketchSigns n k k) :
    writtenCost (estimateFraction (walkTensor n arcs k) a b w)≤26*medianWidth n k a+10 := by
  have h := fraction_bits_bounds arcs hk w
  unfold writtenCost
  omega

lemma fraction_code_length {n k a b : ℕ} (arcs : List (Fin n × Fin n)) (hk : 1≤ k)
    (w : Fin (2*b+1)→Fin (groupTrials k a)→Labels n k × SketchSigns n k k) :
    (fracCode (estimateFraction (walkTensor n arcs k) a b w)).length≤4*medianWidth n k a+2 := by
  have h := fraction_bits_bounds arcs hk w
  simp only [fracCode,natCode,List.length_append,List.length_replicate,List.length_cons,List.length_map,List.length_nil]
  omega

end KoanaKPaths.Machine.Trial

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Input
open KoanaKPaths.Main HypergraphUnreliability.FPRAS

lemma fieldCost_bound {S : ℕ} (fs : List (Fin S × ℕ)) :
    fieldCost fs≤6*(fieldSymbols fs).length+1 := by
  induction fs with
  | nil => simp [fieldCost,fieldSymbols]
  | cons p fs ih =>
    rcases p with ⟨d,n⟩
    simp only [fieldCost,fieldSymbols,List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,
      List.length_map,natCode,List.length_replicate,List.length_cons,List.length_nil] at *
    omega

lemma arcCost_bound (arcs : List (ℕ×ℕ)) : arcCost arcs≤8*(arcSymbols arcs).length+1 := by
  induction arcs with
  | nil => simp [arcCost,arcSymbols]
  | cons p arcs ih =>
    rcases p with ⟨u,v⟩
    simp only [arcCost,arcSymbols,List.length_append,List.length_map,natCode,List.length_replicate,
      List.length_cons,List.length_nil] at *
    omega

lemma arcCount_le_symbols (arcs : List (ℕ×ℕ)) : arcs.length≤(arcSymbols arcs).length := by
  induction arcs with
  | nil => simp [arcSymbols]
  | cons p arcs ih =>
    rcases p with ⟨u,v⟩
    simp only [List.length_cons,arcSymbols,List.length_append,List.length_map,natCode,List.length_replicate,
      List.length_nil] at *
    omega

lemma graphReadCost_linear (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    graphReadCost n arcs k a b≤2010*((graphInputControls n arcs k a b).length+1) := by
  have hf := fieldCost_bound (headerFields n k a b arcs.length)
  have ha := arcCost_bound (arcValues arcs)
  have hm := arcCount_le_symbols (arcValues arcs)
  have hl : (arcValues arcs).length=arcs.length := by simp [arcValues]
  rw [hl] at hm
  unfold graphReadCost
  rw [graphInput_length]
  omega

lemma natCode_length_le (n : ℕ) : (natCode n).length≤2*n+1 := by
  have h : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  simp [natCode,Nat.size_eq_bits_len]
  omega

lemma graphInput_length_graphCode (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    (graphInputControls n arcs k a b).length=(graphCode n arcs).length+
      (natCode k).length+(natCode a).length+(natCode b).length := by
  simp only [graphInputControls,graphCode,List.length_append]
  omega

lemma graphInput_length_budget (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    (graphInputControls n arcs k a b).length+1 ≤
      8*(1+k+n+(graphCode n arcs).length)*4^a*(b+1) := by
  let P := 1+k+n+(graphCode n arcs).length
  let F := 4^a
  let q := b+1
  let H := P*F*q
  have hP : 1≤P := by dsimp [P]; omega
  have hF : 1≤F := Nat.one_le_pow a 4 (by omega)
  have hq : 1≤q := by dsimp [q]; omega
  have hpH : P≤H := by
    have h1 := Nat.mul_le_mul_left P hF
    have h2 := Nat.mul_le_mul_left (P*F) hq
    dsimp [H]
    nlinarith
  have hfH : F≤H := by
    have h1 := Nat.mul_le_mul_right F hP
    have h2 := Nat.mul_le_mul_left (P*F) hq
    dsimp [H]
    nlinarith
  have hqH : q≤H := by
    have hPF : 1≤P*F := by nlinarith
    simpa only [one_mul,H] using Nat.mul_le_mul_right q hPF
  have ha : a≤F := (Nat.le_of_lt (Nat.lt_two_pow_self (n := a))).trans
    (Nat.pow_le_pow_left (by omega : 2≤4) a)
  have hk := natCode_length_le k
  have hca := natCode_length_le a
  have hcb := natCode_length_le b
  rw [graphInput_length_graphCode]
  change (graphCode n arcs).length+(natCode k).length+(natCode a).length+(natCode b).length+1 ≤8*P*F*q
  have hl : (graphCode n arcs).length+(natCode k).length+(natCode a).length+(natCode b).length+1 ≤
      2*P+2*a+4*q := by dsimp [P,q]; omega
  have hsum : 2*P+2*a+4*q≤8*H := by omega
  have he : 8*H=8*P*F*q := by dsimp [H]; ring
  omega

lemma graphReadCost_budget (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) :
    graphReadCost n arcs k a b≤timeBudget 16080 1 k (n+(graphCode n arcs).length) a b := by
  calc
    _ ≤ 2010*((graphInputControls n arcs k a b).length+1) := graphReadCost_linear n arcs k a b
    _ ≤ 2010*(8*(1+k+n+(graphCode n arcs).length)*4^a*(b+1)) :=
      Nat.mul_le_mul_left _ (graphInput_length_budget n arcs k a b)
    _ = 16080*(1+k+n+(graphCode n arcs).length)*4^a*(b+1) := by ring
    _ ≤ 16080*2^k*(1+k+n+(graphCode n arcs).length)*4^a*(b+1) := by
      gcongr
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 16080 (Nat.one_le_pow k 2 (by omega))
    _ = _ := by simp [timeBudget,Nat.add_assoc]

end KoanaKPaths.Machine.Input

end

section

set_option autoImplicit false
open NLogN
namespace KoanaKPaths.Main
open HypergraphUnreliability.FPRAS

lemma arcs_length_le_graphCode {n : ℕ} (arcs : List (Fin n × Fin n)) : arcs.length≤(graphCode n arcs).length := by
  have h : arcs.length≤(arcs.flatMap (fun p => natCode p.1.val++natCode p.2.val)).length := by
    induction arcs with
    | nil => simp
    | cons p ps ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append,natCode,List.length_replicate,
        List.length_singleton] at *
      omega
  unfold graphCode listCode
  simp only [List.length_append]
  omega

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine.Controls
open Arithmetic KoanaKPaths.Main

lemma countPlansCost_eq {v : ℕ} (values : Fin v→ℕ) (w : ℕ) (ps : List (CountPlan v)) :
    countPlansCost values w ps=
      11000*(ps.map (fun p => p.1.size+1)).sum*(w+1)^2+
        1100*((ps.map (fun p => p.1.eval values)).sum+ps.length)+1 := by
  induction ps with
  | nil => simp [countPlansCost]
  | cons p ps ih => simp only [countPlansCost,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

lemma plans_size_sum : (plans.map (fun p => p.1.size+1)).sum=96 := by decide

lemma sample_dominates (n k a b : ℕ) (hn : 1≤ n) (hk : 1≤ k) :
    n≤ sampleBits n k a b ∧ k≤ sampleBits n k a b ∧
    groupTrials k a≤ sampleBits n k a b ∧ 2*b+1≤ sampleBits n k a b ∧
    trialBits n k≤ sampleBits n k a b ∧ n*k≤ sampleBits n k a b := by
  have hM : 1≤ groupTrials k a := by
    have hp : 0< groupTrials k a := by unfold groupTrials; positivity
    omega
  have hT : 1≤ trialBits n k := by
    have hprod : 1≤ n*k := Nat.mul_le_mul hn hk
    unfold trialBits
    omega
  have hQ : 1≤2*b+1 := by omega
  have hQS : 2*b+1≤ sampleBits n k a b := by
    unfold sampleBits
    calc
      2*b+1 = (2*b+1)*1*1 := by ring
      _ ≤ (2*b+1)*groupTrials k a*trialBits n k :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hT
  have hMS : groupTrials k a≤ sampleBits n k a b := by
    unfold sampleBits
    calc
      groupTrials k a = 1*groupTrials k a*1 := by ring
      _ ≤ (2*b+1)*groupTrials k a*trialBits n k :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ hQ) hT
  have hTS : trialBits n k≤ sampleBits n k a b := by
    unfold sampleBits
    calc
      trialBits n k = 1*1*trialBits n k := by ring
      _ ≤ (2*b+1)*groupTrials k a*trialBits n k :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hQ hM)
  have hNK : n*k≤ trialBits n k := by unfold trialBits; omega
  have hN : n≤ n*k := by simpa using Nat.mul_le_mul_left n hk
  have hK : k≤ n*k := by simpa using Nat.mul_le_mul_right k hn
  exact ⟨hN.trans (hNK.trans hTS),hK.trans (hNK.trans hTS),hMS,hQS,hTS,hNK.trans hTS⟩

lemma plans_values_sum (n k a b m : ℕ) (hn : 1≤ n) (hk : 1≤ k) :
    (plans.map (fun p => p.1.eval (inputValues n k a b m))).sum≤
      8*sampleBits n k a b+m+medianWidth n k a := by
  obtain ⟨hN,hK,hM,hQ,hT,hNK⟩ := sample_dominates n k a b hn hk
  have hth : b+1≤ sampleBits n k a b := by omega
  simp only [plans,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,exprM_eval,
    exprQ_eval,exprTrial_eval,exprNK_eval,exprWidth_eval,exprSample_eval,exprThreshold_eval]
  change _≤8*sampleBits n k a b+m+medianWidth n k a
  have hnE : exprN.eval (inputValues n k a b m)=n := rfl
  have hkE : exprK.eval (inputValues n k a b m)=k := rfl
  have hmE : exprArcCount.eval (inputValues n k a b m)=m := rfl
  rw [hnE,hkE,hmE]
  omega

lemma setupCost_bound (n k a b m : ℕ) (hn : 1≤ n) (hk : 1≤ k) :
    setupCost n k a b m≤12000000000*(controlWidth n k a b m+1)^2+
      10000*(sampleBits n k a b+m+medianWidth n k a+1) := by
  have hs := plans_values_sum n k a b m hn hk
  have hpreA := zsz_nat_le a
  have hpreK := zsz_nat_le k
  have hU : a≤ controlWidth n k a b m ∧ k≤ controlWidth n k a b m := by unfold controlWidth; omega
  have hpre : 22000*(zsz (a : ℤ)+1)^2+1600*(a+1)+12000*(zsz (k : ℤ)+2)^2≤
      100000*(controlWidth n k a b m+1)^2 := by
    nlinarith [Nat.pow_le_pow_left (Nat.add_le_add_right (hpreA.trans hU.1) 1) 2,
      Nat.pow_le_pow_left (Nat.add_le_add_right (hpreK.trans hU.2) 2) 2]
  have hpoly : 11000*96*(100*(controlWidth n k a b m+1)+1)^2≤
      11000000000*(controlWidth n k a b m+1)^2 := by nlinarith
  unfold setupCost
  rw [countPlansCost_eq,plans_size_sum]
  have hlen : plans.length=10 := rfl
  rw [hlen]
  nlinarith

end KoanaKPaths.Machine.Controls

end

section

namespace KoanaKPaths.Main

lemma trialBits_le (n k s : ℕ) : trialBits n k ≤ 3*(1+k+n+s)^4 := by
  let P := 1+k+n+s
  have hn : n ≤ P := by dsimp [P]; omega
  have hk : k ≤ P := by dsimp [P]; omega
  have hp : 1 ≤ P := by dsimp [P]; omega
  have hp2 : P^2 ≤ P^4 := Nat.pow_le_pow_right hp (by omega)
  have h1 : n*k ≤ P^4 := (Nat.mul_le_mul hn hk).trans (by simpa [pow_two] using hp2)
  have h2 : k*n ≤ P^4 := by simpa only [Nat.mul_comm] using h1
  have h3 : (k-1)*(k*(k*n)) ≤ P^4 := by
    calc
      _ ≤ P*(P*(P*P)) := Nat.mul_le_mul (le_trans (Nat.sub_le k 1) hk)
        (Nat.mul_le_mul hk (Nat.mul_le_mul hk hn))
      _ = P^4 := by ring
  unfold trialBits
  change n*k+(k*n+(k-1)*(k*(k*n))) ≤ 3*P^4
  omega

lemma sampleBits_le_budget (n k a b s : ℕ) :
    sampleBits n k a b ≤ timeBudget 6144 7 k (n+s) a b := by
  let P := 1+k+n+s
  have hk : k ≤ P := by dsimp [P]; omega
  have hpow : k^3 ≤ P^3 := Nat.pow_le_pow_left hk 3
  have ht : trialBits n k ≤ 3*P^4 := trialBits_le n k s
  have hq : 2*b+1 ≤ 2*(b+1) := by omega
  have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by omega)
  unfold sampleBits groupTrials timeBudget
  calc
    _ ≤ (2*(b+1))*(1024*P^3*4^a)*(3*P^4) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq (Nat.mul_le_mul_right (4^a)
        (Nat.mul_le_mul_left 1024 hpow))) ht
    _ = 6144*P^7*4^a*(b+1) := by ring
    _ ≤ 6144*2^k*P^7*4^a*(b+1) := by gcongr; omega
    _ = _ := by dsimp [P]; congr 4 <;> omega

end KoanaKPaths.Main

end

section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main



lemma wholeCost_budget (n : ℕ) (arcs : List (Fin n × Fin n)) (k a b : ℕ) (tape : List Bool) (hk : 1≤ k) :
    rootCost n arcs k a b tape+(HypergraphUnreliability.FPRAS.fracCode (tapeEstimate n arcs k a b tape)).length+2≤
      timeBudget 10000000000000000000000000000 20 k (n+(graphCode n arcs).length) a b := by
  let P := 1+k+n+(graphCode n arcs).length
  let E := 2^k
  let F := 4^a
  let Q := b+1
  have hP : 1≤ P := by dsimp [P]; omega
  have hE : 1≤ E := Nat.one_le_pow k 2 (by omega)
  have hF : 1≤ F := Nat.one_le_pow a 4 (by omega)
  have hQ : 1≤ Q := by dsimp [Q]; omega
  have hm : arcs.length≤ P := by have hh := arcs_length_le_graphCode arcs; dsimp [P]; omega
  have hbase : 1+n+k+arcs.length≤ P := by have hh := arcs_length_le_graphCode arcs; dsimp [P]; omega
  have hsmall : 1+n+k≤ P := by dsimp [P]; omega
  have hfront : Input.graphReadCost n arcs k a b≤16080*E*P*F*Q := by
    simpa [timeBudget,E,P,F,Q,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Input.graphReadCost_budget n arcs k a b
  have hS : sampleBits n k a b≤6144*E*P^7*F*Q := by
    simpa [timeBudget,E,P,F,Q,Nat.add_assoc] using sampleBits_le_budget n k a b (graphCode n arcs).length
  have hbig := cost_sum_bound E P F Q hE hP hF hQ
  have htarget : timeBudget 10000000000000000000000000000 20 k (n+(graphCode n arcs).length) a b=
      10000000000000000000000000000*E*P^20*F*Q := by simp [timeBudget,E,P,F,Q,Nat.add_assoc]
  rw [htarget]
  by_cases hz : n=0
  · have hout : (HypergraphUnreliability.FPRAS.fracCode (tapeEstimate n arcs k a b tape)).length=4 := by
      simp [tapeEstimate,hz,HypergraphUnreliability.FPRAS.fracCode,HypergraphUnreliability.FPRAS.natCode]
    rw [rootCost,if_pos hz,hout]
    omega
  · have hn : 1≤ n := by omega
    have hCtrl : (Controls.controlWidth n k a b arcs.length+1)^2≤1000*P^2*F*Q :=
      (Controls.controlWidth_square n k a b arcs.length).trans (by dsimp only [F,Q]; gcongr)
    have hL2 : (medianWidth n k a+1)^2≤11000*P^4*F :=
      (medianWidth_cost n k a).trans (by dsimp only [F]; gcongr)
    have hL : medianWidth n k a≤11000*P^4*F := by nlinarith
    have hLbig : 10030*medianWidth n k a≤110330000*P^4*F := by nlinarith
    have hSetup : Controls.setupCost n k a b arcs.length≤12000000000000*P^2*F*Q+
        10000*(sampleBits n k a b+arcs.length+medianWidth n k a+1) := by
      have hh := Controls.setupCost_bound n k a b arcs.length hn hk
      nlinarith
    have hEst : estimatorCost n k a b arcs.length≤10000000000000000000000000*E*P^14*F*Q :=
      (estimatorCost_polynomial n k a b arcs.length hk).trans (by dsimp only [E,F,Q]; gcongr)
    have hWrite := fraction_writtenCost arcs hk (tapeSamples n k a b tape)
    have hOut := fraction_code_length arcs hk (tapeSamples n k a b tape)
    rw [tapeEstimate,if_neg hz] at *
    rw [rootCost,if_neg hz,positiveCost]
    omega

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (n : Nat) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n))) (k a b : Nat) (tape : List.{0} Bool)
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (KoanaKPaths.Machine.Trial.rootCost n arcs k a b tape)
        (@List.length.{0} Bool
          (HypergraphUnreliability.FPRAS.fracCode (KoanaKPaths.Main.tapeEstimate n arcs k a b tape))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (KoanaKPaths.Main.timeBudget
      (@OfNat.ofNat.{0} Nat (nat_lit 10000000000000000000000000000)
        (instOfNatNat (nat_lit 10000000000000000000000000000)))
      (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) k
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@List.length.{0} Bool (KoanaKPaths.Main.graphCode n arcs)))
      a b) := by
  exact @KoanaKPaths.Machine.Trial.wholeCost_budget
