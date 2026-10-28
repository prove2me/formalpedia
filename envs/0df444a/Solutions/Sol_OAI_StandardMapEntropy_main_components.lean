-- Prove2me | solution 1 for OAI.StandardMapEntropy.main_components
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:41:44.872633+00:00
-- url     : https://prove2.me/submissions/ce488e1c-b000-44bd-9dc0-dfa6c32291d4

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_actual_cyclic_weakBernoulli_component_q44
import Theorems.Thm_OAI_StandardMapEntropy_actual_return_bernoulli_q44
import Theorems.Thm_OAI_StandardMapEntropy_eventually_meanDeficit_doubling_q44
import Theorems.Thm_OAI_StandardMapEntropy_no_critical_scale_sequence_q44

section
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

theorem measurePreserving_standardMap (k : ℝ) : MeasurePreserving (standardMap k) area area := by
  unfold area
  have hkick : MeasurePreserving
      (fun z : Torus => (z.1, z.2 + kick k z.1))
        ((volume : Measure Circle).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Circle)).skew_product
      (g := fun x y : Circle => y + kick k x) ?_ ?_
    · exact measurable_snd.add ((continuous_kick k).measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun x => map_add_right_eq_self volume (kick k x))
  convert (measurePreserving_add_prod (volume : Measure Circle) volume).comp hkick using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply, standardMap, kick]
  congr 1
  abel

lemma recurrenceCoordinates_involutive : Function.Involutive recurrenceCoordinates := by
  intro z
  apply Prod.ext <;> simp [recurrenceCoordinates]

lemma standardMap_conjugacy (k : ℝ) (z : Torus) :
    recurrenceCoordinates (standardMap k z) =
      recurrenceMap k (recurrenceCoordinates z) := by
  apply Prod.ext <;> simp only [recurrenceCoordinates, recurrenceMap, standardMap, kick, two_smul]
  · abel
  · abel

open scoped Matrix.Norms.Operator

open Filter
open scoped Topology

open Metric

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SegmentObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftShortfall_mem (k : ℝ) (hk : 0 ≤ k) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    liftShortfall k z a n ∈ Icc 0 1 := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < Real.log (growthBase k) := Real.log_pos hM
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨hlo,hhi⟩ := liftSegmentTransfer_norm_bounds k hk z a n
  have hlog0 : 0 ≤ Real.log ‖liftSegmentTransfer k z a n‖ := Real.log_nonneg hlo
  have hlog1 : Real.log ‖liftSegmentTransfer k z a n‖ ≤ (n:ℝ)*Real.log (growthBase k) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hhi
  unfold liftShortfall
  constructor
  · have := (div_le_one (mul_pos hnp hp)).mpr hlog1; linarith
  · have := div_nonneg hlog0 (mul_pos hnp hp).le; linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measurePreserving_recurrenceCoordinates : MeasurePreserving recurrenceCoordinates area area := by
  unfold area
  apply (MeasurePreserving.id (volume : Measure Circle)).skew_product
  · exact measurable_fst.sub measurable_snd
  · exact Eventually.of_forall fun x => (Measure.measurePreserving_sub_left (volume : Measure Circle) x).map_eq
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
lemma measurePreserving_torusStep_symm (k : ℝ) : MeasurePreserving (torusStep k).symm area area :=
  (measurePreserving_torusStep k).symm (torusStep_measurableEquiv k)
lemma measurePreserving_torusIter (k : ℝ) (i : ℤ) : MeasurePreserving (torusIter k i) area area := by
  cases i with
  | ofNat n =>
      change MeasurePreserving (torusIter k (n : ℤ)) area area
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (measurePreserving_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (measurePreserving_torusStep_symm k).iterate (n+1)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TorusObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_torusShortfall (k : ℝ) (hk : 0 ≤ k) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusShortfall k z a n) := by
  apply continuous_const.sub
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k a n).norm.log
    (fun z => by have := (torusSegmentTransfer_norm_bounds k hk z a n).1; linarith)
lemma torusShortfall_mem (k : ℝ) (hk : 0 ≤ k) (z : Torus) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    torusShortfall k z a n ∈ Icc 0 1 := by
  obtain ⟨w,rfl⟩ := liftProjection_surjective z
  rw [torusShortfall_lift]
  exact liftShortfall_mem k hk w a n hn
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CancellationTheorem
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma cancellationConstant_pos : 0 < cancellationConstant := by unfold cancellationConstant; positivity
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_DoublingPointwise
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma cancellationLoss_bounds (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    0 ≤ cancellationLoss k z n ∧ cancellationLoss k z n ≤ 2*(n:ℝ) := by
  have htri := productDistance_triangle k hk z (-(n:ℤ)) 0 (n:ℤ)
  rw [productDistance_symm k z (-(n:ℤ)) 0] at htri
  have hL := productDistance_le k hk z 0 (-(n:ℤ))
  have hR := productDistance_le k hk z 0 (n:ℤ)
  simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hL hR
  have hn := productDistance_nonneg k hk z (-(n:ℤ)) (n:ℤ)
  unfold cancellationLoss
  constructor  <;> linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanDeficit
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma integral_torusIter (k : ℝ) (a : ℤ) (f : Torus → ℝ) :
    (∫ z, f (torusIter k a z) ∂area)=∫ z, f z ∂area :=
  (measurePreserving_torusIter k a).integral_comp (torusIterMeasurableEquiv k a).measurableEmbedding f
lemma integrable_productDistance (k : ℝ) (hk : 0 ≤ k) (i j : ℤ) :
    Integrable (fun z => productDistance k z i j) area :=
  (continuous_productDistance k hk i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma integral_productDistance_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    0 ≤ (∫ z, productDistance k z 0 (n:ℤ) ∂area) ∧ (∫ z, productDistance k z 0 (n:ℤ) ∂area) ≤ (n:ℝ) := by
  refine ⟨integral_nonneg (fun z => productDistance_nonneg k hk z 0 (n:ℤ)),?_⟩
  have hh := integral_mono (integrable_productDistance k hk 0 (n:ℤ)) (integrable_const (n:ℝ)) (fun z => by simpa using productDistance_le k hk z 0 (n:ℤ))
  simpa only [Int.cast_natCast,Int.cast_zero,sub_zero,Nat.abs_cast,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using hh
lemma meanDeficit_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) : 0 ≤ meanDeficit k n ∧ meanDeficit k n ≤ 1 := by
  obtain ⟨h0,h1⟩ := integral_productDistance_bounds k hk n
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hdiv : (∫ z, productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ) ≤ 1 := (div_le_one hnp).mpr h1
  have hdiv0 := div_nonneg h0 hnp.le
  unfold meanDeficit; constructor <;> linarith
lemma integral_distance_shift (k : ℝ) (i j a : ℤ) :
    (∫ z,productDistance k z (i+a) (j+a) ∂area)=∫ z,productDistance k z i j ∂area := by
  calc
    _ = ∫ z,productDistance k (torusIter k a z) i j ∂area := by simp only [productDistance_shift]
    _ = _ := by convert! integral_torusIter k a (fun z => productDistance k z i j) using 1
lemma integral_wing_left (k : ℝ) (n : ℕ) :
    (∫ z, productDistance k z 0 (-(n:ℤ)) ∂area)=∫ z, productDistance k z 0 (n:ℤ) ∂area := by
  simp_rw [productDistance_symm k _ 0 (-(n:ℤ))]
  convert integral_distance_shift k 0 (n:ℤ) (-(n:ℤ)) using 1 ; simp
lemma integral_cancellationLoss (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    (∫ z,cancellationLoss k z n ∂area)=2*(n:ℝ)*(meanDeficit k (n+n)-meanDeficit k n) := by
  have hL := integrable_productDistance k hk 0 (-(n:ℤ))
  have hR := integrable_productDistance k hk 0 (n:ℤ)
  have hT := integrable_productDistance k hk (-(n:ℤ)) (n:ℤ)
  have ht : (∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area)=∫ z,productDistance k z 0 ((n+n:ℕ):ℤ) ∂area := by
    convert integral_distance_shift k 0 ((n+n:ℕ):ℤ) (-(n:ℤ)) using 1 ; push_cast ; ring_nf
  have hsum : (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ)) ∂area)+(∫ z,productDistance k z 0 (n:ℤ) ∂area) := by
    convert! integral_add hL hR using 1
    all_goals try with_reducible_and_instances rfl
  have hsub : (∫ z,cancellationLoss k z n ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)-(∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area) := by
    convert! integral_sub (hL.add hR) hT using 1
    all_goals try with_reducible_and_instances rfl
  rw [hsub,hsum,integral_wing_left,ht]
  unfold meanDeficit
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp [hn0]; ring
lemma meanDeficit_doubling_mono (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    meanDeficit k n ≤ meanDeficit k (n+n) := by
  have hh : 0 ≤ ∫ z,cancellationLoss k z n ∂area := integral_nonneg fun z => (cancellationLoss_bounds k hk z n).1
  rw [integral_cancellationLoss k hk n hn] at hh
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanCancellation
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma doublingConstant_pos : 0<doublingConstant := by
  unfold doublingConstant; nlinarith [cancellationConstant_pos]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MeanGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma meanLoss_nonneg (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : 0 ≤ meanLoss k n :=
  sub_nonneg.mpr (integral_productDistance_bounds k hk n).2
lemma meanLoss_eq (k : ℝ) (n : ℕ) : meanLoss k n=(n:ℝ)*meanDeficit k n := by
  cases n with
  | zero => simp [meanLoss,meanDeficit]
  | succ n => unfold meanLoss meanDeficit; field_simp
lemma meanLoss_superadditive (k : ℝ) (hk : 0 ≤ k) (n m : ℕ) :
    meanLoss k n+meanLoss k m ≤ meanLoss k (n+m) := by
  have hi := integral_mono (integrable_productDistance k hk 0 ((n+m:ℕ):ℤ))
    ((integrable_productDistance k hk 0 (n:ℤ)).add (integrable_productDistance k hk (n:ℤ) ((n+m:ℕ):ℤ)))
    (fun z => productDistance_triangle k hk z 0 (n:ℤ) ((n+m:ℕ):ℤ))
  have he : (∫ z,productDistance k z 0 (n:ℤ)+productDistance k z (n:ℤ) ((n+m:ℕ):ℤ) ∂area)=
      (∫ z,productDistance k z 0 (n:ℤ) ∂area)+(∫ z,productDistance k z 0 (m:ℤ) ∂area) := by
    rw [integral_add (integrable_productDistance k hk 0 _) (integrable_productDistance k hk _ _)]
    congr 1
    simpa only [zero_add,add_zero,Nat.cast_add,add_comm] using integral_distance_shift k 0 (m:ℤ) (n:ℤ)
  simp only [Pi.add_apply] at hi
  rw [he] at hi
  unfold meanLoss
  simp only [Nat.cast_add] at hi ⊢
  linarith
lemma meanLoss_mono (k : ℝ) (hk : 0 ≤ k) : Monotone (meanLoss k) := by
  intro n m hnm
  have hh := meanLoss_superadditive k hk n (m-n)
  rw [Nat.add_sub_of_le hnm] at hh
  linarith [meanLoss_nonneg k hk (m-n)]
lemma meanDeficit_comparison (k : ℝ) (hk : 0 ≤ k) (n m : ℕ) (hnm : n ≤ m) :
    (n:ℝ)*meanDeficit k n ≤ (m:ℝ)*meanDeficit k m := by
  simpa only [← meanLoss_eq] using meanLoss_mono k hk hnm
lemma meanDeficit_pow_mono (k : ℝ) (hk : 0 ≤ k) : Monotone (fun j : ℕ => meanDeficit k (2^j)) := by
  apply monotone_nat_of_le_succ
  intro j
  have hh := meanDeficit_doubling_mono k hk (2^j) (by positivity)
  simpa only [pow_succ,Nat.mul_two] using hh
lemma first_dyadic_crossing (k θ C : ℝ) (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p : ℕ) (hp : meanDeficit k (2^p) ≤ θ)
    (hex : ∃ q : ℕ, θ < meanDeficit k (2^q)) :
    ∃ q : ℕ, p < q ∧ θ < meanDeficit k (2^q) ∧
      (∀ j, j < q → meanDeficit k (2^j) ≤ θ) ∧
      meanDeficit k (2^q) ≤ C*θ+C/((2^p:ℕ):ℝ) := by
  let q := Nat.find hex
  have hq : θ < meanDeficit k (2^q) := Nat.find_spec hex
  have hprev (j : ℕ) (hj : j < q) : meanDeficit k (2^j) ≤ θ :=
    le_of_not_gt (Nat.find_min hex hj)
  have hpq : p < q := by
    by_contra h
    have hle := meanDeficit_pow_mono k hk (show q ≤ p by omega)
    linarith
  refine ⟨q,hpq,hq,hprev,?_⟩
  have hq0 : 0 < q := by omega
  have hm := hdouble (2^(q-1)) (by positivity)
  have he : 2^(q-1)+2^(q-1)=2^q := by
    rw [← Nat.mul_two,← pow_succ]
    congr 1; omega
  rw [he] at hm
  have hθ := mul_le_mul_of_nonneg_left (hprev (q-1) (by omega)) hC
  have hpow : ((2^p:ℕ):ℝ) ≤ ((2^(q-1):ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (show p ≤ q-1 by omega)
  have hd : C/((2^(q-1):ℕ):ℝ) ≤ C/((2^p:ℕ):ℝ) :=
    div_le_div_of_nonneg_left hC (by positivity) hpow
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CosineNull
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma countable_cosine_zero : Set.Countable {x : Circle | cosine x=0} := by
  apply (Set.countable_range (fun m : ℤ => (((2*(m:ℝ)+1)/4:ℝ) : Circle))).mono
  intro x hx
  obtain ⟨r,rfl⟩ := (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1:ℝ))) x
  change Real.cos (2*Real.pi*r)=0 at hx
  obtain ⟨m,hm⟩ := Real.cos_eq_zero_iff.mp hx
  refine ⟨m,?_⟩
  have he : r=(2*(m:ℝ)+1)/4 := by
    have hp := Real.pi_pos
    nlinarith
  rw [he]
lemma volume_cosine_zero : volume {x : Circle | cosine x=0}=0 := countable_cosine_zero.measure_zero volume
lemma cosine_small_measure (η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ volume {x : Circle | |cosine x|≤δ}<ENNReal.ofReal η := by
  let E : ℕ → Set Circle := fun n => {x | |cosine x|≤1/((n:ℝ)+1)}
  have hm : Antitone E := by
    intro i j hij x hx
    change |cosine x|≤1/((i:ℝ)+1)
    change |cosine x|≤1/((j:ℝ)+1) at hx
    exact hx.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1))
  have he : (⋂ n,E n)={x : Circle | cosine x=0} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,E]
    constructor
    · intro hx
      apply abs_eq_zero.mp
      by_contra hn
      have hp : 0 < |cosine x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hn)
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt hp
      exact (not_lt_of_ge (hx n)) hn
    · intro hx n; simp [hx]; positivity
  have ht := tendsto_measure_iInter_atTop
    (μ := (volume : Measure Circle)) (s := E)
    (fun n => ((isClosed_le continuous_cosine.abs continuous_const).measurableSet.nullMeasurableSet)) hm
    ⟨0,measure_ne_top _ _⟩
  rw [he,volume_cosine_zero] at ht
  have hh : ∀ᶠ n : ℕ in atTop, volume (E n)<ENNReal.ofReal η :=
    ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨n,hn⟩ := hh.exists
  refine ⟨1/((n:ℝ)+1),by positivity,?_,hn⟩
  exact (div_le_one (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ConeGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma transferStep_cone (v : ℝ) (B : ℝ) (hB : 2 ≤ B) (hv : B ≤ |v|) (z : ℂ)
    (hz : |z.im| ≤ |z.re|) :
    (B-1)*|z.re| ≤ |(transferStep v z).re| ∧ |(transferStep v z).im| ≤ |(transferStep v z).re| := by
  have htri := abs_sub_abs_le_abs_sub (v*z.re) z.im
  rw [abs_mul] at htri
  have hm := mul_le_mul_of_nonneg_right hv (abs_nonneg z.re)
  simp only [transferStep_re,transferStep_im]
  constructor <;> nlinarith [abs_nonneg z.re]
lemma transferProduct_cone (v : ℕ → ℝ) (B : ℝ) (hB : 2 ≤ B) (n : ℕ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → B ≤ |v i|) :
    (B-1)^n ≤ |(transferProduct v n 1).re| ∧ |(transferProduct v n 1).im| ≤ |(transferProduct v n 1).re| := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
      obtain ⟨hg,hc⟩ := ih (fun i hi hin => hv i hi (by omega))
      obtain ⟨h1,h2⟩ := transferStep_cone (v (n+1)) B hB (hv _ (by omega) le_rfl) (transferProduct v n 1) hc
      simp only [transferProduct,ContinuousLinearMap.comp_apply]
      refine ⟨?_,h2⟩
      rw [pow_succ]
      have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ B-1 by linarith)
      nlinarith
lemma transferProduct_norm_lower_of_coefficients (v : ℕ → ℝ) (B : ℝ) (hB : 2 ≤ B) (n : ℕ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → B ≤ |v i|) : (B-1)^n ≤ ‖transferProduct v n‖ := by
  calc
    _  ≤  |(transferProduct v n 1).re| := (transferProduct_cone v B hB n hv).1
    _  ≤  ‖transferProduct v n 1‖ := Complex.abs_re_le_norm _
    _  ≤  ‖transferProduct v n‖ := by simpa using (transferProduct v n).le_opNorm (1:ℂ)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FixedDeficit
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma integrable_cosineBad (δ : ℝ) : Integrable (cosineBad δ) volume :=
  (integrable_const _).indicator (isClosed_le continuous_cosine.abs continuous_const).measurableSet
lemma integral_cosineBad (δ : ℝ) : (∫ x,cosineBad δ x ∂volume)=(volume {x : Circle | |cosine x|≤δ}).toReal := by
  unfold cosineBad
  rw [integral_indicator (isClosed_le continuous_cosine.abs continuous_const).measurableSet]
  simp [Measure.real]
lemma circleFst_preserving : MeasurePreserving (Prod.fst : Torus → Circle) area volume :=
  measurePreserving_fst
lemma bad_time_integrable (k δ : ℝ) (i : ℤ) :
    Integrable (fun z => cosineBad δ (torusIter k i z).1) area :=
  (circleFst_preserving.comp (measurePreserving_torusIter k i)).integrable_comp_of_integrable (integrable_cosineBad δ)
lemma bad_time_integral (k δ : ℝ) (i : ℤ) :
    (∫ z,cosineBad δ (torusIter k i z).1 ∂area)=(volume {x : Circle | |cosine x|≤δ}).toReal := by
  calc
    _ = ∫ z,cosineBad δ z.1 ∂area := by
      convert! integral_torusIter k i (fun z => cosineBad δ z.1) using 1
      all_goals try with_reducible_and_instances rfl
    _ = _ := by rw [area,integral_fun_fst,integral_cosineBad]; simp
lemma potential_large_of_cosine (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (x : Circle) (hx : δ≤|cosine x|) :
    growthBase k*δ/2≤|torusPotential k x| := by
  have hK : 0≤2*Real.pi*k := by positivity
  have ht := abs_sub_abs_le_abs_sub ((2*Real.pi*k)*cosine x) (-2)
  rw [abs_mul,abs_of_nonneg hK] at ht
  have hm := mul_le_mul_of_nonneg_left hx hK
  have hMd : 12≤growthBase k*δ := (div_le_iff₀ hδ0).mp hM
  unfold torusPotential
  have hg : growthBase k=2*Real.pi*k+4 := rfl
  have he : (2*Real.pi*k)*cosine x-(-2)=2+(2*Real.pi*k)*cosine x := by ring
  rw [he] at ht
  norm_num at ht
  nlinarith
lemma shortfall_small_of_cosine (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) (z : Torus)
    (hgood : ∀ i∈Finset.range n, δ≤|cosine (torusIter k (i:ℤ) z).1|) :
    torusShortfall k z 0 n≤-Real.log (δ/4)/Real.log (growthBase k) := by
  have hMd : 12≤growthBase k*δ := (div_le_iff₀ hδ0).mp hM
  have hMp : 0<growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL : 0<Real.log (growthBase k) := log_growthBase_pos k hk
  have hg := transferProduct_norm_lower_of_coefficients (torusSegmentCoefficient k z 0)
    (growthBase k*δ/2) (by linarith) n (by
      intro i hi hin
      have hidx : (0:ℤ)+(i:ℤ)-1=((i-1:ℕ):ℤ) := by omega
      unfold torusSegmentCoefficient
      rw [hidx]
      exact potential_large_of_cosine k δ hk hδ0 hδ1 hM _ (hgood (i-1) (Finset.mem_range.mpr (by omega))))
  have hlower : (growthBase k*(δ/4))^n≤‖torusSegmentTransfer k z 0 n‖ := by
    apply (pow_le_pow_left₀ (by positivity : 0≤growthBase k*(δ/4)) (by nlinarith : growthBase k*(δ/4)≤growthBase k*δ/2-1) n).trans hg
  have hl := Real.log_le_log (show 0<(growthBase k*(δ/4))^n by positivity) hlower
  rw [Real.log_pow,Real.log_mul hMp.ne' (by positivity : δ/4≠0)] at hl
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn
  unfold torusShortfall
  apply (le_div_iff₀ hL).mpr
  have he : (1-Real.log ‖torusSegmentTransfer k z 0 n‖/((n:ℝ)*Real.log (growthBase k)))*Real.log (growthBase k)=
      Real.log (growthBase k)-Real.log ‖torusSegmentTransfer k z 0 n‖/(n:ℝ) := by field_simp
  rw [he]
  have hnd : Real.log (growthBase k)+Real.log (δ/4)≤Real.log ‖torusSegmentTransfer k z 0 n‖/(n:ℝ) := (le_div_iff₀ hnpos).mpr (by nlinarith [hl])
  nlinarith
lemma fixed_shortfall_pointwise (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) (z : Torus) :
    torusShortfall k z 0 n≤-Real.log (δ/4)/Real.log (growthBase k)+
      ∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1 := by
  have h0 (i : ℕ) : 0 ≤ cosineBad δ (torusIter k (i:ℤ) z).1 := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases hg : ∀ i∈Finset.range n, δ≤|cosine (torusIter k (i:ℤ) z).1|
  · exact (shortfall_small_of_cosine k δ hk hδ0 hδ1 hM n hn z hg).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi => h0 i)))
  · push Not at hg
    obtain ⟨i,hi,hbad⟩ := hg
    have h1 : cosineBad δ (torusIter k (i:ℤ) z).1=1 := by
      simp [cosineBad,le_of_lt hbad]
    have hs := Finset.single_le_sum (fun j _ => h0 j) hi
    rw [h1] at hs
    have hr : 0≤-Real.log (δ/4)/Real.log (growthBase k) :=
      div_nonneg (neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))) (log_growthBase_pos k hk).le
    have hsf := (torusShortfall_mem k hk z 0 n hn).2
    linarith
lemma meanDeficit_eq_integral_shortfall (k : ℝ) (hk : 0≤k) (n : ℕ) :
    meanDeficit k n=∫ z,torusShortfall k z 0 n ∂area := by
  have he (z : Torus) : torusShortfall k z 0 n=1-productDistance k z 0 (n:ℤ)/(n:ℝ) := by
    have hh := productDistance_forward k z 0 n
    simp only [zero_add] at hh
    rw [hh]
    unfold torusShortfall
    ring
  simp_rw [he]
  rw [integral_sub (integrable_const _) ((integrable_productDistance k hk 0 _).div_const _),integral_div]
  simp [meanDeficit]
lemma meanDeficit_fixed_bound (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) :
    meanDeficit k n≤-Real.log (δ/4)/Real.log (growthBase k)+
      (n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal := by
  rw [meanDeficit_eq_integral_shortfall k hk n]
  have hi : Integrable (fun z => torusShortfall k z 0 n) area :=
    (continuous_torusShortfall k hk 0 n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun z => ∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1) area :=
    integrable_finsetSum _ (fun i hi => bad_time_integrable k δ (i:ℤ))
  have hb := integral_mono hi ((integrable_const _).add hs) (fixed_shortfall_pointwise k δ hk hδ0 hδ1 hM n hn)
  have he : (∫ z,-Real.log (δ/4)/Real.log (growthBase k)+∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1 ∂area)=
      -Real.log (δ/4)/Real.log (growthBase k)+(n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal := by
    rw [integral_add (integrable_const _) hs]
    have he := integral_finsetSum (Finset.range n) (fun (i : ℕ) _ => bad_time_integrable k δ (i:ℤ))
    rw [he]
    simp [bad_time_integral]
  exact he ▸ hb
lemma meanDeficit_fixed_small (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0≤k → M₀≤growthBase k → meanDeficit k n≤ε := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨δ,hδ0,hδ1,hδm⟩ := cosine_small_measure (ε/(2*(n:ℝ))) (by positivity)
  let C := -Real.log (δ/4)
  have hC : 0≤C := neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  refine ⟨max (12/δ) (Real.exp (2*C/ε+1)),?_⟩
  intro k hk hM
  have hMd : 12/δ≤growthBase k := (le_max_left _ _).trans hM
  have hMe : Real.exp (2*C/ε+1)≤growthBase k := (le_max_right _ _).trans hM
  have hlog := Real.log_le_log (Real.exp_pos _) hMe
  rw [Real.log_exp] at hlog
  have hr : C/Real.log (growthBase k)≤ε/2 := by
    apply (div_le_iff₀ (log_growthBase_pos k hk)).mpr
    have hm := mul_le_mul_of_nonneg_left hlog (show 0≤ε/2 by positivity)
    have he : (ε/2)*(2*C/ε+1)=C+ε/2 := by field_simp
    rw [he] at hm
    linarith
  have hv := ENNReal.toReal_lt_of_lt_ofReal hδm
  have hnv : (n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal<ε/2 := by
    have hh := (lt_div_iff₀ (show 0<2*(n:ℝ) by positivity)).mp hv
    nlinarith
  have hb := meanDeficit_fixed_bound k δ hk hδ0 hδ1 hMd n hn
  change meanDeficit k n≤C/Real.log (growthBase k)+(n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal at hb
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalScales
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma exists_dyadic_ceiling (n : ℕ) (hn : 0 < n) : ∃ q : ℕ, n ≤ 2^q ∧ 2^q < 2*n := by
  have hx : ∃ q : ℕ, n ≤ 2^q := ⟨n,by
    have hh := (Nat.lt_two_pow_self (n := n))
    omega⟩
  let q := Nat.find hx
  have hl : n ≤ 2^q := Nat.find_spec hx
  refine ⟨q,hl,?_⟩
  by_cases hq : q=0
  · simp only [hq,pow_zero]; omega
  · have hp : 2^(q-1) < n := lt_of_not_ge (Nat.find_min hx (show q-1 < q by omega))
    have he : 2^q=2^(q-1)*2 := by rw [← pow_succ]; congr 1; omega
    rw [he]; omega
lemma positive_deficit_dyadic (k η : ℝ) (hk : 0 ≤ k) (hη : 0 < η)
    (hex : ∃ n : ℕ, 0 < n ∧ η ≤ meanDeficit k n) :
    ∃ q : ℕ, η/2 < meanDeficit k (2^q) := by
  obtain ⟨n,hn,hnη⟩ := hex
  obtain ⟨q,hq,hq2⟩ := exists_dyadic_ceiling n hn
  have hh := meanDeficit_comparison k hk n (2^q) hq
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hqR : ((2^q:ℕ):ℝ) < 2*(n:ℝ) := by exact_mod_cast hq2
  have hp : (0:ℝ) < (2^q:ℕ) := by positivity
  have he : 0 ≤ meanDeficit k (2^q) := (meanDeficit_bounds k hk _ (by positivity)).1
  refine ⟨q,?_⟩
  nlinarith
lemma meanDeficit_iterated_doubling (k C : ℝ) (hk : 0 ≤ k) (hC : 1 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p m : ℕ) :
    meanDeficit k (2^(p+m)) ≤ (2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)) := by
  have hp : (0:ℝ) < (2^p:ℕ) := by positivity
  have he0 := (meanDeficit_bounds k hk (2^p) (by positivity)).1
  induction m with
  | zero => simp only [Nat.add_zero,pow_zero,one_mul]; linarith [one_div_nonneg.mpr hp.le]
  | succ m ih =>
    have hh := hdouble (2^(p+m)) (by positivity)
    rw [show 2^(p+(m+1))=2^(p+m)+2^(p+m) by rw [show p+(m+1)=(p+m)+1 by omega,pow_succ,Nat.mul_two]]
    have hpM : ((2^p:ℕ):ℝ) ≤ ((2^(p+m):ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : p ≤ p+m)
    have hd : C/((2^(p+m):ℕ):ℝ) ≤ C/((2^p:ℕ):ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hp hpM
    have hpow : (1:ℝ) ≤ (2*C)^m := one_le_pow₀ (by linarith)
    have ht := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ C)
    rw [pow_succ]
    have hz : 0 ≤ 1/((2^p:ℕ):ℝ) := by positivity
    have hB : 1/((2^p:ℕ):ℝ) ≤ (2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)) := by nlinarith
    have hhB := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ C)
    calc
      _ ≤ C*meanDeficit k (2^(p+m))+C/((2^(p+m):ℕ):ℝ) := hh
      _ ≤ C*((2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)))+C/((2^p:ℕ):ℝ) := add_le_add ht hd
      _ ≤ _ := by simp only [div_eq_mul_inv] at hhB ⊢; nlinarith

lemma critical_scale_finite (k C θ : ℝ) (hk : 0 ≤ k) (hC : 1 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p : ℕ) (hp : meanDeficit k (2^p) ≤ θ^2) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hex : ∃ q : ℕ, θ < meanDeficit k (2^q)) :
    ∃ q : ℕ, p < q ∧ θ < meanDeficit k (2^q) ∧
      meanDeficit k (2^q) ≤ C*θ+C/((2^p:ℕ):ℝ) ∧
      (∀ m : ℕ, meanDeficit k (2^(p+m)) ≤ (2*C)^m*(θ^2+1/((2^p:ℕ):ℝ))) ∧
      (∀ m : ℕ, meanDeficit k (2^(q+m)) ≤ (2*C)^m*(meanDeficit k (2^q)+1/((2^p:ℕ):ℝ))) := by
  obtain ⟨q,hpq,hq,hprev,hup⟩ := first_dyadic_crossing k θ C hk (by linarith) hdouble p (by nlinarith) hex
  refine ⟨q,hpq,hq,hup,?_,?_⟩
  · intro m
    exact (meanDeficit_iterated_doubling k C hk hC hdouble p m).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  · intro m
    have hpqR : ((2^p:ℕ):ℝ) ≤ ((2^q:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hpq.le
    have hd : 1/((2^q:ℕ):ℝ) ≤ 1/((2^p:ℕ):ℝ) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpqR
    exact (meanDeficit_iterated_doubling k C hk hC hdouble q m).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalSequence
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology Classical
namespace StandardMapEntropy
lemma doublingConstant_ge_one : 1 ≤ doublingConstant := by
  unfold doublingConstant
  linarith [cancellationConstant_pos]

lemma badGrowth_arbitrarily_large (η : ℝ)
    (hbad : ¬ ∃ K : ℝ, ∀ k : ℝ, K≤k → ∀ n : ℕ, 0<n → meanDeficit k n < η) :
    ∀ K : ℝ, ∃ k : ℝ, K≤k ∧ BadGrowth η k := by
  push Not at hbad
  exact hbad

lemma choose_critical_parameter (η θ : ℝ) (hη : 0<η) (hθ : 0<θ) (hθ1 : θ<1)
    (hθη : θ<η/2) (p : ℕ) (R : ℝ)
    (hbad : ∀ K : ℝ, ∃ k : ℝ, K≤k ∧ BadGrowth η k) :
    ∃ k : ℝ, ∃ q : ℕ, 0<k ∧ R≤k ∧ p<q ∧ meanDeficit k (2^p)≤θ^2 ∧
      θ < meanDeficit k (2^q) ∧ meanDeficit k (2^q)≤doublingConstant*θ+doublingConstant/((2^p:ℕ):ℝ) ∧
      (∀ m : ℕ, meanDeficit k (2^(p+m))≤(2*doublingConstant)^m*(θ^2+1/((2^p:ℕ):ℝ))) ∧
      (∀ m : ℕ, meanDeficit k (2^(q+m))≤(2*doublingConstant)^m*(meanDeficit k (2^q)+1/((2^p:ℕ):ℝ))) := by
  obtain ⟨M₀,hM₀⟩ := eventually_meanDeficit_doubling_q44
  obtain ⟨M₁,hM₁⟩ := meanDeficit_fixed_small (2^p) (by positivity) (θ^2) (sq_pos_of_pos hθ)
  let A := max M₀ M₁
  obtain ⟨k,hk,hbadk⟩ := hbad (max (max R 1) ((A-4)/(2*Real.pi)))
  have hk0 : 0<k := lt_of_lt_of_le (by norm_num) ((le_max_right R 1).trans ((le_max_left _ _).trans hk))
  have hkR : R≤k := (le_max_left R 1).trans ((le_max_left _ _).trans hk)
  have hKA : A≤growthBase k := by
    have hh := (le_max_right (max R 1) ((A-4)/(2*Real.pi))).trans hk
    have hpi : 0<2*Real.pi := by positivity
    have he := (div_le_iff₀ hpi).mp hh
    unfold growthBase
    nlinarith
  have hsmall := hM₁ k hk0.le ((le_max_right M₀ M₁).trans hKA)
  have hdouble := fun n hn => (hM₀ k hk0 ((le_max_left M₀ M₁).trans hKA) n hn).2
  have hex : ∃ q : ℕ, θ < meanDeficit k (2^q) := by
    obtain ⟨q,hq⟩ := positive_deficit_dyadic k η hk0.le hη hbadk
    exact ⟨q,hθη.trans hq⟩
  obtain ⟨q,hpq,hq,hup,hlo,hhi⟩ := critical_scale_finite k doublingConstant θ hk0.le doublingConstant_ge_one hdouble p hsmall hθ hθ1 hex
  exact ⟨k,q,hk0,hkR,hpq,hsmall,hq,hup,hlo,hhi⟩

lemma criticalTheta_pos (r i : ℕ) : 0 < criticalTheta r i := by unfold criticalTheta; positivity
lemma criticalTheta_lt_one (r i : ℕ) : criticalTheta r i < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
lemma criticalTheta_square (r i : ℕ) :
    1/((2^(criticalLowerExponent r i):ℕ):ℝ)=(criticalTheta r i)^2 := by
  unfold criticalLowerExponent criticalTheta
  push_cast
  simp only [div_pow,one_pow,← pow_mul]
  rw [Nat.mul_comm 2]
lemma exists_critical_scale_sequence (η : ℝ) (hη : 0<η)
    (hbad : ∀ K : ℝ, ∃ k : ℝ, K≤k ∧ BadGrowth η k) : Nonempty CriticalScaleSequence := by
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show 0<η/2 by positivity) (by norm_num : (1/2:ℝ)<1)
  have htη (i : ℕ) : criticalTheta r i < η/2 := by
    apply lt_of_le_of_lt _ hr
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hx (i : ℕ) := choose_critical_parameter η (criticalTheta r i) hη (criticalTheta_pos r i)
    (criticalTheta_lt_one r i) (htη i) (criticalLowerExponent r i) (i:ℝ) hbad
  choose k q hk hkR hpq hsmall hq hqU hlo hhi using hx
  refine ⟨⟨r,k,q,hk,hkR,hpq,hq,?_,?_,?_⟩⟩
  · intro i
    have hh := hqU i
    rw [show doublingConstant/((2^(criticalLowerExponent r i):ℕ):ℝ)=
      doublingConstant*(1/((2^(criticalLowerExponent r i):ℕ):ℝ)) by ring,criticalTheta_square] at hh
    have ht := criticalTheta_pos r i
    have ht1 := criticalTheta_lt_one r i
    have hmul := mul_le_mul_of_nonneg_left (show (criticalTheta r i)^2 ≤ criticalTheta r i by nlinarith) doublingConstant_pos.le
    nlinarith
  · intro i m
    have hh := hlo i m
    rw [criticalTheta_square] at hh
    nlinarith
  · intro i m
    have hh := hhi i m
    rw [criticalTheta_square] at hh
    have ht := criticalTheta_pos r i
    have ht1 := criticalTheta_lt_one r i
    have ht2 : (criticalTheta r i)^2 ≤ meanDeficit (k i) (2^(q i)) := by nlinarith [hq i]
    have hp : 0 ≤ (2*doublingConstant)^m := pow_nonneg (mul_nonneg (by norm_num) doublingConstant_pos.le) _
    nlinarith [mul_le_mul_of_nonneg_left ht2 hp]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_NoCriticalSequence
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy

theorem eventually_meanDeficit_small (η:ℝ) (hη:0<η) :
    ∃K:ℝ,0<K ∧ ∀k:ℝ,K≤k → ∀n:ℕ,0<n → meanDeficit k n<η := by
  have hex:∃K:ℝ,∀k:ℝ,K≤k → ∀n:ℕ,0<n → meanDeficit k n<η := by
    by_contra h
    obtain ⟨S⟩:=exists_critical_scale_sequence η hη (badGrowth_arbitrarily_large η h)
    exact no_critical_scale_sequence_q44 S
  obtain ⟨K,hK⟩:=hex
  exact ⟨max K 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),fun k hk=>hK k ((le_max_left _ _).trans hk)⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Subadditive
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace BoundedSubadditive

variable {X : Type*}

lemma excess_nonneg (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    0 ≤ excess T h δ n x := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma excess_succ_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    excess T h δ n x ≤ excess T h δ (n + 1) x := by
  induction n generalizing x with
  | zero => exact excess_nonneg T h δ 1 x
  | succ n ih =>
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma excess_mono (T : X → X) (h : X → ℝ) (δ : ℝ) (x : X) :
    Monotone (fun n => excess T h δ n x) :=
  monotone_nat_of_le_succ (fun n => excess_succ_mono T h δ n x)

lemma sum_sub_le_excess (T : X → X) (h : X → ℝ) (δ : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T h n x - (n : ℝ) * δ ≤ excess T h δ n x := by
  induction n generalizing x with
  | zero => simp [birkhoffSum, excess]
  | succ n ih =>
    rw [birkhoffSum_succ']
    have hm : h x - δ + excess T h δ n (T x) ≤ excess T h δ (n + 1) x :=
      le_max_right _ _
    have hi := ih (T x)
    push_cast
    linarith

lemma excess_account (T : X → X) (h : X → ℝ) (δ : ℝ)
    (hh : ∀ x, 0 ≤ h x) (n : ℕ) (x : X) :
    (if 0 < excess T h δ (n + 1) x then δ else 0) ≤
      h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x := by
  split_ifs with hp
  · have he : excess T h δ (n + 1) x = h x - δ + excess T h δ n (T x) := by
      apply max_eq_right
      change 0 < max 0 (h x - δ + excess T h δ n (T x)) at hp
      exact (lt_max_iff.mp hp).resolve_left (lt_irrefl 0) |>.le
    rw [he]
    linarith [excess_succ_mono T h δ n (T x)]
  · have he : excess T h δ (n + 1) x = 0 :=
      le_antisymm (not_lt.mp hp) (excess_nonneg T h δ _ x)
    rw [he]
    linarith [hh x, excess_nonneg T h δ (n + 1) (T x)]

section Measure
variable [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {T : X → X} {h : X → ℝ} {δ : ℝ}

lemma measurable_excess (hT : Measurable T) (hh : Measurable h) (n : ℕ) :
    Measurable (excess T h δ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max ((hh.sub measurable_const).add (ih.comp hT))

lemma integrable_excess (hT : MeasurePreserving T μ μ) (hh : Integrable h μ) (n : ℕ) :
    Integrable (excess T h δ n) μ := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (integrable_const (0 : ℝ)).sup
      ((hh.sub (integrable_const δ)).add (hT.integrable_comp_of_integrable ih))

omit [IsFiniteMeasure μ] in
lemma integral_comp (hT : MeasurePreserving T μ μ) {g : X → ℝ}
    (hg : AEStronglyMeasurable g μ) : (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hg' : AEStronglyMeasurable g (Measure.map T μ) := by rwa [hT.map_eq]
  simpa only [hT.map_eq] using (integral_map hT.measurable.aemeasurable hg').symm

lemma excess_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) (n : ℕ) :
    μ {x | 0 < excess T h δ n x} ≤ ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  cases n with
  | zero => simp [excess]
  | succ n =>
    let s : Set X := {x | 0 < excess T h δ (n + 1) x}
    have hs : MeasurableSet s := measurableSet_lt measurable_const
      (measurable_excess hT.measurable hm _)
    have he := integrable_excess (δ := δ) hT hi (n + 1)
    have heT : Integrable (fun x => excess T h δ (n + 1) (T x)) μ :=
      hT.integrable_comp_of_integrable he
    have hb : (∫ x, s.indicator (fun _ => δ) x ∂μ) ≤
        ∫ x, h x + excess T h δ (n + 1) (T x) - excess T h δ (n + 1) x ∂μ := by
      apply integral_mono ((integrable_const δ).indicator hs)
        ((hi.add heT).sub he)
      intro x
      simpa only [Set.indicator, s, Set.mem_ofPred_eq, Pi.sub_apply, Pi.add_apply, Function.comp_apply] using excess_account T h δ h0 n x
    have hsub := integral_sub (hi.add heT) he
    have hadd := integral_add hi heT
    simp only [Pi.add_apply] at hsub hadd
    rw [integral_indicator_const δ hs, hsub, hadd,
      integral_comp hT he.aestronglyMeasurable] at hb
    have hb' : μ.real s ≤ (∫ x, h x ∂μ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      simpa only [smul_eq_mul, add_sub_cancel_right] using hb
    calc
      μ s = ENNReal.ofReal (μ.real s) := (ENNReal.ofReal_toReal (measure_ne_top μ s)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb'

lemma maximal_measure_bound (hT : MeasurePreserving T μ μ) (hm : Measurable h)
    (hi : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) (hδ : 0 < δ) :
    μ {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ≤
      ENNReal.ofReal ((∫ x, h x ∂μ) / δ) := by
  have hsub : {x | ∃ n : ℕ, (n : ℝ) * δ < birkhoffSum T h n x} ⊆
      ⋃ n : ℕ, {x | 0 < excess T h δ n x} := by
    rintro x ⟨n, hn⟩
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    exact lt_of_lt_of_le (sub_pos.mpr hn) (sum_sub_le_excess T h δ n x)
  refine (measure_mono hsub).trans ?_
  have hm' : Monotone (fun n : ℕ => {x | 0 < excess T h δ n x}) := by
    intro m n hmn x hx
    exact lt_of_lt_of_le hx (excess_mono T h δ x hmn)
  rw [hm'.measure_iUnion]
  exact iSup_le (fun n => excess_measure_bound hT hm hi h0 hδ n)

end Measure

namespace Cocycle
variable [MeasurableSpace X] {T : X → X} (f : Cocycle X T)

lemma average_bounds (n : ℕ) (x : X) : 0 ≤ f.average n x ∧ f.average n x ≤ 1 := by
  refine ⟨div_nonneg (f.nonneg n x) (Nat.cast_nonneg n), ?_⟩
  by_cases hn : n = 0
  · simp [average, hn]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr (f.le_time n x)

lemma average_bdd_above (x : X) : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨1, fun n => (f.average_bounds n x).2⟩

lemma average_bdd_below (x : X) : IsBoundedUnder (· ≥ ·) atTop (fun n => f.average n x) :=
  isBoundedUnder_of ⟨0, fun n => (f.average_bounds n x).1⟩

lemma lowerRate_bounds (x : X) : 0 ≤ f.lowerRate x ∧ f.lowerRate x ≤ 1 := by
  constructor
  · exact le_liminf_of_le (f.average_bdd_above x).isCoboundedUnder_ge
      (Eventually.of_forall fun n => (f.average_bounds n x).1)
  · have hh := liminf_le_liminf (Eventually.of_forall fun n => (f.average_bounds n x).2)
      (f.average_bdd_below x) (isBoundedUnder_const.isCoboundedUnder_ge)
    simpa only [liminf_const, lowerRate] using hh

lemma measurable_average (n : ℕ) : Measurable (f.average n) :=
  (f.measurable n).div_const _

lemma measurable_lowerRate : Measurable f.lowerRate :=
  Measurable.liminf (fun n => f.measurable_average n)

lemma average_shift_bound (n : ℕ) (x : X) :
    |f.average n (T x) - f.average n x| ≤ 2 / (n : ℝ) := by
  rw [average, average, ← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)]
  exact div_le_div_of_nonneg_right (f.shift_bound n x) (Nat.cast_nonneg n)

lemma lowerRate_shift (x : X) : f.lowerRate (T x) = f.lowerRate x := by
  have hc : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have haux (a b : X) (hab : ∀ n, f.average n a - f.average n b ≤ 2 / (n : ℝ)) :
      f.lowerRate a ≤ f.lowerRate b := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have he : ∀ᶠ n : ℕ in atTop, f.average n a ≤ f.average n b + ε := by
      filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
      linarith [hab n]
    have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => f.average n b + ε) :=
      isBoundedUnder_of ⟨1 + ε, fun n => add_le_add (f.average_bounds n b).2 le_rfl⟩
    have hh := liminf_le_liminf he (f.average_bdd_below a) hb.isCoboundedUnder_ge
    rw [liminf_add_const atTop (fun n => f.average n b) ε
      (f.average_bdd_above b).isCoboundedUnder_ge (f.average_bdd_below b)] at hh
    exact hh
  apply le_antisymm
  · exact haux (T x) x (fun n => (abs_le.mp (f.average_shift_bound n x)).2)
  · apply haux x (T x)
    intro n
    have hh := (abs_le.mp (f.average_shift_bound n x)).1
    linarith

lemma lowerRate_iterate (n : ℕ) (x : X) : f.lowerRate (T^[n] x) = f.lowerRate x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', f.lowerRate_shift, ih]

lemma measurableSet_badSet (ε : ℝ) (N : ℕ) : MeasurableSet (f.badSet ε N) := by
  apply MeasurableSet.compl
  apply MeasurableSet.biUnion (Set.to_countable _)
  intro n hn
  exact measurableSet_le (f.measurable n)
    (measurable_const.mul (f.measurable_lowerRate.add_const ε))

lemma measurable_badObservation (ε : ℝ) (N : ℕ) : Measurable (f.badObservation ε N) :=
  measurable_const.indicator (f.measurableSet_badSet ε N)

lemma badObservation_bounds (ε : ℝ) (N : ℕ) (x : X) :
    0 ≤ f.badObservation ε N x ∧ f.badObservation ε N x ≤ 1 := by
  classical
  by_cases hx : x ∈ f.badSet ε N <;> simp [badObservation, hx]

lemma exists_good_block (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) := by
  have hh : ∃ᶠ n : ℕ in atTop, f.average n x < f.lowerRate x + ε :=
    frequently_lt_of_liminf_lt (f.average_bdd_above x).isCoboundedUnder_ge (lt_add_of_pos_right _ hε)
  obtain ⟨n, hn, he⟩ := frequently_atTop.mp hh 1
  have hn' : 0 < n := by omega
  refine ⟨n, hn', ?_⟩
  have hi := (div_lt_iff₀ (Nat.cast_pos.mpr hn')).mp he
  nlinarith

lemma badObservation_tendsto_zero (x : X) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => f.badObservation ε N x) atTop (𝓝 0) := by
  obtain ⟨n, hn, hg⟩ := f.exists_good_block x ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with N hN
  symm
  apply Set.indicator_of_notMem
  simp only [badSet, mem_compl_iff, mem_iUnion, mem_ofPred_eq, not_not]
  exact ⟨n, ⟨hn, hN⟩, hg⟩

lemma birkhoff_bad_nonneg (ε : ℝ) (N n : ℕ) (x : X) :
    0 ≤ birkhoffSum T (f.badObservation ε N) n x := by
  exact Finset.sum_nonneg fun i hi => (f.badObservation_bounds ε N (T^[i] x)).1

lemma block_bound (ε : ℝ) (hε : 0 ≤ ε) (N n : ℕ) (x : X) :
    f.value n x ≤ (n : ℝ) * (f.lowerRate x + ε) +
      birkhoffSum T (f.badObservation ε N) n x + (N : ℝ) := by
  classical
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    have ha : 0 ≤ f.lowerRate x + ε := add_nonneg (f.lowerRate_bounds x).1 hε
    by_cases hn : n ≤ N
    · have hcast : (n : ℝ) ≤ N := by exact_mod_cast hn
      have hp := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) ha
      linarith [f.le_time n x, f.birkhoff_bad_nonneg ε N n x]
    · by_cases hx : x ∈ f.badSet ε N
      · have hn0 : 1 ≤ n := by omega
        have he : 1 + (n - 1) = n := by omega
        have hs := f.subadd 1 (n - 1) x
        simp only [he, Function.iterate_one] at hs
        have hi := ih (n - 1) (by omega) (T x)
        rw [f.lowerRate_shift] at hi
        rw [Nat.cast_sub hn0, Nat.cast_one, sub_mul, one_mul] at hi
        have hb : f.badObservation ε N x = 1 := by simp [badObservation, hx]
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            1 + birkhoffSum T (f.badObservation ε N) (n - 1) (T x) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [birkhoffSum_succ', hb]
        rw [hsum]
        have h1 := f.le_time 1 x
        norm_num only [Nat.cast_one] at h1
        linarith
      · have hg : x ∈ ⋃ m ∈ Set.Ioc 0 N,
            {y | f.value m y ≤ (m : ℝ) * (f.lowerRate y + ε)} := not_not.mp hx
        obtain ⟨m, hgm⟩ := mem_iUnion.mp hg
        obtain ⟨hm, hfm⟩ := mem_iUnion.mp hgm
        have hmn : m ≤ n := by have := hm.2; omega
        have he : m + (n - m) = n := Nat.add_sub_of_le hmn
        have hs := f.subadd m (n - m) x
        rw [he] at hs
        have hi := ih (n - m) (by have := hm.1; omega) (T^[m] x)
        rw [f.lowerRate_iterate, Nat.cast_sub hmn, sub_mul] at hi
        have hsum : birkhoffSum T (f.badObservation ε N) n x =
            birkhoffSum T (f.badObservation ε N) m x +
              birkhoffSum T (f.badObservation ε N) (n - m) (T^[m] x) := by
          simpa only [he] using birkhoffSum_add T (f.badObservation ε N) m (n - m) x
        rw [hsum]
        have hp := f.birkhoff_bad_nonneg ε N m x
        change f.value m x ≤ (m : ℝ) * (f.lowerRate x + ε) at hfm
        linarith

lemma upperRate_le_of_bad_averages (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (δ : ℝ) (x : X)
    (hb : ∀ n, birkhoffSum T (f.badObservation ε N) n x ≤ (n : ℝ) * δ) :
    f.upperRate x ≤ f.lowerRate x + ε + δ := by
  apply le_of_forall_pos_le_add
  intro γ hγ
  have hc : Tendsto (fun n : ℕ => (N : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply limsup_le_of_le (f.average_bdd_below x).isCoboundedUnder_le
  filter_upwards [hc.eventually (gt_mem_nhds hγ), eventually_gt_atTop 0] with n hsmall hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hN := (div_lt_iff₀ hn').mp hsmall
  apply (div_le_iff₀ hn').mpr
  have hB := f.block_bound ε hε N n x
  have hbad := hb n
  nlinarith

section Measure
variable {μ : Measure X} [IsFiniteMeasure μ]

lemma integrable_badObservation (ε : ℝ) (N : ℕ) :
    Integrable (f.badObservation ε N) μ :=
  (integrable_const (1 : ℝ)).indicator (f.measurableSet_badSet ε N)

lemma integral_badObservation_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => ∫ x, f.badObservation ε N x ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1 : ℝ))
    (fun N => (f.measurable_badObservation ε N).aestronglyMeasurable)
    (integrable_const 1)
    (fun N => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.badObservation_bounds ε N x).1]
      exact (f.badObservation_bounds ε N x).2)
    (Eventually.of_forall fun x => f.badObservation_tendsto_zero x ε hε)
  simpa only [integral_zero] using hh

lemma ae_upperRate_le_add (hT : MeasurePreserving T μ μ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ x ∂μ, f.upperRate x ≤ f.lowerRate x + 2 * ε := by
  let E : Set X := {x | f.lowerRate x + 2 * ε < f.upperRate x}
  have hbound (N : ℕ) : μ E ≤
      ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε) := by
    have hsub : E ⊆ {x | ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x} := by
      intro x hx
      by_contra hn
      change ¬ ∃ n : ℕ, (n : ℝ) * ε < birkhoffSum T (f.badObservation ε N) n x at hn
      push Not at hn
      have hh := f.upperRate_le_of_bad_averages ε hε.le N ε x hn
      change f.lowerRate x + 2 * ε < f.upperRate x at hx
      linarith
    exact (measure_mono hsub).trans
      (maximal_measure_bound hT (f.measurable_badObservation ε N)
        (f.integrable_badObservation ε N) (fun x => (f.badObservation_bounds ε N x).1) hε)
  have hc : Tendsto (fun N => ENNReal.ofReal ((∫ x, f.badObservation ε N x ∂μ) / ε))
      atTop (𝓝 0) := by
    have hh := (f.integral_badObservation_tendsto_zero (μ := μ) ε hε).div_const ε
    simpa only [Function.comp_def, zero_div, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hzero : μ E = 0 := le_antisymm (ge_of_tendsto' hc hbound) zero_le
  simpa only [ae_iff, not_le] using hzero

theorem ae_tendsto_average (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f.average n x) atTop (𝓝 (f.lowerRate x)) := by
  have ha : ∀ᵐ x ∂μ, ∀ j : ℕ, f.upperRate x ≤ f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)) := by
    apply ae_all_iff.mpr
    intro j
    exact f.ae_upperRate_le_add hT _ (by positivity)
  filter_upwards [ha] with x hx
  have hc : Tendsto (fun j : ℕ => f.lowerRate x + 2 * (1 / ((j : ℝ) + 1)))
      atTop (𝓝 (f.lowerRate x)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hu : f.upperRate x ≤ f.lowerRate x := ge_of_tendsto' hc hx
  exact tendsto_of_le_liminf_of_limsup_le le_rfl hu
    (f.average_bdd_above x) (f.average_bdd_below x)

lemma integrable_lowerRate : Integrable f.lowerRate μ :=
  (integrable_const (1 : ℝ)).mono' f.measurable_lowerRate.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.lowerRate_bounds x).1]
      exact (f.lowerRate_bounds x).2)

theorem tendsto_integral_average (hT : MeasurePreserving T μ μ) :
    Tendsto (fun n => ∫ x, f.average n x ∂μ) atTop (𝓝 (∫ x, f.lowerRate x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ))
    (fun n => (f.measurable_average n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (f.average_bounds n x).1]
      exact (f.average_bounds n x).2)
    (f.ae_tendsto_average hT)

end Measure
end Cocycle
end BoundedSubadditive

namespace StandardMapEntropy
open BoundedSubadditive

lemma lognorm_average_eq (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (z : Torus) :
    Real.log ‖torusSegmentTransfer k z 0 n‖ / (n : ℝ) =
      Real.log (growthBase k) * (transferCocycle k hk).average n z := by
  change _ = Real.log (growthBase k) * (productDistance k z 0 (n : ℤ) / (n : ℝ))
  have hf : productDistance k z 0 (n : ℤ) =
      Real.log ‖torusSegmentTransfer k z 0 n‖ / Real.log (growthBase k) := by
    simpa only [zero_add] using productDistance_forward k z 0 n
  rw [hf]
  have hlog := (log_growthBase_pos k hk).ne'
  calc
    _ = (Real.log (growthBase k) * (Real.log ‖torusSegmentTransfer k z 0 n‖ /
        Real.log (growthBase k))) / (n : ℝ) := by rw [mul_div_cancel₀ _ hlog]
    _ = _ := by ring

lemma transferLyapunov_limit (k : ℝ) (hk : 0 ≤ k) :
    TransferLimit k (transferLyapunov k hk) := by
  let f := transferCocycle k hk
  refine ⟨measurable_const.mul f.measurable_lowerRate,
    f.integrable_lowerRate.const_mul _, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonneg (log_growthBase_pos k hk).le (f.lowerRate_bounds z).1
  · intro z
    exact congrArg (fun a => Real.log (growthBase k) * a) (f.lowerRate_shift z)
  · filter_upwards [f.ae_tendsto_average (measurePreserving_torusStep k)] with z hz
    have hh : Tendsto (fun n => Real.log (growthBase k) * f.average n z) atTop
        (𝓝 (Real.log (growthBase k) * f.lowerRate z)) := tendsto_const_nhds.mul hz
    simpa only [transferLyapunov, f, ← lognorm_average_eq] using hh

lemma integral_lowerRate_of_deficit (k : ℝ) (hk : 0 ≤ k) (η : ℝ)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < η) :
    1 - η ≤ ∫ z, (transferCocycle k hk).lowerRate z ∂area := by
  have hc := (transferCocycle k hk).tendsto_integral_average (measurePreserving_torusStep k)
  apply ge_of_tendsto hc
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hh := hdef n hn
  have he : (∫ z, (transferCocycle k hk).average n z ∂area) =
      (∫ z, productDistance k z 0 (n : ℤ) ∂area) / (n : ℝ) := by
    change (∫ z, productDistance k z 0 (n : ℤ) / (n : ℝ) ∂area) = _
    exact integral_div (n : ℝ) _
  rw [he]
  unfold meanDeficit at hh
  linarith

lemma positive_transferLyapunov_of_deficit (k : ℝ) (hk : 0 ≤ k)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < (1 / 8 : ℝ)) :
    0 < area {z | 0 < transferLyapunov k hk z} := by
  have hl := integral_lowerRate_of_deficit k hk (1 / 8) hdef
  have hI : 0 < ∫ z, transferLyapunov k hk z ∂area := by
    unfold transferLyapunov
    rw [integral_const_mul]
    exact mul_pos (log_growthBase_pos k hk) (by linarith)
  by_contra hh
  have hz : area {z | 0 < transferLyapunov k hk z} = 0 :=
    le_antisymm (not_lt.mp hh) zero_le
  have hae : ∀ᵐ z ∂area, transferLyapunov k hk z = 0 := by
    have hnone : ∀ᵐ z ∂area, ¬ 0 < transferLyapunov k hk z := by
      simpa only [ae_iff, not_not] using hz
    filter_upwards [hnone] with z hnot
    exact le_antisymm (not_lt.mp hnot) ((transferLyapunov_limit k hk).2.2.1 z)
  have hi : (∫ z, transferLyapunov k hk z ∂area) = 0 := by
    rw [integral_congr_ae hae, integral_zero]
  linarith

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_DerivativeGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

lemma positive_standardLyapunov_of_deficit (k : ℝ) (hk : 0 ≤ k)
    (hdef : ∀ n : ℕ, 0 < n → meanDeficit k n < (1/8 : ℝ)) :
    0 < area {z | 0 < standardLyapunov k hk z} := by
  have hm : MeasurableSet {z | 0 < transferLyapunov k hk z} :=
    measurableSet_lt measurable_const (transferLyapunov_limit k hk).1
  have he := measurePreserving_recurrenceCoordinates.measure_preimage hm.nullMeasurableSet
  change 0 < area (recurrenceCoordinates ⁻¹' {z | 0 < transferLyapunov k hk z})
  rw [he]
  exact positive_transferLyapunov_of_deficit k hk hdef

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Components_PowerAtomCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped Topology ENNReal
open BoundedSubadditive

lemma exists_positive_spectral_gap (k : ℝ) (hk : 0≤k)
    (hpos : 0<area {z | 0 < standardLyapunov k hk z}) :
    ∃ χ : ℝ,0<χ ∧ 0<area (spectralGapRegion k hk χ) := by
  by_contra h
  push Not at h
  have hz (n : ℕ) : area (spectralGapRegion k hk (1/((n : ℝ)+1)))=0 :=
    le_antisymm (h _ (by positivity)) (bot_le)
  have hsub : {z | 0 < standardLyapunov k hk z}⊆⋃ n : ℕ,spectralGapRegion k hk (1/((n : ℝ)+1)) := by
    intro z hzL
    obtain ⟨n,hn⟩ := exists_nat_gt (1/standardLyapunov k hk z)
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    change 1/((n : ℝ)+1) < standardLyapunov k hk z
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<(n : ℝ)+1)).mpr
    have ha := (div_lt_iff₀ hzL).mp hn
    nlinarith
  exact hpos.ne' (measure_mono_null hsub (measure_iUnion_null hz))

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Bernoulli_ErgodicL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory MeasureTheory.Measure Set Filter Topology HyperbolicCoding BoundedSubadditive
open scoped ENNReal

theorem eventually_actual_cyclic_weakBernoulli_component :
    ∃ k₀ : ℝ,0<k₀ ∧ ∀ k : ℝ,k₀≤k →
    ∃ E : Set Torus,MeasurableSet E ∧ 0<area E ∧
      (standardMap k ⁻¹' E=E) ∧ Ergodic (standardMap k) (normalizedArea E) ∧
      (∀ᵐ z ∂normalizedArea E,∃ l : ℝ,0<l ∧ LyapunovSpectrumAt k z l) ∧
      ∃ (N : ℕ) (hN : 0<N) (P : Fin N → Set Torus),
        (∀ j,MeasurableSet (P j)) ∧ ((⋃ j,P j) =ᵐ[area] E) ∧
        (∀ i j,i≠j → area (P i∩P j)=0) ∧
        (∀ j,(standardMap k '' P j) =ᵐ[area] P ⟨(j.val+1)%N,Nat.mod_lt _ hN⟩) ∧
        (∀ j,area (P j)=area E/(N : ℝ≥0∞) ∧ 0<area (P j)) ∧
        (∀ j,∀ r : ℕ,0 < r → Ergodic (((standardMap k)^[N])^[r]) (normalizedArea (P j))) ∧
        (∀ j,∃ α : ℕ → ℕ → Torus → Bool,
          (∀ i r,Measurable (α i r)) ∧ Function.Injective (fun z => fun i r => α i r z) ∧
          ∀ M : ℕ,WeakBernoulliProcess (normalizedArea (P j))
            (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M)) := by
  obtain ⟨K,hK,hdef⟩ := eventually_meanDeficit_small (1/8 : ℝ) (by norm_num)
  refine ⟨K,hK,?_⟩
  intro k hk
  have hk0 : 0≤k := hK.le.trans hk
  obtain ⟨χ,hχ,hgap⟩ := exists_positive_spectral_gap k hk0
    (positive_standardLyapunov_of_deficit k hk0 (hdef k hk))
  exact actual_cyclic_weakBernoulli_component_q44 k hk0 hχ hgap

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ComponentsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped ENNReal

theorem main_components_oai : MainComponentsObligation := by
  obtain ⟨K,hK,hpieces⟩ := eventually_actual_cyclic_weakBernoulli_component
  refine ⟨K,hK,?_⟩
  intro k hk
  obtain ⟨E,hE,hEpos,hEinv,hEerg,hEspec,N,hN,P,hPM,hPU,hPD,hPC,hPA,hPT,hPW⟩ := hpieces k hk
  refine ⟨E,hE,hEpos,?_,hEerg,hEspec,N,hN,P,hPM,hPU,hPD,hPC,hPA,?_⟩
  · exact Filter.EventuallyEq.of_eq hEinv
  · intro j
    obtain ⟨α,hα,hsep,hwb⟩ := hPW j
    exact actual_return_bernoulli_q44 k (hK.le.trans hk) N (P j) (hPA j).2
      (hPT j) α hα hsep hwb

end StandardMapEntropy

end

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.main_components_oai := @OAI.StandardMapEntropy.main_components_oai
