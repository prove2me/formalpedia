-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected_q3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:48:17.472781+00:00
-- url     : https://prove2.me/submissions/095a49da-d203-4d43-9451-8751f5e6c38b

import Mathlib
import Definitions.Def_StandardMapLyapunov
import Definitions.Def_OAIQ3St000
import Theorems.Thm_OAI_StandardMapEntropy_actual_fast_bridge_real_q3

section
-- module Solutions.OAIQ3_Std.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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

lemma tendsto_growthBase : Filter.Tendsto growthBase Filter.atTop Filter.atTop := by
  have h : Filter.Tendsto (fun k : ℝ => (2 * Real.pi) * k) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
  exact Filter.tendsto_atTop_mono (fun k => by dsimp [growthBase]; linarith) h

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
-- module Solutions.OAIQ3_Std.StandardMap_SegmentObservations
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
-- module Solutions.OAIQ3_Std.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
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
-- module Solutions.OAIQ3_Std.StandardMap_TorusObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
lemma torusShortfall_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusShortfall k (torusIter k b z) a n=torusShortfall k z (a+b) n := by
  have he : torusSegmentCoefficient k (torusIter k b z) a=torusSegmentCoefficient k z (a+b) := by
    funext i
    unfold torusSegmentCoefficient
    rw [← torusIter_add]
    congr 3
    ring
  simp only [torusShortfall,torusSegmentTransfer,he]
lemma continuous_shortfall_observation (k : ℝ) (hk : 0 ≤ k) {R : ℕ}
    (a : Fin R → ℤ) (n : Fin R → ℕ) (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun z => F (fun i => torusShortfall k z (a i) (n i))) :=
  hF.comp (continuous_pi (fun i => continuous_torusShortfall k hk (a i) (n i)))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CancellationTheorem
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
lemma cancellationConstant_pos : 0<cancellationConstant := by unfold cancellationConstant; positivity
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_DoublingPointwise
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
-- module Solutions.OAIQ3_Std.StandardMap_MeanDeficit
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
  have hsub : (∫ z,cancellationLoss k z n ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)-(∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area) := by
    convert! integral_sub (hL.add hR) hT using 1
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
-- module Solutions.OAIQ3_Std.StandardMap_MeanCancellation
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
-- module Solutions.OAIQ3_Std.StandardMap_MeanGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_FixedDeficit
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CriticalSequence
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local
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
lemma criticalTheta_pos (r i : ℕ) : 0 < criticalTheta r i := by unfold criticalTheta; positivity
lemma criticalTheta_tendsto (r : ℕ) : Tendsto (criticalTheta r) atTop (𝓝 0) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have he (i : ℕ) : criticalTheta r i=(1/2:ℝ)^i*(1/2:ℝ)^(r+1) := by
    unfold criticalTheta
    rw [← pow_add]
    congr 1
  have heq : criticalTheta r=(fun i => (1/2:ℝ)^i*(1/2:ℝ)^(r+1)) := funext he
  rw [heq]
  simpa only [zero_mul] using ht.mul_const ((1/2:ℝ)^(r+1))
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
lemma epsilon_pos (i : ℕ) : 0 < S.epsilon i := (criticalTheta_pos S.offset i).trans (S.threshold i)
lemma epsilon_tendsto : Tendsto S.epsilon atTop (𝓝 0) := by
  apply squeeze_zero (fun i => (S.epsilon_pos i).le) S.upper
  simpa using (criticalTheta_tendsto S.offset).const_mul (2*doublingConstant)
lemma parameter_tendsto : Tendsto S.parameter atTop atTop :=
  tendsto_atTop_mono S.large tendsto_natCast_atTop_atTop
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ArrayTests
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_arrayShortfall (s t : DyadicTime) : Continuous (arrayShortfall s t) :=
  continuous_const.sub ((continuous_arrayEval s t).div_const _)
lemma continuous_arrayJ (s t : DyadicTime) : Continuous (arrayJ s t) :=
  (continuous_arrayShortfall s t).sub (((continuous_arrayShortfall s (dyadicMid s t)).add
    (continuous_arrayShortfall (dyadicMid s t) t)).div_const 2)
lemma continuous_arrayV (s t : DyadicTime) : Continuous (arrayV s t) :=
  ((continuous_arrayShortfall s (dyadicMid s t)).sub (continuous_arrayShortfall (dyadicMid s t) t)).pow 2
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ArrayAffinity
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma continuous_arrayTest (i : ArrayTestIndex) : Continuous (arrayTest i) :=
  (continuous_arrayJ _ _).add (continuous_arrayV _ _)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_RescaledArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma continuous_sampleArray (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) : Continuous (fun z => sampleArray k hk z n hn) := by
  apply Continuous.subtype_mk
  apply continuous_pi; intro s
  apply continuous_pi; intro t
  exact (continuous_productDistance k hk _ _).div_const _
lemma rescaledDistance_aligned (k : ℝ) (z : Torus) (n : ℕ) (s t : DyadicTime) (a b : ℤ)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(b:ℝ)) :
    rescaledDistance k z n s t=productDistance k z a b/(n:ℝ) := by
  simp only [rescaledDistance,hs,ht,Int.floor_intCast]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_SampleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
instance sampleLawProbability (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) :
    IsProbabilityMeasure (sampleLaw k hk n hn) := by
  unfold sampleLaw
  exact (Measure.isProbabilityMeasure_map_iff (continuous_sampleArray k hk n hn).measurable.aemeasurable).2 inferInstance
lemma integral_sampleLaw (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) (F : DistanceArray → ℝ)
    (hF : Continuous F) :
    (∫ d,F d ∂sampleLaw k hk n hn)=∫ z,F (sampleArray k hk z n hn) ∂area :=
  integral_map_of_stronglyMeasurable (continuous_sampleArray k hk n hn).measurable hF.stronglyMeasurable
lemma shortfall_sample_aligned (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    arrayShortfall s t (sampleArray k hk z n hn)=torusShortfall k z a m := by
  have hni : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hlen : (t:ℝ)-(s:ℝ)=(m:ℝ)/(n:ℝ) := (eq_div_iff hni).mpr (by nlinarith)
  unfold arrayShortfall
  change 1-rescaledDistance k z n s t/((t:ℝ)-(s:ℝ))=_
  rw [rescaledDistance_aligned k z n s t a (a+(m:ℤ)) hs (by simpa only [Int.cast_add,Int.cast_natCast] using ht),hlen,
    productDistance_forward]
  unfold torusShortfall
  field_simp
lemma integral_shortfall_sample (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    (∫ d,arrayShortfall s t d ∂sampleLaw k hk n hn)=meanDeficit k m := by
  rw [integral_sampleLaw k hk n hn _ (continuous_arrayShortfall s t)]
  simp_rw [shortfall_sample_aligned k hk _ n hn s t a m hm hs ht]
  have he (z : Torus) : torusShortfall k z a m=torusShortfall k (torusIter k a z) 0 m := by
    rw [torusShortfall_shift,zero_add]
  simp_rw [he]
  rw [integral_torusIter k a (fun z => torusShortfall k z 0 m),← meanDeficit_eq_integral_shortfall k hk m]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ArrayMoments
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma meanSquareDeficit_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0 < n) :
    0 ≤ meanSquareDeficit k n ∧ meanSquareDeficit k n ≤ meanDeficit k n := by
  refine ⟨integral_nonneg (fun z => sq_nonneg _),?_⟩
  rw [meanDeficit_eq_integral_shortfall k hk n]
  apply integral_mono
  · exact ((continuous_torusShortfall k hk 0 n).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (continuous_torusShortfall k hk 0 n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro z
    have h := torusShortfall_mem k hk z 0 n hn
    nlinarith [h.1,h.2]
lemma integrable_arrayShortfall (μ : Measure DistanceArray) [IsFiniteMeasure μ] (s t : DyadicTime) :
    Integrable (arrayShortfall s t) μ :=
  (continuous_arrayShortfall s t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma integrable_arrayShortfall_sq (μ : Measure DistanceArray) [IsFiniteMeasure μ] (s t : DyadicTime) :
    Integrable (fun d => (arrayShortfall s t d)^2) μ :=
  ((continuous_arrayShortfall s t).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma integral_shortfall_sq_sample (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0 < n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    (∫ d,(arrayShortfall s t d)^2 ∂sampleLaw k hk n hn)=meanSquareDeficit k m := by
  rw [integral_sampleLaw k hk n hn (fun d => (arrayShortfall s t d)^2) ((continuous_arrayShortfall s t).pow 2)]
  simp_rw [shortfall_sample_aligned k hk _ n hn s t a m hm hs ht]
  have he (z : Torus) : torusShortfall k z a m=torusShortfall k (torusIter k a z) 0 m := by
    rw [torusShortfall_shift,zero_add]
  simp_rw [he]
  exact integral_torusIter k a (fun z => (torusShortfall k z 0 m)^2)
lemma integral_J_sample (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0 < n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ)) :
    (∫ d,arrayJ s t d ∂sampleLaw k hk n hn)=meanDeficit k (m+m)-meanDeficit k m := by
  have hmid : (n:ℝ)*(dyadicMid s t:ℝ)=(a:ℝ)+(m:ℝ) := by rw [dyadicMid_val]; nlinarith
  have hwhole := integral_shortfall_sample k hk n hn s t a (m+m) (by omega) hs (by simpa only [Nat.cast_add,two_mul] using ht)
  have hl := integral_shortfall_sample k hk n hn s (dyadicMid s t) a m hm hs hmid
  have hr := integral_shortfall_sample k hk n hn (dyadicMid s t) t (a+(m:ℤ)) m hm
    (by simpa only [Int.cast_add,Int.cast_natCast] using hmid) (by push_cast; linarith)
  have hadd : (∫ d,arrayShortfall s (dyadicMid s t) d+arrayShortfall (dyadicMid s t) t d ∂sampleLaw k hk n hn)=
      (∫ d,arrayShortfall s (dyadicMid s t) d ∂sampleLaw k hk n hn)+
        (∫ d,arrayShortfall (dyadicMid s t) t d ∂sampleLaw k hk n hn) := by
    convert! integral_add (integrable_arrayShortfall (sampleLaw k hk n hn) s (dyadicMid s t)) (integrable_arrayShortfall (sampleLaw k hk n hn) (dyadicMid s t) t) using 1
  have hsub : (∫ d,arrayJ s t d ∂sampleLaw k hk n hn)=
      (∫ d,arrayShortfall s t d ∂sampleLaw k hk n hn)-
        (∫ d,(arrayShortfall s (dyadicMid s t) d+arrayShortfall (dyadicMid s t) t d)/2 ∂sampleLaw k hk n hn) := by
    convert! integral_sub (integrable_arrayShortfall (sampleLaw k hk n hn) s t)
      (((integrable_arrayShortfall (sampleLaw k hk n hn) s (dyadicMid s t)).add (integrable_arrayShortfall (sampleLaw k hk n hn) (dyadicMid s t) t)).div_const 2) using 1
  rw [hsub,integral_div,hadd,hwhole,hl,hr]
  ring
lemma scalar_variance_test {a b c : ℝ} (ha : a∈Icc 0 1) (hb : b∈Icc 0 1)
    (hc : c∈Icc 0 1) (hJ : 0 ≤ c-(a+b)/2) :
    (a-b)^2/4 ≤ (a^2+b^2)/2-c^2+2*(c-(a+b)/2) ∧ (a-b)^2 ≤ a+b ∧ c-(a+b)/2 ≤ c := by
  have hab : 0 ≤ a*b := mul_nonneg ha.1 hb.1
  have hca : (a+b)/2 ≤ c := by linarith
  have hbar : 0 ≤ (a+b)/2 := by linarith [ha.1,hb.1]
  have hcc : 0 ≤ (c-(a+b)/2)*(2-c-(a+b)/2) := mul_nonneg hJ (by linarith [hc.2])
  refine ⟨by nlinarith,by nlinarith [ha.1,ha.2,hb.1,hb.2],by linarith⟩
lemma integral_V_sample_bound (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0 < n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ)) :
    (∫ d,arrayV s t d ∂sampleLaw k hk n hn)/4 ≤
      meanSquareDeficit k m-meanSquareDeficit k (m+m)+2*(meanDeficit k (m+m)-meanDeficit k m) := by
  let μ := sampleLaw k hk n hn
  have : IsProbabilityMeasure μ := sampleLawProbability k hk n hn
  have hmid : (n:ℝ)*(dyadicMid s t:ℝ)=(a:ℝ)+(m:ℝ) := by rw [dyadicMid_val]; nlinarith
  have hwhole : (n:ℝ)*(t:ℝ)=(a:ℝ)+((m+m:ℕ):ℝ) := by push_cast; linarith
  have hrstart : (n:ℝ)*(dyadicMid s t:ℝ)=((a+(m:ℤ):ℤ):ℝ) := by simpa only [Int.cast_add,Int.cast_natCast] using hmid
  have hrend : (n:ℝ)*(t:ℝ)=((a+(m:ℤ):ℤ):ℝ)+(m:ℝ) := by push_cast; linarith
  have hslt : (s:ℝ) < (t:ℝ) := by
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    nlinarith
  let F : DistanceArray → ℝ := fun d =>
    ((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2-
      (arrayShortfall s t d)^2+2*arrayJ s t d
  have hF : Continuous F := by
    exact ((((continuous_arrayShortfall s _).pow 2).add ((continuous_arrayShortfall _ t).pow 2)).div_const 2).sub
      ((continuous_arrayShortfall s t).pow 2) |>.add (continuous_const.mul (continuous_arrayJ s t))
  have hb (z : Torus) : arrayV s t (sampleArray k hk z n hn)/4 ≤ F (sampleArray k hk z n hn) := by
    have ha := torusShortfall_mem k hk z a m hm
    have hb := torusShortfall_mem k hk z (a+(m:ℤ)) m hm
    have hcc := torusShortfall_mem k hk z a (m+m) (by omega)
    rw [← shortfall_sample_aligned k hk z n hn s (dyadicMid s t) a m hm hs hmid] at ha
    rw [← shortfall_sample_aligned k hk z n hn (dyadicMid s t) t (a+(m:ℤ)) m hm hrstart hrend] at hb
    rw [← shortfall_sample_aligned k hk z n hn s t a (m+m) (by omega) hs hwhole] at hcc
    exact (scalar_variance_test ha hb hcc (arrayJ_nonneg s t hslt _)).1
  have hi := integral_mono (μ := area)
    (((continuous_arrayV s t).comp (continuous_sampleArray k hk n hn)).div_const 4 |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hF.comp (continuous_sampleArray k hk n hn)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hb
  simp only [Function.comp_apply] at hi
  rw [integral_div,← integral_sampleLaw k hk n hn _ (continuous_arrayV s t),← integral_sampleLaw k hk n hn F hF] at hi
  have hEval : (∫ d,F d ∂μ)=meanSquareDeficit k m-meanSquareDeficit k (m+m)+2*(meanDeficit k (m+m)-meanDeficit k m) := by
    have h1 : (∫ d,F d ∂μ)=
        (∫ d,((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2-(arrayShortfall s t d)^2 ∂μ)+
          (∫ d,2*arrayJ s t d ∂μ) := by
      convert! integral_add
        ((((integrable_arrayShortfall_sq μ s (dyadicMid s t)).add (integrable_arrayShortfall_sq μ (dyadicMid s t) t)).div_const 2).sub (integrable_arrayShortfall_sq μ s t))
        (((continuous_arrayJ s t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul 2) using 1
    have h2 : (∫ d,((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2-(arrayShortfall s t d)^2 ∂μ)=
        (∫ d,((arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2)/2 ∂μ)-
          (∫ d,(arrayShortfall s t d)^2 ∂μ) := by
      convert! integral_sub (((integrable_arrayShortfall_sq μ s (dyadicMid s t)).add (integrable_arrayShortfall_sq μ (dyadicMid s t) t)).div_const 2) (integrable_arrayShortfall_sq μ s t) using 1
    have h3 : (∫ d,(arrayShortfall s (dyadicMid s t) d)^2+(arrayShortfall (dyadicMid s t) t d)^2 ∂μ)=
        (∫ d,(arrayShortfall s (dyadicMid s t) d)^2 ∂μ)+(∫ d,(arrayShortfall (dyadicMid s t) t d)^2 ∂μ) := by
      convert! integral_add (integrable_arrayShortfall_sq μ s (dyadicMid s t)) (integrable_arrayShortfall_sq μ (dyadicMid s t) t) using 1
    rw [h1,h2,integral_div,h3,integral_const_mul]
    change ((∫ d,(arrayShortfall s (dyadicMid s t) d)^2 ∂sampleLaw k hk n hn)+
      (∫ d,(arrayShortfall (dyadicMid s t) t d)^2 ∂sampleLaw k hk n hn))/2-
      (∫ d,(arrayShortfall s t d)^2 ∂sampleLaw k hk n hn)+2*(∫ d,arrayJ s t d ∂sampleLaw k hk n hn)=_
    rw [integral_shortfall_sq_sample k hk n hn s (dyadicMid s t) a m hm hs hmid,
      integral_shortfall_sq_sample k hk n hn (dyadicMid s t) t (a+(m:ℤ)) m hm hrstart hrend,
      integral_shortfall_sq_sample k hk n hn s t a (m+m) (by omega) hs hwhole,
      integral_J_sample k hk n hn s t a m hm hs ht]
    ring
  exact hi.trans_eq hEval
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
noncomputable instance scaleLawFinite (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) :
    IsFiniteMeasure (scaleLaw k hk p l ε) := by
  unfold scaleLaw
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top
lemma integral_scaleLaw (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (F : DistanceArray → ℝ) (hF : Continuous F) :
    (∫ d,F d ∂scaleLaw k hk p l ε)=(∑ i∈Finset.range l,∫ d,F d ∂sampleLaw k hk (2^(p+i)) (by positivity))/ε := by
  rw [scaleLaw,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/ε)]
  rw [integral_finsetSum_measure]
  · simp only [smul_eq_mul]; ring
  · intro i hi
    exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaleTelescopes
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
lemma sum_successive_difference (f : ℕ → ℝ) (p l : ℕ) :
    (∑ i∈Finset.range l,(f (p+i+1)-f (p+i)))=f (p+l)-f p := by
  induction l with
  | zero => simp
  | succ l ih => rw [Finset.sum_range_succ,ih]; simp only [Nat.add_assoc]; ring
lemma sum_variance_telescope (e q J V : ℕ → ℝ) (p l : ℕ)
    (hq0 : ∀ n,0≤q n) (hqe : ∀ n,q n≤e n) (he0 : ∀ n,0≤e n)
    (hJ : ∀ n,J n=e (n+1)-e n)
    (hV : ∀ n,V n/4≤q n-q (n+1)+2*(e (n+1)-e n)) :
    (∑ i∈Finset.range l,(J (p+i)+V (p+i)))≤9*e (p+l) := by
  have hj : (∑ i∈Finset.range l,J (p+i))=e (p+l)-e p := by
    simp_rw [hJ]
    exact sum_successive_difference e p l
  have hv : (∑ i∈Finset.range l,V (p+i))/4≤q p-q (p+l)+2*(e (p+l)-e p) := by
    have hh := Finset.sum_le_sum (s := Finset.range l) (fun i hi => hV (p+i))
    rw [← Finset.sum_div] at hh
    have hr : (∑ i∈Finset.range l,(q (p+i)-q (p+i+1)+2*(e (p+i+1)-e (p+i))))=
        q p-q (p+l)+2*(e (p+l)-e p) := by
      have hrev : (∑ i∈Finset.range l,(q (p+i)-q (p+i+1)))= -(∑ i∈Finset.range l,(q (p+i+1)-q (p+i))) := by
        rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i hi; ring
      rw [Finset.sum_add_distrib,hrev,← Finset.mul_sum,sum_successive_difference,sum_successive_difference]
      ring
    rwa [hr] at hh
  rw [Finset.sum_add_distrib,hj]
  nlinarith [hq0 (p+l),hqe p,he0 p]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaleTestBounds
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma dyadic_aligned_eventually (s : DyadicTime) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀≤p → ∃ a : ℤ, ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ) := by
  obtain ⟨p₀,a,ha⟩ := dyadicTime_mem s
  refine ⟨p₀,fun p hp => ⟨a*2^(p-p₀),?_⟩⟩
  push_cast
  have he : (2:ℝ)^p=(2:ℝ)^p₀*2^(p-p₀) := by rw [← pow_add,Nat.add_sub_of_le hp]
  rw [ha,he]
  field_simp
lemma dyadic_interval_aligned_eventually (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) :
    ∃ p₀ : ℕ, ∀ p : ℕ, p₀≤p → ∃ a : ℤ, ∃ m : ℕ, 0 < m ∧
      ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ) ∧ ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ) := by
  obtain ⟨p₁,hp₁⟩ := dyadic_aligned_eventually s
  obtain ⟨p₂,hp₂⟩ := dyadic_aligned_eventually (dyadicMid s t)
  refine ⟨max p₁ p₂,?_⟩
  intro p hp
  obtain ⟨a,ha⟩ := hp₁ p ((le_max_left _ _).trans hp)
  obtain ⟨b,hb⟩ := hp₂ p ((le_max_right _ _).trans hp)
  rw [dyadicMid_val] at hb
  have hpR : (0:ℝ)<(2^p:ℕ) := by positivity
  have hab : a<b := by exact_mod_cast (show (a:ℝ)<(b:ℝ) by nlinarith)
  let m := (b-a).toNat
  have hm : 0 < m := by omega
  have he : (m:ℝ)=(b:ℝ)-(a:ℝ) := by
    rw [show (m:ℝ)=((b-a).toNat:ℝ) from rfl,← Int.cast_natCast,Int.toNat_of_nonneg (sub_nonneg.mpr hab.le)]
    push_cast; rfl
  exact ⟨a,m,hm,ha,by rw [he]; nlinarith⟩
lemma aligned_times_scale (p i : ℕ) (s t : DyadicTime) (a : ℤ) (m : ℕ)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ))
    (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ)) :
    ((2^(p+i):ℕ):ℝ)*(s:ℝ)=((a*2^i:ℤ):ℝ) ∧
    ((2^(p+i):ℕ):ℝ)*(t:ℝ)=((a*2^i:ℤ):ℝ)+2*((m*2^i:ℕ):ℝ) := by
  push_cast at hs ht ⊢
  rw [pow_add]
  constructor
  · calc
      _ = (((2:ℝ)^p)*(s:ℝ))*(2:ℝ)^i := by ring
      _ = _ := by rw [hs]
  · calc
      _ = (((2:ℝ)^p)*(t:ℝ))*(2:ℝ)^i := by ring
      _ = _ := by rw [ht]; ring
lemma integral_test_scalelaw (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ)) :
    (∫ d,arrayTest ⟨(s,t),hst⟩ d ∂scaleLaw k hk p l ε)≤9*meanDeficit k (m*2^l)/ε := by
  let e : ℕ → ℝ := fun i => meanDeficit k (m*2^i)
  let q : ℕ → ℝ := fun i => meanSquareDeficit k (m*2^i)
  let J : ℕ → ℝ := fun i => ∫ d,arrayJ s t d ∂sampleLaw k hk (2^(p+i)) (by positivity)
  let V : ℕ → ℝ := fun i => ∫ d,arrayV s t d ∂sampleLaw k hk (2^(p+i)) (by positivity)
  have hnext (i : ℕ) : m*2^(i+1)=m*2^i+m*2^i := by rw [pow_succ]; ring
  have hJ (i : ℕ) : J i=e (i+1)-e i := by
    have hal := aligned_times_scale p i s t a m hs ht
    have hh := integral_J_sample k hk (2^(p+i)) (by positivity) s t (a*2^i) (m*2^i) (by positivity) hal.1 hal.2
    exact hh.trans (by rw [← hnext])
  have hV (i : ℕ) : V i/4≤q i-q (i+1)+2*(e (i+1)-e i) := by
    have hal := aligned_times_scale p i s t a m hs ht
    have hh := integral_V_sample_bound k hk (2^(p+i)) (by positivity) s t (a*2^i) (m*2^i) (by positivity) hal.1 hal.2
    simpa only [← hnext] using hh
  have hh := sum_variance_telescope e q J V 0 l
    (fun i => (meanSquareDeficit_bounds k hk (m*2^i) (by positivity)).1)
    (fun i => (meanSquareDeficit_bounds k hk (m*2^i) (by positivity)).2)
    (fun i => (meanDeficit_bounds k hk (m*2^i) (by positivity)).1) hJ hV
  simp only [Nat.zero_add] at hh
  rw [integral_scaleLaw k hk p l ε hε _ (continuous_arrayTest _)]
  apply (div_le_div_iff_of_pos_right hε).mpr
  have hi (i : ℕ) : (∫ d,arrayTest ⟨(s,t),hst⟩ d ∂sampleLaw k hk (2^(p+i)) (by positivity))=J i+V i := by
    convert! integral_add (μ := sampleLaw k hk (2^(p+i)) (by positivity)) ((continuous_arrayJ s t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      ((continuous_arrayV s t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) using 1
  simp_rw [hi]
  exact hh
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CriticalLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma meanDeficit_ratio (k : ℝ) (hk : 0≤k) (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    meanDeficit k n ≤ ((m:ℝ)/(n:ℝ))*meanDeficit k m := by
  have hh := meanDeficit_comparison k hk n m hnm
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (show (0:ℝ)<n by exact_mod_cast hn)).mpr
  nlinarith
lemma dyadic_aligned_deficit_bound (k : ℝ) (hk : 0≤k) (p l H : ℕ)
    (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (a : ℤ) (m : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (hH : (t:ℝ)-(s:ℝ)≤2^(H+1)) :
    meanDeficit k (m*2^l) ≤ (2^(H+1)/((t:ℝ)-(s:ℝ)))*meanDeficit k (2^(p+l+H)) := by
  have hlen : ((t:ℝ)-(s:ℝ))*(2:ℝ)^p=2*(m:ℝ) := by push_cast at hs ht; nlinarith
  have hlen0 : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hratio : (((2^(p+l+H):ℕ):ℝ)/((m*2^l:ℕ):ℝ))=(2:ℝ)^(H+1)/((t:ℝ)-(s:ℝ)) := by
    push_cast
    apply (div_eq_div_iff (by positivity) hlen0.ne').mpr
    rw [pow_add,pow_add,pow_succ]
    nlinarith [congrArg (fun x : ℝ => x*((2:ℝ)^l*(2:ℝ)^H)) hlen]
  have hn : m*2^l≤2^(p+l+H) := by
    have hR : (m:ℝ)*2^l≤2^(p+l+H) := by
      rw [pow_add,pow_add]
      have hh := mul_le_mul_of_nonneg_right hH (show (0:ℝ)≤2^p by positivity)
      rw [pow_succ] at hh
      have hmH : (m:ℝ)≤2^p*2^H := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hmH (show (0:ℝ)≤2^l by positivity)]
    exact_mod_cast hR
  exact (meanDeficit_ratio k hk (m*2^l) (2^(p+l+H)) (by positivity) hn).trans_eq (by rw [hratio])
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
instance initialLaw_finite (i : ℕ) : IsFiniteMeasure (S.initialLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
instance terminalLaw_finite (i : ℕ) : IsFiniteMeasure (S.terminalLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
instance multiLaw_finite (i : ℕ) : IsFiniteMeasure (S.multiLaw i) := inferInstanceAs (IsFiniteMeasure (scaleLaw _ _ _ _ _))
lemma lowerExponent_tendsto : Tendsto (criticalLowerExponent S.offset) atTop atTop := by
  apply tendsto_atTop_mono (f := fun i : ℕ => i) _ tendsto_id
  intro i
  unfold criticalLowerExponent
  omega
lemma exponent_tendsto : Tendsto S.exponent atTop atTop := tendsto_atTop_mono (fun i => (S.lower_lt i).le) S.lowerExponent_tendsto
lemma multiLaw_test_bound (j : ArrayTestIndex) :
    ∃ C : ℝ, ∀ᶠ i in atTop, (∫ d,arrayTest j d ∂S.multiLaw i)≤C := by
  rcases j with ⟨⟨s,t⟩,hst⟩
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨H,hH⟩ := pow_unbounded_of_one_lt ((t:ℝ)-(s:ℝ)) (by norm_num : (1:ℝ)<2)
  have hH' : (t:ℝ)-(s:ℝ)≤(2:ℝ)^(H+1) := hH.le.trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) H])
  let R : ℝ := 2^(H+1)/((t:ℝ)-(s:ℝ))
  have hR : 0<R := div_pos (by positivity) (sub_pos.mpr hst)
  refine ⟨18*R*(2*doublingConstant)^H,?_⟩
  filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop p₀] with i hi
  obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
  have hb := integral_test_scalelaw (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i)
    (S.exponent i-criticalLowerExponent S.offset i) (S.epsilon i) (S.epsilon_pos i) s t hst a m hm hs ht
  have hh := dyadic_aligned_deficit_bound (S.parameter i) (S.positive i).le (criticalLowerExponent S.offset i)
    (S.exponent i-criticalLowerExponent S.offset i) H s t hst a m hm hs ht hH'
  rw [Nat.add_sub_of_le (S.lower_lt i).le] at hh
  have hterm := S.terminal i H
  have heps := S.epsilon_pos i
  change _ ≤ R*meanDeficit (S.parameter i) (2^(S.exponent i+H)) at hh
  have hl := hh.trans (mul_le_mul_of_nonneg_left hterm hR.le)
  apply hb.trans
  apply (div_le_iff₀ heps).mpr
  change 9*meanDeficit (S.parameter i) (m*2^(S.exponent i-criticalLowerExponent S.offset i))≤_
  change _ ≤ R*(2*(2*doublingConstant)^H*S.epsilon i) at hl
  nlinarith
lemma singleLaw_test_bound (p : ℕ) (k : ℝ) (hk : 0 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (s t : DyadicTime) (hst : (s:ℝ) < (t:ℝ)) (a : ℤ) (m H : ℕ) (hm : 0 < m)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) (ht : ((2^p:ℕ):ℝ)*(t:ℝ)=(a:ℝ)+2*(m:ℝ))
    (hH : (t:ℝ)-(s:ℝ) ≤ 2^(H+1)) :
    (∫ d,arrayTest ⟨(s,t),hst⟩ d ∂scaleLaw k hk p 1 ε) ≤
      (9*(2^(H+1)/((t:ℝ)-(s:ℝ))))*(meanDeficit k (2^(p+(H+1)))/ε) := by
  have hb := integral_test_scalelaw k hk p 1 ε hε s t hst a m hm hs ht
  have hh := dyadic_aligned_deficit_bound k hk p 1 H s t hst a m hm hs ht hH
  rw [show p+1+H=p+(H+1) by omega] at hh
  apply hb.trans
  have hmul := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ 9 by norm_num)
  have hd := (div_le_div_iff_of_pos_right hε).mpr hmul
  simpa only [mul_div_assoc,mul_assoc] using hd
lemma terminalLaw_test_bound (j : ArrayTestIndex) :
    ∃ C : ℝ, ∀ᶠ i in atTop, (∫ d,arrayTest j d ∂S.terminalLaw i) ≤ C := by
  rcases j with ⟨⟨s,t⟩,hst⟩
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨H,hH⟩ := pow_unbounded_of_one_lt ((t:ℝ)-(s:ℝ)) (by norm_num : (1:ℝ) < 2)
  have hH' : (t:ℝ)-(s:ℝ) ≤ (2:ℝ)^(H+1) := hH.le.trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) H])
  let R : ℝ := 2^(H+1)/((t:ℝ)-(s:ℝ))
  have hR : 0 < R := div_pos (by positivity) (sub_pos.mpr hst)
  refine ⟨18*R*(2*doublingConstant)^(H+1),?_⟩
  filter_upwards [S.exponent_tendsto.eventually_ge_atTop p₀] with i hi
  obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
  have hb := singleLaw_test_bound (S.exponent i) (S.parameter i) (S.positive i).le (S.epsilon i)
    (S.epsilon_pos i) s t hst a m H hm hs ht hH'
  have hh := S.terminal i (H+1)
  have he : meanDeficit (S.parameter i) (2^(S.exponent i+(H+1)))/S.epsilon i ≤ 2*(2*doublingConstant)^(H+1) := by
    apply (div_le_iff₀ (S.epsilon_pos i)).mpr
    exact hh
  exact hb.trans ((mul_le_mul_of_nonneg_left he (show 0 ≤ 9*R by positivity)).trans_eq (by ring))
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ArrayActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma arrayTestExtend_affine (g : C_c(NonAffineArray,ℝ)) (d : DistanceArray) (hd : d∈affineLocus) :
    arrayTestExtend g d=0 := by
  apply Function.extend_apply' _ _ _
  rintro ⟨u,rfl⟩
  exact u.property hd
lemma integral_arrayTestExtend (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (g : C_c(NonAffineArray,ℝ)) : (∫ d,arrayTestExtend g d ∂μ)=∫ d,g d ∂nonaffinePart μ := by
  have he : (∫ d,g d ∂nonaffinePart μ)=∫ d in affineLocusᶜ,arrayTestExtend g d ∂μ := by
    convert! integral_subtype_comap isClosed_affineLocus.isOpen_compl.measurableSet (arrayTestExtend g) using 1
    simp only [arrayTestExtend_apply]
    rfl
  rw [he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro d hd
  exact arrayTestExtend_affine g d (not_not.mp hd)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_VagueSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma open_null_of_integral_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (μ : Measure X) [μ.Regular] {U : Set X} (hU : IsOpen U)
    (hzero : ∀ g : C_c(X,ℝ), (∀ x,0 ≤ g x) → (∀ x∉U,g x=0) → ∫ x,g x ∂μ=0) : μ U=0 := by
  rw [hU.measure_eq_iSup_isCompact μ]
  apply le_antisymm _ bot_le
  simp only [iSup_le_iff]
  intro K hKU hK
  obtain ⟨⟨f,hfc⟩,hfK,hfU,hfs,hfr⟩ := exists_continuous_one_zero_of_isCompact
    hK hU.isClosed_compl (disjoint_compl_right_iff_subset.mpr hKU)
  let g : C_c(X,ℝ) := ⟨⟨f,hfc⟩,hfs⟩
  have hint := hzero g (fun x => (hfr x).1) (fun x hx => hfU hx)
  have hb := (hfc.integrable_of_hasCompactSupport hfs (μ := μ)).measure_le_integral
    (Eventually.of_forall fun x => (hfr x).1) (fun x hx => (hfK hx).ge)
  change μ K ≤ ENNReal.ofReal (∫ x,g x ∂μ) at hb
  rw [hint,ENNReal.ofReal_zero] at hb
  convert! hb using 1
lemma vague_open_null {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X] [RegularSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) (ν : Measure X) [ν.Regular]
    (hconv : ∀ g : C_c(X,ℝ), Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 (∫ x,g x ∂ν)))
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ g : C_c(X,ℝ), (∀ x,0 ≤ g x) → (∀ x∉U,g x=0) →
      Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 0)) : ν U=0 := by
  apply open_null_of_integral_zero ν hU
  intro g hg hz
  exact tendsto_nhds_unique (hconv g) (hzero g hg hz)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeScalars
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
lemma eventually_bridgeScalarControl : ∀ᶠ k : ℝ in atTop, BridgeScalarControl k := by
  have he (a C ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
      ∀ᶠ k : ℝ in atTop, C*growthBase k^(-a) ≤ ε := by
    have ht := ((tendsto_rpow_neg_atTop ha).comp tendsto_growthBase).const_mul C
    have hh := ht.eventually (gt_mem_nhds (show C*0 < ε by simpa using hε))
    exact hh.mono fun k hk => hk.le
  filter_upwards [eventually_ge_atTop (0:ℝ),he (49/25) 1 (1/2) (by norm_num) (by norm_num),
    he (47/50) 3 (1/4) (by norm_num) (by norm_num),he (3/5) 1 (1/2) (by norm_num) (by norm_num),
    he (7/10) (384*Real.pi) (1/2) (by norm_num) (by norm_num),he (4/5) 24 (1/2) (by norm_num) (by norm_num)]
    with k hk h1 h2 h3 h4 h5
  refine ⟨hk,by simpa only [one_mul] using h1,h2,by simpa only [one_mul] using h3,h4,?_⟩
  simpa only [Real.rpow_neg (by have := growthBase_ge_four k hk; linarith : 0 ≤ growthBase k),div_eq_mul_inv] using h5
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ObservationExponential
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
lemma eventually_bridge_observation_scalars (L : ℝ) :
    ∀ᶠ k : ℝ in atTop, 1 ≤ Real.log (growthBase k) ∧ 16*Real.pi*L ≤ growthBase k := by
  have hlog := (Real.tendsto_log_atTop.comp tendsto_growthBase).eventually (eventually_ge_atTop (1:ℝ))
  have hL := tendsto_growthBase.eventually (eventually_ge_atTop (16*Real.pi*L))
  exact hlog.and hL
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeAveraging
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
lemma measurableSet_torusFastBridge (k : ℝ) (N : ℕ) : MeasurableSet {z | torusFastBridge k z N} :=
  (isClosed_le continuous_const (continuous_torusSegmentTransfer k 0 N).norm).measurableSet
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MiddleObservationBridge
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
lemma shortfallObservation_shift (k : ℝ) {R : ℕ} (a : Fin R → ℤ) (n : Fin R → ℕ)
    (F : (Fin R → ℝ) → ℝ) (b : ℤ) (z : Torus) :
    shortfallObservation k a n F (torusIter k b z)=shortfallObservation k (fun j => a j+b) n F z := by
  unfold shortfallObservation
  congr 1
  funext j
  exact torusShortfall_shift k z (a j) b (n j)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeRealBound
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
lemma bridgeRealConstant_nonneg : 0≤bridgeRealConstant := ENNReal.toReal_nonneg
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeSamples
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
lemma continuous_arrayObservation {R : ℕ} (a b : Fin R → DyadicTime)
    (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) : Continuous (arrayObservation a b F) :=
  hF.comp (continuous_pi fun i => continuous_arrayShortfall (a i) (b i))
lemma arrayObservation_sample {R : ℕ} (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (a b : Fin R → DyadicTime) (A : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀i,0< m i)
    (ha : ∀i,(n:ℝ)*(a i:ℝ)=(A i:ℝ)) (hb : ∀i,(n:ℝ)*(b i:ℝ)=(A i:ℝ)+(m i:ℝ))
    (F : (Fin R → ℝ) → ℝ) (z : Torus) :
    arrayObservation a b F (sampleArray k hk z n hn)=shortfallObservation k A m F z := by
  unfold arrayObservation shortfallObservation
  congr 1
  funext i
  exact shortfall_sample_aligned k hk z n hn (a i) (b i) (A i) (m i) (hm i) (ha i) (hb i)
lemma array_fast_sample (k : ℝ) (hk : 0≤ k) (z : Torus) (n : ℕ) (hn : 0< n)
    (u v : DyadicTime) (a : ℤ) (N : ℕ)
    (hu : (n:ℝ)*(u:ℝ)=(a:ℝ)) (hv : (n:ℝ)*(v:ℝ)=(a:ℝ)+(N:ℝ))
    (hf : (999/1000:ℝ)*((v:ℝ)-(u:ℝ))< (sampleArray k hk z n hn).val u v) :
    torusFastBridge k (torusIter k a z) N := by
  change _< rescaledDistance k z n u v at hf
  rw [rescaledDistance_aligned k z n u v a (a+(N:ℤ)) hu (by push_cast; exact hv),
    productDistance_forward] at hf
  have hshift := torusSegmentTransfer_shift k z 0 a N
  rw [zero_add] at hshift
  unfold torusFastBridge
  rw [hshift,Real.rpow_le_iff_le_log (by linarith [growthBase_ge_four k hk])
    (lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk z a N).1)]
  have hnp : (0:ℝ)< n := by exact_mod_cast hn
  have hg : 0< Real.log (growthBase k) := log_growthBase_pos k hk
  have hl : (n:ℝ)*((v:ℝ)-(u:ℝ))=N := by linarith
  have he := (lt_div_iff₀ hnp).mp hf
  have he' := (lt_div_iff₀ hg).mp he
  nlinarith
lemma integral_observable_sample {R : ℕ} (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (a b : Fin R → DyadicTime) (A : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀i,0< m i)
    (ha : ∀i,(n:ℝ)*(a i:ℝ)=(A i:ℝ)) (hb : ∀i,(n:ℝ)*(b i:ℝ)=(A i:ℝ)+(m i:ℝ))
    (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) :
    (∫ d,arrayObservation a b F d ∂sampleLaw k hk n hn)=∫ z,shortfallObservation k A m F z ∂area := by
  rw [integral_sampleLaw k hk n hn _ (continuous_arrayObservation a b F hF)]
  apply integral_congr_ae
  exact Eventually.of_forall (arrayObservation_sample k hk n hn a b A m hm ha hb F)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgePattern
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
lemma sample_bridge_integral (k : ℝ) (hc : BridgeScalarControl k)
    (n N r : ℕ) (hn : 0< n) (hN : 100≤ N) (hr : (r:ℝ)≤ (N:ℝ)/1000)
    (u v : DyadicTime) (b : ℤ) (hu : (n:ℝ)*(u:ℝ)=(b:ℝ)) (hv : (n:ℝ)*(v:ℝ)=(b:ℝ)+(N:ℝ))
    {Rw Rh : ℕ} (sw tw : Fin Rw → DyadicTime) (sh th : Fin Rh → DyadicTime)
    (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀j,0< nw j) (hnh : ∀j,0< nh j)
    (hsw : ∀j,(n:ℝ)*(sw j:ℝ)=((aw j+b):ℤ))
    (htw : ∀j,(n:ℝ)*(tw j:ℝ)=((aw j+b):ℤ)+(nw j:ℝ))
    (hsh : ∀j,(n:ℝ)*(sh j:ℝ)=((ah j+b):ℤ))
    (hth : ∀j,(n:ℝ)*(th j:ℝ)=((ah j+b):ℤ)+(nh j:ℝ))
    (L : NNReal) (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀j,nw j≤ 2*r) (hlenh : ∀j,nh j≤ 2*r)
    (hwinw : ∀j l,1≤ l → l≤ nw j → (aw j+(l:ℤ)-1).natAbs≤ r)
    (hwinh : ∀j l,1≤ l → l≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs≤ r)
    (hW0 : ∀z,0≤ shortfallObservation k aw nw Fw z)
    (hH0 : ∀z,0≤ shortfallObservation k ah nh Fh z)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (η : ℝ) (hη : 0<η) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ))<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation sw tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((v:ℝ)-(u:ℝ))< d.val u v ∧ η< arrayObservation sh th Fh d) → F d=0) :
    (∫ d,F d ∂sampleLaw k hc.nonneg n hn)≤ D*bridgeRealConstant*
      ((∫ d,arrayObservation sw tw Fw d ∂sampleLaw k hc.nonneg n hn)+growthBase k^(-(1/10:ℝ)*(N:ℝ)))*
      ((∫ d,arrayObservation sh th Fh d ∂sampleLaw k hc.nonneg n hn)/(η/2)) := by
  let W := shortfallObservation k aw nw Fw
  let H := shortfallObservation k ah nh Fh
  let E := {z | torusFastBridge k z N} ∩ {z | η< H z}
  have hW : Continuous W := continuous_shortfall_observation k hc.nonneg _ _ _ hFw.continuous
  have hH : Continuous H := continuous_shortfall_observation k hc.nonneg _ _ _ hFh.continuous
  have hiW := hW.integrable_of_hasCompactSupport (μ := area) (HasCompactSupport.of_compactSpace _)
  have hE : MeasurableSet E := (measurableSet_torusFastBridge k N).inter (isOpen_lt continuous_const hH).measurableSet
  have heW (z : Torus) : arrayObservation sw tw Fw (sampleArray k hc.nonneg z n hn)=W (torusIter k b z) := by
    rw [arrayObservation_sample k hc.nonneg n hn sw tw (fun j => aw j+b) nw hnw hsw htw Fw]
    exact (shortfallObservation_shift k aw nw Fw b z).symm
  have heH (z : Torus) : arrayObservation sh th Fh (sampleArray k hc.nonneg z n hn)=H (torusIter k b z) := by
    rw [arrayObservation_sample k hc.nonneg n hn sh th (fun j => ah j+b) nh hnh hsh hth Fh]
    exact (shortfallObservation_shift k ah nh Fh b z).symm
  have hiI : Integrable (fun z => E.indicator W (torusIter k b z)) area :=
    (measurePreserving_torusIter k b).integrable_comp_of_integrable (hiW.indicator hE)
  have hbound : (∫ z,F (sampleArray k hc.nonneg z n hn) ∂area)≤ D*(∫ z in E,W z ∂area) := by
    rw [←integral_indicator hE,←integral_torusIter k b (E.indicator W),←integral_const_mul]
    apply integral_mono ((hF.comp (continuous_sampleArray k hc.nonneg n hn)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (hiI.const_mul D)
    intro z
    dsimp only [Function.comp_apply]
    by_cases hz : torusIter k b z∈E
    · rw [indicator_of_mem hz]
      simpa only [heW] using hFW (sampleArray k hc.nonneg z n hn)
    · rw [indicator_of_notMem hz,mul_zero]
      have hfz : F (sampleArray k hc.nonneg z n hn)=0 := hzero _ (by
        intro h
        apply hz
        exact ⟨array_fast_sample k hc.nonneg z n hn u v b N hu hv h.1,by simpa only [Set.mem_ofPred_eq,←heH z] using h.2⟩)
      exact hfz.le
  have hwint : (∫ d,arrayObservation sw tw Fw d ∂sampleLaw k hc.nonneg n hn)=∫ z,W z ∂area := by
    rw [integral_sampleLaw k hc.nonneg n hn _ (continuous_arrayObservation sw tw Fw hFw.continuous)]
    simp_rw [heW]
    exact integral_torusIter k b W
  have hhint : (∫ d,arrayObservation sh th Fh d ∂sampleLaw k hc.nonneg n hn)=∫ z,H z ∂area := by
    rw [integral_sampleLaw k hc.nonneg n hn _ (continuous_arrayObservation sh th Fh hFh.continuous)]
    simp_rw [heH]
    exact integral_torusIter k b H
  rw [integral_sampleLaw k hc.nonneg n hn F hF,hwint,hhint]
  have hb := actual_fast_bridge_real_q3 k hc N r hN hr aw nw Fw ah nh Fh hnw hnh L hFw hFh hlenw hlenh
    hwinw hwinh hW0 hH0 hlog hLM η hη hδ
  exact hbound.trans ((mul_le_mul_of_nonneg_left hb hD).trans_eq (by dsimp only [W,H]; ring))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeDecay
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
lemma bridge_error_geom (M : ℝ) (hM : (2:ℝ)^10≤ M) (N j : ℕ) (_hN : 1≤ N) :
    M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ))≤ (1/2:ℝ)^(N*2^j) := by
  have hMp : 0< M := lt_of_lt_of_le (by norm_num) hM
  have hbase : M^(-(1/10:ℝ))≤ (1/2:ℝ) := by
    rw [Real.rpow_neg hMp.le]
    apply (inv_le_comm₀ (Real.rpow_pos_of_pos hMp _) (by norm_num)).mpr
    have hh := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤ 2^10) hM (by norm_num : (0:ℝ)≤ 1/10)
    norm_num [←Real.rpow_natCast,←Real.rpow_mul] at hh
    simpa using hh
  rw [Real.rpow_mul_natCast hMp.le]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hMp.le _) hbase _
lemma half_pow_nat_le_inverse (N : ℕ) (hN : 1≤ N) : (1/2:ℝ)^N≤ 1/(N:ℝ) := by
  have hh : (N:ℝ)≤ (2:ℝ)^N := by exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n := N)))
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by exact_mod_cast hN) hh
lemma bridge_error_inverse (M : ℝ) (hM : (2:ℝ)^10≤ M) (N j : ℕ) (hN : 1≤ N) :
    M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ))≤ 1/((N*2^j:ℕ):ℝ) :=
  (bridge_error_geom M hM N j hN).trans (half_pow_nat_le_inverse _ (by have : 0 < N*2^j := Nat.mul_pos (by omega) (by positivity); omega))
lemma bridge_error_sum (M : ℝ) (hM : (2:ℝ)^10≤ M) (N l : ℕ) (hN : 1≤ N) :
    (∑j∈Finset.range l,M^(-(1/10:ℝ)*((N*2^j:ℕ):ℝ)))≤ 2/(N:ℝ) := by
  calc
    _ ≤ ∑j∈Finset.range l,1/((N*2^j:ℕ):ℝ) := Finset.sum_le_sum (fun j _ => bridge_error_inverse M hM N j hN)
    _ = (1/(N:ℝ))*∑j∈Finset.range l,(1/2:ℝ)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      rw [div_pow,one_pow,one_div_mul_one_div]
    _ ≤ (1/(N:ℝ))*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le l) (by positivity)
    _ = _ := by ring
lemma window_indices {a b : ℤ} {m r : ℕ}
    (ha : -(r:ℤ)≤ a-b) (hb : a+(m:ℤ)-b≤ r)
    (l : ℕ) (hl : 1≤ l) (hlm : l≤ m) : (a+(l:ℤ)-1-b).natAbs≤ r := by
  apply Nat.cast_le (α := ℤ) |>.mp
  rw [Int.natCast_natAbs,abs_le]
  constructor <;> omega
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeGrid
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

lemma aligned_scale (p l : ℕ) (s : DyadicTime) (a : ℤ)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) :
    ((2^(p+l):ℕ):ℝ)*(s:ℝ)=((a*2^l:ℤ):ℝ) := by
  push_cast at hs ⊢
  rw [pow_add]
  nlinarith [congrArg (fun x : ℝ => x*(2:ℝ)^l) hs]
lemma aligned_scale_end (p l : ℕ) (s : DyadicTime) (a : ℤ) (m : ℕ)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)+(m:ℝ)) :
    ((2^(p+l):ℕ):ℝ)*(s:ℝ)=((a*2^l:ℤ):ℝ)+((m*2^l:ℕ):ℝ) := by
  have hh := aligned_scale p l s (a+(m:ℤ)) (by simpa only [Int.cast_add,Int.cast_natCast] using hs)
  push_cast at hh ⊢
  nlinarith
lemma observation_nonneg_aligned {R : ℕ} (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (s t : Fin R → DyadicTime) (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀i,0< m i)
    (hs : ∀i,(n:ℝ)*(s i:ℝ)=(a i:ℝ)) (ht : ∀i,(n:ℝ)*(t i:ℝ)=(a i:ℝ)+(m i:ℝ))
    (F : (Fin R → ℝ) → ℝ) (hF0 : ∀d,0≤ arrayObservation s t F d) :
    ∀z,0≤ shortfallObservation k a m F z := by
  intro z
  rw [←arrayObservation_sample k hk n hn s t a m hm hs ht F]
  exact hF0 _
lemma length_from_window (a : ℤ) (m r : ℕ) (h1 : -(r:ℤ)≤ a) (h2 : a+(m:ℤ)≤ r) : m≤ 2*r := by omega
lemma BridgeGrid.sample_bound {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (k : ℝ) (hc : BridgeScalarControl k) (l : ℕ)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (η : ℝ) (hη : 0<η) (hδ : growthBase k^(-(1/10:ℝ)*((B.N*2^l:ℕ):ℝ))<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation B.sw B.tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))< d.val B.u B.v ∧ η< arrayObservation B.sh B.th Fh d) → F d=0) :
    (∫ d,F d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))≤ D*bridgeRealConstant*
      ((∫ d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))+
        growthBase k^(-(1/10:ℝ)*((B.N*2^l:ℕ):ℝ)))*
      ((∫ d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))/(η/2)) := by
  have hp : (0:ℤ)≤ 2^l := by positivity
  have h1 : 1≤ 2^l := Nat.one_le_pow l 2 (by omega)
  have hwL (j) : -((B.r*2^l:ℕ):ℤ)≤ B.aw j*2^l := by
    have hh := mul_le_mul_of_nonneg_right (B.hwleft j) hp
    push_cast; nlinarith
  have hwR (j) : B.aw j*2^l+((B.nw j*2^l:ℕ):ℤ)≤ ((B.r*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hwright j) hp
    push_cast; nlinarith
  have hhL (j) : -((B.r*2^l:ℕ):ℤ)≤ B.ah j*2^l-((B.N*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hhleft j) hp
    push_cast; nlinarith
  have hhR (j) : B.ah j*2^l+((B.nh j*2^l:ℕ):ℤ)-((B.N*2^l:ℕ):ℤ)≤ ((B.r*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hhright j) hp
    push_cast; nlinarith
  have hsw (j) : ((2^(B.p+l):ℕ):ℝ)*(B.sw j:ℝ)=(((B.aw j*2^l+B.b*2^l):ℤ):ℝ) := by
    simpa only [add_mul] using aligned_scale B.p l (B.sw j) (B.aw j+B.b) (B.hsw j)
  have htw (j) : ((2^(B.p+l):ℕ):ℝ)*(B.tw j:ℝ)=(((B.aw j*2^l+B.b*2^l):ℤ):ℝ)+((B.nw j*2^l:ℕ):ℝ) := by
    simpa only [add_mul] using aligned_scale_end B.p l (B.tw j) (B.aw j+B.b) (B.nw j) (B.htw j)
  have hsh (j) : ((2^(B.p+l):ℕ):ℝ)*(B.sh j:ℝ)=(((B.ah j*2^l+B.b*2^l):ℤ):ℝ) := by
    simpa only [add_mul] using aligned_scale B.p l (B.sh j) (B.ah j+B.b) (B.hsh j)
  have hth (j) : ((2^(B.p+l):ℕ):ℝ)*(B.th j:ℝ)=(((B.ah j*2^l+B.b*2^l):ℤ):ℝ)+((B.nh j*2^l:ℕ):ℝ) := by
    simpa only [add_mul] using aligned_scale_end B.p l (B.th j) (B.ah j+B.b) (B.nh j) (B.hth j)
  have hnonnegW : ∀z,0≤ shortfallObservation k (fun j => B.aw j*2^l) (fun j => B.nw j*2^l) Fw z := by
    intro z
    have hh := observation_nonneg_aligned k hc.nonneg (2^(B.p+l)) (by positivity) B.sw B.tw
      (fun j => B.aw j*2^l+B.b*2^l) (fun j => B.nw j*2^l) (fun j => Nat.mul_pos (B.pw j) (by positivity)) hsw htw Fw hW0
      (torusIter k (-(B.b*2^l)) z)
    rw [←shortfallObservation_shift,←torusIter_add,add_neg_cancel,torusIter_zero] at hh
    exact hh
  have hnonnegH : ∀z,0≤ shortfallObservation k (fun j => B.ah j*2^l) (fun j => B.nh j*2^l) Fh z := by
    intro z
    have hh := observation_nonneg_aligned k hc.nonneg (2^(B.p+l)) (by positivity) B.sh B.th
      (fun j => B.ah j*2^l+B.b*2^l) (fun j => B.nh j*2^l) (fun j => Nat.mul_pos (B.ph j) (by positivity)) hsh hth Fh hH0
      (torusIter k (-(B.b*2^l)) z)
    rw [←shortfallObservation_shift,←torusIter_add,add_neg_cancel,torusIter_zero] at hh
    exact hh
  apply sample_bridge_integral k hc (2^(B.p+l)) (B.N*2^l) (B.r*2^l) (by positivity)
    (le_trans B.large (Nat.le_mul_of_pos_right _ (by positivity)))
    (by push_cast; nlinarith [mul_le_mul_of_nonneg_right B.narrow (show (0:ℝ)≤ 2^l by positivity)])
    B.u B.v (B.b*2^l) (aligned_scale B.p l B.u B.b B.hu) (aligned_scale_end B.p l B.v B.b B.N B.hv)
    B.sw B.tw B.sh B.th (fun j => B.aw j*2^l) (fun j => B.nw j*2^l) Fw
    (fun j => B.ah j*2^l) (fun j => B.nh j*2^l) Fh
    (fun j => Nat.mul_pos (B.pw j) (by positivity)) (fun j => Nat.mul_pos (B.ph j) (by positivity))
    hsw htw hsh hth L hFw hFh
    (fun j => length_from_window _ _ _ (hwL j) (hwR j))
    (fun j => length_from_window (B.ah j*2^l-((B.N*2^l:ℕ):ℤ)) _ _ (hhL j) (by linarith [hhR j]))
    (fun j x hx hx' => by simpa only [sub_zero] using window_indices (a := B.aw j*2^l) (b := 0) (r := B.r*2^l) (by simpa only [sub_zero] using hwL j) (by simpa only [sub_zero] using hwR j) x hx hx')
    (fun j x hx hx' => window_indices (hhL j) (hhR j) x hx hx')
    hnonnegW hnonnegH hlog hLM η hη hδ F hF D hD hFW hzero
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeExist
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
lemma aligned_intervals_eventually {R : ℕ} (s t : Fin R → DyadicTime)
    (hst : ∀ j,(s j:ℝ)<(t j:ℝ)) :
    ∀ᶠ p : ℕ in atTop, ∃ (a : Fin R → ℤ) (m : Fin R → ℕ),
      (∀ j,0< m j) ∧ (∀ j,((2^p:ℕ):ℝ)*(s j:ℝ)=(a j:ℝ)) ∧
      (∀ j,((2^p:ℕ):ℝ)*(t j:ℝ)=(a j:ℝ)+(m j:ℝ)) := by
  have he (j : Fin R) : ∀ᶠ p : ℕ in atTop,∃ a : ℤ,∃ m : ℕ,0< m ∧
      ((2^p:ℕ):ℝ)*(s j:ℝ)=(a:ℝ) ∧ ((2^p:ℕ):ℝ)*(t j:ℝ)=(a:ℝ)+(m:ℝ) := by
    obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually (s j) (t j) (hst j)
    filter_upwards [eventually_ge_atTop p₀] with p hp
    obtain ⟨a,m,hm,ha,hb⟩ := hp₀ p hp
    exact ⟨a,2*m,by omega,ha,by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hb⟩
  filter_upwards [Filter.eventually_all.mpr he] with p hp
  choose a m hm ha hb using hp
  exact ⟨a,m,hm,ha,hb⟩
lemma exists_bridgeGrid {Rw Rh : ℕ} (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ))
    (sw tw : Fin Rw → DyadicTime) (sh th : Fin Rh → DyadicTime)
    (hw : ∀j,(sw j:ℝ)<(tw j:ℝ)) (hh : ∀j,(sh j:ℝ)<(th j:ℝ))
    (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
    (hwl : ∀j,-((1:ℝ)/(2:ℝ)^q)≤(sw j:ℝ)-(u:ℝ))
    (hwr : ∀j,(tw j:ℝ)-(u:ℝ)≤(1:ℝ)/(2:ℝ)^q)
    (hhl : ∀j,-((1:ℝ)/(2:ℝ)^q)≤(sh j:ℝ)-(v:ℝ))
    (hhr : ∀j,(th j:ℝ)-(v:ℝ)≤(1:ℝ)/(2:ℝ)^q) :
    ∃ B : BridgeGrid Rw Rh,B.u=u ∧ B.v=v ∧ B.sw=sw ∧ B.tw=tw ∧ B.sh=sh ∧ B.th=th := by
  have hlarge : ∀ᶠ p : ℕ in atTop,(100:ℝ)≤((2^p:ℕ):ℝ)*((v:ℝ)-(u:ℝ)) := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const (sub_pos.mpr huv)
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht.eventually_ge_atTop 100
  have huv' := aligned_intervals_eventually (fun _ : Fin 1 => u) (fun _ : Fin 1 => v) (fun _ => huv)
  obtain ⟨p,hpq,hpN,⟨aa,mm,hmm,haa,hmm'⟩,⟨aw,nw,hnw,haw,htw⟩,⟨ah,nh,hnh,hah,hth⟩⟩ :=
    (eventually_ge_atTop q |>.and (hlarge.and (huv'.and ((aligned_intervals_eventually sw tw hw).and
      (aligned_intervals_eventually sh th hh))))).exists
  let b := aa 0
  let N := mm 0
  let r := 2^(p-q)
  have hN : (N:ℝ)=((2^p:ℕ):ℝ)*((v:ℝ)-(u:ℝ)) := by
    have h1 := haa 0
    have h2 := hmm' 0
    dsimp [b,N] at *
    linarith
  have hr : (r:ℝ)=((2^p:ℕ):ℝ)*((1:ℝ)/(2:ℝ)^q) := by
    dsimp [r]
    push_cast
    rw [show p=q+(p-q) from (Nat.add_sub_of_le hpq).symm,pow_add]
    simp only [Nat.add_sub_cancel_left]
    field_simp
  have hpow : (0:ℝ)≤((2^p:ℕ):ℝ) := by positivity
  refine ⟨{
    p := p
    u := u
    v := v
    b := b
    N := N
    r := r

    large := ?_
    narrow := ?_
    hu := haa 0
    hv := hmm' 0,
    sw := sw
    tw := tw
    sh := sh
    th := th
    aw := fun j => aw j-b
    nw := nw
    ah := fun j => ah j-b
    nh := nh,
    pw := hnw
    ph := hnh
    hwleft := ?_
    hwright := ?_
    hhleft := ?_
    hhright := ?_,
    hsw := ?_
    htw := ?_
    hsh := ?_
    hth := ?_},rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact_mod_cast (by rw [hN]; exact hpN : (100:ℝ)≤N)
  · rw [hr,hN]
    nlinarith [mul_le_mul_of_nonneg_left hq hpow]
  · intro j
    have hb := haa 0
    have hj := haw j
    have h := mul_le_mul_of_nonneg_left (hwl j) hpow
    rw [mul_neg,←hr] at h
    exact_mod_cast (show -(r:ℝ)≤(aw j:ℝ)-(b:ℝ) by dsimp [b]; nlinarith)
  · intro j
    have hb := haa 0
    have hj := htw j
    have h := mul_le_mul_of_nonneg_left (hwr j) hpow
    rw [←hr] at h
    exact_mod_cast (show (aw j:ℝ)-(b:ℝ)+(nw j:ℝ)≤r by dsimp [b]; nlinarith)
  · intro j
    have hb := hmm' 0
    have hj := hah j
    have h := mul_le_mul_of_nonneg_left (hhl j) hpow
    rw [mul_neg,←hr] at h
    exact_mod_cast (show -(r:ℝ)≤(ah j:ℝ)-(b:ℝ)-(N:ℝ) by dsimp [b,N]; nlinarith)
  · intro j
    have hb := hmm' 0
    have hj := hth j
    have h := mul_le_mul_of_nonneg_left (hhr j) hpow
    rw [←hr] at h
    exact_mod_cast (show (ah j:ℝ)-(b:ℝ)+(nh j:ℝ)-(N:ℝ)≤r by dsimp [b,N]; nlinarith)
  · intro j; simpa only [sub_add_cancel] using haw j
  · intro j; simpa only [sub_add_cancel] using htw j
  · intro j; simpa only [sub_add_cancel] using hah j
  · intro j; simpa only [sub_add_cancel] using hth j
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ProductSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open scoped BigOperators
namespace StandardMapEntropy
lemma sum_product_error (s : Finset ℕ) (A B E : ℕ → ℝ) (C ε T : ℝ)
    (hC : 0≤ C) (hε : 0≤ ε)
    (hA : ∀j∈s,0≤ A j) (hB : ∀j∈s,0≤ B j) (hE : ∀j∈s,0≤ E j)
    (hAC : ∀j∈s,A j≤ C*ε) (hBC : ∀j∈s,B j≤ C*ε)
    (hT : (∑j∈s,A j)≤ T*ε ∨ (∑j∈s,B j)≤ T*ε) :
    (∑j∈s,(A j+E j)*B j)≤ C*ε*(T*ε+∑j∈s,E j) := by
  have hp : (∑j∈s,A j*B j)≤ C*ε*(T*ε) := by
    rcases hT with hT|hT
    · calc
        _ ≤ ∑j∈s,A j*(C*ε) := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hBC j hj) (hA j hj))
        _ = (∑j∈s,A j)*(C*ε) := by rw [Finset.sum_mul]
        _ ≤ (T*ε)*(C*ε) := mul_le_mul_of_nonneg_right hT (mul_nonneg hC hε)
        _ = _ := mul_comm _ _
    · calc
        _ ≤ ∑j∈s,(C*ε)*B j := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right (hAC j hj) (hB j hj))
        _ = C*ε*(∑j∈s,B j) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hT (mul_nonneg hC hε)
  have he : (∑j∈s,E j*B j)≤ C*ε*(∑j∈s,E j) := by
    calc
      _ ≤ ∑j∈s,E j*(C*ε) := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hBC j hj) (hE j hj))
      _ = _ := by rw [←Finset.sum_mul]; ring
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib,mul_add]
  exact add_le_add hp he
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeAggregate
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
lemma BridgeGrid.scale_bound {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (k : ℝ) (hc : BridgeScalarControl k) (lo len : ℕ) (ε : ℝ) (hε : 0< ε)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (hM : (2:ℝ)^10≤ growthBase k) (η : ℝ) (hη : 0<η)
    (hδ : 1/((B.N*2^lo:ℕ):ℝ)<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation B.sw B.tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))< d.val B.u B.v ∧ η< arrayObservation B.sh B.th Fh d) → F d=0)
    (C T : ℝ) (hC : 0≤ C)
    (hbW : ∀j<len,(∫ d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity))≤ C*ε)
    (hbH : ∀j<len,(∫ d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity))≤ C*ε)
    (hT : (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤ T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤ T) :
    (∫d,F d ∂scaleLaw k hc.nonneg (B.p+lo) len ε)≤
      (D*bridgeRealConstant/(η/2))*C*(T*ε+2/((B.N*2^lo:ℕ):ℝ)) := by
  let A (j : ℕ) := ∫d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  let H (j : ℕ) := ∫d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  let E (j : ℕ) := growthBase k^(-(1/10:ℝ)*((B.N*2^(lo+j):ℕ):ℝ))
  let V (j : ℕ) := ∫d,F d ∂sampleLaw k hc.nonneg (2^(B.p+lo+j)) (by positivity)
  have hNp : 1≤ B.N*2^lo := by
    have hN : 0< B.N := by have := B.large; omega
    have hh : 0< B.N*2^lo := Nat.mul_pos hN (by positivity)
    omega
  have hE0 (j) : 0≤ E j := by apply Real.rpow_nonneg; linarith [growthBase_ge_four k hc.nonneg]
  have hEb (j) : E j≤1/((B.N*2^lo:ℕ):ℝ) := by
    have hh := bridge_error_inverse (growthBase k) hM (B.N*2^lo) j hNp
    have he : B.N*2^(lo+j)=(B.N*2^lo)*2^j := by rw [pow_add,mul_assoc]
    dsimp [E]
    rw [he]
    apply hh.trans
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.le_mul_of_pos_right (B.N*2^lo) (by positivity : 0<2^j)
  have hEs : (∑j∈Finset.range len,E j)≤2/((B.N*2^lo:ℕ):ℝ) := by
    simpa only [E,pow_add,mul_assoc] using bridge_error_sum (growthBase k) hM (B.N*2^lo) len hNp
  have hV (j) : V j≤ (D*bridgeRealConstant/(η/2))*((A j+E j)*H j) := by
    have hh := B.sample_bound k hc (lo+j) Fw Fh L hFw hFh hW0 hH0 hlog hLM η hη ((hEb j).trans_lt hδ)
      F hF D hD hFW hzero
    dsimp only [V,A,E,H]
    simpa only [Nat.add_assoc,mul_div_assoc,mul_assoc,div_mul_eq_mul_div] using hh
  have hT' : (∑j∈Finset.range len,A j)≤T*ε ∨ (∑j∈Finset.range len,H j)≤T*ε := by
    rcases hT with hT|hT
    · left
      rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε _ (continuous_arrayObservation _ _ _ hFw.continuous)] at hT
      exact (div_le_iff₀ hε).mp hT
    · right
      rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε _ (continuous_arrayObservation _ _ _ hFh.continuous)] at hT
      exact (div_le_iff₀ hε).mp hT
  have hp := sum_product_error (Finset.range len) A H E C ε T hC hε.le
    (fun j _ => integral_nonneg hW0) (fun j _ => integral_nonneg hH0) (fun j _ => hE0 j)
    (fun j hj => hbW j (Finset.mem_range.mp hj)) (fun j hj => hbH j (Finset.mem_range.mp hj)) hT'
  have hd : 0≤ D*bridgeRealConstant/(η/2) := div_nonneg (mul_nonneg hD bridgeRealConstant_nonneg) (by linarith)
  rw [integral_scaleLaw k hc.nonneg (B.p+lo) len ε hε F hF]
  apply (div_le_iff₀ hε).mpr
  calc
    _ ≤ ∑j∈Finset.range len,(D*bridgeRealConstant/(η/2))*((A j+E j)*H j) := Finset.sum_le_sum (fun j _ => hV j)
    _ = (D*bridgeRealConstant/(η/2))*(∑j∈Finset.range len,(A j+E j)*H j) := by rw [Finset.mul_sum]
    _ ≤ (D*bridgeRealConstant/(η/2))*(C*ε*(T*ε+∑j∈Finset.range len,E j)) := mul_le_mul_of_nonneg_left hp hd
    _ ≤ (D*bridgeRealConstant/(η/2))*(C*ε*(T*ε+2/((B.N*2^lo:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add le_rfl hEs) (mul_nonneg hC hε.le)) hd
    _ = _ := by ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeMean
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
lemma integral_torusShortfall (k : ℝ) (hk : 0≤ k) (a : ℤ) (m : ℕ) :
    (∫z,torusShortfall k z a m ∂area)=meanDeficit k m := by
  have hz (z : Torus) : torusShortfall k z a m=torusShortfall k (torusIter k a z) 0 m := by rw [torusShortfall_shift,zero_add]
  simp_rw [hz]
  rw [integral_torusIter k a (fun z => torusShortfall k z 0 m),←meanDeficit_eq_integral_shortfall k hk m]
lemma lipschitz_sum_nonneg {R : ℕ} (F : (Fin R → ℝ) → ℝ) (L : NNReal)
    (hF : LipschitzWith L F) (hFz : F 0=0) (x : Fin R → ℝ) (hx : ∀j,0≤ x j) :
    F x≤ L*∑j,x j := by
  have hh := hF.dist_le_mul x 0
  simp only [hFz,dist_zero_right] at hh
  have hb : ‖x‖≤∑j,x j := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => hx j))).mpr
    intro j
    rw [Real.norm_eq_abs,abs_of_nonneg (hx j)]
    exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ j)
  exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_left hb L.coe_nonneg))
lemma integral_observation_bound {R : ℕ} (k : ℝ) (hk : 0≤ k)
    (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀j,0< m j)
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F) (hFz : F 0=0) :
    (∫z,shortfallObservation k a m F z ∂area)≤ L*∑j,meanDeficit k (m j) := by
  have hi (j) : Integrable (fun z => torusShortfall k z (a j) (m j)) area :=
    (continuous_torusShortfall k hk _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have his := integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hh : (∫z,shortfallObservation k a m F z ∂area)≤
      ∫z,(L:ℝ)*∑j,torusShortfall k z (a j) (m j) ∂area := by
    apply integral_mono ((continuous_shortfall_observation k hk a m F hF.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (his.const_mul L)
    intro z
    exact lipschitz_sum_nonneg F L hF hFz _ (fun j => (torusShortfall_mem k hk z (a j) (m j) (hm j)).1)
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hi j)] at hh
  simpa only [integral_torusShortfall k hk] using hh
lemma deficit_fixed_scaled (k : ℝ) (hk : 0≤ k) (m p l H q : ℕ) (hm : 0< m)
    (hmp : m≤ 2^(p+H)) (hq : p+l≤ q) :
    meanDeficit k (m*2^l)≤ (2:ℝ)^(p+H)*meanDeficit k (2^(q+H)) := by
  have hn : m*2^l≤ 2^(p+l+H) := by
    calc
      _ ≤ 2^(p+H)*2^l := Nat.mul_le_mul_right _ hmp
      _ = _ := by rw [←pow_add]; congr 1; omega
  have hr : ((2^(p+l+H):ℕ):ℝ)/((m*2^l:ℕ):ℝ)≤ (2:ℝ)^(p+H) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<((m*2^l:ℕ):ℝ))).mpr
    have hmR : (1:ℝ)≤ m := by exact_mod_cast hm
    push_cast
    rw [show p+l+H=(p+H)+l by omega,pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hmR (show (0:ℝ)≤ 2^(p+H)*2^l by positivity)]
  exact (meanDeficit_ratio k hk _ _ (by positivity) hn).trans
    ((mul_le_mul_of_nonneg_right hr (meanDeficit_bounds k hk _ (by positivity)).1).trans
      (mul_le_mul_of_nonneg_left (meanDeficit_pow_mono k hk (Nat.add_le_add_right hq H)) (by positivity)))
namespace CriticalScaleSequence
lemma observation_scaled_bound (S : CriticalScaleSequence) {R : ℕ}
    (p : ℕ) (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀j,0< m j)
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F) (hFz : F 0=0) :
    ∃ C : ℝ,0≤ C ∧ ∀i l,p+l≤ S.exponent i →
      (∫z,shortfallObservation (S.parameter i) (fun j => a j*2^l) (fun j => m j*2^l) F z ∂area)≤ C*S.epsilon i := by
  obtain ⟨H,hH⟩ := exists_nat_gt (∑j,m j)
  have hmH (j) : m j≤ 2^(p+H) := by
    have hh : m j≤ ∑j,m j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    have hpow : H≤ 2^H := Nat.le_of_lt (Nat.lt_two_pow_self (n := H))
    exact hh.trans (hH.le.trans (hpow.trans (Nat.pow_le_pow_right (by omega) (by omega))))
  have hdc := doublingConstant_pos
  refine ⟨L*(R:ℝ)*((2:ℝ)^(p+H)*(2*(2*doublingConstant)^H)),by positivity,?_⟩
  intro i l hl
  apply (integral_observation_bound (S.parameter i) (S.positive i).le _ _
    (fun j => Nat.mul_pos (hm j) (by positivity)) F L hF hFz).trans
  have hb (j) : meanDeficit (S.parameter i) (m j*2^l)≤
      ((2:ℝ)^(p+H)*(2*(2*doublingConstant)^H))*S.epsilon i := by
    exact (deficit_fixed_scaled _ (S.positive i).le (m j) p l H (S.exponent i) (hm j) (hmH j) hl).trans
      ((mul_le_mul_of_nonneg_left (S.terminal i H) (by positivity)).trans_eq (by dsimp [epsilon]; ring))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  have hmul := mul_le_mul_of_nonneg_left hh L.coe_nonneg
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hmul
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ClippedTests
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
lemma clippedTest_le (j : ArrayTestIndex) (d : DistanceArray) : clippedTest j d≤ arrayTest j d := by
  rw [clippedTest_eq]
  have hh := unitClip_lipschitz.dist_le_mul
    (arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d)
    (arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hh
  have hs := mul_self_le_mul_self (abs_nonneg _) hh
  simp only [←sq, sq_abs] at hs
  change _≤ arrayJ j.val.1 j.val.2 d+arrayV j.val.1 j.val.2 d
  unfold arrayV
  linarith
lemma continuous_clippedTest (j : ArrayTestIndex) : Continuous (clippedTest j) :=
  continuous_arrayObservation _ _ _ testObservation_lipschitz.continuous
lemma integrable_clippedTest (μ : Measure DistanceArray) [IsFiniteMeasure μ] (j : ArrayTestIndex) :
    Integrable (clippedTest j) μ :=
  (continuous_clippedTest j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeCritical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
lemma aligned_observation_bound (S : CriticalScaleSequence) {R : ℕ}
    (p : ℕ) (s t : Fin R → DyadicTime) (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀j,0< m j)
    (hs : ∀j,((2^p:ℕ):ℝ)*(s j:ℝ)=(a j:ℝ))
    (ht : ∀j,((2^p:ℕ):ℝ)*(t j:ℝ)=(a j:ℝ)+(m j:ℝ))
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F) (hFz : F 0=0) :
    ∃ C : ℝ,0≤ C ∧ ∀i l,p+l≤ S.exponent i →
      (∫d,arrayObservation s t F d ∂sampleLaw (S.parameter i) (S.positive i).le (2^(p+l)) (by positivity))≤ C*S.epsilon i := by
  obtain ⟨C,hC,hb⟩ := S.observation_scaled_bound p a m hm F L hF hFz
  refine ⟨C,hC,?_⟩
  intro i l hl
  rw [integral_observable_sample _ (S.positive i).le _ (by positivity) s t (fun j => a j*2^l) (fun j => m j*2^l)
    (fun j => Nat.mul_pos (hm j) (by positivity)) (fun j => aligned_scale p l (s j) (a j) (hs j))
    (fun j => aligned_scale_end p l (t j) (a j) (m j) (ht j)) F hF.continuous]
  exact hb i l hl
lemma bridge_grid_mean_bounds (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0) :
    ∃ C : ℝ,0≤ C ∧ ∀i l,B.p+l≤ S.exponent i →
      (∫d,arrayObservation B.sw B.tw Fw d ∂sampleLaw (S.parameter i) (S.positive i).le (2^(B.p+l)) (by positivity))≤ C*S.epsilon i ∧
      (∫d,arrayObservation B.sh B.th Fh d ∂sampleLaw (S.parameter i) (S.positive i).le (2^(B.p+l)) (by positivity))≤ C*S.epsilon i := by
  obtain ⟨Cw,hCw,hw⟩ := S.aligned_observation_bound B.p B.sw B.tw (fun j => B.aw j+B.b) B.nw B.pw B.hsw B.htw Fw L hFw hFwz
  obtain ⟨Ch,hCh,hh⟩ := S.aligned_observation_bound B.p B.sh B.th (fun j => B.ah j+B.b) B.nh B.ph B.hsh B.hth Fh L hFh hFhz
  refine ⟨max Cw Ch,hCw.trans (le_max_left _ _),?_⟩
  intro i l hl
  exact ⟨(hw i l hl).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (S.epsilon_pos i).le),
    (hh i l hl).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (S.epsilon_pos i).le)⟩
lemma bridge_integral_tendsto (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (p len : ℕ → ℕ) (hp : Tendsto p atTop atTop)
    (hpl : ∀i j,j<len i → p i+j≤ S.exponent i)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (T : ℝ) (hT : ∀ᶠ i in atTop,
      (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤ T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤ T)
    (η : ℝ) (hη : 0<η) (F : DistanceArray → ℝ) (hF : Continuous F) (hF0 : ∀d,0≤ F d)
    (D : ℝ) (hD : 0≤ D) (hFW : ∀d,F d≤ D*arrayObservation B.sw B.tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))< d.val B.u B.v ∧ η< arrayObservation B.sh B.th Fh d) → F d=0) :
    Tendsto (fun i => ∫d,F d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hmeans⟩ := S.bridge_grid_mean_bounds B Fw Fh L hFw hFh hFwz hFhz
  have hlo : Tendsto (fun i => p i-B.p) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    filter_upwards [hp.eventually_ge_atTop (n+B.p)] with i hi
    omega
  have hn : Tendsto (fun i => ((B.N*2^(p i-B.p):ℕ):ℝ)) atTop atTop := by
    have hpow : Tendsto (fun i => (2:ℝ)^(p i-B.p)) atTop atTop := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp hlo
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hpow.const_mul_atTop (show (0:ℝ)<B.N by exact_mod_cast (show 0<B.N from by have := B.large; omega))
  have hinv : Tendsto (fun i => 1/((B.N*2^(p i-B.p):ℕ):ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hn
  have hdelta : ∀ᶠ i in atTop,1/((B.N*2^(p i-B.p):ℕ):ℝ)<η/2 := hinv.eventually_lt_const (by linarith)
  have hc := S.parameter_tendsto.eventually eventually_bridgeScalarControl
  have hs := S.parameter_tendsto.eventually (eventually_bridge_observation_scalars (L:ℝ))
  have hM := (tendsto_growthBase.comp S.parameter_tendsto).eventually_ge_atTop ((2:ℝ)^10)
  apply squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg hF0))
  · filter_upwards [hp.eventually_ge_atTop B.p,hdelta,hc,hs,hM,hT] with i hi hdi hci hsi hMi hTi
    have he : B.p+(p i-B.p)=p i := Nat.add_sub_of_le hi
    have hb := B.scale_bound (S.parameter i) hci (p i-B.p) (len i) (S.epsilon i) (S.epsilon_pos i)
      Fw Fh L hFw hFh hW0 hH0 hsi.1 hsi.2 hMi η hη hdi F hF D hD hFW hzero C T hC
      (fun j hj => by simpa only [←Nat.add_assoc,he] using (hmeans i (p i-B.p+j) (by have := hpl i j hj; omega)).1)
      (fun j hj => by simpa only [←Nat.add_assoc,he] using (hmeans i (p i-B.p+j) (by have := hpl i j hj; omega)).2)
      (by simpa only [he] using hTi)
    simpa only [he] using hb
  · have ht := (S.epsilon_tendsto.const_mul T).add (hinv.const_mul 2)
    have hh := ht.const_mul ((D*bridgeRealConstant/(η/2))*C)
    convert! hh using 1 <;> simp only [mul_zero,add_zero,mul_one_div]
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeVague
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma isOpen_arrayBridgeEvent {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (ηw ηh : ℝ)
    (hw : Continuous Fw) (hh : Continuous Fh) : IsOpen (arrayBridgeEvent B Fw Fh ηw ηh) :=
  (isOpen_lt continuous_const (continuous_arrayEval B.u B.v)).inter
    ((isOpen_lt continuous_const (continuous_arrayObservation _ _ _ hw)).inter
      (isOpen_lt continuous_const (continuous_arrayObservation _ _ _ hh)))
namespace CriticalScaleSequence
lemma bridge_vague_tendsto (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (p len : ℕ → ℕ) (hp : Tendsto p atTop atTop)
    (hpl : ∀i j,j<len i → p i+j≤S.exponent i)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (T : ℝ) (hT : ∀ᶠ i in atTop,
      (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤T)
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) (g : C_c(NonAffineArray,ℝ))
    (hg : ∀d,0≤g d) (hz : ∀d : NonAffineArray,d.val∉arrayBridgeEvent B Fw Fh ηw ηh → g d=0) :
    Tendsto (fun i => ∫d,g d ∂nonaffinePart (scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))) atTop (𝓝 0) := by
  let F := arrayTestExtend g
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
  have hFz : ∀d,d∉arrayBridgeEvent B Fw Fh ηw ηh → F d=0 := by
    intro d hd
    by_cases ha : d∈affineLocus
    · exact arrayTestExtend_affine g d ha
    · exact (arrayTestExtend_apply g ⟨d,ha⟩).trans (hz ⟨d,ha⟩ hd)
  have hF0 : ∀d,0≤F d := by
    intro d
    by_cases ha : d∈affineLocus
    · rw [show F d=0 from arrayTestExtend_affine g d ha]
    · rw [arrayTestExtend_apply g ⟨d,ha⟩]; exact hg _
  have hFB : ∀d,F d≤ max C 0 := by
    intro d
    have hb : |F d|≤C := by convert! hC d (mem_univ d) using 1
    exact (le_abs_self _).trans (hb.trans (le_max_left _ _))
  have hFW : ∀d,F d≤(max C 0/ηw)*arrayObservation B.sw B.tw Fw d := by
    intro d
    by_cases hd : d∈arrayBridgeEvent B Fw Fh ηw ηh
    · have hpos := hd.2.1
      have hh := mul_le_mul_of_nonneg_left hpos.le (div_nonneg (le_max_right C 0) hηw.le)
      rw [div_mul_cancel₀ _ hηw.ne'] at hh
      exact (hFB d).trans hh
    · rw [hFz d hd]
      exact mul_nonneg (div_nonneg (le_max_right _ _) hηw.le) (hW0 d)
  have hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))<d.val B.u B.v ∧ ηh<arrayObservation B.sh B.th Fh d) → F d=0 := by
    intro d hd
    apply hFz
    exact fun h => hd ⟨h.1,h.2.2⟩
  have hh := S.bridge_integral_tendsto B p len hp hpl Fw Fh L hFw hFh hFwz hFhz hW0 hH0 T hT
    ηh hηh F F.continuous hF0 (max C 0/ηw) (div_nonneg (le_max_right _ _) hηw.le) hFW hzero
  simpa only [F,integral_arrayTestExtend] using hh
lemma bridge_null_of_limit (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (p len : ℕ → ℕ) (hp : Tendsto p atTop atTop)
    (hpl : ∀i j,j<len i → p i+j≤S.exponent i)
    (ν : Measure NonAffineArray) [ν.Regular] (l : Filter ℕ) [l.NeBot] (hl : l≤atTop)
    (hconv : ∀g : C_c(NonAffineArray,ℝ),Tendsto (fun i => ∫d,g d ∂nonaffinePart
      (scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))) l (𝓝 (∫d,g d ∂ν)))
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤arrayObservation B.sh B.th Fh d)
    (T : ℝ) (hT : ∀ᶠ i in atTop,
      (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤T ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤T)
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    ν {d | d.val∈arrayBridgeEvent B Fw Fh ηw ηh}=0 := by
  apply vague_open_null l _ ν hconv ((isOpen_arrayBridgeEvent B Fw Fh ηw ηh hFw.continuous hFh.continuous).preimage continuous_subtype_val)
  intro g hg hz
  exact (S.bridge_vague_tendsto B p len hp hpl Fw Fh L hFw hFh hFwz hFhz hW0 hH0 T hT ηw ηh hηw hηh g hg hz).mono_left hl
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_LimitBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
lemma bridge_test_bound (S : CriticalScaleSequence) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (p len : ℕ → ℕ) (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ)
    (j : ArrayTestIndex)
    (htest : (∀d,arrayObservation B.sw B.tw Fw d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th Fh d=clippedTest j d))
    (C : ℝ) (hC : ∀ᶠ i in atTop,(∫d,arrayTest j d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤C) :
    ∀ᶠ i in atTop,
      (∫d,arrayObservation B.sw B.tw Fw d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤C ∨
      (∫d,arrayObservation B.sh B.th Fh d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤C := by
  filter_upwards [hC] with i hi
  have hh : (∫d,clippedTest j d ∂scaleLaw (S.parameter i) (S.positive i).le (p i) (len i) (S.epsilon i))≤C := by
    apply le_trans _ hi
    apply integral_mono (integrable_clippedTest _ j)
      ((continuous_arrayTest j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    exact clippedTest_le j
  rcases htest with htest|htest
  · left; simpa only [htest] using hh
  · right; simpa only [htest] using hh
lemma bridge_null_multi (S : CriticalScaleSequence) (K : S.LimitLaws) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤arrayObservation B.sh B.th Fh d)
    (j : ArrayTestIndex)
    (htest : (∀d,arrayObservation B.sw B.tw Fw d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th Fh d=clippedTest j d))
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    K.multi {d | d.val∈arrayBridgeEvent B Fw Fh ηw ηh}=0 := by
  obtain ⟨C,hC⟩ := S.multiLaw_test_bound j
  exact S.bridge_null_of_limit B (criticalLowerExponent S.offset)
    (fun i => S.exponent i-criticalLowerExponent S.offset i) S.lowerExponent_tendsto
    (fun i j hj => by have := S.lower_lt i; omega) K.multi K.filter K.refines K.multi_converges
    Fw Fh L hFw hFh hFwz hFhz hW0 hH0 C (S.bridge_test_bound B _ _ Fw Fh j htest C hC) ηw ηh hηw hηh
lemma bridge_null_terminal (S : CriticalScaleSequence) (K : S.LimitLaws) {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh) (hFwz : Fw 0=0) (hFhz : Fh 0=0)
    (hW0 : ∀d,0≤arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤arrayObservation B.sh B.th Fh d)
    (j : ArrayTestIndex)
    (htest : (∀d,arrayObservation B.sw B.tw Fw d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th Fh d=clippedTest j d))
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    K.terminal {d | d.val∈arrayBridgeEvent B Fw Fh ηw ηh}=0 := by
  obtain ⟨C,hC⟩ := S.terminalLaw_test_bound j
  exact S.bridge_null_of_limit B S.exponent (fun _ => 1) S.exponent_tendsto
    (fun i j hj => by omega) K.terminal K.filter K.refines K.terminal_converges
    Fw Fh L hFw hFh hFwz hFhz hW0 hH0 C (S.bridge_test_bound B _ _ Fw Fh j htest C hC) ηw ηh hηw hηh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EndpointObservations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
lemma endpoint_bridge_null (S : CriticalScaleSequence) (K : S.LimitLaws) (select : Bool)
    (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ)) (W H : EndpointObservation)
    (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
    (hW : W.inWindow u q) (hH : H.inWindow v q) (j : ArrayTestIndex)
    (htest : (∀d,W.value d=clippedTest j d) ∨ (∀d,H.value d=clippedTest j d))
    (ηw ηh : ℝ) (hηw : 0<ηw) (hηh : 0<ηh) :
    K.selected S select {d | d.val∈endpointBridgeEvent u v W H ηw ηh}=0 := by
  obtain ⟨B,hu,hv,hsw,htw,hsh,hth⟩ := exists_bridgeGrid u v huv W.left W.right H.left H.right W.ordered H.ordered
    q hq hW.1 hW.2 hH.1 hH.2
  have hW0 : ∀d,0≤ arrayObservation B.sw B.tw W.function d := by simpa only [hsw,htw] using W.nonneg
  have hH0 : ∀d,0≤ arrayObservation B.sh B.th H.function d := by simpa only [hsh,hth] using H.nonneg
  have htest' : (∀d,arrayObservation B.sw B.tw W.function d=clippedTest j d) ∨
      (∀d,arrayObservation B.sh B.th H.function d=clippedTest j d) := by
    simpa only [hsw,htw,hsh,hth,EndpointObservation.value] using htest
  have he : {d : NonAffineArray | d.val∈arrayBridgeEvent B W.function H.function ηw ηh}=
      {d : NonAffineArray | d.val∈endpointBridgeEvent u v W H ηw ηh} := by
    simp only [arrayBridgeEvent,endpointBridgeEvent,hu,hv,hsw,htw,hsh,hth,EndpointObservation.value]
  cases select
  · exact he ▸ S.bridge_null_terminal K B W.function H.function 6 W.lipschitz H.lipschitz W.at_zero H.at_zero hW0 hH0 j htest' ηw ηh hηw hηh
  · exact he ▸ S.bridge_null_multi K B W.function H.function 6 W.lipschitz H.lipschitz W.at_zero H.at_zero hW0 hH0 j htest' ηw ηh hηw hηh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_BridgeExclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (K : S.LimitLaws)
lemma endpoint_bridge_ae (select : Bool) (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ))
    (W H : EndpointObservation) (q : ℕ) (hq : (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000)
    (hW : W.inWindow u q) (hH : H.inWindow v q) (j : ArrayTestIndex)
    (htest : (∀d,W.value d=clippedTest j d) ∨ (∀d,H.value d=clippedTest j d)) :
    ∀ᵐ d ∂K.selected S select,0< W.value d.val → 0< H.value d.val →
      d.val.val u v≤(999/1000:ℝ)*((v:ℝ)-(u:ℝ)) := by
  have hh (a c : ℚ) : ∀ᵐ d ∂K.selected S select,
      0<(a:ℝ) → 0<(c:ℝ) → ¬ d.val∈endpointBridgeEvent u v W H a c := by
    by_cases ha : 0<(a:ℝ)
    · by_cases hc : 0<(c:ℝ)
      · have hn : ∀ᵐ d ∂K.selected S select,¬d.val∈endpointBridgeEvent u v W H a c :=
          ae_iff.mpr (by simpa only [not_not] using S.endpoint_bridge_null K select u v huv W H q hq hW hH j htest a c ha hc)
        filter_upwards [hn] with d hd
        exact fun _ _ => hd
      · exact Eventually.of_forall fun d _ hc' => (hc hc').elim
    · exact Eventually.of_forall fun d ha' _ => (ha ha').elim
  filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (hh a))] with d hd
  intro hw hh
  obtain ⟨a,ha0,ha⟩ := exists_rat_btwn hw
  obtain ⟨c,hc0,hc⟩ := exists_rat_btwn hh
  by_contra hn
  exact hd a c ha0 hc0 ⟨lt_of_not_ge hn,ha,hc⟩
lemma dyadicBridge_aeselected_q3_oai (select : Bool) : ∀ᵐ d ∂K.selected S select,DyadicBridgeExclusions d.val := by
  have hh (u v : DyadicTime) (q : ℕ) (j l : ArrayTestIndex) (b : Bool) :
      ∀ᵐ d ∂K.selected S select,
      (u:ℝ)<(v:ℝ) → (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 →
      (bridgeLeft b j l).inWindow u q → (bridgeRight b j l).inWindow v q →
      0<(bridgeLeft b j l).value d.val → 0<(bridgeRight b j l).value d.val →
      d.val.val u v≤(999/1000:ℝ)*((v:ℝ)-(u:ℝ)) := by
    by_cases h : (u:ℝ)<(v:ℝ) ∧ (1:ℝ)/(2:ℝ)^q≤((v:ℝ)-(u:ℝ))/1000 ∧
        (bridgeLeft b j l).inWindow u q ∧ (bridgeRight b j l).inWindow v q
    · have he : (∀d,(bridgeLeft b j l).value d=clippedTest j d) ∨
          (∀d,(bridgeRight b j l).value d=clippedTest j d) := by
        cases b <;> simp [bridgeLeft,bridgeRight]
      filter_upwards [S.endpoint_bridge_ae K select u v h.1 _ _ q h.2.1 h.2.2.1 h.2.2.2 j he] with d hd
      exact fun _ _ _ _ => hd
    · exact Eventually.of_forall fun d h1 h2 h3 h4 => (h ⟨h1,h2,h3,h4⟩).elim
  exact ae_all_iff.mpr fun u => ae_all_iff.mpr fun v => ae_all_iff.mpr fun q =>
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun l => ae_all_iff.mpr (hh u v q j l)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected_q3_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.dyadicBridge_aeselected_q3_oai
