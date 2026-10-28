-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:35:46.938+00:00
-- url     : https://prove2.me/submissions/4d203a58-cc26-49e5-a933-266a60c4dc9a

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_shape_aeterminal_q44

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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SmoothCap
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Interval Topology
namespace StandardMapEntropy
lemma capSlope_contDiff : ContDiff ℝ 2 capSlope := by unfold capSlope; fun_prop
lemma capSlope_continuous : Continuous capSlope := capSlope_contDiff.continuous
lemma capSlope_bounds (u : ℝ) : 0≤ capSlope u ∧ capSlope u≤1 := by
  unfold capSlope
  constructor <;> linarith [Real.smoothTransition.le_one (10000*u-1),Real.smoothTransition.nonneg (10000*u-1)]
lemma capSlope_one {u : ℝ} (hu : u≤1/10000) : capSlope u=1 := by
  unfold capSlope
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring
lemma capSlope_zero {u : ℝ} (hu : 1/5000≤ u) : capSlope u=0 := by
  unfold capSlope
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring
lemma capPrimitive_hasDerivAt (u : ℝ) : HasDerivAt capPrimitive (capSlope u) u := by
  exact intervalIntegral.integral_hasDerivAt_right (capSlope_continuous.intervalIntegrable 0 u)
    (capSlope_continuous.stronglyMeasurableAtFilter volume (𝓝 u)) capSlope_continuous.continuousAt
lemma capPrimitive_deriv : deriv capPrimitive=capSlope := funext (fun u => (capPrimitive_hasDerivAt u).deriv)
lemma capPrimitive_contDiff : ContDiff ℝ 2 capPrimitive := by
  suffices ContDiff ℝ ((1 : WithTop ℕ∞)+1) capPrimitive by (convert this using 1; norm_num)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun u => (capPrimitive_hasDerivAt u).differentiableAt,?_,?_⟩
  · norm_num
  · rw [capPrimitive_deriv]
    exact capSlope_contDiff.of_le (by norm_num)
lemma capPrimitive_monotone : Monotone capPrimitive := by
  intro x y hxy
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (capSlope_continuous.intervalIntegrable 0 x) (capSlope_continuous.intervalIntegrable x y)
  have h0 := intervalIntegral.integral_nonneg (μ := volume) hxy (fun t _ => (capSlope_bounds t).1)
  change (∫ t in (0:ℝ)..x,capSlope t)≤(∫ t in (0:ℝ)..y,capSlope t)
  linarith
lemma capPrimitive_linear {u : ℝ} (hu : u≤1/10000) : capPrimitive u=u := by
  unfold capPrimitive
  have he : (∫ t in (0:ℝ)..u,capSlope t)=(∫ _t in (0:ℝ)..u,(1:ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply capSlope_one
    rw [mem_uIcc] at ht
    rcases ht with ⟨h0,h1⟩|⟨h0,h1⟩ <;> linarith
  rw [he,intervalIntegral.integral_const]
  simp
lemma capPrimitive_constant {u : ℝ} (hu : 1/5000≤ u) : capPrimitive u=capBase := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (capSlope_continuous.intervalIntegrable 0 (1/5000)) (capSlope_continuous.intervalIntegrable (1/5000) u)
  have hzero : (∫ t in (1/5000:ℝ)..u,capSlope t)=0 := by
    calc
      (∫ t in (1/5000:ℝ)..u,capSlope t)=(∫ _t in (1/5000:ℝ)..u,(0:ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact capSlope_zero (by rw [uIcc_of_le hu] at ht; exact ht.1)
      _=0 := by simp
  rw [hzero,add_zero] at he
  exact he.symm
lemma capBase_bounds : (1/10000:ℝ)≤ capBase ∧ capBase≤1/5000 := by
  constructor
  · have hh := capPrimitive_monotone (by norm_num : (1/10000:ℝ)≤1/5000)
    rwa [capPrimitive_linear (by norm_num : (1/10000:ℝ)≤1/10000)] at hh
  · unfold capBase capPrimitive
    calc
      (∫ t in (0:ℝ)..(1/5000:ℝ),capSlope t)≤∫ _t in (0:ℝ)..(1/5000:ℝ),(1:ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num) (capSlope_continuous.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        exact fun t _ => (capSlope_bounds t).2
      _=1/5000 := by simp
lemma entropyCap_contDiff (α : ℝ) : ContDiff ℝ 2 (entropyCap α) := by
  unfold entropyCap
  exact (contDiff_const.mul capPrimitive_contDiff).add
    (contDiff_const.mul (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))
lemma entropyCap_linear {α u : ℝ} (hu : u≤1/10000) : entropyCap α u=α*u := by
  unfold entropyCap
  rw [capPrimitive_linear hu,Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring
lemma entropyCap_one {α u : ℝ} (hu : 3/10000≤ u) : entropyCap α u=1 := by
  unfold entropyCap
  rw [capPrimitive_constant (by linarith),Real.smoothTransition.one_of_one_le (by linarith)]
  ring
lemma entropyCap_monotone {α : ℝ} (hα : 0≤α) (hα1 : α≤1) : Monotone (entropyCap α) := by
  have hc : 0≤1-α*capBase := by nlinarith [capBase_bounds.1,capBase_bounds.2]
  intro x y hxy
  unfold entropyCap
  exact add_le_add (mul_le_mul_of_nonneg_left (capPrimitive_monotone hxy) hα)
    (mul_le_mul_of_nonneg_left (Real.smoothTransition.monotone (by linarith)) hc)
lemma entropyCap_bounds {α u : ℝ} (hα : 0≤α) (hα1 : α≤1) (hu : u∈Icc (0:ℝ) 1) :
    0≤ entropyCap α u ∧ entropyCap α u≤1 := by
  have h0 := entropyCap_monotone hα hα1 hu.1
  have h1 := entropyCap_monotone hα hα1 hu.2
  rw [entropyCap_linear (by norm_num),mul_zero] at h0
  rw [entropyCap_one (u := 1) (by norm_num)] at h1
  exact ⟨h0,h1⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SmoothControl
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
lemma c2_deriv_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) := by
  apply ContDiff.deriv'
  convert! hf using 1
  all_goals try with_reducible_and_instances rfl
lemma c2_compact_bounds {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (a b : ℝ) :
    ∃C≥0,(∀x∈Icc a b,|deriv f x|≤C) ∧ (∀x∈Icc a b,|deriv (deriv f) x|≤C) := by
  obtain ⟨C1,h1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuous_deriv (by norm_num)).continuousOn (s := Icc a b)
  obtain ⟨C2,h2⟩ := isCompact_Icc.exists_bound_of_continuousOn ((c2_deriv_contDiff hf).continuous_deriv_one).continuousOn (s := Icc a b)
  refine ⟨max 0 (max C1 C2),le_max_left _ _,?_,?_⟩
  · intro x hx
    exact (h1 x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro x hx
    exact (h2 x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
lemma deriv_bound_lipschitz {f : ℝ → ℝ} (hf : Differentiable ℝ f) {a b C x y : ℝ}
    (hb : ∀u∈Icc a b,|deriv f u|≤C) (hx : x∈Icc a b) (hy : y∈Icc a b) :
    |f y-f x|≤C*|y-x| := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => hf u) hb (convex_Icc _ _) hx hy
lemma entropyCap_upper {α : ℝ} (hα : 0≤α) (hα1 : α≤1) :
    ∃C>0,∀u∈Icc (0:ℝ) 1,entropyCap α u≤C*u := by
  obtain ⟨C,hC,h1,_⟩ := c2_compact_bounds (entropyCap_contDiff α) 0 1
  refine ⟨C+1,by linarith,?_⟩
  intro u hu
  have hh := deriv_bound_lipschitz ((entropyCap_contDiff α).differentiable (by norm_num)) h1
    (by constructor <;> norm_num : (0:ℝ)∈Icc 0 1) hu
  rw [entropyCap_linear (u := 0) (by norm_num),mul_zero,sub_zero,sub_zero,abs_of_nonneg hu.1,
    abs_of_nonneg (entropyCap_bounds hα hα1 hu).1] at hh
  nlinarith [hu.1]
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
lemma criticalTheta_pos (r i : ℕ) : 0 < criticalTheta r i := by unfold criticalTheta; positivity
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
lemma epsilon_pos (i : ℕ) : 0 < S.epsilon i := (criticalTheta_pos S.offset i).trans (S.threshold i)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayTests
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RescaledArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma sampleArray_translate (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n)
    (r : DyadicTime) (a : ℤ) (ha : (n:ℝ)*(r:ℝ)=(a:ℝ)) :
    arrayTranslate r (sampleArray k hk z n hn)=sampleArray k hk (torusIter k a z) n hn := by
  apply Subtype.ext
  funext s t
  change productDistance k z ⌊(n:ℝ)*(↑(s+r):ℝ)⌋ ⌊(n:ℝ)*(↑(t+r):ℝ)⌋/(n:ℝ)=
    productDistance k (torusIter k a z) ⌊(n:ℝ)*(s:ℝ)⌋ ⌊(n:ℝ)*(t:ℝ)⌋/(n:ℝ)
  rw [productDistance_shift]
  simp only [AddSubgroup.coe_add,mul_add,ha,Int.floor_add_intCast]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SampleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma sampleLaw_translate (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n)
    (r : DyadicTime) (a : ℤ) (ha : (n:ℝ)*(r:ℝ)=(a:ℝ)) :
    (sampleLaw k hk n hn).map (arrayTranslate r)=sampleLaw k hk n hn := by
  unfold sampleLaw
  rw [Measure.map_map (continuous_arrayTranslate r).measurable (continuous_sampleArray k hk n hn).measurable]
  have he : (arrayTranslate r) ∘ (fun z => sampleArray k hk z n hn)=
      (fun z => sampleArray k hk z n hn) ∘ (torusIter k a) := by
    funext z; exact sampleArray_translate k hk z n hn r a ha
  rw [he,← Measure.map_map (continuous_sampleArray k hk n hn).measurable (continuous_torusIter k a).measurable,
    (measurePreserving_torusIter k a).map_eq]
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
-- module Solutions.OAIQ44_CM.StandardMap_ScaleLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma scaleLaw_translate (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (r : DyadicTime)
    (a : ℤ) (ha : ((2^p:ℕ):ℝ)*(r:ℝ)=(a:ℝ)) :
    (scaleLaw k hk p l ε).map (arrayTranslate r)=scaleLaw k hk p l ε := by
  unfold scaleLaw
  rw [Measure.map_smul,Measure.map_finset_sum (continuous_arrayTranslate r).measurable.aemeasurable]

  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply sampleLaw_translate k hk _ _ r (a*2^i)
  push_cast at ha ⊢
  rw [pow_add]
  calc
    _ = (((2:ℝ)^p)*(r:ℝ))*(2:ℝ)^i := by ring
    _ = _ := by rw [ha]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ScaleTestBounds
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CriticalLaws
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_NonaffineLimits
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal CompactlySupported Classical
namespace StandardMapEntropy
lemma integral_nonaffinePart_le (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (F : DistanceArray → ℝ) (hF : Continuous F) (hF0 : ∀ d,0≤F d) :
    (∫ d : NonAffineArray,F d.val ∂nonaffinePart μ)≤∫ d,F d ∂μ := by
  have he : (∫ d : NonAffineArray,F d.val ∂nonaffinePart μ)=∫ d in affineLocusᶜ,F d ∂μ := by
    convert! integral_subtype_comap isClosed_affineLocus.isOpen_compl.measurableSet F using 1
    all_goals try with_reducible_and_instances rfl
  rw [he]
  exact setIntegral_le_integral (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall hF0)
lemma integrable_nonaffinePart (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (F : DistanceArray → ℝ) (hF : Continuous F) : Integrable (fun d : NonAffineArray => F d.val) (nonaffinePart μ) := by
  have hi := (hF.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)).restrict (s := affineLocusᶜ)
  rw [← map_comap_subtype_coe isClosed_affineLocus.isOpen_compl.measurableSet,
    (MeasurableEmbedding.subtype_coe isClosed_affineLocus.isOpen_compl.measurableSet).integrable_map_iff] at hi
  exact hi
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
    all_goals try with_reducible_and_instances rfl
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
-- module Solutions.OAIQ44_CM.StandardMap_LimitActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma arrayTestExtend_translate (g : C_c(NonAffineArray,ℝ)) (r : DyadicTime) (d : DistanceArray) :
    arrayTestExtend (g.comp (nonaffineTranslation r).toCocompactMap) d=
      arrayTestExtend g (arrayTranslate r d) := by
  by_cases hd : d∈affineLocus
  · rw [arrayTestExtend_affine _ d hd,arrayTestExtend_affine _ _ ((arrayTranslate_mem_affine_iff r d).mpr hd)]
  · exact (arrayTestExtend_apply _ ⟨d,hd⟩).trans (arrayTestExtend_apply g (nonaffineTranslation r ⟨d,hd⟩)).symm
lemma integral_translate_nonaffine (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (r : DyadicTime) (hμ : μ.map (arrayTranslate r)=μ) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart μ)=
      ∫ d,g d ∂nonaffinePart μ := by
  rw [← integral_arrayTestExtend,← integral_arrayTestExtend]
  simp_rw [arrayTestExtend_translate]
  rw [← integral_map (f := fun d => arrayTestExtend g d) (continuous_arrayTranslate r).measurable.aemeasurable (arrayTestExtend g).continuous.aestronglyMeasurable,hμ]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma terminalLaw_translate_eventually (r : DyadicTime) :
    ∀ᶠ i in atTop, (S.terminalLaw i).map (arrayTranslate r)=S.terminalLaw i := by
  obtain ⟨p,hp⟩ := dyadic_aligned_eventually r
  filter_upwards [S.exponent_tendsto.eventually_ge_atTop p] with i hi
  obtain ⟨a,ha⟩ := hp _ hi
  exact scaleLaw_translate _ _ _ _ _ r a ha
lemma terminal_integral_translate (r : DyadicTime) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,g (nonaffineTranslation r d) ∂L.terminal)=∫ d,g d ∂L.terminal := by
  have hh : (fun i => ∫ d,(g.comp (nonaffineTranslation r).toCocompactMap) d ∂nonaffinePart (S.terminalLaw i))
      =ᶠ[L.filter] (fun i => ∫ d,g d ∂nonaffinePart (S.terminalLaw i)) := by
    filter_upwards [L.refines (S.terminalLaw_translate_eventually r)] with i hi
    exact integral_translate_nonaffine (S.terminalLaw i) r hi g
  exact tendsto_nhds_unique (L.terminal_converges (g.comp (nonaffineTranslation r).toCocompactMap))
    ((L.terminal_converges g).congr' hh.symm)
lemma terminal_translate (r : DyadicTime) : L.terminal.map (nonaffineTranslation r)=L.terminal := by
  let := Measure.Regular.map (μ := L.terminal) (nonaffineTranslation r)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_map (f := fun d => g d) (nonaffineTranslation r).continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable]
  exact S.terminal_integral_translate L r g
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_VagueSupport
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
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
  all_goals try with_reducible_and_instances rfl
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
lemma ae_le_zero_of_positive_rational_null {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hn : ∀ q : ℚ,0<q → μ {x | (q:ℝ)<f x}=0) : ∀ᵐ x ∂μ, f x ≤ 0 := by
  have hh : ∀ q : ℚ,0<q → ∀ᵐ x ∂μ,¬(q:ℝ)<f x := fun q hq => ae_iff.mpr (by simpa using hn q hq)
  have h := ae_all_iff.mpr (fun q : ℚ => ae_all_iff.mpr (hh q))
  filter_upwards [h] with x hx
  by_contra hpos
  obtain ⟨q,hq,hqx⟩ := exists_rat_btwn (lt_of_not_ge hpos)
  exact hx q (by exact_mod_cast hq) hqx
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RealArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma unitArray_diff (d : DistanceArray) (hd : UnitArray d) (s t u v : DyadicTime) :
    |d.val s t-d.val u v| ≤ |(s:ℝ)-(u:ℝ)|+|(t:ℝ)-(v:ℝ)| := by
  have ht := d.property.2.2.2.1
  have hsy := d.property.2.2.1
  have h1 := ht s u t
  have h2 := ht u v t
  have h3 := ht u s v
  have h4 := ht s t v
  have hsu := hd s u
  have htv := hd t v
  rw [abs_sub_comm] at hsu htv
  have hste : d.val u s=d.val s u := hsy _ _
  have hvte : d.val v t=d.val t v := hsy _ _
  rw [abs_le]
  constructor <;> linarith
lemma unitArray_lipschitz (d : DistanceArray) (hd : UnitArray d) :
    LipschitzWith 2 (fun p : DyadicTime × DyadicTime => d.val p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := unitArray_diff d hd p.1 p.2 q.1 q.2
  rw [Real.dist_eq,Prod.dist_eq]
  change |d.val p.1 p.2-d.val q.1 q.2| ≤ (2:ℝ)*max |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|
  linarith [le_max_left |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|,
    le_max_right |(p.1:ℝ)-(q.1:ℝ)| |(p.2:ℝ)-(q.2:ℝ)|]
@[simp] lemma realArray_coe (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) :
    realArray d (s:ℝ) (t:ℝ)=d.val s t :=
  uniformly_extend_of_ind
    ((isUniformInducing_val (dyadicTimes:Set ℝ)).prod (isUniformInducing_val (dyadicTimes:Set ℝ)))
    (denseRange_dyadicTime.prodMap denseRange_dyadicTime) (unitArray_lipschitz d hd).uniformContinuous (s,t)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_ArrayLimitSupport
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma integral_nonaffine_scale_zero (k : ℝ) (hk : 0 ≤ k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (g : C_c(NonAffineArray,ℝ))
    (hz : ∀ j∈Finset.range l,∀ z,arrayTestExtend g (sampleArray k hk z (2^(p+j)) (by positivity))=0) :
    (∫ d,g d ∂nonaffinePart (scaleLaw k hk p l ε))=0 := by
  rw [←integral_arrayTestExtend,integral_scaleLaw k hk p l ε hε (fun d => arrayTestExtend g d) (arrayTestExtend g).continuous]
  have hs : (∑ j∈Finset.range l,∫ d,arrayTestExtend g d ∂sampleLaw k hk (2^(p+j)) (by positivity))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [integral_sampleLaw _ _ _ _ (fun d => arrayTestExtend g d) (arrayTestExtend g).continuous]
    simp_rw [hz j hj]
    simp
  rw [hs,zero_div]
lemma integral_nonaffine_scale_zero_of_bound (k : ℝ) (hk : 0 ≤ k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (g : C_c(NonAffineArray,ℝ)) (f : DistanceArray → ℝ) (q : ℝ)
    (hg : ∀ d : NonAffineArray, f d.val ≤ q → g d=0)
    (hf : ∀ j∈Finset.range l,∀ z,f (sampleArray k hk z (2^(p+j)) (by positivity)) ≤ q) :
    (∫ d,g d ∂nonaffinePart (scaleLaw k hk p l ε))=0 := by
  apply integral_nonaffine_scale_zero k hk p l ε hε g
  intro j hj z
  let d := sampleArray k hk z (2^(p+j)) (by positivity)
  by_cases hd : d∈affineLocus
  · exact arrayTestExtend_affine g d hd
  · exact (arrayTestExtend_apply g ⟨d,hd⟩).trans (hg ⟨d,hd⟩ (hf j hj z))
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma power_terminal_tendsto : Tendsto (fun i => (2:ℝ)^(S.exponent i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.exponent_tendsto
lemma sample_constraint_aeterminal (f : DistanceArray → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℝ,∀ hk : 0 ≤ k,∀ z : Torus,∀ n : ℕ,∀ hn : 0<n,
      f (sampleArray k hk z n hn) ≤ C/(n:ℝ)) : ∀ᵐ d ∂L.terminal, f d.val ≤ 0 := by
  apply ae_le_zero_of_positive_rational_null
  intro q hq
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply vague_open_null L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))
  intro g hg hz
  have he : ∀ᶠ i in atTop,C/(2:ℝ)^(S.exponent i)<q :=
    (tendsto_const_nhds.div_atTop S.power_terminal_tendsto).eventually (gt_mem_nhds hqR)
  apply tendsto_const_nhds.congr'
  filter_upwards [L.refines he] with i hi
  symm
  apply integral_nonaffine_scale_zero_of_bound _ _ _ _ _ (S.epsilon_pos i) g f q
  · intro d hd; exact hz d (not_lt.mpr hd)
  · intro j hj z
    exact (hb _ _ z _ (by positivity)).trans ((div_le_div_of_nonneg_left hC (by positivity)
      (by exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (S.exponent i) j))).trans hi.le)
lemma unit_aeterminal : ∀ᵐ d ∂L.terminal, UnitArray d.val := by
  have h (s t : DyadicTime) : ∀ᵐ d ∂L.terminal,d.val.val s t-|(t:ℝ)-(s:ℝ)| ≤ 0 := by
    apply S.sample_constraint_aeterminal L (fun d => d.val s t-|(t:ℝ)-(s:ℝ)|)
      ((continuous_arrayEval s t).sub continuous_const) 1 (by norm_num)
    intro k hk z n hn
    change rescaledDistance k z n s t-|(t:ℝ)-(s:ℝ)| ≤ 1/(n:ℝ)
    linarith [rescaledDistance_bound k hk z n hn s t]
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h s))] with d hd
  intro s t
  linarith [hd s t]
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_HalfDecomposition
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal
namespace StandardMapEntropy
lemma map_iterate_succ {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map (f^[n])).map f=μ.map (f^[n+1]) := by
  rw [Measure.map_map hf (hf.iterate n)]
  congr 1
  exact funext (fun x => (Function.iterate_succ_apply' f n x).symm)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_VagueBounds
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma lintegral_le_of_cc_le {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [RegularSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (f : X → ℝ) (hf : Continuous f)
    (h0 : ∀ x,0 ≤ f x) (C : ℝ)
    (hb : ∀ g : C_c(X,ℝ),(∀ x,0 ≤ g x) → (∀ x,g x ≤ f x) → (∫ x,g x ∂μ) ≤ C) :
    (∫⁻ x,ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have hcompact (K : Set X) (hK : IsCompact K) : ν K ≤ ENNReal.ofReal C := by
    obtain ⟨⟨b,hbc⟩,hbK,hbZ,hbs,hbr⟩ := exists_continuous_one_zero_of_isCompact
      hK isClosed_empty (disjoint_empty K)
    let g : C_c(X,ℝ) := ⟨⟨fun x => b x*f x,hbc.mul hf⟩,hbs.mul_right⟩
    have hg0 : ∀ x,0 ≤ g x := fun x => mul_nonneg (hbr x).1 (h0 x)
    have hgf : ∀ x,g x ≤ f x := fun x => by
      change b x*f x ≤ f x
      exact mul_le_of_le_one_left (h0 x) (hbr x).2
    have hge : ∀ x∈K,g x=f x := by intro x hx; change b x*f x=f x; have he : b x=1 := hbK hx; rw [he]; simp
    have hm : ν K ≤ ∫⁻ x,ENNReal.ofReal (g x) ∂μ := by
      rw [withDensity_apply _ hK.isClosed.measurableSet]
      rw [← lintegral_indicator hK.isClosed.measurableSet]
      apply lintegral_mono
      intro x
      by_cases hx : x∈K
      · simp only [Set.indicator_of_mem hx,hge x hx,le_refl]
      · simp only [Set.indicator_of_notMem hx]; exact bot_le
    have hi : Integrable (fun x => g x) μ := g.continuous.integrable_of_hasCompactSupport (μ := μ) g.hasCompactSupport
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => g x) hi (Eventually.of_forall hg0)] at hm
    exact hm.trans (ENNReal.ofReal_le_ofReal (hb g hg0 hgf))
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => (hcompact K hK).trans_lt ENNReal.ofReal_lt_top⟩
  have hv : ν univ ≤ ENNReal.ofReal C := by
    rw [isOpen_univ.measure_eq_iSup_isCompact ν]
    simp only [iSup_le_iff]
    intro K hKU hK
    exact hcompact K hK
  simpa only [ν,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] using hv
lemma vague_integrable_bound {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [RegularSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) [∀ i,IsFiniteMeasureOnCompacts (μ i)]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hconv : ∀ g : C_c(X,ℝ), Tendsto (fun i => ∫ x,g x ∂μ i) l (𝓝 (∫ x,g x ∂ν)))
    (f : X → ℝ) (hf : Continuous f) (h0 : ∀ x,0 ≤ f x) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ i,Integrable f (μ i)) (hb : ∀ᶠ i in l,(∫ x,f x ∂μ i)≤C) :
    Integrable f ν ∧ (∫ x,f x ∂ν) ≤ C := by
  have hb' : ∀ g : C_c(X,ℝ),(∀ x,0 ≤ g x) → (∀ x,g x ≤ f x) → (∫ x,g x ∂ν) ≤ C := by
    intro g hg hgf
    apply le_of_tendsto (hconv g)
    filter_upwards [hb] with i hiC
    exact (integral_mono (g.continuous.integrable_of_hasCompactSupport (μ := μ i) g.hasCompactSupport)
      (hi i) hgf).trans hiC
  have hbL := lintegral_le_of_cc_le ν f hf h0 C hb'
  have hif : HasFiniteIntegral f ν := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mpr
    (hbL.trans_lt ENNReal.ofReal_lt_top)
  have hiv : Integrable f ν := ⟨hf.aestronglyMeasurable,hif⟩
  refine ⟨hiv,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hiv (Eventually.of_forall h0)] at hbL
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbL
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_RemainderLaws
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
lemma arrayTranslate_unit (r : DyadicTime) (d : DistanceArray) (hu : UnitArray d) : UnitArray (arrayTranslate r d) := by
  intro s t
  change d.val (s+r) (t+r)≤|(t:ℝ)-(s:ℝ)|
  have hh := hu (s+r) (t+r)
  change d.val (s+r) (t+r)≤|((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ))| at hh
  simpa only [add_sub_add_right_eq_sub] using hh
lemma dyadicHalf_add (s t : DyadicTime) : dyadicHalf (s+t)=dyadicHalf s+dyadicHalf t := by
  apply Subtype.ext; change ((s:ℝ)+(t:ℝ))/2=(s:ℝ)/2+(t:ℝ)/2; ring
lemma half_translate (r : DyadicTime) (d : NonAffineArray) (hu : UnitArray d.val) :
    nonaffineTranslation r (nonaffineHalf d)=nonaffineHalf (nonaffineTranslation (dyadicHalf r) d) := by
  have hu' : UnitArray (nonaffineTranslation (dyadicHalf r) d).val := arrayTranslate_unit _ _ hu
  rw [nonaffineHalf,dite_eq_left hu,nonaffineHalf,dite_eq_left hu']
  apply Subtype.ext; apply Subtype.ext; funext s t
  change 2*d.val.val (dyadicHalf (s+r)) (dyadicHalf (t+r))=
    2*d.val.val (dyadicHalf s+dyadicHalf r) (dyadicHalf t+dyadicHalf r)
  rw [dyadicHalf_add,dyadicHalf_add]
lemma unit_half_map (μ : Measure NonAffineArray) (hu : ∀ᵐd ∂μ,UnitArray d.val) :
    ∀ᵐd ∂μ.map nonaffineHalf,UnitArray d.val := by
  apply (ae_map_iff measurable_nonaffineHalf.aemeasurable
    ((isClosed_unitArray.preimage continuous_subtype_val).measurableSet)).mpr
  exact hu.mono (fun d hd => nonaffineHalf_unit d hd)
lemma half_map_translation_invariant (μ : Measure NonAffineArray) (hu : ∀ᵐd ∂μ,UnitArray d.val)
    (ht : ∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (r : DyadicTime) :
    (μ.map nonaffineHalf).map (nonaffineTranslation r)=μ.map nonaffineHalf := by
  rw [Measure.map_map (nonaffineTranslation r).continuous.measurable measurable_nonaffineHalf]
  calc
    μ.map (nonaffineTranslation r ∘ nonaffineHalf)=μ.map (nonaffineHalf ∘ nonaffineTranslation (dyadicHalf r)) :=
      Measure.map_congr (hu.mono (fun d hd => half_translate r d hd))
    _=(μ.map (nonaffineTranslation (dyadicHalf r))).map nonaffineHalf := by
      rw [Measure.map_map measurable_nonaffineHalf (nonaffineTranslation _).continuous.measurable]
    _=μ.map nonaffineHalf := by rw [ht]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma backwardLaw_zero : S.backwardLaw L 0=L.terminal := by simp [backwardLaw]
lemma backwardLaw_succ (n : ℕ) : S.backwardLaw L (n+1)=(S.backwardLaw L n).map nonaffineHalf :=
  (map_iterate_succ L.terminal nonaffineHalf measurable_nonaffineHalf n).symm
lemma backwardLaw_unit (n : ℕ) : ∀ᵐd ∂S.backwardLaw L n,UnitArray d.val := by
  induction n with
  | zero => rw [S.backwardLaw_zero L]; exact S.unit_aeterminal L
  | succ n ih => rw [S.backwardLaw_succ L]; exact unit_half_map _ ih
lemma backwardLaw_translate (n : ℕ) (r : DyadicTime) : (S.backwardLaw L n).map (nonaffineTranslation r)=S.backwardLaw L n := by
  induction n generalizing r with
  | zero => rw [S.backwardLaw_zero L]; exact S.terminal_translate L r
  | succ n ih => rw [S.backwardLaw_succ L]; exact half_map_translation_invariant _ (S.backwardLaw_unit L n) ih r
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TerminalShortfall
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma shortfall_unit_mem (d : DistanceArray) (hu : UnitArray d) (s t : DyadicTime)
    (hst : (s:ℝ)<(t:ℝ)) : arrayShortfall s t d∈Icc (0:ℝ) 1 := by
  have hl : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have hb := hu s t
  rw [abs_of_pos hl] at hb
  have h0 := d.property.1 s t
  unfold arrayShortfall
  constructor
  · have hh := (div_le_one hl).mpr hb; linarith
  · have hh := div_nonneg h0 hl.le; linarith
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma terminal_shortfall_max_integral (i : ℕ) :
    (∫ d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂S.terminalLaw i)=1 := by
  rw [terminalLaw,integral_scaleLaw _ _ _ _ _ (S.epsilon_pos i) _
    ((continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const)]
  simp only [Finset.range_one,Finset.sum_singleton,Nat.add_zero]
  let n := 2^(S.exponent i)
  have hn : 0<n := by dsimp [n]; positivity
  have hs : (n:ℝ)*(0:DyadicTime)=((0:ℤ):ℝ) := by simp
  have ht : (n:ℝ)*(dyadicInt 1:ℝ)=((0:ℤ):ℝ)+(n:ℝ) := by simp
  have he : (∫ d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂sampleLaw (S.parameter i) (S.positive i).le n hn)=
      ∫ d,arrayShortfall 0 (dyadicInt 1) d ∂sampleLaw (S.parameter i) (S.positive i).le n hn := by
    rw [integral_sampleLaw _ _ _ _ _ ((continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const),
      integral_sampleLaw _ _ _ _ _ (continuous_arrayShortfall 0 (dyadicInt 1))]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [shortfall_sample_aligned _ _ _ n hn 0 (dyadicInt 1) 0 n hn hs ht]
    exact max_eq_left (torusShortfall_mem _ (S.positive i).le z 0 n hn).1
  rw [he,integral_shortfall_sample _ _ n hn 0 (dyadicInt 1) 0 n hn hs ht]
  exact div_self (S.epsilon_pos i).ne'
lemma terminal_shortfall_integrable_bound :
    Integrable (fun d : NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) L.terminal ∧
      (∫ d,arrayShortfall 0 (dyadicInt 1) d.val ∂L.terminal) ≤ 1 := by
  let F : DistanceArray → ℝ := fun d => max (arrayShortfall 0 (dyadicInt 1) d) 0
  have hF : Continuous F := (continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const
  obtain ⟨hi,hb⟩ := vague_integrable_bound L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (fun d => F d.val) (hF.comp continuous_subtype_val) (fun d => le_max_right _ _) 1 (by norm_num)
    (fun i => integrable_nonaffinePart _ F hF) (Eventually.of_forall (fun i => by
      exact (integral_nonaffinePart_le _ F hF (fun d => le_max_right _ _)).trans (S.terminal_shortfall_max_integral i).le))
  have he : (fun d : NonAffineArray => F d.val)=ᵐ[L.terminal] (fun d => arrayShortfall 0 (dyadicInt 1) d.val) := by
    filter_upwards [S.unit_aeterminal L] with d hd
    exact max_eq_left (shortfall_unit_mem d.val hd 0 (dyadicInt 1) (by norm_num)).1
  exact ⟨hi.congr he,by rw [←integral_congr_ae he]; exact hb⟩
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CappedTests
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical ENNReal
namespace StandardMapEntropy
lemma dyadicMid_zero_two : dyadicMid 0 (dyadicInt 2)=dyadicInt 1 := by
  apply Subtype.ext; norm_num
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FineArrays
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
lemma dyadicFine_zero (n : ℕ) : dyadicFine n 0=0 := by
  apply Subtype.ext
  simp only [dyadicFine_val,ZeroMemClass.coe_zero,zero_div]
lemma halfIterate_unit (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) : UnitArray ((nonaffineHalf^[n]) d).val := by
  induction n with
  | zero => exact hu
  | succ n ih => simpa only [Function.iterate_succ_apply'] using nonaffineHalf_unit _ ih
lemma halfIterate_eval (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) (s t : DyadicTime) :
    ((nonaffineHalf^[n]) d).val.val s t=(2:ℝ)^n*d.val.val (dyadicFine n s) (dyadicFine n t) := by
  induction n generalizing s t with
  | zero => simp [dyadicFine]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [nonaffineHalf,dite_eq_left (halfIterate_unit n d hu)]
    change 2*((nonaffineHalf^[n]) d).val.val (dyadicHalf s) (dyadicHalf t)=_
    rw [ih,pow_succ]
    have he (s:DyadicTime) : dyadicFine n (dyadicHalf s)=dyadicFine (n+1) s := by
      exact (Function.iterate_succ_apply _ _ _).symm
    rw [he,he]
    ring
lemma halfIterate_shortfall (n : ℕ) (d : NonAffineArray) (hu : UnitArray d.val) (s t : DyadicTime) :
    arrayShortfall s t ((nonaffineHalf^[n]) d).val=arrayShortfall (dyadicFine n s) (dyadicFine n t) d.val := by
  unfold arrayShortfall
  rw [halfIterate_eval n d hu,dyadicFine_val,dyadicFine_val,←sub_div]
  congr 1
  rw [div_div_eq_mul_div,mul_comm]
lemma shortfall_half_bound (d : NonAffineArray) (hu : UnitArray d.val) :
    arrayShortfall 0 (dyadicInt 1) (nonaffineHalf d).val≤2*arrayShortfall 0 (dyadicInt 1) d.val := by
  have hj := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) (nonaffineHalf d).val
  have hz := (shortfall_unit_mem (nonaffineHalf d).val (nonaffineHalf_unit d hu) (dyadicInt 1) (dyadicInt 2) (by norm_num)).1
  have he : arrayShortfall 0 (dyadicInt 2) (nonaffineHalf d).val=arrayShortfall 0 (dyadicInt 1) d.val := by
    rw [nonaffineHalf,dite_eq_left hu]
    dsimp only [arrayShortfall,nonaffineHalfOn,arrayHalf]
    simp only [dyadicInt_val,ZeroMemClass.coe_zero,Int.cast_one,Int.cast_ofNat,sub_zero]
    have h0 : dyadicHalf 0=0 := by apply Subtype.ext; norm_num
    have h1 : dyadicHalf (dyadicInt 2)=dyadicInt 1 := by apply Subtype.ext; norm_num
    rw [h0,h1]; ring
  simp only [arrayJ,dyadicMid_zero_two,he] at hj
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TerminalCap
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
lemma continuous_capF (α : ℝ) : Continuous (capF α) := (entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FineMoments
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
lemma shortfall_translate (d:DistanceArray) (s t r:DyadicTime) :
    arrayShortfall s t (arrayTranslate r d)=arrayShortfall (s+r) (t+r) d := by
  unfold arrayShortfall
  change 1-d.val (s+r) (t+r)/((t:ℝ)-(s:ℝ))=1-d.val (s+r) (t+r)/(((t:ℝ)+(r:ℝ))-((s:ℝ)+(r:ℝ)))
  rw [add_sub_add_right_eq_sub]
lemma shortfall_dilate (d:DistanceArray) (s t:DyadicTime) :
    arrayShortfall s t (arrayDilate d)=arrayShortfall (s+s) (t+t) d := by
  unfold arrayShortfall
  change 1-(d.val (s+s) (t+t)/2)/((t:ℝ)-(s:ℝ))=1-d.val (s+s) (t+t)/(((t:ℝ)+(t:ℝ))-((s:ℝ)+(s:ℝ)))
  congr 1
  rw [div_div]
  congr 1
  ring
lemma integral_invariant_translation (μ:Measure NonAffineArray) (r:DyadicTime)
    (ht:μ.map (nonaffineTranslation r)=μ) (f:NonAffineArray→ℝ) (hf:Measurable f) :
    (∫d,f (nonaffineTranslation r d) ∂μ)=∫d,f d ∂μ := by
  rw [←integral_map (nonaffineTranslation r).continuous.measurable.aemeasurable hf.aestronglyMeasurable,ht]
lemma half_shortfall_average (d:NonAffineArray) (hu:UnitArray d.val) :
    (arrayShortfall 0 (dyadicInt 1) (nonaffineHalf d).val+
      arrayShortfall 0 (dyadicInt 1) (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d)).val)/2≤arrayShortfall 0 (dyadicInt 1) d.val := by
  have hj := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) (nonaffineHalf d).val
  have hs : arrayShortfall 0 (dyadicInt 2) (nonaffineHalf d).val=arrayShortfall 0 (dyadicInt 1) d.val := by
    have he := shortfall_dilate (nonaffineHalf d).val 0 (dyadicInt 1)
    rw [show (0:DyadicTime)+0=0 by simp,show dyadicInt 1+dyadicInt 1=dyadicInt 2 by apply Subtype.ext; norm_num] at he
    rw [show arrayDilate (nonaffineHalf d).val=d.val from congrArg Subtype.val (nonaffineDilate_half d hu)] at he
    exact he.symm
  have ht : arrayShortfall (dyadicInt 1) (dyadicInt 2) (nonaffineHalf d).val=
      arrayShortfall 0 (dyadicInt 1) (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d)).val := by
    rw [←half_translate (dyadicInt 1) d hu]
    change _=arrayShortfall 0 (dyadicInt 1) (arrayTranslate (dyadicInt 1) (nonaffineHalf d).val)
    rw [shortfall_translate,zero_add,show dyadicInt 1+dyadicInt 1=dyadicInt 2 by apply Subtype.ext; norm_num]
  simp only [arrayJ,dyadicMid_zero_two,hs,ht] at hj
  linarith
lemma shortfall_half_moment (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val)
    (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ)
    (hi:Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) μ) :
    Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) (μ.map nonaffineHalf) ∧
      (∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂μ.map nonaffineHalf)≤
        ∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂μ := by
  let f:NonAffineArray→ℝ := fun d => arrayShortfall 0 (dyadicInt 1) d.val
  have hf:Measurable f := (continuous_arrayShortfall _ _).measurable.comp measurable_subtype_coe
  have hb : Integrable (fun d => f (nonaffineHalf d)) μ := (hi.const_mul 2).mono'
    (hf.comp measurable_nonaffineHalf).aestronglyMeasurable (by
      filter_upwards [hu] with d hd
      rw [Real.norm_eq_abs,abs_of_nonneg (shortfall_unit_mem _ (nonaffineHalf_unit d hd) _ _ (by norm_num)).1]
      exact shortfall_half_bound d hd)
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable measurable_nonaffineHalf.aemeasurable).mpr hb,?_⟩
  rw [integral_map measurable_nonaffineHalf.aemeasurable hf.aestronglyMeasurable]
  have hbt : Integrable (fun d => f (nonaffineHalf (nonaffineTranslation (dyadicHalf (dyadicInt 1)) d))) μ := by
    have hmap : Integrable (fun d => f (nonaffineHalf d)) (μ.map (nonaffineTranslation (dyadicHalf (dyadicInt 1)))) := by rw [ht]; exact hb
    exact (integrable_map_measure (hf.comp measurable_nonaffineHalf).aestronglyMeasurable (nonaffineTranslation _).continuous.measurable.aemeasurable).mp hmap
  have havg := integral_mono_ae ((hb.add hbt).div_const 2) hi (hu.mono (fun d hd => half_shortfall_average d hd))
  simp only [Pi.add_apply] at havg
  rw [integral_div,integral_add hb hbt] at havg
  have he := integral_invariant_translation μ (dyadicHalf (dyadicInt 1)) (ht _) (fun d => f (nonaffineHalf d)) (hf.comp measurable_nonaffineHalf)
  rw [he] at havg
  linarith
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma backward_shortfall_moment (n:ℕ) :
    Integrable (fun d:NonAffineArray => arrayShortfall 0 (dyadicInt 1) d.val) (S.backwardLaw L n) ∧
    (∫d:NonAffineArray,arrayShortfall 0 (dyadicInt 1) d.val ∂S.backwardLaw L n)≤1 := by
  induction n with
  | zero => rw [S.backwardLaw_zero L]; exact S.terminal_shortfall_integrable_bound L
  | succ n ih =>
    rw [S.backwardLaw_succ L]
    obtain ⟨hi,hb⟩ := shortfall_half_moment _ (S.backwardLaw_unit L n) (S.backwardLaw_translate L n) ih.1
    exact ⟨hi,hb.trans ih.2⟩
lemma backward_cap_integrable {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) :
    Integrable (fun d:NonAffineArray => capF α d.val) (S.backwardLaw L n) := by
  obtain ⟨C,hC,hb⟩ := entropyCap_upper hα hα1
  exact ((S.backward_shortfall_moment L n).1.const_mul C).mono'
    ((continuous_capF α).comp continuous_subtype_val).aestronglyMeasurable (by
      filter_upwards [S.backwardLaw_unit L n] with d hd
      rw [Real.norm_eq_abs,capF,abs_of_nonneg (entropyCap_bounds hα hα1 (shortfall_unit_mem d.val hd _ _ (by norm_num))).1]
      exact hb _ (shortfall_unit_mem d.val hd _ _ (by norm_num)))
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointShapes
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma dyadic_between {a b : ℝ} (hab : a < b) : ∃s : DyadicTime,a < (s:ℝ) ∧ (s:ℝ) < b := by
  obtain ⟨x,⟨s,rfl⟩,ha,hb⟩ := dyadicTime_dense.exists_between hab
  exact ⟨s,ha,hb⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointClasses
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
lemma slowShape_dyadic {d : DistanceArray} {c:ℝ} (hu:UnitArray d) (h:SlowShape (realArray d) c) :
    (∀s t:DyadicTime,d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|) ∨
    (∃a:ℝ,(∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,a≤(s:ℝ) → a≤(t:ℝ) → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃b:ℝ,(∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)≤b → (t:ℝ)≤b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) ∨
    (∃a b:ℝ,a<b ∧
      (∀s t:DyadicTime,(s:ℝ)≤a → (t:ℝ)≤a → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,b≤(s:ℝ) → b≤(t:ℝ) → d.val s t=|(t:ℝ)-(s:ℝ)|) ∧
      (∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)|)) := by
  rcases h with hs|⟨a,hl,hs⟩|⟨b,hr,hs⟩|⟨a,b,hab,⟨hl,hr⟩,hs⟩
  · exact Or.inl (fun s t => by simpa only [realArray_coe d hu] using hs s t)
  · exact Or.inr (Or.inl ⟨a,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨b,fun s t hp hq => by simpa only [realArray_coe d hu] using hr s hp t hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a,b,hab,fun s t hp hq => by simpa only [realArray_coe d hu] using hl s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hr s t hp hq,
      fun s t hp hq => by simpa only [realArray_coe d hu] using hs s hp t hq⟩))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TerminalStrict
attribute [-instance] _root_.OAI.StandardMapEntropy.LocalCoding.optionFinsetMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
lemma measurable_fineCap (α:ℝ) (n:ℕ) (z:DyadicTime) : Measurable (fineCap α n z) :=
  (continuous_capF α).measurable.comp (measurable_subtype_coe.comp ((measurable_nonaffineHalf.iterate n).comp (nonaffineTranslation z).continuous.measurable))
lemma fineCap_zero (α:ℝ) (n:ℕ) (d:NonAffineArray) : fineCap α n 0 d=capF α ((nonaffineHalf^[n]) d).val := by
  have he : nonaffineTranslation 0 d=d := by apply Subtype.ext; exact arrayTranslate_zero d.val
  simp only [fineCap,he]
lemma fineCap_translate (α:ℝ) (n:ℕ) (z:DyadicTime) (d:NonAffineArray) :
    fineCap α n z d=fineCap α n 0 (nonaffineTranslation z d) := by rw [fineCap_zero]; rfl
lemma slow_interval_exists {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hs:SlowShape (realArray d) c) :
    ∃a b:ℝ,a<b ∧ ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t ≤ c*|(t:ℝ)-(s:ℝ)| := by
  rcases slowShape_dyadic hu hs with h|⟨a,hl,h⟩|⟨b,hr,h⟩|⟨a,b,hab,hl,hr,h⟩
  · exact ⟨0,1,by norm_num,fun s t _ _ => h s t⟩
  · exact ⟨a,a+1,by linarith,fun s t hs ht => h s t hs.1 ht.1⟩
  · exact ⟨b-1,b,by linarith,fun s t hs ht => h s t hs.2 ht.2⟩
  · exact ⟨a,b,hab,h⟩
lemma fineCap_eventually_one (α:ℝ) {d:NonAffineArray} (hu:UnitArray d.val)
    (hs:SlowShape (realArray d.val) (999/1000)) : ∃z:DyadicTime,∀ᶠn:ℕ in atTop,fineCap α n z d=1 := by
  obtain ⟨a,b,hab,hslow⟩ := slow_interval_exists hu hs
  obtain ⟨z,haz,hzb⟩ := dyadic_between hab
  have ht : Tendsto (fun n:ℕ => (1:ℝ)/(2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [one_div,inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num : (2:ℝ)⁻¹<1)
  refine ⟨z,?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.mpr hzb))] with n hn
  unfold fineCap capF
  rw [halfIterate_shortfall n _ (arrayTranslate_unit _ _ hu),dyadicFine_zero]
  change entropyCap α (arrayShortfall 0 (dyadicFine n (dyadicInt 1)) (arrayTranslate z d.val))=1
  rw [shortfall_translate,zero_add]
  apply entropyCap_one
  have hp : 0<(1:ℝ)/(2:ℝ)^n := by positivity
  have he : ((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)=(1:ℝ)/(2:ℝ)^n+(z:ℝ) := by simp only [AddSubgroup.coe_add,dyadicFine_val,dyadicInt_val,Int.cast_one]
  have hb := hslow z (dyadicFine n (dyadicInt 1)+z) ⟨haz.le,hzb.le⟩ (by rw [he]; constructor <;> linarith)
  rw [he,abs_of_pos (by linarith)] at hb
  have hh : d.val.val z (dyadicFine n (dyadicInt 1)+z)/(((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)-(z:ℝ))≤999/1000 := by
    apply (div_le_iff₀ (show 0<((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)-(z:ℝ) by rw [he]; linarith)).mpr
    simpa only [he] using hb
  unfold arrayShortfall
  linarith
lemma measurableSet_fineCapEvent (α:ℝ) (z:DyadicTime) (N:ℕ) : MeasurableSet (fineCapEvent α z N) := by
  have he : fineCapEvent α z N=⋂n:ℕ,⋂_:N≤n,(fineCap α n z)⁻¹'{1} := by
    ext d; simp only [fineCapEvent,mem_ofPred_eq,mem_iInter,mem_preimage,mem_singleton_iff]
  rw [he]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun _ : N≤n => (measurable_fineCap α n z) (measurableSet_singleton 1)))
lemma fineCapEvent_translate (α:ℝ) (z:DyadicTime) (N:ℕ) :
    fineCapEvent α z N=(nonaffineTranslation z)⁻¹'fineCapEvent α 0 N := by
  ext d
  change (∀n≥N,fineCap α n z d=1) ↔ (∀n≥N,fineCap α n 0 (nonaffineTranslation z d)=1)
  constructor <;> intro h n hn
  · rw [←fineCap_translate]; exact h n hn
  · rw [fineCap_translate]; exact h n hn
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma fineCap_integrable {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) : Integrable (fineCap α n 0) L.terminal := by
  change Integrable (fun d => fineCap α n 0 d) L.terminal
  simp_rw [fineCap_zero]
  exact (integrable_map_measure ((continuous_capF α).measurable.comp measurable_subtype_coe).aestronglyMeasurable
    (measurable_nonaffineHalf.iterate n).aemeasurable).mp (S.backward_cap_integrable L hα hα1 n)
lemma fineCap_integral (α:ℝ) (n:ℕ) : (∫d,fineCap α n 0 d ∂L.terminal)=(∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n) := by
  simp_rw [fineCap_zero]
  exact (integral_map (measurable_nonaffineHalf.iterate n).aemeasurable (show AEStronglyMeasurable (fun d:NonAffineArray => capF α d.val) (S.backwardLaw L n) from ((continuous_capF α).measurable.comp measurable_subtype_coe).aestronglyMeasurable)).symm
lemma terminal_has_positive_event (α:ℝ) (hne:L.terminal≠0) : ∃N:ℕ,0<L.terminal (fineCapEvent α 0 N) := by
  have hc : ∀ᵐd ∂L.terminal,d∈⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N := by
    filter_upwards [S.unit_aeterminal L,S.shape_aeterminal_q44 L] with d hu hs
    obtain ⟨z,hz⟩ := fineCap_eventually_one α hu hs
    obtain ⟨N,hN⟩ := eventually_atTop.mp hz
    exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨N,hN⟩⟩
  by_contra h
  push Not at h
  have hz (z:DyadicTime) (N:ℕ) : L.terminal (fineCapEvent α z N)=0 := by
    rw [fineCapEvent_translate,←Measure.map_apply (nonaffineTranslation z).continuous.measurable (measurableSet_fineCapEvent α 0 N),S.terminal_translate L z]
    exact le_zero_iff.mp (h N)
  have hm : L.terminal (⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N)=0 := measure_iUnion_null (fun z => measure_iUnion_null (hz z))
  have he : L.terminal univ=0 := by
    have hae : (⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N)=ᵐ[L.terminal] (univ:Set NonAffineArray) := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [hc] with d hd
      exact ⟨fun _ => mem_univ d,fun _ => hd⟩
    rw [←measure_congr hae]
    exact hm
  exact hne (Measure.measure_univ_eq_zero.mp he)

lemma terminal_event_lower_q44_oai {α:ℝ} (hα:0≤α) (hα1:α≤1) (hne:L.terminal≠0) :
    ∃δ:ℝ,0<δ ∧ ∀ᶠn:ℕ in atTop,δ≤∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n := by
  obtain ⟨N,hN⟩ := S.terminal_has_positive_event L α hne
  let E:=fineCapEvent α 0 N
  have hE : MeasurableSet E := measurableSet_fineCapEvent α 0 N
  have he (n:ℕ) (hn:N≤n) : (fineCap α n 0)=ᵐ[L.terminal.restrict E] (fun _ => (1:ℝ)) :=
    (ae_restrict_mem hE).mono (fun d hd => hd n hn)
  have hi : Integrable (fun _:NonAffineArray => (1:ℝ)) (L.terminal.restrict E) :=
    (S.fineCap_integrable L hα hα1 N).restrict.congr (he N le_rfl)
  have : IsFiniteMeasure (L.terminal.restrict E) := (integrable_const_iff_isFiniteMeasure (by norm_num : (1:ℝ)≠0)).mp hi
  have hf : L.terminal E≠∞ := by
    have hh : L.terminal E<∞ := by simpa only [Measure.restrict_apply_univ] using (measure_lt_top (L.terminal.restrict E) univ)
    exact hh.ne
  refine ⟨L.terminal.real E,ENNReal.toReal_pos hN.ne' hf,?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [←S.fineCap_integral L α n]
  have hh := integral_mono_measure (Measure.restrict_le_self : L.terminal.restrict E≤L.terminal)
    (show 0≤ᵐ[L.terminal] fineCap α n 0 from (S.unit_aeterminal L).mono (fun d hd => by
      rw [fineCap_zero,capF]
      exact (entropyCap_bounds hα hα1 (shortfall_unit_mem _ (halfIterate_unit n d hd) _ _ (by norm_num))).1))
    (S.fineCap_integrable L hα hα1 n)
  rw [integral_congr_ae (he n hn),integral_const] at hh
  simpa only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] using hh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower_q44_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.terminal_event_lower_q44_oai
