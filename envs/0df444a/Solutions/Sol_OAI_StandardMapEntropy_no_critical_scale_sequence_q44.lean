-- Prove2me | solution 1 for OAI.StandardMapEntropy.no_critical_scale_sequence_q44
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:43:54.960321+00:00
-- url     : https://prove2.me/submissions/4b9fbb54-939d-4f2a-882c-0b8628a9e995

import Mathlib
import Definitions.Def_StandardMapComponents
import Definitions.Def_OAIQ44C002
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_capG_integral_decomposition_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_capG_limit_balance_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_exists_limitLaws_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_remainder_cap_nonpos_q44
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_terminal_cap_strict_q44

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
lemma entropyCap_lower {α u : ℝ} (hα : 0≤α) (hα1 : α≤1) (hu : u∈Icc (0:ℝ) 1) :
    (α/10000)*u≤ entropyCap α u := by
  by_cases hh : u≤1/10000
  · rw [entropyCap_linear hh]
    nlinarith [mul_nonneg hα hu.1]
  · have hh' := entropyCap_monotone hα hα1 (le_of_not_ge hh)
    rw [entropyCap_linear (by norm_num : (1/10000:ℝ)≤1/10000)] at hh'
    nlinarith [mul_nonneg hα (sub_nonneg.mpr hu.2)]
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
lemma initial_ratio_bound (i m : ℕ) :
    meanDeficit (S.parameter i) (2^(criticalLowerExponent S.offset i+m))/S.epsilon i ≤
      2*(2*doublingConstant)^m*criticalTheta S.offset i := by
  apply (div_le_iff₀ (S.epsilon_pos i)).mpr
  have hh := S.initial i m
  have ht := (S.threshold i).le
  change criticalTheta S.offset i ≤ S.epsilon i at ht
  have ht0 := criticalTheta_pos S.offset i
  have hc := doublingConstant_pos
  have hp : 0 ≤ 2*(2*doublingConstant)^m*criticalTheta S.offset i := by positivity
  nlinarith [mul_le_mul_of_nonneg_left ht hp]
lemma initial_ratio_tendsto (m : ℕ) :
    Tendsto (fun i => meanDeficit (S.parameter i) (2^(criticalLowerExponent S.offset i+m))/S.epsilon i) atTop (𝓝 0) := by
  apply squeeze_zero (fun i => div_nonneg ((meanDeficit_bounds _ (S.positive i).le _ (by positivity)).1) (S.epsilon_pos i).le)
    (fun i => S.initial_ratio_bound i m)
  simpa using (criticalTheta_tendsto S.offset).const_mul (2*(2*doublingConstant)^m)
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
lemma sampleArray_dilate (k : ℝ) (hk : 0≤k) (z : Torus) (n : ℕ) (hn : 0<n) :
    arrayDilate (sampleArray k hk z n hn)=sampleArray k hk z (n+n) (by omega) := by
  apply Subtype.ext
  funext s t
  change (productDistance k z ⌊(n:ℝ)*(↑(s+s):ℝ)⌋ ⌊(n:ℝ)*(↑(t+t):ℝ)⌋/(n:ℝ))/2=
    productDistance k z ⌊((n+n:ℕ):ℝ)*(s:ℝ)⌋ ⌊((n+n:ℕ):ℝ)*(t:ℝ)⌋/((n+n:ℕ):ℝ)
  simp only [AddSubgroup.coe_add,Nat.cast_add]
  rw [show (n:ℝ)*((s:ℝ)+(s:ℝ))=((n:ℝ)+(n:ℝ))*(s:ℝ) by ring,
    show (n:ℝ)*((t:ℝ)+(t:ℝ))=((n:ℝ)+(n:ℝ))*(t:ℝ) by ring]
  ring
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
lemma sampleLaw_dilate (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) :
    (sampleLaw k hk n hn).map arrayDilate=sampleLaw k hk (n+n) (by omega) := by
  unfold sampleLaw
  rw [Measure.map_map continuous_arrayDilate.measurable (continuous_sampleArray k hk n hn).measurable]
  congr 1
  funext z
  exact sampleArray_dilate k hk z n hn
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
lemma scaleLaw_dilate_boundary (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) :
    (scaleLaw k hk p l ε).map arrayDilate+
      ENNReal.ofReal (1/ε) • sampleLaw k hk (2^p) (by positivity)=
      scaleLaw k hk p l ε+ENNReal.ofReal (1/ε) • sampleLaw k hk (2^(p+l)) (by positivity) := by
  unfold scaleLaw
  rw [Measure.map_smul,Measure.map_finset_sum continuous_arrayDilate.measurable.aemeasurable]

  simp_rw [sampleLaw_dilate]
  have he (i : ℕ) : 2^(p+i)+2^(p+i)=2^(p+(i+1)) := by
    rw [show p+(i+1)=(p+i)+1 by omega,pow_succ,Nat.mul_two]
  simp_rw [he]
  have hsum : (∑ i∈Finset.range l,sampleLaw k hk (2^(p+(i+1))) (by positivity))+
      sampleLaw k hk (2^p) (by positivity)=
      (∑ i∈Finset.range l,sampleLaw k hk (2^(p+i)) (by positivity))+
        sampleLaw k hk (2^(p+l)) (by positivity) := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Finset.sum_range_succ,Finset.sum_range_succ]
      calc
        _ = ((∑ i∈Finset.range l,sampleLaw k hk (2^(p+(i+1))) (by positivity))+sampleLaw k hk (2^p) (by positivity))+
          sampleLaw k hk (2^(p+(l+1))) (by positivity) := by ac_rfl
        _ = _ := by rw [ih]
  rw [← smul_add,← smul_add,hsum]
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
-- module Solutions.OAIQ44_CM.StandardMap_LimitBalance
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
lemma scaleLaw_one (k : ℝ) (hk : 0 ≤ k) (p : ℕ) (ε : ℝ) :
    scaleLaw k hk p 1 ε=ENNReal.ofReal (1/ε) • sampleLaw k hk (2^p) (by positivity) := by
  simp [scaleLaw]
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma law_dilation_balance (i : ℕ) :
    (S.multiLaw i).map arrayDilate+S.initialLaw i=S.multiLaw i+S.terminalLaw i := by
  unfold multiLaw initialLaw terminalLaw
  rw [scaleLaw_one,scaleLaw_one]
  convert! scaleLaw_dilate_boundary (S.parameter i) (S.positive i).le
    (criticalLowerExponent S.offset i) (S.exponent i-criticalLowerExponent S.offset i) (S.epsilon i) using 1
  all_goals try with_reducible_and_instances rfl
  rw [Nat.add_sub_of_le (S.lower_lt i).le]
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
end CriticalScaleSequence
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
lemma continuous_capFpos (α : ℝ) : Continuous (capFpos α) := (entropyCap_contDiff α).continuous.comp ((continuous_arrayShortfall _ _).max continuous_const)
lemma shortfall_one_max_mem (d : DistanceArray) : max (arrayShortfall 0 (dyadicInt 1) d) 0∈Icc (0:ℝ) 1 := by
  refine ⟨le_max_right _ _,max_le ?_ (by norm_num)⟩
  have hh := d.property.1 0 (dyadicInt 1)
  convert! sub_le_self (1:ℝ) hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [arrayShortfall,dyadicInt_val,ZeroMemClass.coe_zero,Int.cast_one,sub_zero,div_one]
lemma capFpos_nonneg {α : ℝ} (hα : 0≤α) (hα1 : α≤1) (d : DistanceArray) : 0 ≤ capFpos α d :=
  (entropyCap_bounds hα hα1 (shortfall_one_max_mem d)).1
lemma capF_sample_integral (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 0<n) (α : ℝ) :
    (∫d,capF α d ∂sampleLaw k hk n hn)=(∫d,capFpos α d ∂sampleLaw k hk n hn) := by
  rw [integral_sampleLaw _ _ _ _ _ (continuous_capF α),integral_sampleLaw _ _ _ _ _ (continuous_capFpos α)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  unfold capF capFpos
  dsimp only
  rw [shortfall_sample_aligned k hk z n hn 0 (dyadicInt 1) 0 n hn (by simp) (by simp)]
  rw [max_eq_left (torusShortfall_mem k hk z 0 n hn).1]
lemma capF_scale_integral (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (hε : 0<ε) (α : ℝ) :
    (∫d,capF α d ∂scaleLaw k hk p l ε)=(∫d,capFpos α d ∂scaleLaw k hk p l ε) := by
  rw [integral_scaleLaw _ _ _ _ _ hε _ (continuous_capF α),integral_scaleLaw _ _ _ _ _ hε _ (continuous_capFpos α)]
  simp_rw [capF_sample_integral]
lemma vague_integrable_tendsto_bound {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X] [RegularSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
    (l : Filter ι) [l.NeBot] (μ : ι → Measure X) [∀i,IsFiniteMeasureOnCompacts (μ i)]
    (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hconv : ∀g:C_c(X,ℝ),Tendsto (fun i => ∫x,g x ∂μ i) l (𝓝 (∫x,g x ∂ν)))
    (f:X→ℝ) (hf:Continuous f) (h0:∀x,0≤f x) (a:ι→ℝ) (A:ℝ) (hA:0≤A)
    (ha:Tendsto a l (𝓝 A)) (hi:∀i,Integrable f (μ i)) (hb:∀ᶠi in l,(∫x,f x ∂μ i)≤a i) :
    Integrable f ν ∧ (∫x,f x ∂ν)≤A := by
  have hcc : ∀g:C_c(X,ℝ),(∀x,0≤g x) → (∀x,g x≤f x) → (∫x,g x ∂ν)≤A := by
    intro g hg hgf
    apply le_of_tendsto_of_tendsto (hconv g) ha
    filter_upwards [hb] with i hiA
    exact (integral_mono (g.continuous.integrable_of_hasCompactSupport (μ := μ i) g.hasCompactSupport) (hi i) hgf).trans hiA
  have hL := lintegral_le_of_cc_le ν f hf h0 A hcc
  have hiν : Integrable f ν := ⟨hf.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mpr (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hiν,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hiν (Eventually.of_forall h0)] at hL
  exact (ENNReal.ofReal_le_ofReal_iff hA).mp hL
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma terminal_cap_bounds {α : ℝ} (hα : 0≤α) (hα1 : α≤1) {C : ℝ}
    (hb : ∀u∈Icc (0:ℝ) 1,entropyCap α u≤C*u) (i : ℕ) :
    α/10000≤(∫d,capFpos α d ∂S.terminalLaw i) ∧ (∫d,capFpos α d ∂S.terminalLaw i)≤C := by
  have hi := (continuous_capFpos α).integrable_of_hasCompactSupport (μ := S.terminalLaw i) (HasCompactSupport.of_compactSpace _)
  have hh : Integrable (fun d => max (arrayShortfall 0 (dyadicInt 1) d) 0) (S.terminalLaw i) := ((continuous_arrayShortfall 0 (dyadicInt 1)).max continuous_const).integrable_of_hasCompactSupport (μ := S.terminalLaw i) (HasCompactSupport.of_compactSpace _)
  constructor
  · have he := integral_mono (hh.const_mul (α/10000)) hi (fun d => entropyCap_lower hα hα1 (shortfall_one_max_mem d))
    simpa only [integral_const_mul,S.terminal_shortfall_max_integral i,mul_one] using he
  · have he := integral_mono hi (hh.const_mul C) (fun d => hb _ (shortfall_one_max_mem d))
    simpa only [integral_const_mul,S.terminal_shortfall_max_integral i,mul_one] using he
lemma exists_terminal_cap_limit {α : ℝ} (hα : 0<α) (hα1 : α≤1) :
    ∃H:ℝ,0<H ∧ Tendsto (fun i => ∫d,capF α d ∂S.terminalLaw i) (L.filter:Filter ℕ) (𝓝 H) ∧
      Integrable (fun d:NonAffineArray => capF α d.val) L.terminal ∧
      (∫d:NonAffineArray,capF α d.val ∂L.terminal)≤H := by
  obtain ⟨C,hC,hb⟩ := entropyCap_upper hα.le hα1
  let a : ℕ→ℝ := fun i => ∫d,capFpos α d ∂S.terminalLaw i
  have hmem : ∀i,a i∈Icc (α/10000) C := S.terminal_cap_bounds hα.le hα1 hb
  obtain ⟨H,hH,ht⟩ := (isCompact_Icc : IsCompact (Icc (α/10000) C)).ultrafilter_le_nhds (L.filter.map a) (by
    rw [Filter.le_principal_iff]
    change Icc (α/10000) C∈Filter.map a (L.filter:Filter ℕ)
    exact Filter.mem_map.mpr (Eventually.of_forall hmem))
  have hH0 : 0<H := (div_pos hα (by norm_num)).trans_le hH.1
  have ht' : Tendsto a (L.filter:Filter ℕ) (𝓝 H) := ht
  obtain ⟨hi,hle⟩ := vague_integrable_tendsto_bound L.filter (fun i => nonaffinePart (S.terminalLaw i)) L.terminal L.terminal_converges
    (fun d => capFpos α d.val) ((continuous_capFpos α).comp continuous_subtype_val)
    (fun d => capFpos_nonneg hα.le hα1 d.val) a H hH0.le ht'
    (fun i => integrable_nonaffinePart _ _ (continuous_capFpos α)) (Eventually.of_forall (fun i =>
      integral_nonaffinePart_le _ _ (continuous_capFpos α) (capFpos_nonneg hα.le hα1)))
  have he : (fun d:NonAffineArray => capFpos α d.val)=ᵐ[L.terminal] (fun d => capF α d.val) := by
    filter_upwards [S.unit_aeterminal L] with d hd
    unfold capFpos capF
    rw [max_eq_left (shortfall_unit_mem d.val hd _ _ (by norm_num)).1]
  refine ⟨H,hH0,?_,hi.congr he,by rw [←integral_congr_ae he]; exact hle⟩
  convert! ht' using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  exact capF_scale_integral _ _ _ _ _ (S.epsilon_pos i) α
end CriticalScaleSequence
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
lemma capG_coboundary (α:ℝ) (d:DistanceArray) :
    capG α d=capF α (arrayDilate d)-(capF α d+capF α (arrayTranslate (dyadicInt 1) d))/2 := by
  unfold capG capF
  rw [shortfall_dilate,shortfall_translate,zero_add,zero_add]
  have h2 : dyadicInt 1+dyadicInt 1=dyadicInt 2 := by apply Subtype.ext; norm_num
  rw [h2]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_CappedPrelimit
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
lemma single_shortfall_max_integral (k:ℝ) (hk:0≤k) (p:ℕ) (ε:ℝ) (hε:0<ε) :
    (∫d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂scaleLaw k hk p 1 ε)=meanDeficit k (2^p)/ε := by
  rw [integral_scaleLaw _ _ _ _ _ hε _ ((continuous_arrayShortfall _ _).max continuous_const)]
  simp only [Finset.range_one,Finset.sum_singleton,Nat.add_zero]
  let n:ℕ:=2^p
  have hn : 0<n := by dsimp [n]; positivity
  have hs : (n:ℝ)*(0:DyadicTime)=((0:ℤ):ℝ) := by simp
  have ht : (n:ℝ)*(dyadicInt 1:ℝ)=((0:ℤ):ℝ)+(n:ℝ) := by simp
  have he : (∫d,max (arrayShortfall 0 (dyadicInt 1) d) 0 ∂sampleLaw k hk (2^p) hn)=
      ∫d,arrayShortfall 0 (dyadicInt 1) d ∂sampleLaw k hk (2^p) hn := by
    rw [integral_sampleLaw _ _ _ _ _ ((continuous_arrayShortfall _ _).max continuous_const),
      integral_sampleLaw _ _ _ _ _ (continuous_arrayShortfall _ _)]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only
    rw [shortfall_sample_aligned k hk z n hn 0 (dyadicInt 1) 0 (2^p) hn hs ht]
    exact max_eq_left (torusShortfall_mem k hk z 0 (2^p) hn).1
  rw [he,integral_shortfall_sample k hk n hn 0 (dyadicInt 1) 0 (2^p) hn hs ht]
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma initial_cap_tendsto {α:ℝ} (hα:0≤α) (hα1:α≤1) :
    Tendsto (fun i => ∫d,capF α d ∂S.initialLaw i) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := entropyCap_upper hα hα1
  have he (i:ℕ) : (∫d,capF α d ∂S.initialLaw i)=(∫d,capFpos α d ∂S.initialLaw i) :=
    capF_scale_integral _ _ _ _ _ (S.epsilon_pos i) α
  simp_rw [he]
  apply squeeze_zero (fun i => integral_nonneg (capFpos_nonneg hα hα1))
    (fun i => ?_) (by simpa only [mul_zero,Nat.add_zero] using (S.initial_ratio_tendsto 0).const_mul C)
  have hi := (continuous_capFpos α).integrable_of_hasCompactSupport (μ := S.initialLaw i) (HasCompactSupport.of_compactSpace _)
  have hh : Integrable (fun d => max (arrayShortfall 0 (dyadicInt 1) d) 0) (S.initialLaw i) :=
    ((continuous_arrayShortfall _ _).max continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hx := integral_mono hi (hh.const_mul C) (fun d => hb _ (shortfall_one_max_mem d))
  rw [integral_const_mul,initialLaw,single_shortfall_max_integral _ _ _ _ (S.epsilon_pos i)] at hx
  exact hx
lemma multiLaw_translate_one (i:ℕ) : (S.multiLaw i).map (arrayTranslate (dyadicInt 1))=S.multiLaw i := by
  apply scaleLaw_translate _ _ _ _ _ _ ((2:ℤ)^(criticalLowerExponent S.offset i))
  simp
lemma integral_F_dilation_balance (i:ℕ) (F:DistanceArray→ℝ) (hF:Continuous F) :
    (∫d,F (arrayDilate d) ∂S.multiLaw i)+(∫d,F d ∂S.initialLaw i)=
      (∫d,F d ∂S.multiLaw i)+(∫d,F d ∂S.terminalLaw i) := by
  rw [←integral_map continuous_arrayDilate.measurable.aemeasurable hF.aestronglyMeasurable]
  have hi (μ:Measure DistanceArray) [IsFiniteMeasure μ] : Integrable F μ :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [←integral_add_measure (hi _) (hi _),←integral_add_measure (hi _) (hi _),S.law_dilation_balance i]
lemma capG_prelimit_balance (i:ℕ) (α:ℝ) :
    (∫d,capG α d ∂S.multiLaw i)=(∫d,capF α d ∂S.terminalLaw i)-(∫d,capF α d ∂S.initialLaw i) := by
  have h1 := (continuous_capF α).integrable_of_hasCompactSupport (μ := S.multiLaw i) (HasCompactSupport.of_compactSpace _)
  have hd := ((continuous_capF α).comp continuous_arrayDilate).integrable_of_hasCompactSupport (μ := S.multiLaw i) (HasCompactSupport.of_compactSpace _)
  have ht := ((continuous_capF α).comp (continuous_arrayTranslate (dyadicInt 1))).integrable_of_hasCompactSupport (μ := S.multiLaw i) (HasCompactSupport.of_compactSpace _)
  simp_rw [capG_coboundary]
  have he := integral_sub hd ((h1.add ht).div_const 2)
  simp only [Pi.add_apply,Function.comp_apply] at he
  rw [he,integral_div]
  have hea := integral_add h1 ht
  simp only [Function.comp_apply] at hea
  rw [hea]
  rw [←integral_map (continuous_arrayTranslate (dyadicInt 1)).measurable.aemeasurable (continuous_capF α).aestronglyMeasurable,S.multiLaw_translate_one i]
  linarith [S.integral_F_dilation_balance i (capF α) (continuous_capF α)]
lemma capG_prelimit_tendsto {α H:ℝ} (hα:0≤α) (hα1:α≤1)
    (hH:Tendsto (fun i => ∫d,capF α d ∂S.terminalLaw i) (L.filter:Filter ℕ) (𝓝 H)) :
    Tendsto (fun i => ∫d,capG α d ∂S.multiLaw i) (L.filter:Filter ℕ) (𝓝 H) := by
  simp_rw [S.capG_prelimit_balance]
  simpa only [sub_zero] using hH.sub ((S.initial_cap_tendsto hα hα1).mono_left L.refines)
end CriticalScaleSequence
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

theorem no_critical_scale_sequence_q44_oai (S:CriticalScaleSequence) : False := by
  obtain ⟨L⟩:=S.exists_limitLaws_q44
  let α:ℝ:=1/(32*1200000004)
  have ha:0<α := by norm_num [α]
  have ha1:α≤1 := by norm_num [α]
  have haS:α*1200000004≤1/16 := by norm_num [α]
  obtain ⟨H,hH,hconv,hint,hbound⟩:=S.exists_terminal_cap_limit L ha ha1
  have hbalance:(∫d:NonAffineArray,capG α d.val ∂L.multi)=H :=
    tendsto_nhds_unique (S.capG_limit_balance_q44 L ha.le) (S.capG_prelimit_tendsto L ha.le ha1 hconv)
  have hstrict:=S.terminal_cap_strict_q44 L ha.le ha1 hH hbound
  have hrem:=S.remainder_cap_nonpos_q44 L ha.le ha1 haS
  rw [S.capG_integral_decomposition_q44 L] at hbalance
  linarith

end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.no_critical_scale_sequence_q44_oai := @OAI.StandardMapEntropy.no_critical_scale_sequence_q44_oai
