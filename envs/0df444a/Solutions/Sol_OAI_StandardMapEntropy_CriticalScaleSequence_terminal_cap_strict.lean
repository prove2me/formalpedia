-- Prove2me | solution 1 for OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T00:24:10.686885+00:00
-- url     : https://prove2.me/submissions/76bdd2a7-b428-4cf4-839f-b066a6cb829e

import Mathlib
import Definitions.Def_StandardMapEntropy
import Definitions.Def_OAIQ2St000
import Theorems.Thm_OAI_StandardMapEntropy_CriticalScaleSequence_terminal_event_lower

section
-- module Solutions.OAIQ2_Std.StandardMap_LocalScarcity
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
-- module Solutions.OAIQ2_Std.StandardMap_ObservationTransport
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
lemma transferStep_difference_bound (v w : ℝ) : ‖transferStep v-transferStep w‖ ≤ |v-w| := by
  apply (transferStep v-transferStep w).opNorm_le_bound (abs_nonneg _)
  intro z
  have he : (transferStep v-transferStep w) z=((v-w)*z.re : ℝ) := by
    apply Complex.ext <;> simp only [sub_apply,Complex.sub_re,Complex.sub_im,
      transferStep_re,transferStep_im,Complex.ofReal_re,Complex.ofReal_im] <;> ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) (abs_nonneg _)

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_SegmentObservations
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
-- module Solutions.OAIQ2_Std.StandardMap_TorusDynamics
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
lemma torusIter_add (k : ℝ) (i j : ℤ) (z : Torus) :
    torusIter k (i+j) z=torusIter k i (torusIter k j z) := by
  simp only [torusIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
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
-- module Solutions.OAIQ2_Std.StandardMap_ClosedEligibility
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

lemma continuous_transferStep : Continuous transferStep := by
  apply Metric.continuous_iff.mpr
  intro v ε hε
  refine ⟨ε,hε,?_⟩
  intro w hw
  rw [dist_eq_norm]
  exact (transferStep_difference_bound w v).trans_lt (by simpa only [Real.dist_eq] using hw)

lemma continuous_transferProduct_params {α : Type*} [TopologicalSpace α]
    (v : α → ℕ → ℝ) (hv : ∀ n, Continuous (fun x => v x n)) (n : ℕ) :
    Continuous (fun x => transferProduct (v x) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (continuous_transferStep.comp (hv (n+1))).clm_comp ih

end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TorusObservations
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
lemma continuous_cosine : Continuous cosine := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
  change Continuous (fun x : ℝ => cosine (x : Circle))
  simpa only [cosine_coe,Function.comp_def,Pi.mul_apply,id_eq] using
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
lemma continuous_torusPotential (k : ℝ) : Continuous (torusPotential k) :=
  continuous_const.add (continuous_const.mul continuous_cosine)
lemma continuous_torusSegmentCoefficient (k : ℝ) (a : ℤ) (i : ℕ) :
    Continuous (fun z => torusSegmentCoefficient k z a i) :=
  (continuous_torusPotential k).comp (continuous_fst.comp (continuous_torusIter k _))
lemma continuous_torusSegmentTransfer (k : ℝ) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusSegmentTransfer k z a n) :=
  continuous_transferProduct_params (fun z i => torusSegmentCoefficient k z a i)
    (fun i => continuous_torusSegmentCoefficient k a i) n
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CocycleAlgebra
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
lemma torusSegmentTransfer_shift (k : ℝ) (z : Torus) (a b : ℤ) (n : ℕ) :
    torusSegmentTransfer k (torusIter k b z) a n=torusSegmentTransfer k z (a+b) n := by
  unfold torusSegmentTransfer
  congr 1
  funext i
  unfold torusSegmentCoefficient
  rw [← torusIter_add]
  congr 3
  ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ProductDistances
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
lemma productDistance_forward (k : ℝ) (z : Torus) (i : ℤ) (n : ℕ) :
    productDistance k z i (i+(n:ℤ))=Real.log ‖torusSegmentTransfer k z i n‖/Real.log (growthBase k) := by
  simp only [productDistance,torusTransfer_forward]
lemma productDistance_shift (k : ℝ) (z : Torus) (i j a : ℤ) :
    productDistance k (torusIter k a z) i j=productDistance k z (i+a) (j+a) := by
  wlog hij : i≤j generalizing i j
  · rw [productDistance_symm k _ i j,productDistance_symm k _ (i+a) (j+a)]
    exact this j i (le_of_not_ge hij)
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  have hn' : i+a+((j-i).toNat:ℤ)=j+a := by omega
  rw [← hn,productDistance_forward]
  conv_rhs => rw [show i+((j-i).toNat:ℤ)+a=i+a+((j-i).toNat:ℤ) by ring]
  rw [productDistance_forward,torusSegmentTransfer_shift]
lemma continuous_productDistance (k : ℝ) (hk : 0≤k) (i j : ℤ) :
    Continuous (fun z => productDistance k z i j) := by
  wlog hij : i≤j generalizing i j
  · have hh := this j i (le_of_not_ge hij)
    simpa only [productDistance_symm k _ j i] using hh
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  rw [← hn]
  simp only [productDistance_forward]
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k i _).norm.log (fun z => by
    have := (torusSegmentTransfer_norm_bounds k hk z i (j-i).toNat).1; linarith)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_SmoothCap
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
-- module Solutions.OAIQ2_Std.StandardMap_SmoothControl
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
lemma c2_remainder_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x z : ℝ} (hC : 0≤C)
    (hb : ∀u∈Icc a b,|deriv (deriv f) u|≤C) (hx : x∈Icc a b) (hz : z∈Icc a b) :
    |f x-f z-deriv f z*(x-z)|≤C*(x-z)^2 := by
  have hsub : uIcc z x⊆Icc a b := by
    intro u hu
    rw [mem_uIcc] at hu
    rcases hu with ⟨hzu,hux⟩|⟨hxu,huz⟩
    · exact ⟨hz.1.trans hzu,hux.trans hx.2⟩
    · exact ⟨hx.1.trans hxu,huz.trans hz.2⟩
  let R : ℝ → ℝ := fun u => f u-f z-deriv f z*(u-z)
  have hd (u : ℝ) : HasDerivAt R (deriv f u-deriv f z) u := by
    convert! (((hf.differentiable (by norm_num) u).hasDerivAt.sub_const (f z)).sub
      (((hasDerivAt_id u).sub_const z).const_mul (deriv f z))) using 1 ; simp
  have hR : ∀u∈uIcc z x,|deriv R u|≤C*|x-z| := by
    intro u hu
    rw [(hd u).deriv]
    have h1 := deriv_bound_lipschitz hf.differentiable_deriv_two hb hz (hsub hu)
    have hu' : |u-z|≤|x-z| := by
      rw [mem_uIcc] at hu
      rcases hu with ⟨hzu,hux⟩|⟨hxu,huz⟩
      · rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_left hu' hC)
  have hr := Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => (hd u).differentiableAt)
    hR (convex_uIcc z x) (left_mem_uIcc) (right_mem_uIcc)
  change |R x-R z|≤(C*|x-z|)*|x-z| at hr
  have he : R z=0 := by dsimp [R]; ring
  rw [he,sub_zero,mul_assoc,←pow_two, sq_abs] at hr
  exact hr
lemma c2_midpoint_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x y : ℝ} (hC : 0≤C)
    (hb : ∀u∈Icc a b,|deriv (deriv f) u|≤C) (hx : x∈Icc a b) (hy : y∈Icc a b) :
    |f ((x+y)/2)-(f x+f y)/2|≤(C/4)*(x-y)^2 := by
  have hm : (x+y)/2∈Icc a b := ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
  have h1 := c2_remainder_bound hf hC hb hx hm
  have h2 := c2_remainder_bound hf hC hb hy hm
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1,h1.2,h2.1,h2.2]
lemma c2_capped_difference {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b C x y z : ℝ} (hC : 0≤C)
    (h1 : ∀u∈Icc a b,|deriv f u|≤C) (h2 : ∀u∈Icc a b,|deriv (deriv f) u|≤C)
    (hx : x∈Icc a b) (hy : y∈Icc a b) (hz : z∈Icc a b) (hJ : 0≤z-(x+y)/2) :
    |f z-(f x+f y)/2|≤C*((z-(x+y)/2)+(x-y)^2) := by
  have hm : (x+y)/2∈Icc a b := ⟨by linarith [hx.1,hy.1],by linarith [hx.2,hy.2]⟩
  have hh := deriv_bound_lipschitz (hf.differentiable (by norm_num)) h1 hm hz
  rw [abs_of_nonneg hJ] at hh
  have ht := c2_midpoint_bound hf hC h2 hx hy
  have htri := abs_add_le (f z-f ((x+y)/2)) (f ((x+y)/2)-(f x+f y)/2)
  rw [sub_add_sub_cancel] at htri
  nlinarith [mul_nonneg hC (sq_nonneg (x-y))]
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
-- module Solutions.OAIQ2_Std.StandardMap_CancellationTheorem
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
-- module Solutions.OAIQ2_Std.StandardMap_MeanDeficit
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_MeanCancellation
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
-- module Solutions.OAIQ2_Std.StandardMap_MeanGrowth
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
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_FixedDeficit
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
-- module Solutions.OAIQ2_Std.StandardMap_CriticalSequence
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayTests
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
lemma arrayV_nonneg (s t : DyadicTime) (d : DistanceArray) : 0≤arrayV s t d := sq_nonneg _
lemma array_zero_test_halves (s t : DyadicTime) (hst : (s:ℝ)<(t:ℝ)) (d : DistanceArray)
    (hzero : arrayJ s t d+arrayV s t d=0) :
    d.val s (dyadicMid s t)=d.val s t/2 ∧ d.val (dyadicMid s t) t=d.val s t/2 := by
  have hJ : arrayJ s t d=0 := by linarith [arrayJ_nonneg s t hst d,arrayV_nonneg s t d]
  have hV : arrayV s t d=0 := by linarith
  have he : arrayShortfall s (dyadicMid s t) d=arrayShortfall (dyadicMid s t) t d := by
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hV)
  rw [arrayJ_eq s t hst d] at hJ
  have hsum : d.val s (dyadicMid s t)+d.val (dyadicMid s t) t=d.val s t := by
    have := (div_eq_zero_iff.mp hJ).resolve_right (sub_ne_zero.mpr hst.ne')
    linarith
  unfold arrayShortfall at he
  rw [dyadicMid_val] at he
  have hm : ((s:ℝ)+(t:ℝ))/2-(s:ℝ)=((t:ℝ)-(s:ℝ))/2 := by ring
  have hm' : (t:ℝ)-((s:ℝ)+(t:ℝ))/2=((t:ℝ)-(s:ℝ))/2 := by ring
  rw [hm,hm'] at he
  have hn : ((t:ℝ)-(s:ℝ))/2≠0 := by positivity
  have he' : d.val s (dyadicMid s t)=d.val (dyadicMid s t) t := (div_left_inj' hn).mp (by linarith)
  constructor <;> linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ArrayGrid
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
lemma dyadic_zsmul_val (i : ℤ) (h : DyadicTime) : ((i • h : DyadicTime):ℝ)=(i:ℝ)*(h:ℝ) := by
  simp only [AddSubgroup.coe_zsmul,zsmul_eq_mul]
lemma dyadic_mid_grid (h : DyadicTime) (i : ℤ) : dyadicMid (i • h) ((i+2) • h)=(i+1) • h := by
  apply Subtype.ext
  simp only [dyadicMid_val,dyadic_zsmul_val,Int.cast_add,Int.cast_one,Int.cast_ofNat]
  ring
lemma int_constant_of_succ (f : ℤ → ℝ) (hf : ∀ i,f (i+1)=f i) (i : ℤ) : f i=f 0 := by
  induction i using Int.induction_on with
  | zero => rfl
  | succ n ih => rw [hf,ih]
  | pred n ih => rw [← hf (- (n:ℤ)-1),sub_add_cancel,ih]
lemma array_grid_edges (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (h : DyadicTime) (hh : 0<(h:ℝ)) (i : ℤ) :
    d.val (i • h) ((i+1) • h)=d.val 0 h := by
  let f : ℤ → ℝ := fun i => d.val (i • h) ((i+1) • h)
  have hf (i : ℤ) : f (i+1)=f i := by
    have hi : ((i • h : DyadicTime):ℝ)<(((i+2) • h : DyadicTime):ℝ) := by
      simp only [dyadic_zsmul_val,Int.cast_add,Int.cast_ofNat]; nlinarith
    obtain ⟨hL,hR⟩ := array_zero_test_halves (i • h) ((i+2) • h) hi d (hz _ _ hi)
    rw [dyadic_mid_grid] at hL hR
    dsimp only [f]
    simpa only [show i+1+1=i+2 by ring] using hR.trans hL.symm
  have he := int_constant_of_succ f hf i
  simpa only [f,zero_smul,zero_add,one_zsmul] using he
lemma array_grid_upper (d : DistanceArray) (h : DyadicTime) (c : ℝ)
    (he : ∀ i : ℤ,d.val (i • h) ((i+1) • h)=c) (i : ℤ) (n : ℕ) :
    d.val (i • h) ((i+(n:ℤ)) • h) ≤ (n:ℝ)*c := by
  induction n with
  | zero => simpa using (show d.val (i • h) (i • h) ≤ 0 by rw [d.property.2.1])
  | succ n ih =>
      have ht := d.property.2.2.2.1 (i • h) ((i+(n:ℤ)) • h) ((i+((n+1:ℕ):ℤ)) • h)
      have hn : i+((n+1:ℕ):ℤ)=i+(n:ℤ)+1 := by omega
      rw [hn,he] at ht
      rw [hn]
      push_cast
      linarith
lemma array_grid_power (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (h : DyadicTime) (hh : 0<(h:ℝ)) (i : ℤ) (m : ℕ) :
    d.val (i • h) ((i+(2:ℤ)^m) • h)=(2:ℝ)^m*d.val 0 h := by
  induction m with
  | zero => simpa using array_grid_edges d hz h hh i
  | succ m ih =>
      have hm : (0:ℝ)<(2:ℝ)^(m+1) := by positivity
      have hi : ((i • h : DyadicTime):ℝ)<(((i+(2:ℤ)^(m+1)) • h : DyadicTime):ℝ) := by
        simp only [dyadic_zsmul_val,Int.cast_add,Int.cast_pow,Int.cast_ofNat]
        nlinarith
      have hmid : dyadicMid (i • h) ((i+(2:ℤ)^(m+1)) • h)=(i+(2:ℤ)^m) • h := by
        apply Subtype.ext
        simp only [dyadicMid_val,dyadic_zsmul_val,Int.cast_add,Int.cast_pow,Int.cast_ofNat,pow_succ]
        push_cast
        ring
      have hl := (array_zero_test_halves _ _ hi d (hz _ _ hi)).1
      rw [hmid,ih] at hl
      calc
        _ = 2*((2:ℝ)^m*d.val 0 h) := by linarith
        _ = _ := by rw [pow_succ]; ring
lemma nat_le_two_power (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 1 ≤ (2:ℕ)^n := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      omega
lemma array_grid_distance_nat (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (h : DyadicTime) (hh : 0<(h:ℝ)) (i : ℤ) (n : ℕ) :
    d.val (i • h) ((i+(n:ℤ)) • h)=(n:ℝ)*d.val 0 h := by
  have he := array_grid_edges d hz h hh
  apply le_antisymm (array_grid_upper d h (d.val 0 h) he i n)
  let N : ℕ := 2^n
  have hn : n ≤ N := nat_le_two_power n
  have hu := array_grid_upper d h (d.val 0 h) he (i+(n:ℤ)) (N-n)
  have hidx : i+(n:ℤ)+((N-n:ℕ):ℤ)=i+(2:ℤ)^n := by
    rw [Nat.cast_sub hn]
    dsimp only [N]
    push_cast; ring
  rw [hidx] at hu
  have ht := d.property.2.2.2.1 (i • h) ((i+(n:ℤ)) • h) ((i+(2:ℤ)^n) • h)
  rw [array_grid_power d hz h hh i n] at ht
  have hcast : ((N-n:ℕ):ℝ)=(2:ℝ)^n-(n:ℝ) := by rw [Nat.cast_sub hn]; simp [N]
  rw [hcast] at hu
  nlinarith
lemma array_grid_distance (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (h : DyadicTime) (hh : 0<(h:ℝ)) (i j : ℤ) :
    d.val (i • h) (j • h)=|(j:ℝ)-(i:ℝ)| *d.val 0 h := by
  wlog hij : i ≤ j generalizing i j
  · rw [d.property.2.2.1,abs_sub_comm]
    exact this j i (le_of_not_ge hij)
  have hn : i+((j-i).toNat:ℤ)=j := by rw [Int.toNat_of_nonneg (sub_nonneg.mpr hij)]; ring
  have he := array_grid_distance_nat d hz h hh i (j-i).toNat
  rw [hn] at he
  have hcast : ((j-i).toNat:ℝ)=(j:ℝ)-(i:ℝ) := by
    have hh := congrArg (fun a : ℤ => (a:ℝ)) (Int.toNat_of_nonneg (sub_nonneg.mpr hij))
    simpa only [Int.cast_natCast,Int.cast_sub] using hh
  rw [hcast] at he
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hij))]
  exact he
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ArrayAffinity
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
lemma dyadicUnit_pos (n : ℕ) : 0<(dyadicUnit n:ℝ) := by change 0<(1:ℝ)/(2:ℝ)^n; positivity
lemma dyadic_common_grid (s t : DyadicTime) :
    ∃ m : ℕ, ∃ a b : ℤ,s=a • dyadicUnit m ∧ t=b • dyadicUnit m := by
  obtain ⟨n,a,hs⟩ := dyadicTime_mem s
  obtain ⟨m,b,ht⟩ := dyadicTime_mem t
  refine ⟨n+m,a*2^m,b*2^n,?_,?_⟩
  · apply Subtype.ext
    rw [dyadic_zsmul_val,dyadicUnit_val,hs,pow_add]
    push_cast
    field_simp
  · apply Subtype.ext
    rw [dyadic_zsmul_val,dyadicUnit_val,ht,pow_add]
    push_cast
    field_simp
lemma dyadic_unit_power (n : ℕ) : (2:ℤ)^n • dyadicUnit n=dyadicInt 1 := by
  apply Subtype.ext
  simp only [dyadic_zsmul_val,dyadicUnit_val,dyadicInt_val,Int.cast_pow,Int.cast_ofNat,Int.cast_one]
  field_simp
lemma array_affine_values_of_zero (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0)
    (s t : DyadicTime) : d.val s t=d.val 0 (dyadicInt 1)*|(t:ℝ)-(s:ℝ)| := by
  obtain ⟨m,a,b,rfl,rfl⟩ := dyadic_common_grid s t
  have hpow : (0:ℝ)<(2:ℝ)^m := by positivity
  have hc := array_grid_distance d hz (dyadicUnit m) (dyadicUnit_pos m) 0 ((2:ℤ)^m)
  simp only [zero_smul,dyadic_unit_power,Int.cast_pow,Int.cast_ofNat,Int.cast_zero,sub_zero,abs_of_pos hpow] at hc
  have he := array_grid_distance d hz (dyadicUnit m) (dyadicUnit_pos m) a b
  rw [he,dyadic_zsmul_val,dyadic_zsmul_val,dyadicUnit_val]
  rw [show (b:ℝ)*((1:ℝ)/2^m)-(a:ℝ)*((1:ℝ)/2^m)=((b:ℝ)-(a:ℝ))*((1:ℝ)/2^m) by ring,abs_mul,
    abs_of_pos (by positivity : (0:ℝ)<1/(2:ℝ)^m),hc]
  field_simp
lemma array_affine_of_zero_tests (d : DistanceArray)
    (hz : ∀ s t : DyadicTime, (s:ℝ)<(t:ℝ) → arrayJ s t d+arrayV s t d=0) : d∈affineLocus := by
  let w := d.val 0 (dyadicInt 1)
  have hw0 : 0 ≤ w := d.property.1 _ _
  have hw1 : w ≤ 1 := by
    by_contra hn
    have hp : 0<w-1 := by linarith
    obtain ⟨n,hn⟩ := exists_nat_gt (2/(w-1))
    have hbig : 2<(n:ℝ)*(w-1) := (div_lt_iff₀ hp).mp hn
    have hb := d.property.2.2.2.2 0 (dyadicInt (n:ℤ))
    rw [array_affine_values_of_zero d hz] at hb
    simp only [dyadicInt_val,Int.cast_natCast,ZeroMemClass.coe_zero,sub_zero,Nat.abs_cast] at hb
    change w*(n:ℝ) ≤ (n:ℝ)+2 at hb
    nlinarith
  refine ⟨⟨w,hw0,hw1⟩,?_⟩
  apply Subtype.ext
  funext s t
  exact (array_affine_values_of_zero d hz s t).symm
lemma continuous_arrayTest (i : ArrayTestIndex) : Continuous (arrayTest i) :=
  (continuous_arrayJ _ _).add (continuous_arrayV _ _)
lemma arrayTest_nonneg (i : ArrayTestIndex) (d : DistanceArray) : 0 ≤ arrayTest i d :=
  add_nonneg (arrayJ_nonneg _ _ i.property d) (arrayV_nonneg _ _ d)
lemma arrayTest_affine_zero (i : ArrayTestIndex) (w : Icc (0:ℝ) 1) : arrayTest i (affineArray w)=0 := by
  obtain ⟨⟨s,t⟩,hst⟩ := i
  have hmid := dyadicMid_val s t
  have h1 : 0<(t:ℝ)-(s:ℝ) := sub_pos.mpr hst
  have h2 : 0<((s:ℝ)+(t:ℝ))/2-(s:ℝ) := by linarith
  have h3 : 0<(t:ℝ)-((s:ℝ)+(t:ℝ))/2 := by linarith
  have hs (u v : DyadicTime) (huv : (u:ℝ)<(v:ℝ)) :
      arrayShortfall u v (affineArray w)=1-w.val := by
    unfold arrayShortfall affineArray
    dsimp only
    rw [abs_of_pos (sub_pos.mpr huv),mul_div_cancel_right₀ _ (sub_ne_zero.mpr huv.ne')]
  unfold arrayTest arrayJ arrayV
  dsimp only
  rw [hs s t hst,hs s (dyadicMid s t) (by rw [dyadicMid_val]; linarith),
    hs (dyadicMid s t) t (by rw [dyadicMid_val]; linarith)]
  ring
lemma nonaffine_iff_positive_test (d : DistanceArray) : d∉affineLocus ↔ ∃ i : ArrayTestIndex,0<arrayTest i d := by
  constructor
  · intro hd
    by_contra hn
    push Not at hn
    apply hd
    apply array_affine_of_zero_tests d
    intro s t hst
    exact le_antisymm (hn ⟨(s,t),hst⟩) (arrayTest_nonneg ⟨(s,t),hst⟩ d)
  · rintro ⟨i,hi⟩ ⟨w,rfl⟩
    rw [arrayTest_affine_zero] at hi
    exact lt_irrefl _ hi
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_RescaledArrays
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
-- module Solutions.OAIQ2_Std.StandardMap_SampleLaws
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayMoments
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleLaws
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleTelescopes
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
-- module Solutions.OAIQ2_Std.StandardMap_ScaleTestBounds
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
-- module Solutions.OAIQ2_Std.StandardMap_CriticalLaws
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
lemma initialLaw_test_tendsto (j : ArrayTestIndex) :
    Tendsto (fun i => ∫ d,arrayTest j d ∂S.initialLaw i) atTop (𝓝 0) := by
  rcases j with ⟨⟨s,t⟩,hst⟩
  obtain ⟨p₀,hp₀⟩ := dyadic_interval_aligned_eventually s t hst
  obtain ⟨H,hH⟩ := pow_unbounded_of_one_lt ((t:ℝ)-(s:ℝ)) (by norm_num : (1:ℝ) < 2)
  have hH' : (t:ℝ)-(s:ℝ) ≤ (2:ℝ)^(H+1) := hH.le.trans (by rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) H])
  let R : ℝ := 2^(H+1)/((t:ℝ)-(s:ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg (fun d => arrayTest_nonneg _ d)))
  · filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop p₀] with i hi
    obtain ⟨a,m,hm,hs,ht⟩ := hp₀ _ hi
    exact singleLaw_test_bound (criticalLowerExponent S.offset i) (S.parameter i) (S.positive i).le (S.epsilon i)
      (S.epsilon_pos i) s t hst a m H hm hs ht hH'
  · simpa only [mul_zero] using (S.initial_ratio_tendsto (H+1)).const_mul (9*R)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ArrayTestCover
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instIsFiniteMeasureNonAffineArrayNonaffinePartOfDistanceArray _root_.OAI.StandardMapEntropy.instLocallyCompactSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology Classical
namespace StandardMapEntropy
lemma compact_nonaffine_finite_tests (F : Set DistanceArray) (hF : IsCompact F) (hFa : F⊆affineLocusᶜ) :
    ∃ t : Finset ArrayTestIndex, ∃ c : ℝ, 0<c ∧ ∀ d∈F,c ≤ ∑ i∈t,arrayTest i d := by
  classical
  by_cases hne : F.Nonempty
  · let U : ArrayTestIndex → Set DistanceArray := fun i => {d | 0<arrayTest i d}
    have hU : ∀ i,IsOpen (U i) := fun i => isOpen_lt continuous_const (continuous_arrayTest i)
    have hcover : F⊆⋃ i,U i := by
      intro d hd
      obtain ⟨i,hi⟩ := (nonaffine_iff_positive_test d).mp (hFa hd)
      exact Set.mem_iUnion.mpr ⟨i,hi⟩
    obtain ⟨t,ht⟩ := hF.elim_finite_subcover U hU hcover
    let f : DistanceArray → ℝ := fun d => ∑ i∈t,arrayTest i d
    have hcont : Continuous f := continuous_finsetSum _ (fun i hi => continuous_arrayTest i)
    have hpos : ∀ d∈F,0<f d := by
      intro d hd
      obtain ⟨i,hi,hd⟩ := Set.mem_iUnion₂.mp (ht hd)
      exact lt_of_lt_of_le hd (Finset.single_le_sum (fun j hj => arrayTest_nonneg j d) hi)
    obtain ⟨d,hd,hmin⟩ := hF.exists_isMinOn hne hcont.continuousOn
    exact ⟨t,f d,hpos d hd,fun e he => hmin he⟩
  · exact ⟨∅,1,by norm_num,fun d hd => (hne ⟨d,hd⟩).elim⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_NonaffineLimits
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
  rw [he]
  exact setIntegral_le_integral (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall hF0)
lemma integrable_nonaffinePart (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (F : DistanceArray → ℝ) (hF : Continuous F) : Integrable (fun d : NonAffineArray => F d.val) (nonaffinePart μ) := by
  have hi := (hF.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)).restrict (s := affineLocusᶜ)
  rw [← map_comap_subtype_coe isClosed_affineLocus.isOpen_compl.measurableSet,
    (MeasurableEmbedding.subtype_coe isClosed_affineLocus.isOpen_compl.measurableSet).integrable_map_iff] at hi
  exact hi
lemma compact_test_domination (g : C_c(NonAffineArray,ℝ)) :
    ∃ t : Finset ArrayTestIndex, ∃ C : ℝ, 0≤C ∧ ∀ d : NonAffineArray, |g d|≤C*∑ i∈t,arrayTest i d.val := by
  let F : Set DistanceArray := Subtype.val '' tsupport g
  have hF : IsCompact F := g.hasCompactSupport.isCompact.image continuous_subtype_val
  have hFa : F⊆affineLocusᶜ := by rintro d ⟨u,hu,rfl⟩; exact u.property
  obtain ⟨t,c,hc,hcover⟩ := compact_nonaffine_finite_tests F hF hFa
  obtain ⟨B,hB⟩ := g.hasCompactSupport.isCompact.exists_bound_of_continuousOn g.continuous.continuousOn
  let M : ℝ := max B 0
  have hM : 0≤M := le_max_right _ _
  refine ⟨t,M/c,div_nonneg hM hc.le,?_⟩
  intro d
  by_cases hd : d∈tsupport g
  · have h1 : |g d|≤M := by
      have hh : |g d|≤B := by convert! hB d hd using 1
      exact hh.trans (le_max_left _ _)
    have h2 := hcover d.val ⟨d,hd,rfl⟩
    have h3 := mul_le_mul_of_nonneg_left h2 (div_nonneg hM hc.le)
    rw [div_mul_cancel₀ M hc.ne'] at h3
    exact h1.trans h3
  · rw [image_eq_zero_of_notMem_tsupport hd,abs_zero]
    exact mul_nonneg (div_nonneg hM hc.le) (Finset.sum_nonneg (fun i hi => arrayTest_nonneg i d.val))
lemma cc_integral_nonaffine_bound (μ : Measure DistanceArray) [IsFiniteMeasure μ]
    (g : C_c(NonAffineArray,ℝ)) (t : Finset ArrayTestIndex) (C : ℝ) (hC : 0≤C)
    (hdom : ∀ d : NonAffineArray, |g d|≤C*∑ i∈t,arrayTest i d.val) :
    |∫ d,g d ∂nonaffinePart μ|≤C*∑ i∈t,∫ d,arrayTest i d ∂μ := by
  let F : DistanceArray → ℝ := fun d => ∑ i∈t,arrayTest i d
  have hF : Continuous F := continuous_finsetSum _ (fun i hi => continuous_arrayTest i)
  have hF0 : ∀ d,0≤F d := fun d => Finset.sum_nonneg (fun i hi => arrayTest_nonneg i d)
  have hiF := integrable_nonaffinePart μ F hF
  have hi := g.continuous.integrable_of_hasCompactSupport (μ := nonaffinePart μ) g.hasCompactSupport
  have h1 : |∫ d,g d ∂nonaffinePart μ|≤∫ d,|g d| ∂nonaffinePart μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := nonaffinePart μ) g
  have h2 : (∫ d,|g d| ∂nonaffinePart μ)≤C*(∫ d,F d.val ∂nonaffinePart μ) := by
    calc
      _ ≤ ∫ d,C*F d.val ∂nonaffinePart μ := integral_mono hi.abs (hiF.const_mul C) hdom
      _ = _ := integral_const_mul C _
  have h3 := integral_nonaffinePart_le μ F hF hF0
  apply (h1.trans h2).trans
  have he : (∫ d,F d ∂μ)=∑ i∈t,∫ d,arrayTest i d ∂μ := by
    apply integral_finsetSum
    intro i hi
    exact (continuous_arrayTest i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← he]
  exact mul_le_mul_of_nonneg_left h3 hC
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_CriticalLimits
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma vague_zero_of_tests {ι : Type*} (l : Filter ι) (μ : ι → Measure DistanceArray)
    [∀ i, IsFiniteMeasure (μ i)]
    (ht : ∀ j : ArrayTestIndex,Tendsto (fun i => ∫ d,arrayTest j d ∂μ i) l (𝓝 0))
    (g : C_c(NonAffineArray,ℝ)) : Tendsto (fun i => ∫ d,g d ∂nonaffinePart (μ i)) l (𝓝 0) := by
  obtain ⟨t,C,hC,hdom⟩ := compact_test_domination g
  have hsum : Tendsto (fun i => ∑ j∈t,∫ d,arrayTest j d ∂μ i) l (𝓝 0) := by
    simpa using tendsto_finsetSum t (fun j hj => ht j)
  have hbound := fun i => cc_integral_nonaffine_bound (μ i) g t C hC hdom
  apply squeeze_zero_norm (fun i => by simpa only [Real.norm_eq_abs] using hbound i)
  simpa only [mul_zero] using hsum.const_mul C
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence)
lemma initial_vague_zero (g : C_c(NonAffineArray,ℝ)) :
    Tendsto (fun i => ∫ d,g d ∂nonaffinePart (S.initialLaw i)) atTop (𝓝 0) :=
  vague_zero_of_tests atTop S.initialLaw S.initialLaw_test_tendsto g

end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_ArrayActions
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
-- module Solutions.OAIQ2_Std.StandardMap_LimitActions
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceDistanceArray _root_.OAI.StandardMapEntropy.instPseudoMetrizableSpaceNonAffineArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyDistanceArray _root_.OAI.StandardMapEntropy.instSecondCountableTopologyNonAffineArray _root_.OAI.StandardMapEntropy.instSigmaCompactSpaceNonAffineArray
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
lemma arrayTestExtend_dilate (g : C_c(NonAffineArray,ℝ)) (d : DistanceArray) :
    arrayTestExtend (g.comp nonaffineDilation) d=arrayTestExtend g (arrayDilate d) := by
  by_cases hd : d∈affineLocus
  · rw [arrayTestExtend_affine _ d hd,arrayTestExtend_affine _ _ ((arrayDilate_mem_affine_iff d).mpr hd)]
  · exact (arrayTestExtend_apply _ ⟨d,hd⟩).trans (arrayTestExtend_apply g (nonaffineDilate ⟨d,hd⟩)).symm
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
-- module Solutions.OAIQ2_Std.StandardMap_LimitBalance
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
  rw [Nat.add_sub_of_le (S.lower_lt i).le]
lemma integral_law_dilation_balance (i : ℕ) (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,(g.comp nonaffineDilation) d ∂nonaffinePart (S.multiLaw i))+
      (∫ d,g d ∂nonaffinePart (S.initialLaw i))=
      (∫ d,g d ∂nonaffinePart (S.multiLaw i))+(∫ d,g d ∂nonaffinePart (S.terminalLaw i)) := by
  rw [←integral_arrayTestExtend,←integral_arrayTestExtend,←integral_arrayTestExtend,←integral_arrayTestExtend]
  simp_rw [arrayTestExtend_dilate]
  rw [← integral_map (f := fun d => arrayTestExtend g d) continuous_arrayDilate.measurable.aemeasurable (arrayTestExtend g).continuous.aestronglyMeasurable]
  have hi (μ : Measure DistanceArray) [IsFiniteMeasure μ] : Integrable (fun d => arrayTestExtend g d) μ :=
    (arrayTestExtend g).continuous.integrable_of_hasCompactSupport (arrayTestExtend g).hasCompactSupport
  rw [← integral_add_measure (hi _) (hi _),← integral_add_measure (hi _) (hi _),S.law_dilation_balance i]
lemma integral_dilation_balance (g : C_c(NonAffineArray,ℝ)) :
    (∫ d,g (nonaffineDilate d) ∂L.multi)=(∫ d,g d ∂L.multi)+(∫ d,g d ∂L.terminal) := by
  have ht := (L.multi_converges (g.comp nonaffineDilation)).add ((S.initial_vague_zero g).mono_left L.refines)
  rw [add_zero] at ht
  apply tendsto_nhds_unique ht
  have hh := (L.multi_converges g).add (L.terminal_converges g)
  exact hh.congr (fun i => (S.integral_law_dilation_balance i g).symm)
lemma dilation_balance : L.multi.map nonaffineDilate=L.multi+L.terminal := by
  let : IsFiniteMeasureOnCompacts (L.multi+L.terminal) := S.multi_terminal_local L
  let : IsLocallyFiniteMeasure (L.multi+L.terminal) := inferInstance
  let : (L.multi+L.terminal).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [integral_map (f := fun d => g d) continuous_nonaffineDilate.measurable.aemeasurable g.continuous.aestronglyMeasurable,
    integral_add_measure (f := fun d => g d) (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)
      (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)]
  exact S.integral_dilation_balance L g
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_VagueSupport
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayLimitSupport
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
lemma power_lower_tendsto : Tendsto (fun i => (2:ℝ)^(criticalLowerExponent S.offset i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.lowerExponent_tendsto
lemma power_terminal_tendsto : Tendsto (fun i => (2:ℝ)^(S.exponent i)) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp S.exponent_tendsto
lemma sample_constraint_aemulti (f : DistanceArray → ℝ) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℝ,∀ hk : 0 ≤ k,∀ z : Torus,∀ n : ℕ,∀ hn : 0<n,
      f (sampleArray k hk z n hn) ≤ C/(n:ℝ)) : ∀ᵐ d ∂L.multi, f d.val ≤ 0 := by
  apply ae_le_zero_of_positive_rational_null
  intro q hq
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply vague_open_null L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    (isOpen_lt continuous_const (hf.comp continuous_subtype_val))
  intro g hg hz
  have he : ∀ᶠ i in atTop,C/(2:ℝ)^(criticalLowerExponent S.offset i)<q :=
    (tendsto_const_nhds.div_atTop S.power_lower_tendsto).eventually (gt_mem_nhds hqR)
  apply tendsto_const_nhds.congr'
  filter_upwards [L.refines he] with i hi
  symm
  apply integral_nonaffine_scale_zero_of_bound _ _ _ _ _ (S.epsilon_pos i) g f q
  · intro d hd; exact hz d (not_lt.mpr hd)
  · intro j hj z
    exact (hb _ _ z _ (by positivity)).trans ((div_le_div_of_nonneg_left hC (by positivity)
      (by exact_mod_cast pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_right (criticalLowerExponent S.offset i) j))).trans hi.le)
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
lemma unit_aemulti : ∀ᵐ d ∂L.multi, UnitArray d.val := by
  have h (s t : DyadicTime) : ∀ᵐ d ∂L.multi,d.val.val s t-|(t:ℝ)-(s:ℝ)| ≤ 0 := by
    apply S.sample_constraint_aemulti L (fun d => d.val s t-|(t:ℝ)-(s:ℝ)|)
      ((continuous_arrayEval s t).sub continuous_const) 1 (by norm_num)
    intro k hk z n hn
    change rescaledDistance k z n s t-|(t:ℝ)-(s:ℝ)| ≤ 1/(n:ℝ)
    linarith [rescaledDistance_bound k hk z n hn s t]
  filter_upwards [ae_all_iff.mpr (fun s => ae_all_iff.mpr (h s))] with d hd
  intro s t
  linarith [hd s t]
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
-- module Solutions.OAIQ2_Std.StandardMap_ArrayHalf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Topology Classical
namespace StandardMapEntropy
lemma map_half_dilate (μ : Measure NonAffineArray) (hu : ∀ᵐ d ∂μ,UnitArray d.val) :
    (μ.map nonaffineDilate).map nonaffineHalf=μ := by
  rw [Measure.map_map measurable_nonaffineHalf continuous_nonaffineDilate.measurable]
  calc
    μ.map (nonaffineHalf ∘ nonaffineDilate)=μ.map id := Measure.map_congr (hu.mono (fun d hd => nonaffineHalf_dilate d hd))
    _=μ := Measure.map_id
lemma map_dilate_half (μ : Measure NonAffineArray) (hu : ∀ᵐ d ∂μ,UnitArray d.val) :
    (μ.map nonaffineHalf).map nonaffineDilate=μ := by
  rw [Measure.map_map continuous_nonaffineDilate.measurable measurable_nonaffineHalf]
  calc
    μ.map (nonaffineDilate ∘ nonaffineHalf)=μ.map id := Measure.map_congr (hu.mono (fun d hd => nonaffineDilate_half d hd))
    _=μ := Measure.map_id
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma half_balance : L.multi=L.multi.map nonaffineHalf+L.terminal.map nonaffineHalf := by
  have hh := congrArg (fun μ : Measure NonAffineArray => μ.map nonaffineHalf) (S.dilation_balance L)
  rw [map_half_dilate L.multi (S.unit_aemulti L),Measure.map_add] at hh <;> try exact measurable_nonaffineHalf
  exact hh
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_HalfDecomposition
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
lemma map_iterate_succ' {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f) (n : ℕ) :
    (μ.map f).map (f^[n])=μ.map (f^[n+1]) := by
  rw [Measure.map_map (hf.iterate n) hf]
  congr 1
lemma renewal_partial {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (f : X → X) (hf : Measurable f)
    (hb : μ=μ.map f+ν.map f) (n : ℕ) :
    μ=μ.map (f^[n])+∑j∈Finset.range n,ν.map (f^[j+1]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := congrArg (fun m : Measure X => m.map (f^[n])) hb
    rw [Measure.map_add _ _ (hf.iterate n),map_iterate_succ' μ f hf n,map_iterate_succ' ν f hf n] at hh
    rw [Finset.sum_range_succ]
    calc
      μ=μ.map (f^[n])+∑j∈Finset.range n,ν.map (f^[j+1]) := ih
      _=μ.map (f^[n+1])+(∑j∈Finset.range n,ν.map (f^[j+1])+ν.map (f^[n+1])) := by rw [hh]; ac_rfl
lemma renewal_sum_le {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (f : X → X) (hf : Measurable f)
    (hb : μ=μ.map f+ν.map f) : (Measure.sum (fun j : ℕ => ν.map (f^[j+1])))≤μ := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.sum_apply _ hs]
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  have hh : (∑j∈Finset.range n,ν.map (f^[j+1]))≤μ := by
    rw [renewal_partial μ ν f hf hb n]
    exact Measure.le_add_left le_rfl
  simpa only [Measure.finsetSum_apply] using hh s
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_VagueBounds
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
-- module Solutions.OAIQ2_Std.StandardMap_LimitMoments
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
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma test_integrable_multi (j : ArrayTestIndex) :
    Integrable (fun d : NonAffineArray => arrayTest j d.val) L.multi := by
  obtain ⟨C,hC⟩ := S.multiLaw_test_bound j
  exact (vague_integrable_bound L.filter (fun i => nonaffinePart (S.multiLaw i)) L.multi L.multi_converges
    _ ((continuous_arrayTest j).comp continuous_subtype_val) (fun d => arrayTest_nonneg j d.val)
    (max C 0) (le_max_right _ _) (fun i => integrable_nonaffinePart _ _ (continuous_arrayTest j))
    (by filter_upwards [L.refines hC] with i hi
        exact (integral_nonaffinePart_le _ _ (continuous_arrayTest j) (arrayTest_nonneg j)).trans
          (hi.trans (le_max_left _ _)))).1
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_RemainderLaws
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
lemma backwardSum_le : S.backwardSum L≤L.multi := renewal_sum_le _ _ _ measurable_nonaffineHalf (S.half_balance L)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TerminalShortfall
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
-- module Solutions.OAIQ2_Std.StandardMap_CappedTests
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
lemma continuous_capG (α : ℝ) : Continuous (capG α) := by
  unfold capG
  exact ((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)).sub
    ((((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _)).add
      ((entropyCap_contDiff α).continuous.comp (continuous_arrayShortfall _ _))).div_const 2)
lemma shortfall_ambient_mem (d : DistanceArray) (s t : DyadicTime) (hst : 1≤(t:ℝ)-(s:ℝ)) :
    arrayShortfall s t d∈Icc (-2:ℝ) 1 := by
  have hlen : 0<(t:ℝ)-(s:ℝ) := by linarith
  have hh := d.property.2.2.2.2 s t
  rw [abs_of_pos hlen] at hh
  have hl : d.val s t/((t:ℝ)-(s:ℝ))≤3 := (div_le_iff₀ hlen).mpr (by linarith)
  have hu := div_nonneg (d.property.1 s t) hlen.le
  unfold arrayShortfall
  constructor <;> linarith
lemma capG_bound (α : ℝ) : ∃C≥0,∀d:DistanceArray,|capG α d|≤C*arrayTest coreTestIndex d := by
  obtain ⟨C,hC,h1,h2⟩ := c2_compact_bounds (entropyCap_contDiff α) (-2) 1
  refine ⟨C,hC,?_⟩
  intro d
  have hm := arrayJ_nonneg 0 (dyadicInt 2) (by norm_num) d
  simp only [arrayJ,dyadicMid_zero_two] at hm
  have hh := c2_capped_difference (entropyCap_contDiff α) hC h1 h2
    (shortfall_ambient_mem d 0 (dyadicInt 1) (by norm_num))
    (shortfall_ambient_mem d (dyadicInt 1) (dyadicInt 2) (by norm_num))
    (shortfall_ambient_mem d 0 (dyadicInt 2) (by norm_num)) hm
  simpa only [capG,arrayTest,coreTestIndex,arrayJ,arrayV,dyadicMid_zero_two] using hh
namespace CriticalScaleSequence
variable (S : CriticalScaleSequence) (L : S.LimitLaws)
lemma capG_integrable_multi (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) L.multi := by
  obtain ⟨C,hC,hb⟩ := capG_bound α
  exact ((S.test_integrable_multi L coreTestIndex).const_mul C).mono'
    ((continuous_capG α).comp continuous_subtype_val).aestronglyMeasurable
    (Eventually.of_forall (fun d => by simpa only [Real.norm_eq_abs] using hb d.val))
lemma capG_integrable_sum (α : ℝ) : Integrable (fun d : NonAffineArray => capG α d.val) (S.backwardSum L) :=
  (S.capG_integrable_multi L α).mono_measure (S.backwardSum_le L)
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_FineArrays
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
-- module Solutions.OAIQ2_Std.StandardMap_TerminalCap
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
-- module Solutions.OAIQ2_Std.StandardMap_FineMoments
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
lemma backward_cap_difference {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) :
    (∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (n+1))=
      (∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n)-(∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L (n+1)) := by
  have hm : (S.backwardLaw L (n+1)).map nonaffineDilate=S.backwardLaw L n := by
    rw [S.backwardLaw_succ L,map_dilate_half _ (S.backwardLaw_unit L n)]
  have hf : Measurable (fun d:NonAffineArray => capF α d.val) := (continuous_capF α).measurable.comp measurable_subtype_coe
  have h1 := S.backward_cap_integrable L hα hα1 (n+1)
  have hd : Integrable (fun d:NonAffineArray => capF α (nonaffineDilate d).val) (S.backwardLaw L (n+1)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable continuous_nonaffineDilate.measurable.aemeasurable).mp
    rw [hm]; exact S.backward_cap_integrable L hα hα1 n
  have ht : Integrable (fun d:NonAffineArray => capF α (nonaffineTranslation (dyadicInt 1) d).val) (S.backwardLaw L (n+1)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable (nonaffineTranslation _).continuous.measurable.aemeasurable).mp
    rw [S.backwardLaw_translate L]; exact h1
  simp_rw [capG_coboundary]
  have he := integral_sub hd ((h1.add ht).div_const 2)
  simp only [Pi.add_apply] at he
  change (∫d:NonAffineArray,capF α (nonaffineDilate d).val-(capF α d.val+capF α (nonaffineTranslation (dyadicInt 1) d).val)/2 ∂S.backwardLaw L (n+1))=_
  rw [he,integral_div]
  rw [integral_add h1 ht]
  rw [←integral_map continuous_nonaffineDilate.measurable.aemeasurable hf.aestronglyMeasurable,hm]
  rw [integral_invariant_translation _ _ (S.backwardLaw_translate L _ _) _ hf]
  ring
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ2_Std.StandardMap_TerminalStrict
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
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma capG_backward_partial {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) :
    (∑j∈Finset.range n,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))=
      (∫d:NonAffineArray,capF α d.val ∂L.terminal)-(∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n) := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,S.backwardLaw_zero L,sub_self]
  | succ n ih => rw [Finset.sum_range_succ,ih,S.backward_cap_difference L hα hα1 n]; ring
lemma terminal_cap_strict_oai {α H:ℝ} (hα:0≤α) (hα1:α≤1) (hH:0<H)
    (hb:(∫d:NonAffineArray,capF α d.val ∂L.terminal)≤H) :
    (∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))<H := by
  by_cases hn:L.terminal=0
  · simpa only [backwardLaw,hn,Measure.map_zero,integral_zero_measure,tsum_zero] using hH
  obtain ⟨δ,hδ,hd⟩ := S.terminal_event_lower L hα hα1 hn
  have hs := (hasSum_integral_measure (S.capG_integrable_sum L α)).summable
  have ht := hs.hasSum.tendsto_sum_nat
  have hle : (∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))≤
      (∫d:NonAffineArray,capF α d.val ∂L.terminal)-δ := by
    apply le_of_tendsto ht
    filter_upwards [hd] with n hn
    rw [S.capG_backward_partial L hα hα1 n]
    linarith
  linarith
end CriticalScaleSequence
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_oai := @OAI.StandardMapEntropy.CriticalScaleSequence.terminal_cap_strict_oai
