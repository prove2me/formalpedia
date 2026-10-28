-- Prove2me | solution 1 for OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:45:32.073735+00:00
-- url     : https://prove2.me/submissions/77aff91b-cbad-4773-895c-81cf6140972c

import Mathlib
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceSamplingSquaredError_ae

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Density
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- Finite product estimate used in uniform-product-density; the bound has
no dependence on the choice of endpoint orientation. -/
theorem product_energy_le_exp {ι : Type*} [Fintype ι]
    (A e : ι → ℝ) (hA0 : ∀ i, 0 ≤ A i) (hA : ∀ i, A i ≤ 1 + e i) :
    (∏ i, A i) ≤ Real.exp (∑ i, e i) := by
  calc
    (∏ i, A i) ≤ ∏ i, Real.exp (e i) := by
      apply Finset.prod_le_prod (fun i _ => hA0 i)
      intro i _
      exact (hA i).trans (by linarith [Real.add_one_le_exp (e i)])
    _ = _ := (Real.exp_sum _ _).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Prefix
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

/-- Finite-coordinate factorization under the actual infinite product measure. -/
theorem integral_infinitePi_finset_prod {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) (f : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i)) :
    (∫ x, ∏ i ∈ I, f i (x i) ∂Measure.infinitePi μ) = ∏ i ∈ I, ∫ t, f i t ∂μ i := by
  classical
  have he (x : ∀ i, X i) : (∏ i ∈ I, f i (x i)) = ∏ i : I, f i (x i) :=
    (Finset.prod_coe_sort I (fun i => f i (x i))).symm
  simp_rw [he]
  change (∫ x, (∏ i : I, f i (I.restrict x i)) ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi μ
    (f := fun x : ∀ i : I, X i => ∏ i : I, f i (x i))
    ((Finset.measurable_prod _ fun (i : I) _ => (hf i).comp (measurable_pi_apply i)).aestronglyMeasurable)]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort I (fun i => ∫ t, f i t ∂μ i)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Stages
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter Finset
open scoped Topology
noncomputable section

theorem sourceStage_previous_size (s : ℕ) :
    (sourceStageState s).d = ∑ t ∈ Finset.range s, (sourceStage t).m := by
  induction s with
  | zero => rfl
  | succ s ih => simpa [Finset.sum_range_succ, sourceStageState, SourceStageChoice.next, sourceStage] using congrArg (fun x => x+(sourceStage s).m) ih

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_PeriodizedUniform
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

theorem sourceFract_measurable : Measurable (Int.fract : ℝ → ℝ) := by
  have hh := sourceCircleRepresentative_measurable.comp sourceCircle_mk_preserving.measurable
  simpa only [Function.comp_def, sourceCircleRepresentative_coe] using hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Weights
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

theorem samplingWeight_measurable (triangular : Bool) (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => samplingWeight triangular h α p.1 p.2) := by
  cases triangular <;> unfold samplingWeight samplingDistance <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · apply Measurable.ite _ (by fun_prop) measurable_const
    exact (measurableSet_le measurable_const (measurable_fst.min (measurable_const.sub measurable_fst))).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (measurable_const.mul (measurable_fst.min (measurable_const.sub measurable_fst)))))
  · exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst))) measurable_const measurable_const

theorem samplingWeight_support (triangular : Bool) (h α s t : ℝ)
    (_hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (_hs : s ∈ Set.Ico (0 : ℝ) 1) (hw : samplingWeight triangular h α s t ≠ 0) :
    0 < t ∧ t < 1-s := by
  cases triangular
  · unfold samplingWeight at hw
    simp only [Bool.false_eq_true,ite_false] at hw
    split_ifs at hw with hc
    · have hd : 0 < samplingDistance s := hα.trans_le hc.1
      have hd1 : samplingDistance s ≤ 1-s := min_le_right _ _
      exact ⟨hc.2.1, hc.2.2.trans_le ((by simpa using
        (mul_lt_mul_of_pos_right hh1 hd).le : h * samplingDistance s ≤ samplingDistance s).trans hd1)⟩
    · exact False.elim (hw rfl)
  · simpa only [samplingWeight,ite_true,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hw

/-- The positive weight already orders each prefix coordinate strictly,
with no wrap of the orbit endpoint. -/
theorem samplingWeight_orders (triangular : Bool) (h α s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hw : samplingWeight triangular h α s t ≠ 0) :
    Int.fract (s+t) = s+t ∧ s < Int.fract (s+t) := by
  have ht := samplingWeight_support triangular h α s t hh hh1 hα hs hw
  have he := Int.fract_eq_self.mpr (show s+t ∈ Set.Ico (0 : ℝ) 1 from ⟨by linarith [hs.1],by linarith⟩)
  exact ⟨he,by rw [he]; linarith⟩

/-- Exact first marginal of either untested one-coordinate weight. -/
theorem samplingWeight_first_integral (triangular : Bool) (h α s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    (∫ t, samplingWeight triangular h α s t ∂unitIntervalMeasure) =
      if triangular then 1-s else if α ≤ samplingDistance s then 1 else 0 := by
  have hvol (L : ℝ) (hL : 0 ≤ L) (hL1 : L ≤ 1) :
      unitIntervalMeasure (Set.Ioo (0 : ℝ) L) = ENNReal.ofReal L := by
    unfold unitIntervalMeasure
    rw [Measure.restrict_apply measurableSet_Ioo,Set.inter_eq_left.mpr (by
      intro t ht; exact ⟨ht.1.le,ht.2.trans_le hL1⟩),Real.volume_Ioo,sub_zero]
  cases triangular
  · simp only [Bool.false_eq_true,ite_false]
    by_cases hc : α ≤ samplingDistance s
    · have hd : 0 < samplingDistance s := hα.trans_le hc
      have hL : 0 < h*samplingDistance s := mul_pos hh hd
      have hL1 : h*samplingDistance s ≤ 1 := by
        have := min_le_right s (1-s)
        change samplingDistance s ≤ 1-s at this
        nlinarith [hs.1]
      have he : samplingWeight false h α s =
          (Set.Ioo 0 (h*samplingDistance s)).indicator (fun _ => 1/(h*samplingDistance s)) := by
        funext t
        simp [samplingWeight,hc,Set.indicator,Set.mem_Ioo]
      rw [he,integral_indicator measurableSet_Ioo]
      simp [hc,hvol (h*samplingDistance s) hL.le hL1,ENNReal.toReal_ofReal hL.le,measureReal_def]
      field_simp
    · have he : samplingWeight false h α s = fun _ => 0 := by funext t; simp [samplingWeight,hc]
      simp [he,hc]
  · simp only [ite_true]
    have he : samplingWeight true h α s = (Set.Ioo 0 (1-s)).indicator (fun _ => (1 : ℝ)) := by
      funext t
      simp [samplingWeight,Set.indicator,Set.mem_Ioo]
    rw [he,integral_indicator measurableSet_Ioo]
    simp [hvol (1-s) (by linarith [hs.2]) (by linarith [hs.1]),ENNReal.toReal_ofReal,show 0 ≤ 1-s by linarith [hs.2],measureReal_def]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Weights
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

theorem sourceSamplingWeight_measurable (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : Measurable (sourceSamplingWeight I s θ n) := by
  apply Finset.measurable_prod
  intro i hi
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x i, Int.fract ((n : ℝ)*θ i))) :=
    (measurable_pi_apply i).prodMk measurable_const
  exact (samplingWeight_measurable (decide (i ∈ I)) (sourceSamplingWidth s) (sourceSamplingCutoff s)).comp hp

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Transport
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem unitInterval_split (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    unitIntervalMeasure = volume.restrict (Set.Ioc (0 : ℝ) c) + volume.restrict (Set.Ioc c 1) := by
  unfold unitIntervalMeasure
  rw [restrict_Ico_eq_restrict_Ioc,← Set.Ioc_union_Ioc_eq_Ioc hc hc1,
    Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]

theorem map_interval_affine (a b c d : ℝ) (hc : 0 < c) :
    (volume.restrict (Set.Ioc a b)).map (fun x => c*x+d) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Set.Ioc (c*a+d) (c*b+d)) := by
  have hp : (fun x : ℝ => c*x+d) ⁻¹' Set.Ioc (c*a+d) (c*b+d) = Set.Ioc a b := by
    ext x
    simp only [Set.mem_preimage,Set.mem_Ioc,add_lt_add_iff_right,add_le_add_iff_right,
      mul_lt_mul_iff_right₀ hc,mul_le_mul_iff_right₀ hc]
  have hmap : volume.map (fun x : ℝ => c*x+d) = ENNReal.ofReal c⁻¹ • volume := by
    have he : (fun x : ℝ => c*x+d) = (fun x : ℝ => x+d) ∘ (fun x : ℝ => c*x) := rfl
    rw [he,← Measure.map_map (by fun_prop) (by fun_prop),Real.map_volume_mul_left hc.ne',
      Measure.map_smul,
      (measurePreserving_add_right (volume : Measure ℝ) d).map_eq,abs_of_pos (inv_pos.mpr hc)]
  rw [← hp,← Measure.restrict_map (f := fun x : ℝ => c*x+d) (by fun_prop) measurableSet_Ioc,
    hmap,Measure.restrict_smul]

theorem samplingTransportDensity_measurable :
    Measurable (fun p : ℝ × ℝ => samplingTransportDensity p.1 p.2) := by
  unfold samplingTransportDensity
  exact Measurable.ite (measurableSet_le measurable_snd ((measurable_const.add measurable_fst).div_const 2))
    (by fun_prop) (by fun_prop)

/-- This is the actual push-forward density, not an assumed ideal moment. -/
theorem samplingTransport_density (v : ℝ) (hv : 0 ≤ v) (hv1 : v < 1) :
    unitIntervalMeasure.map (samplingTransport v) =
      unitIntervalMeasure.withDensity (fun s => ENNReal.ofReal (samplingTransportDensity v s)) := by
  let c := (1+v)/2
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hleft : (volume.restrict (Set.Ioc (0 : ℝ) (1/2))).map (samplingTransport v) =
      ENNReal.ofReal (1/(1+v)) • volume.restrict (Set.Ioc (0 : ℝ) c) := by
    have he : samplingTransport v =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (1/2))] (fun z => (1+v)*z+0) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      unfold samplingTransport samplingDistance
      rw [min_eq_left (by linarith [hz.2])]
      ring
    rw [Measure.map_congr he,map_interval_affine _ _ _ _ (by linarith)]
    simp only [mul_zero,add_zero,one_div]
    congr 3
  have hright : (volume.restrict (Set.Ioc (1/2 : ℝ) 1)).map (samplingTransport v) =
      ENNReal.ofReal (1/(1-v)) • volume.restrict (Set.Ioc c (1 : ℝ)) := by
    have he : samplingTransport v =ᵐ[volume.restrict (Set.Ioc (1/2 : ℝ) 1)] (fun z => (1-v)*z+v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      unfold samplingTransport samplingDistance
      rw [min_eq_right (by linarith [hz.1])]
      ring
    rw [Measure.map_congr he,map_interval_affine _ _ _ _ (by linarith)]
    have hc' : (1-v)*(1/2)+v = c := by dsimp [c]; ring
    rw [hc',show (1-v)*1+v = 1 by ring]
    simp [one_div]
  have hdleft : (volume.restrict (Set.Ioc (0 : ℝ) c)).withDensity
      (fun s => ENNReal.ofReal (samplingTransportDensity v s)) =
      ENNReal.ofReal (1/(1+v)) • volume.restrict (Set.Ioc (0 : ℝ) c) := by
    rw [← withDensity_const]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    simp [samplingTransportDensity,show z ≤ (1+v)/2 from hz.2]
  have hdright : (volume.restrict (Set.Ioc c (1 : ℝ))).withDensity
      (fun s => ENNReal.ofReal (samplingTransportDensity v s)) =
      ENNReal.ofReal (1/(1-v)) • volume.restrict (Set.Ioc c (1 : ℝ)) := by
    rw [← withDensity_const]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    simp [samplingTransportDensity,show ¬z ≤ (1+v)/2 from not_le.mpr hz.1]
  conv_lhs => rw [unitInterval_split (1/2) (by norm_num) (by norm_num)]
  have htm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
  rw [Measure.map_add _ _ htm,hleft,hright]
  conv_rhs => rw [unitInterval_split c hc hc1]
  rw [withDensity_add_measure,hdleft,hdright]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SecondMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

theorem samplingTransportDensity_bounds (h v s : ℝ) (hh : 0 ≤ h) (hh1 : h < 1)
    (hv : 0 ≤ v) (hvh : v ≤ h) :
    0 ≤ samplingTransportDensity v s ∧ samplingTransportDensity v s ≤ 1/(1-h) ∧
      |samplingTransportDensity v s-1| ≤ h/(1-h) := by
  have hmh : 0 < 1-h := by linarith
  have hph : 0 < 1+h := by linarith
  have hmv : 0 < 1-v := by linarith
  have hpv : 0 < 1+v := by linarith
  have hlo : 1/(1+h) ≤ samplingTransportDensity v s := by
    unfold samplingTransportDensity
    split_ifs
    · exact one_div_le_one_div_of_le hpv (by linarith)
    · exact one_div_le_one_div_of_le hmv (by linarith)
  have hhi : samplingTransportDensity v s ≤ 1/(1-h) := by
    unfold samplingTransportDensity
    split_ifs <;> exact one_div_le_one_div_of_le hmh (by linarith)
  have hl : 1-h/(1-h) ≤ 1/(1+h) := by
    field_simp
    nlinarith
  have hr : 1/(1-h)-1 = h/(1-h) := by field_simp; ring
  exact ⟨(by positivity : 0 ≤ 1/(1+h)).trans hlo,hhi,
    abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem samplingTransportDensity_integral (v : ℝ) (hv : 0 ≤ v) (hv1 : v < 1) :
    (∫ s, samplingTransportDensity v s ∂unitIntervalMeasure) = 1 := by
  have hm : Measurable (samplingTransportDensity v) :=
    samplingTransportDensity_measurable.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (samplingTransportDensity v) unitIntervalMeasure :=
    (integrable_const (1/(1-v))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall (fun s => by
        rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1]
        exact (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).2.1))
  have hmap := congrArg (fun μ : Measure ℝ => μ Set.univ) (samplingTransport_density v hv hv1)
  have htm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
  rw [Measure.map_apply htm MeasurableSet.univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hmap
  simp only [Set.preimage_univ,measure_univ] at hmap
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun s => (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1))
  rw [← hmap] at he
  have hn : 0 ≤ ∫ s, samplingTransportDensity v s ∂unitIntervalMeasure := integral_nonneg (fun s => (samplingTransportDensity_bounds v v s hv hv1 hv le_rfl).1)
  have hh := congrArg ENNReal.toReal he
  simpa [ENNReal.toReal_ofReal hn] using hh

theorem samplingVelocity_probability (h : ℝ) (hh : 0 < h) : IsProbabilityMeasure (samplingVelocityMeasure h) := by
  apply cond_isProbabilityMeasure_of_finite
  · simp [Real.volume_Ioc,hh]
  · simp [Real.volume_Ioc]

theorem samplingIdealSecond_bounds (h s : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    0 ≤ samplingIdealSecond h s ∧ samplingIdealSecond h s ≤ 1/(1-h) ∧
      |samplingIdealSecond h s-1| ≤ h/(1-h) := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hm : Measurable (fun v => samplingTransportDensity v s) :=
    samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)
  have hqi : Integrable (fun v => samplingTransportDensity v s) (samplingVelocityMeasure h) :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (by
      filter_upwards [hv] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1]
      exact (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1)
  have hnon : 0 ≤ samplingIdealSecond h s := integral_nonneg_of_ae (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1))
  have hu := integral_mono_ae hqi (integrable_const (1/(1-h))) (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1))
  refine ⟨hnon,by simpa [samplingIdealSecond] using hu,?_⟩
  have he : samplingIdealSecond h s-1 = ∫ v, samplingTransportDensity v s-1 ∂samplingVelocityMeasure h := by
    rw [integral_sub hqi (integrable_const 1)]
    simp [samplingIdealSecond]
  rw [he]
  calc
    _ ≤ ∫ v, |samplingTransportDensity v s-1| ∂samplingVelocityMeasure h := by
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun v => samplingTransportDensity v s-1)
    _ ≤ ∫ _v, h/(1-h) ∂samplingVelocityMeasure h := by
      apply integral_mono_ae
      · simpa [Real.norm_eq_abs] using (hqi.sub (integrable_const 1)).norm
      · exact integrable_const _
      · exact hv.mono (fun v hv => (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.2)
    _ = _ := by simp

theorem samplingIdealSecond_measurable (h : ℝ) (hh : 0 < h) : Measurable (samplingIdealSecond h) := by
  have := samplingVelocity_probability h hh
  exact samplingTransportDensity_measurable.stronglyMeasurable.integral_prod_left.measurable

/-- Fubini gives the exact mass identity for the averaged transport density. -/
theorem samplingIdealSecond_integral (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    (∫ s, samplingIdealSecond h s ∂unitIntervalMeasure) = 1 := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hvp : ∀ᵐ p : ℝ × ℝ ∂(samplingVelocityMeasure h).prod unitIntervalMeasure,
      p.1 ∈ Set.Ioc (0 : ℝ) h := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    exact hv.mono (fun v hv => Eventually.of_forall (fun _ => hv))
  have hqi : Integrable (fun p : ℝ × ℝ => samplingTransportDensity p.1 p.2)
      ((samplingVelocityMeasure h).prod unitIntervalMeasure) :=
    (integrable_const (1/(1-h))).mono' samplingTransportDensity_measurable.aestronglyMeasurable (by
      filter_upwards [hvp] with p hp
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h p.1 p.2 hh.le hh1 hp.1.le hp.2).1]
      exact (samplingTransportDensity_bounds h p.1 p.2 hh.le hh1 hp.1.le hp.2).2.1)
  have hswap := integral_integral_swap (f := fun v s => samplingTransportDensity v s) hqi
  calc
    _ = ∫ v, (∫ s, samplingTransportDensity v s ∂unitIntervalMeasure) ∂samplingVelocityMeasure h := hswap.symm
    _ = ∫ _v, (1 : ℝ) ∂samplingVelocityMeasure h := integral_congr_ae
      (hv.mono (fun v hv => samplingTransportDensity_integral v hv.1.le (hv.2.trans_lt hh1)))
    _ = 1 := by simp

/-- The source's quadratic cancellation for the actual averaged uncut
transport density. The exact mass-one identity eliminates the linear term. -/
theorem samplingIdealSecond_square (h : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    (∫ s, samplingIdealSecond h s^2 ∂unitIntervalMeasure) =
      1+(∫ s, (samplingIdealSecond h s-1)^2 ∂unitIntervalMeasure) ∧
    (∫ s, samplingIdealSecond h s^2 ∂unitIntervalMeasure) ≤ 1+h^2/(1-h)^2 := by
  let q := samplingIdealSecond h
  let C := h/(1-h)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm := samplingIdealSecond_measurable h hh
  have hqi : Integrable q unitIntervalMeasure :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingIdealSecond_bounds h s hh hh1).1]
      exact (samplingIdealSecond_bounds h s hh hh1).2.1))
  have hdev (s : ℝ) : (q s-1)^2 ≤ C^2 := by
    have hb := abs_le.mp (samplingIdealSecond_bounds h s hh hh1).2.2
    dsimp [C,q]
    nlinarith
  have hdi : Integrable (fun s => (q s-1)^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (by fun_prop) (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hdev s))
  have heq : (fun s => q s^2) = (fun s => ((q s-1)^2+2*q s)-1) := by funext s; ring
  have hmass : (∫ s, q s ∂unitIntervalMeasure) = 1 := samplingIdealSecond_integral h hh hh1
  have he : (∫ s, q s^2 ∂unitIntervalMeasure) = 1+∫ s, (q s-1)^2 ∂unitIntervalMeasure := by
    rw [heq]
    have hsum : Integrable (fun s => (q s-1)^2+2*q s) unitIntervalMeasure := hdi.add (hqi.const_mul 2)
    rw [integral_sub hsum (integrable_const 1),integral_add hdi (hqi.const_mul 2),integral_const_mul,hmass]
    simp
    ring
  refine ⟨he,?_⟩
  have hu := integral_mono_ae hdi (integrable_const (C^2)) (Eventually.of_forall hdev)
  simp at hu
  have hCeq : C^2 = h^2/(1-h)^2 := by dsimp [C]; rw [div_pow]
  rw [he]
  linarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_WeightTransport
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- At each retained starting coordinate, the source weight is exactly the
law of the displacement v times the distance to the endpoint. -/
theorem samplingWeight_displacement (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (hcut : α ≤ samplingDistance z) :
    unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (samplingWeight false h α z t)) =
      (samplingVelocityMeasure h).map (fun v => samplingDistance z * v) := by
  let d := samplingDistance z
  have hd : 0 < d := hα.trans_le hcut
  have hL : 0 < h*d := mul_pos hh hd
  have hd1 : d ≤ 1-z := min_le_right _ _
  have hL1 : h*d ≤ 1 := by nlinarith [hz.1]
  have he : (fun t => ENNReal.ofReal (samplingWeight false h α z t)) =
      (Set.Ioo 0 (h*d)).indicator (fun _ => ENNReal.ofReal (1/(h*d))) := by
    funext t
    simp only [samplingWeight,Bool.false_eq_true,ite_false,hcut,true_and,Set.indicator,Set.mem_Ioo,d]
    split_ifs <;> simp
  rw [he,withDensity_indicator measurableSet_Ioo,withDensity_const]
  unfold unitIntervalMeasure
  rw [Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_eq_left.mpr (show Set.Ioo 0 (h*d) ⊆ Set.Ico (0 : ℝ) 1 from
      fun t ht => ⟨ht.1.le,ht.2.trans_le hL1⟩),restrict_Ioo_eq_restrict_Ioc]
  unfold samplingVelocityMeasure ProbabilityTheory.cond
  rw [Measure.map_smul]
  have ha := map_interval_affine 0 h d 0 hd
  simp only [mul_zero,add_zero] at ha
  rw [ha,smul_smul,Real.volume_Ioc,sub_zero]
  congr 1
  rw [← ENNReal.ofReal_inv_of_pos hh,← ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)]
  congr 1
  dsimp [d]
  field_simp
  simp [mul_comm]

/-- Exact substitution t=v*Delta(z), at each retained starting point. -/
theorem samplingWeight_transport_integral (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (hcut : α ≤ samplingDistance z)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t) ∂unitIntervalMeasure) =
      ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h := by
  have hw : Measurable (fun t => ENNReal.ofReal (samplingWeight false h α z t)) :=
    ((samplingWeight_measurable false h α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hFz : Measurable (fun t => F (z+t)) := hF.comp (by fun_prop)
  have hi := lintegral_withDensity_eq_lintegral_mul unitIntervalMeasure hw hFz
  simp only [Pi.mul_apply] at hi
  rw [← hi,
    samplingWeight_displacement h α z hh hh1 hα hz hcut,
    lintegral_map hFz (by fun_prop)]
  apply lintegral_congr
  intro v
  simp [samplingTransport,mul_comm]

/-- Discarding the cutoff only increases the weighted endpoint law. -/
theorem samplingWeight_transport_le (h α z : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t) ∂unitIntervalMeasure) ≤
      ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h := by
  by_cases hc : α ≤ samplingDistance z
  · exact (samplingWeight_transport_integral h α z hh hh1 hα hz hc F hF).le
  · simp [samplingWeight,hc]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_AveragedTransport
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- ENNReal form of the constructed averaged density. -/
theorem samplingIdealSecond_lintegral (h s : ℝ) (hh : 0 < h) (hh1 : h < 1) :
    ENNReal.ofReal (samplingIdealSecond h s) =
      ∫⁻ v, ENNReal.ofReal (samplingTransportDensity v s) ∂samplingVelocityMeasure h := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have hm : Measurable (fun v => samplingTransportDensity v s) :=
    samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)
  have hqi : Integrable (fun v => samplingTransportDensity v s) (samplingVelocityMeasure h) :=
    (integrable_const (1/(1-h))).mono' hm.aestronglyMeasurable (by
      filter_upwards [hv] with v hv
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1]
      exact (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).2.1)
  exact ofReal_integral_eq_lintegral_ofReal hqi (hv.mono (fun v hv =>
    (samplingTransportDensity_bounds h v s hh.le hh1 hv.1.le hv.2).1))

/-- The average of the actual transport laws has density q_h. -/
theorem samplingTransport_average (h : ℝ) (hh : 0 < h) (hh1 : h < 1)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ v, F (samplingTransport v z) ∂samplingVelocityMeasure h ∂unitIntervalMeasure) =
      ∫⁻ s, ENNReal.ofReal (samplingIdealSecond h s)*F s ∂unitIntervalMeasure := by
  have := samplingVelocity_probability h hh
  have hv : ∀ᵐ v ∂samplingVelocityMeasure h, v ∈ Set.Ioc (0 : ℝ) h := ae_cond_mem measurableSet_Ioc
  have htm : Measurable (fun p : ℝ × ℝ => samplingTransport p.2 p.1) := by
    unfold samplingTransport samplingDistance
    fun_prop
  have hswap := lintegral_lintegral_swap (μ := unitIntervalMeasure) (ν := samplingVelocityMeasure h) (f := fun z v => F (samplingTransport v z)) (hF.comp htm).aemeasurable
  rw [hswap]
  calc
    _ = ∫⁻ v, (∫⁻ s, ENNReal.ofReal (samplingTransportDensity v s)*F s ∂unitIntervalMeasure)
        ∂samplingVelocityMeasure h := by
      apply lintegral_congr_ae
      filter_upwards [hv] with v hv
      have hm : Measurable (samplingTransport v) := by unfold samplingTransport samplingDistance; fun_prop
      rw [← lintegral_map hF hm,samplingTransport_density v hv.1.le (hv.2.trans_lt hh1)]
      have hmd : Measurable (fun s => ENNReal.ofReal (samplingTransportDensity v s)) :=
        (samplingTransportDensity_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
      exact lintegral_withDensity_eq_lintegral_mul unitIntervalMeasure hmd hF
    _ = ∫⁻ s, (∫⁻ v, ENNReal.ofReal (samplingTransportDensity v s)*F s ∂samplingVelocityMeasure h)
        ∂unitIntervalMeasure := lintegral_lintegral_swap
          (samplingTransportDensity_measurable.ennreal_ofReal.mul (hF.comp measurable_snd)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro s
      have hmd : Measurable (fun v => ENNReal.ofReal (samplingTransportDensity v s)) :=
        (samplingTransportDensity_measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
      rw [lintegral_mul_const _ hmd,← samplingIdealSecond_lintegral h s hh hh1]

/-- An actual cutoff-weight endpoint estimate, with no assumed second-marginal
identification. It holds against every measurable nonnegative test. -/
theorem samplingWeight_endpoint_domination (h α : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t)
      ∂unitIntervalMeasure ∂unitIntervalMeasure) ≤
        ∫⁻ s, ENNReal.ofReal (samplingIdealSecond h s)*F s ∂unitIntervalMeasure := by
  rw [← samplingTransport_average h hh hh1 F hF]
  apply lintegral_mono_ae
  filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
    ae_restrict_mem measurableSet_Ico] with z hz
  exact samplingWeight_transport_le h α z hh hh1 hα hz F hF

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SecondDensity
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

theorem samplingSecondWeight_measurable (h α : ℝ) :
    Measurable (fun p : ℝ × ℝ => samplingSecondWeight h α p.1 p.2) :=
  (samplingWeight_measurable false h α).comp
    ((sourceFract_measurable.comp (measurable_fst.sub measurable_snd)).prodMk measurable_snd)

theorem samplingSecondWeight_integrable (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    Integrable (samplingSecondWeight h α s) unitIntervalMeasure := by
  have hm : Measurable (samplingSecondWeight h α s) :=
    (samplingSecondWeight_measurable h α).comp (measurable_const.prodMk measurable_id)
  exact (integrable_const (max 1 (1/(h*α)))).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs]
      change |samplingWeight false h α (Int.fract (s-t)) t| ≤ _
      rw [abs_of_nonneg (samplingWeight_bounds false h α (Int.fract (s-t)) t hh hα).1]
      exact (samplingWeight_bounds false h α _ t hh hα).2))

theorem samplingSecondDensity_lintegral (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    ENNReal.ofReal (samplingSecondDensity h α s) =
      ∫⁻ t, ENNReal.ofReal (samplingSecondWeight h α s t) ∂unitIntervalMeasure :=
  ofReal_integral_eq_lintegral_ofReal (samplingSecondWeight_integrable h α s hh hα)
    (Eventually.of_forall (fun t => (samplingWeight_bounds false h α _ t hh hα).1))

theorem samplingSecondDensity_measurable (h α : ℝ) : Measurable (samplingSecondDensity h α) :=
  (samplingSecondWeight_measurable h α).stronglyMeasurable.integral_prod_right.measurable

theorem sampling_fract_inverse (z t : ℝ) (hz : z ∈ Set.Ico (0 : ℝ) 1) :
    Int.fract (Int.fract (z+t)-t) = z := by
  have he : Int.fract (z+t)-t = z-(Int.floor (z+t) : ℝ) := by rw [Int.fract]; ring
  rw [he,Int.fract_sub_intCast,Int.fract_eq_self.mpr hz]

/-- Haar substitution identifies the actual second-oriented integral with
the weighted endpoint law; no marginal-density hypothesis is assumed. -/
theorem samplingSecondDensity_test (h α : ℝ) (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ s, ENNReal.ofReal (samplingSecondDensity h α s)*F s ∂unitIntervalMeasure) =
      ∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (z+t)
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
  have hwm := samplingSecondWeight_measurable h α
  calc
    _ = ∫⁻ s, ∫⁻ t, ENNReal.ofReal (samplingSecondWeight h α s t)*F s
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_congr
      intro s
      have hmd : Measurable (fun t => ENNReal.ofReal (samplingSecondWeight h α s t)) :=
        (hwm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
      rw [samplingSecondDensity_lintegral h α s hh hα,lintegral_mul_const _ hmd]
    _ = ∫⁻ t, ∫⁻ s, ENNReal.ofReal (samplingSecondWeight h α s t)*F s
        ∂unitIntervalMeasure ∂unitIntervalMeasure :=
      lintegral_lintegral_swap (hwm.ennreal_ofReal.mul (hF.comp measurable_fst)).aemeasurable
    _ = ∫⁻ t, ∫⁻ z, ENNReal.ofReal (samplingWeight false h α z t)*F (Int.fract (z+t))
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_congr
      intro t
      have hm : Measurable (fun s => ENNReal.ofReal (samplingSecondWeight h α s t)*F s) :=
        ((hwm.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul hF
      rw [← (unitInterval_rotate_preserving t).lintegral_comp hm]
      apply lintegral_congr_ae
      filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
        ae_restrict_mem measurableSet_Ico] with z hz
      simp only [samplingSecondWeight,sampling_fract_inverse z t hz]
    _ = ∫⁻ z, ∫⁻ t, ENNReal.ofReal (samplingWeight false h α z t)*F (Int.fract (z+t))
        ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply lintegral_lintegral_swap
      exact (((samplingWeight_measurable false h α).comp measurable_swap).ennreal_ofReal.mul
        (hF.comp (sourceFract_measurable.comp (measurable_snd.add measurable_fst)))).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [show ∀ᵐ z ∂unitIntervalMeasure, z ∈ Set.Ico (0 : ℝ) 1 from
        ae_restrict_mem measurableSet_Ico] with z hz
      apply lintegral_congr
      intro t
      by_cases hw : samplingWeight false h α z t = 0
      · simp [hw]
      · rw [(samplingWeight_orders false h α z t hh hh1 hα hz hw).1]

/-- The actual cutoff second marginal is dominated almost everywhere by
q_h, completing the missing connection to the quadratic ideal moment. -/
theorem samplingSecondDensity_le_ideal (h α : ℝ) (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) :
    ∀ᵐ s ∂unitIntervalMeasure, samplingSecondDensity h α s ≤ samplingIdealSecond h s := by
  have he : ∀ᵐ s ∂unitIntervalMeasure,
      ENNReal.ofReal (samplingSecondDensity h α s) ≤ ENNReal.ofReal (samplingIdealSecond h s) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (samplingSecondDensity_measurable h α).ennreal_ofReal
    intro S hS _
    have hb := samplingWeight_endpoint_domination h α hh hh1 hα (S.indicator (fun _ => 1))
      (measurable_const.indicator hS)
    rw [← samplingSecondDensity_test h α hh hh1 hα _ (measurable_const.indicator hS)] at hb
    have hind (g : ℝ → ℝ≥0∞) : (fun s => g s*S.indicator (fun _ => 1) s) = S.indicator g := by
      funext s
      by_cases hs : s ∈ S <;> simp [Set.indicator,hs]
    rw [hind,hind,lintegral_indicator hS,lintegral_indicator hS] at hb
    exact hb
  filter_upwards [he] with s hs
  exact (ENNReal.ofReal_le_ofReal_iff (samplingIdealSecond_bounds h s hh hh1).1).mp hs

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_TestedSecondMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

theorem samplingTestedSecondWeight_measurable (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingTestedSecondWeight h α E G p.1 p.2) := by
  unfold samplingTestedSecondWeight
  exact Measurable.ite ((hE.preimage (sourceFract_measurable.comp
    (measurable_fst.sub measurable_snd))).inter (hG.preimage measurable_fst))
    (samplingSecondWeight_measurable h α) measurable_const

theorem samplingTestedSecondWeight_bounds (h α : ℝ) (E G : Set ℝ) (s t : ℝ)
    (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingTestedSecondWeight h α E G s t ∧
      samplingTestedSecondWeight h α E G s t ≤ samplingSecondWeight h α s t := by
  have hn : 0 ≤ samplingSecondWeight h α s t := (samplingWeight_bounds false h α _ t hh hα).1
  unfold samplingTestedSecondWeight
  split_ifs <;> simp [hn]

theorem samplingTestedSecondDensity_measurable (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingTestedSecondDensity h α E G) :=
  (samplingTestedSecondWeight_measurable h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

theorem samplingTestedSecondDensity_bounds (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) (s : ℝ) :
    0 ≤ samplingTestedSecondDensity h α E G s ∧
      samplingTestedSecondDensity h α E G s ≤ samplingSecondDensity h α s := by
  have hm : Measurable (samplingTestedSecondWeight h α E G s) :=
    (samplingTestedSecondWeight_measurable h α E G hE hG).comp (measurable_const.prodMk measurable_id)
  have hi := (samplingSecondWeight_integrable h α s hh hα).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTestedSecondWeight_bounds h α E G s t hh hα).1]
      exact (samplingTestedSecondWeight_bounds h α E G s t hh hα).2))
  exact ⟨integral_nonneg (fun t => (samplingTestedSecondWeight_bounds h α E G s t hh hα).1),
    integral_mono_ae hi (samplingSecondWeight_integrable h α s hh hα)
      (Eventually.of_forall (fun t => (samplingTestedSecondWeight_bounds h α E G s t hh hα).2))⟩

theorem samplingTestedSecondDensity_square (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ s ∂unitIntervalMeasure, 0 ≤ samplingTestedSecondDensity h α E G s ∧
      samplingTestedSecondDensity h α E G s ≤ 1/(1-h)) ∧
    (∫ s, samplingTestedSecondDensity h α E G s^2 ∂unitIntervalMeasure) ≤ 1+h^2/(1-h)^2 := by
  let f := samplingTestedSecondDensity h α E G
  let q := samplingIdealSecond h
  let C := 1/(1-h)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf := samplingTestedSecondDensity_measurable h α E G hE hG
  have hq := samplingIdealSecond_measurable h hh
  have hnon (s : ℝ) : 0 ≤ f s := (samplingTestedSecondDensity_bounds h α E G hh hα hE hG s).1
  have hle : ∀ᵐ s ∂unitIntervalMeasure, f s ≤ q s :=
    (samplingSecondDensity_le_ideal h α hh hh1 hα).mono (fun s hs =>
      (samplingTestedSecondDensity_bounds h α E G hh hα hE hG s).2.trans hs)
  have hqb (s : ℝ) : 0 ≤ q s ∧ q s ≤ C := (samplingIdealSecond_bounds h s hh hh1).imp_right And.left
  have hq2 (s : ℝ) : q s^2 ≤ C^2 := by nlinarith [(hqb s).1,(hqb s).2]
  have hf2 : ∀ᵐ s ∂unitIntervalMeasure, f s^2 ≤ q s^2 := hle.mono (fun s hs => by nlinarith [hnon s,(hqb s).1])
  have hfi : Integrable (fun s => f s^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (hf.pow_const 2).aestronglyMeasurable (hf2.mono (fun s hs => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hs.trans (hq2 s)))
  have hqi : Integrable (fun s => q s^2) unitIntervalMeasure :=
    (integrable_const (C^2)).mono' (hq.pow_const 2).aestronglyMeasurable (Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hq2 s))
  exact ⟨hle.mono (fun s hs => ⟨hnon s,hs.trans (hqb s).2⟩),
    (integral_mono_ae hfi hqi hf2).trans (samplingIdealSecond_square h hh hh1).2⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Moments
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceSamplingWidth_le_half (s : ℕ) : sourceSamplingWidth s ≤ 1/2 := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  have hm0 : 0 ≤ (sourceBlockSize s : ℝ) := by positivity
  have he : sourceSamplingWidth s ≤ (sourceBlockSize s : ℝ)^(-1/2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hs : 2 ≤ Real.sqrt (sourceBlockSize s : ℝ) := by
    nlinarith [Real.sq_sqrt hm0,Real.sqrt_nonneg (sourceBlockSize s : ℝ)]
  apply he.trans
  rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hm0,← Real.sqrt_eq_rpow]
  simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs)

/-- Exact stage parameters discharge all cutoff/width assumptions in the
source's tested second-diagonal one-coordinate moment bound. -/
theorem sourceSampling_tested_second_moment (s : ℕ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ x ∂unitIntervalMeasure,
      0 ≤ samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x ∧
      samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x ≤ 2) ∧
    (∫ x, samplingTestedSecondDensity (sourceSamplingWidth s) (sourceSamplingCutoff s) E G x^2
      ∂unitIntervalMeasure) ≤ 1+4*(sourceBlockSize s : ℝ)^(-6/5 : ℝ) := by
  have hp := sourceSampling_parameters s
  have hhalf := sourceSamplingWidth_le_half s
  have hden : 0 < 1-sourceSamplingWidth s := by linarith [hp.2.1]
  have hb := samplingTestedSecondDensity_square (sourceSamplingWidth s) (sourceSamplingCutoff s)
    E G hp.1 hp.2.1 hp.2.2 hE hG
  have hi : 1/(1-sourceSamplingWidth s) ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  have herror : (sourceSamplingWidth s)^2/(1-sourceSamplingWidth s)^2 ≤ 4*(sourceSamplingWidth s)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    have hsq : (1/4 : ℝ) ≤ (1-sourceSamplingWidth s)^2 := by nlinarith
    nlinarith [sq_nonneg (sourceSamplingWidth s),mul_nonneg (sq_nonneg (sourceSamplingWidth s))
      (show 0 ≤ (1-sourceSamplingWidth s)^2-1/4 by linarith)]
  have he : (sourceSamplingWidth s)^2 = (sourceBlockSize s : ℝ)^(-6/5 : ℝ) := by
    unfold sourceSamplingWidth
    rw [← Real.rpow_natCast,← Real.rpow_mul (sourceBlockSize_pos s).le]
    norm_num
  exact ⟨hb.1.mono (fun x hx => ⟨hx.1,hx.2.trans hi⟩),hb.2.trans (by rw [← he]; linarith)⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_TestedFirstMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem samplingTestedFirstWeight_measurable (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingTestedFirstWeight b h α E G p.1 p.2) := by
  unfold samplingTestedFirstWeight
  exact Measurable.ite ((hE.preimage measurable_fst).inter
    (hG.preimage (sourceFract_measurable.comp (measurable_fst.add measurable_snd))))
    (samplingWeight_measurable b h α) measurable_const

theorem samplingTestedFirstWeight_bounds (b : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ)
    (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingTestedFirstWeight b h α E G s t ∧
    samplingTestedFirstWeight b h α E G s t ≤ samplingWeight b h α s t := by
  have hn := (samplingWeight_bounds b h α s t hh hα).1
  unfold samplingTestedFirstWeight
  split_ifs <;> simp [hn]

theorem samplingWeight_integrable (b : Bool) (h α s : ℝ) (hh : 0 < h) (hα : 0 < α) :
    Integrable (samplingWeight b h α s) unitIntervalMeasure := by
  apply (integrable_const (max 1 (1/(h*α)))).mono'
    ((samplingWeight_measurable b h α).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    change ‖samplingWeight b h α s t‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (samplingWeight_bounds b h α s t hh hα).1]
    exact (samplingWeight_bounds b h α s t hh hα).2)

theorem samplingTestedFirstDensity_measurable (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingTestedFirstDensity b h α E G) :=
  (samplingTestedFirstWeight_measurable b h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

/-- Tests decrease the exact first marginal, which is at most one. -/
theorem samplingTestedFirstDensity_bounds (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G)
    (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    0 ≤ samplingTestedFirstDensity b h α E G s ∧
    samplingTestedFirstDensity b h α E G s ≤ 1 := by
  have hm : Measurable (samplingTestedFirstWeight b h α E G s) := (samplingTestedFirstWeight_measurable b h α E G hE hG).comp
    (measurable_const.prodMk measurable_id)
  have hi := (samplingWeight_integrable b h α s hh hα).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingTestedFirstWeight_bounds b h α E G s t hh hα).1]
      exact (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2))
  refine ⟨integral_nonneg (fun t => (samplingTestedFirstWeight_bounds b h α E G s t hh hα).1), ?_⟩
  calc
    _ ≤ ∫ t, samplingWeight b h α s t ∂unitIntervalMeasure :=
      integral_mono_ae hi (samplingWeight_integrable b h α s hh hα)
        (Eventually.of_forall (fun t => (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2))
    _ ≤ 1 := by
      rw [samplingWeight_first_integral b h α s hh hh1 hα hs]
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · split_ifs <;> norm_num
      · linarith [hs.1]

/-- The first tested marginal has quadratic moment at most one in both
triangular and diagonal coordinates, uniformly in the measurable tests. -/
theorem samplingTestedFirstDensity_square (b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingTestedFirstDensity b h α E G s ^ 2 ∂unitIntervalMeasure) ≤ 1 := by
  have hb : ∀ᵐ s ∂unitIntervalMeasure, 0 ≤ samplingTestedFirstDensity b h α E G s ∧
      samplingTestedFirstDensity b h α E G s ≤ 1 :=
    (ae_restrict_mem measurableSet_Ico).mono (fun s hs =>
      samplingTestedFirstDensity_bounds b h α E G hh hh1 hα hE hG s hs)
  have hb2 := hb.mono (fun s hs => show samplingTestedFirstDensity b h α E G s ^ 2 ≤ 1 by nlinarith)
  have hi : Integrable (fun s => samplingTestedFirstDensity b h α E G s ^ 2) unitIntervalMeasure :=
    (integrable_const (1 : ℝ)).mono'
      ((samplingTestedFirstDensity_measurable b h α E G hE hG).pow_const 2).aestronglyMeasurable
      (hb2.mono (fun s hs => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (samplingTestedFirstDensity b h α E G s))]
        exact hs))
  simpa using integral_mono_ae hi (integrable_const (1 : ℝ)) hb2

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_TestedSelfMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- A bounded measurable real function has an integrable square on a finite measure. -/
theorem sampling_square_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (f : Ω → ℝ) (C : ℝ) (hm : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ C) : Integrable (fun x => f x ^ 2) μ := by
  apply (integrable_const (C^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (f x))]
    nlinarith [(hb x).1,(hb x).2])

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_OrientedMoments
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem samplingOrientedWeight_measurable (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (fun p : ℝ × ℝ => samplingOrientedWeight r b h α E G p.1 p.2) := by
  cases r
  · exact samplingTestedFirstWeight_measurable b h α E G hE hG
  · unfold samplingOrientedWeight
    simp only [ite_true]
    exact Measurable.ite ((hE.preimage (sourceFract_measurable.comp
      (measurable_fst.sub measurable_snd))).inter (hG.preimage measurable_fst))
      ((samplingWeight_measurable b h α).comp
        ((sourceFract_measurable.comp (measurable_fst.sub measurable_snd)).prodMk measurable_snd)) measurable_const

theorem samplingOrientedWeight_bounds (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hh : 0 < h) (hα : 0 < α) (s t : ℝ) :
    0 ≤ samplingOrientedWeight r b h α E G s t ∧
    samplingOrientedWeight r b h α E G s t ≤ max 1 (1/(h*α)) := by
  cases r
  · exact ⟨(samplingTestedFirstWeight_bounds b h α E G s t hh hα).1,
      (samplingTestedFirstWeight_bounds b h α E G s t hh hα).2.trans
        (samplingWeight_bounds b h α s t hh hα).2⟩
  · unfold samplingOrientedWeight
    simp only [ite_true]
    split_ifs
    · exact samplingWeight_bounds b h α _ _ hh hα
    · exact ⟨le_rfl,(by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)⟩

theorem samplingOrientedWeight_triangular_bounds (r : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ) :
    0 ≤ samplingOrientedWeight r true h α E G s t ∧
    samplingOrientedWeight r true h α E G s t ≤ 1 := by
  cases r <;> unfold samplingOrientedWeight samplingTestedFirstWeight samplingWeight <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] <;> split_ifs <;> norm_num

theorem samplingOrientedDensity_measurable (r b : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    Measurable (samplingOrientedDensity r b h α E G) :=
  (samplingOrientedWeight_measurable r b h α E G hE hG).stronglyMeasurable.integral_prod_right.measurable

/-- Both triangular orientations have tested marginal densities between zero and one. -/
theorem samplingOrientedDensity_triangular_bounds (r : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) (s : ℝ) :
    0 ≤ samplingOrientedDensity r true h α E G s ∧
    samplingOrientedDensity r true h α E G s ≤ 1 := by
  have hm : Measurable (samplingOrientedWeight r true h α E G s) :=
    (samplingOrientedWeight_measurable r true h α E G hE hG).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (samplingOrientedWeight r true h α E G s) unitIntervalMeasure :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (samplingOrientedWeight_triangular_bounds r h α E G s t).1]
      exact (samplingOrientedWeight_triangular_bounds r h α E G s t).2))
  refine ⟨integral_nonneg (fun t => (samplingOrientedWeight_triangular_bounds r h α E G s t).1),?_⟩
  simpa [samplingOrientedDensity] using integral_mono_ae hi (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun t => (samplingOrientedWeight_triangular_bounds r h α E G s t).2))

theorem samplingOrientedDensity_triangular_square (r : Bool) (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingOrientedDensity r true h α E G s ^ 2 ∂unitIntervalMeasure) ≤ 1 := by
  have hb := samplingOrientedDensity_triangular_bounds r h α E G hE hG
  have hi := sampling_square_integrable unitIntervalMeasure _ 1
    (samplingOrientedDensity_measurable r true h α E G hE hG) hb
  simpa [samplingOrientedDensity] using integral_mono_ae hi (integrable_const (1 : ℝ))
    (Eventually.of_forall (fun s => show samplingOrientedDensity r true h α E G s ^ 2 ≤ 1 by
      nlinarith [(hb s).1,(hb s).2]))

theorem sourceSampling_oriented_moment (stage : ℕ) (r b : Bool) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∀ᵐ s ∂unitIntervalMeasure,
      0 ≤ samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ∧
      samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ≤ 2) ∧
    (∫ s, samplingOrientedDensity r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ^ 2
      ∂unitIntervalMeasure) ≤ 1+4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) := by
  have hp := sourceSampling_parameters stage
  have herr : (0 : ℝ) ≤ 4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) := by positivity
  cases r
  · have hb : ∀ᵐ s ∂unitIntervalMeasure,
        0 ≤ samplingTestedFirstDensity b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ∧
        samplingTestedFirstDensity b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G s ≤ 1 :=
      (ae_restrict_mem measurableSet_Ico).mono (fun s hs => samplingTestedFirstDensity_bounds b _ _ E G
        hp.1 hp.2.1 hp.2.2 hE hG s hs)
    refine ⟨hb.mono (fun s hs => ⟨hs.1,hs.2.trans (by norm_num)⟩),?_⟩
    exact (samplingTestedFirstDensity_square b _ _ E G hp.1 hp.2.1 hp.2.2 hE hG).trans (by linarith)
  · cases b
    · exact sourceSampling_tested_second_moment stage E G hE hG
    · refine ⟨Eventually.of_forall (fun s => ?_),?_⟩
      · have hb := samplingOrientedDensity_triangular_bounds true (sourceSamplingWidth stage)
          (sourceSamplingCutoff stage) E G hE hG s
        exact ⟨hb.1,hb.2.trans (by norm_num)⟩
      · exact (samplingOrientedDensity_triangular_square true _ _ E G hE hG).trans (by linarith)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_IdealProduct
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- The actual source prefix dimension, including the current block. -/
theorem sourceSamplingPrefix_card (stage : ℕ) :
    (sourceSamplingPrefix stage).card = (sourceStageState stage).d+sourceBlockSize stage := by
  unfold sourceSamplingPrefix CouplingParameters.blockPrefix
  simp only [Finset.card_sigma,Finset.card_univ,Fintype.card_fin]
  change (∑ i ∈ range (stage+1), (sourceStage i).m) = _
  rw [sum_range_succ,← sourceStage_previous_size]
  rfl

theorem sourceSamplingPrefix_card_bound (stage : ℕ) :
    ((sourceSamplingPrefix stage).card : ℝ) ≤ (101/100 : ℝ)*sourceBlockSize stage := by
  rw [sourceSamplingPrefix_card,Nat.cast_add]
  have hp := (sourceStage stage).previous_size
  change ((sourceStageState stage).d : ℝ) ≤ (sourceBlockSize stage : ℝ)/100 at hp
  linarith

/-- The small quadratic coordinate errors stay bounded in the growing prefix. -/
theorem sourceSampling_prefix_quadratic_budget (stage : ℕ) :
    ((sourceSamplingPrefix stage).card : ℝ)*(4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ)) ≤ 5 := by
  have hm := sourceBlockSize_pos stage
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have hh : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    linarith
  have he : (sourceBlockSize stage : ℝ)*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) =
      (sourceBlockSize stage : ℝ)^(-1/5 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (sourceBlockSize stage : ℝ)]
    rw [← Real.rpow_add hm]
    norm_num
  have hp : (sourceBlockSize stage : ℝ)^(-1/5 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  calc
    _ ≤ ((101/100 : ℝ)*sourceBlockSize stage)*(4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ)) :=
      mul_le_mul_of_nonneg_right (sourceSamplingPrefix_card_bound stage) (by positivity)
    _ = (101/25 : ℝ)*(sourceBlockSize stage : ℝ)^(-1/5 : ℝ) := by rw [← he]; ring
    _ ≤ 5 := by linarith

theorem sourceSamplingIdealDensity_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Measurable (sourceSamplingIdealDensity stage r b E G) :=
  Finset.measurable_prod _ (fun i _ =>
    (samplingOrientedDensity_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i)).comp (measurable_pi_apply i))

/-- Exact product factorization of the ideal marginal's quadratic moment. -/
theorem sourceSamplingIdealDensity_square (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ x, sourceSamplingIdealDensity stage r b E G x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) =
      ∏ i ∈ sourceSamplingPrefix stage,
        ∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s ^ 2
          ∂unitIntervalMeasure := by
  simp only [sourceSamplingIdealDensity,← Finset.prod_pow]
  exact integral_infinitePi_finset_prod _ _ _ (fun i =>
    (samplingOrientedDensity_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i)).pow_const 2)

/-- Uniform-in-stage ideal marginal bound. The second orientation uses the
quadratic cancellation established for the actual cutoff diagonal density. -/
theorem sourceSamplingIdealDensity_uniform_square (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ x, sourceSamplingIdealDensity stage r b E G x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤ Real.exp 5 := by
  rw [sourceSamplingIdealDensity_square stage r b E G hE hG,← Finset.prod_coe_sort]
  have he := product_energy_le_exp
    (fun i : sourceSamplingPrefix stage => ∫ s, samplingOrientedDensity r (b i)
      (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s ^ 2 ∂unitIntervalMeasure)
    (fun _ : sourceSamplingPrefix stage => 4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ))
    (fun i => integral_nonneg (fun _ => sq_nonneg _))
    (fun i => (sourceSampling_oriented_moment stage r (b i) (E i) (G i) (hE i) (hG i)).2)
  apply he.trans
  apply Real.exp_le_exp.mpr
  simpa using sourceSampling_prefix_quadratic_budget stage

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_ProductMoments
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

theorem sourceSamplingProduct_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) => sourceSamplingProduct stage r b E G n p.1 p.2) := by
  unfold sourceSamplingProduct
  apply Finset.measurable_prod
  intro i _
  have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      (p.2 i,Int.fract ((n : ℝ)*p.1 i))) :=
    ((measurable_pi_apply i).comp measurable_snd).prodMk
      (sourceFract_measurable.comp (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)))
  exact (samplingOrientedWeight_measurable r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i) (hE i) (hG i)).comp hm

theorem sourceSamplingProduct_bounds (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (n : ℤ) (θ x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingProduct stage r b E G n θ x ∧
    sourceSamplingProduct stage r b E G n θ x ≤
      (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card := by
  have hp := sourceSampling_parameters stage
  have hb (i : SourceCoordinate) := samplingOrientedWeight_bounds r (b i) _ _ (E i) (G i) hp.1 hp.2.2
    (x i) (Int.fract ((n : ℝ)*θ i))
  refine ⟨prod_nonneg (fun i _ => (hb i).1),?_⟩
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage, max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)) :=
      prod_le_prod (fun i _ => (hb i).1) (fun i _ => (hb i).2)
    _ = _ := by simp

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_LayerCake
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- A bounded measurable real function on a finite measure space is integrable. -/
theorem sampling_integrable_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f μ := by
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hb x)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_MixedCorrelation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- A bounded nonnegative coordinate kernel has a measurable bounded mean. -/
theorem sampling_kernel_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : ℝ → Ω → ℝ)
    (hu : Measurable (fun p : ℝ × Ω => u p.1 p.2)) (C : ℝ)
    (hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C) :
    Measurable (fun s => ∫ t, u s t ∂μ) ∧
    ∀ s, 0 ≤ (∫ t, u s t ∂μ) ∧ (∫ t, u s t ∂μ) ≤ C := by
  refine ⟨hu.stronglyMeasurable.integral_prod_right.measurable,?_⟩
  intro s
  have hi : Integrable (u s) μ := sampling_integrable_bounded μ _
    (hu.comp (measurable_const.prodMk measurable_id)) C
    (fun t => by rw [abs_of_nonneg (hb s t).1]; exact (hb s t).2)
  exact ⟨integral_nonneg (fun t => (hb s t).1),by
    simpa using integral_mono_ae hi (integrable_const C) (Eventually.of_forall (fun t => (hb s t).2))⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CrossProducts
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- A global bound used only to justify finite-stage integrations. -/
theorem sourceSamplingIdealDensity_bounds (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingIdealDensity stage r b E G x ∧
      sourceSamplingIdealDensity stage r b E G x ≤
        (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card := by
  have hp := sourceSampling_parameters stage
  have hb (i : SourceCoordinate) := (sampling_kernel_mean unitIntervalMeasure
    (samplingOrientedWeight r (b i) _ _ (E i) (G i))
    (samplingOrientedWeight_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i))
    (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))
    (samplingOrientedWeight_bounds r (b i) _ _ (E i) (G i) hp.1 hp.2.2)).2
  refine ⟨prod_nonneg (fun i _ => (hb i (x i)).1),?_⟩
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage, max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)) :=
      prod_le_prod (fun i _ => (hb i (x i)).1) (fun i _ => (hb i (x i)).2)
    _ = _ := by simp

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Error
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

theorem sourceSamplingSquaredError_nonneg (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingSquaredError stage r b E G θ := integral_nonneg (fun _ => sq_nonneg _)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_EmpiricalL2
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical
noncomputable section

theorem sourceSamplingEmpiricalDensity_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (θ : SourceCoordinate → ℝ) : Measurable (sourceSamplingEmpiricalDensity stage r b E G θ) :=
  (Finset.measurable_sum _ (fun n _ => (sourceSamplingProduct_measurable stage r b E G hE hG n).comp
    (measurable_const.prodMk measurable_id))).div_const _

/-- Every empirical density is bounded at its finite stage, including stages
whose selected set is empty. No asymptotic assumption is used here. -/
theorem sourceSamplingEmpiricalDensity_bounds (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (θ x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingEmpiricalDensity stage r b E G θ x ∧
      sourceSamplingEmpiricalDensity stage r b E G θ x ≤
        (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card := by
  let C := (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card
  have hC : 0 ≤ C := pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)) _
  have hb := sourceSamplingProduct_bounds stage r b E G
  have hn : 0 ≤ sourceSamplingEmpiricalDensity stage r b E G θ x :=
    div_nonneg (sum_nonneg (fun n _ => (hb n θ x).1)) (by positivity)
  refine ⟨hn,?_⟩
  by_cases hS : (sourceSamplingPowers stage).Nonempty
  · have hP : (0 : ℝ) < (sourceSamplingPowers stage).card := by exact_mod_cast hS.card_pos
    apply (div_le_iff₀ hP).mpr
    calc
      _ ≤ ∑ _n ∈ sourceSamplingPowers stage, C := sum_le_sum (fun n _ => (hb n θ x).2)
      _ = _ := by simp [C]; ring
  · have he : sourceSamplingPowers stage = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [sourceSamplingEmpiricalDensity,he]

/-- The empirical densities, not only the ideal products, belong to L2. -/
theorem sourceSamplingEmpiricalDensity_memLp (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (θ : SourceCoordinate → ℝ) :
    MemLp (sourceSamplingEmpiricalDensity stage r b E G θ) 2
      (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) := by
  apply MemLp.of_bound (sourceSamplingEmpiricalDensity_measurable stage r b E G hE hG θ).aestronglyMeasurable
    ((max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sourceSamplingEmpiricalDensity_bounds stage r b E G θ x).1]
  exact (sourceSamplingEmpiricalDensity_bounds stage r b E G θ x).2

/-- The full error and the ideal L2 bound control the actual empirical square. -/
theorem sourceSamplingEmpiricalDensity_square_le (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (θ : SourceCoordinate → ℝ) :
    (∫ x, sourceSamplingEmpiricalDensity stage r b E G θ x^2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤
      2*sourceSamplingSquaredError stage r b E G θ+2*Real.exp 5 := by
  let μ := Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)
  let z := sourceSamplingEmpiricalDensity stage r b E G θ
  let g := sourceSamplingIdealDensity stage r b E G
  let C := (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card
  have hz := sourceSamplingEmpiricalDensity_measurable stage r b E G hE hG θ
  have hg := sourceSamplingIdealDensity_measurable stage r b E G hE hG
  have hzb := sourceSamplingEmpiricalDensity_bounds stage r b E G θ
  have hgb := sourceSamplingIdealDensity_bounds stage r b E G hE hG
  have hzi : Integrable (fun x => z x^2) μ := sampling_square_integrable μ z C hz hzb
  have hgi : Integrable (fun x => g x^2) μ := sampling_square_integrable μ g C hg hgb
  have hei : Integrable (fun x => (z x-g x)^2) μ := by
    apply sampling_integrable_bounded μ _ ((hz.sub hg).pow_const 2) (C^2)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hz' : 0 ≤ z x ∧ z x ≤ C := hzb x
    have hg' : 0 ≤ g x ∧ g x ≤ C := hgb x
    change (z x-g x)^2 ≤ C^2
    nlinarith [mul_nonneg (show 0 ≤ C-(z x-g x) by linarith) (show 0 ≤ C+(z x-g x) by linarith)]
  have hi := integral_mono_ae hzi ((hei.const_mul 2).add (hgi.const_mul 2))
    (Eventually.of_forall (fun x => show z x^2 ≤ 2*(z x-g x)^2+2*g x^2 by nlinarith [sq_nonneg (z x-2*g x)]))
  simp only [Pi.add_apply] at hi
  rw [integral_add (hei.const_mul 2) (hgi.const_mul 2),integral_const_mul,integral_const_mul] at hi
  exact hi.trans (by
    have hb := sourceSamplingIdealDensity_uniform_square stage r b E G hE hG
    change (∫ x, g x^2 ∂μ) ≤ Real.exp 5 at hb
    change _ ≤ 2*(∫ x, (z x-g x)^2 ∂μ)+2*Real.exp 5
    linarith)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Measures
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

theorem sourceSamplingSummand_first_marginal (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    (sourceSamplingSummand I s θ n).map Prod.fst = sourceSamplingWeightedMeasure I s θ n := by
  unfold sourceSamplingSummand
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  rw [Measure.map_map measurable_fst hp]
  exact Measure.map_id

theorem sourceSamplingHaar_cube : ∀ᵐ x ∂sourceSamplingHaar,
    ∀ i : SourceCoordinate, x i ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have hh : ∀ᵐ t ∂sourceSamplingHaar.map (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact ae_restrict_mem measurableSet_Ico
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_UniformEvent
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical Topology
noncomputable section

/-- Actual empirical L2 bounds, uniform over all stages on a conull event. -/
theorem sourceSamplingEmpiricalDensity_uniform (r : Bool) (b : SourceCoordinate → Bool)
    (a c a' c' : SourceCoordinate → ℝ) :
    ∀ᵐ θ ∂sourceAngleLaw, ∃ C : ℝ, ∀ stage,
      MemLp (sourceSamplingEmpiricalDensity stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ) 2
          (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ∧
      (∫ x, sourceSamplingEmpiricalDensity stage r b
        (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ x^2
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤ C := by
  filter_upwards [sourceSamplingSquaredError_ae r b a c a' c'] with θ hθ
  let e := fun stage => sourceSamplingSquaredError stage r b
    (fun i => Set.Icc (a i) (c i)) (fun i => Set.Icc (a' i) (c' i)) θ
  refine ⟨2*(∑' stage, e stage)+2*Real.exp 5,?_⟩
  intro stage
  refine ⟨sourceSamplingEmpiricalDensity_memLp stage r b _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) θ,?_⟩
  have he : e stage ≤ ∑' l, e l := hθ.1.le_tsum stage (fun l _ => sourceSamplingSquaredError_nonneg l r b _ _ θ)
  apply (sourceSamplingEmpiricalDensity_square_le stage r b _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) θ).trans
  change 2*e stage+2*Real.exp 5 ≤ _
  linarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_FirstMarginal
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

/-- The actual first marginal is the verified empirical interval-test density.
The whole-circle tests [0,1] are valid on the Haar cube. -/
theorem sourceSamplingUntrimmed_first_density (I : Finset SourceCoordinate) (stage : ℕ)
    (θ : SourceCoordinate → ℝ) :
    (sourceSamplingUntrimmed I stage θ).map Prod.fst =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I))
          (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) θ x)) := by
  let S := sourceSamplingPowers stage
  let c : ℝ≥0∞ := ENNReal.ofReal (1/((sourceSamplingPowers stage).card : ℝ))
  let w (n : ℤ) := sourceSamplingWeight I stage θ n
  have hrep : (fun x => ENNReal.ofReal (sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I))
        (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) θ x)) =ᵐ[sourceSamplingHaar]
      (fun x => c*(∑ n ∈ S, ENNReal.ofReal (w n x))) := by
    filter_upwards [sourceSamplingHaar_cube] with x hx
    have hw (n : ℤ) : sourceSamplingProduct stage false (fun i => decide (i ∈ I))
        (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) n θ x = w n x := by
      apply Finset.prod_congr rfl
      intro i _
      have hx' : x i ∈ Set.Icc (0 : ℝ) 1 := ⟨(hx i).1,(hx i).2.le⟩
      have hy : Int.fract (x i+Int.fract ((n : ℝ)*θ i)) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
      simp only [samplingOrientedWeight, Bool.false_eq_true, ite_false, samplingTestedFirstWeight,
        hx', hy, and_self, ite_true]
    simp only [sourceSamplingEmpiricalDensity,hw]
    rw [div_eq_mul_inv,mul_comm,← one_div,
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_sum_of_nonneg (fun n _ => (sourceSamplingWeight_bounds I stage θ n x).1)]
  rw [withDensity_congr_ae hrep]
  ext A hA
  rw [Measure.map_apply measurable_fst hA]
  unfold sourceSamplingUntrimmed
  rw [Measure.smul_apply,Measure.finsetSum_apply,withDensity_apply _ hA]
  have hterm (n : ℤ) : sourceSamplingSummand I stage θ n (Prod.fst ⁻¹' A) =
      ∫⁻ x in A, ENNReal.ofReal (w n x) ∂sourceSamplingHaar := by
    rw [← Measure.map_apply measurable_fst hA,sourceSamplingSummand_first_marginal]
    exact withDensity_apply _ hA
  simp only [hterm,smul_eq_mul]
  rw [lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  congr 1
  exact (lintegral_finsetSum S (fun n _ =>
    (sourceSamplingWeight_measurable I stage θ n).ennreal_ofReal)).symm

/-- Uniform L2 densities for the actual untrimmed first marginals. -/
theorem sourceSamplingUntrimmed_first_L2 (I : Finset SourceCoordinate) :
    ∀ᵐ θ ∂sourceAngleLaw, ∃ C : ℝ, ∀ stage,
      ∃ f : (SourceCoordinate → ℝ) → ℝ,
        (sourceSamplingUntrimmed I stage θ).map Prod.fst = sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        MemLp f 2 sourceSamplingHaar ∧ (∫ x, f x^2 ∂sourceSamplingHaar) ≤ C := by
  filter_upwards [sourceSamplingEmpiricalDensity_uniform false (fun i => decide (i ∈ I))
    (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)] with θ hθ
  obtain ⟨C,hC⟩ := hθ
  refine ⟨C,fun stage => ⟨_,sourceSamplingUntrimmed_first_density I stage θ,(hC stage).1,(hC stage).2⟩⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_RotationTransport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

theorem coordinateRotate_neg_cube (θ x : SourceCoordinate → ℝ) (n : ℤ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    coordinateRotate θ (-n) (coordinateRotate θ n x) = x := by
  funext i
  unfold coordinateRotate
  rw [Int.cast_neg,neg_mul]
  have he : Int.fract (x i+(n : ℝ)*θ i) + -((n : ℝ)*θ i) =
      x i - (⌊x i+(n : ℝ)*θ i⌋ : ℝ) := by
    linarith [Int.fract_add_floor (x i+(n : ℝ)*θ i)]
  rw [he,Int.fract_sub_intCast,Int.fract_eq_self.mpr (hx i)]

theorem coordinateRotate_neg_phase (θ x : SourceCoordinate → ℝ) (n : ℤ) (i : SourceCoordinate) :
    coordinateRotate θ (-n) x i = Int.fract (x i-Int.fract ((n : ℝ)*θ i)) := by
  unfold coordinateRotate
  rw [Int.cast_neg,neg_mul]
  have he : x i + -((n : ℝ)*θ i) = (x i-Int.fract ((n : ℝ)*θ i)) - (⌊(n : ℝ)*θ i⌋ : ℝ) := by
    linarith [Int.fract_add_floor ((n : ℝ)*θ i)]
  rw [he,Int.fract_sub_intCast]

/-- Change of variables for an actual weighted Haar law. The inverse identity
is needed only on the conull cube of representatives. -/
theorem sourceSamplingHaar_rotate_withDensity (θ : SourceCoordinate → ℝ) (n : ℤ)
    (w : (SourceCoordinate → ℝ) → ℝ≥0∞) (hw : Measurable w) :
    (sourceSamplingHaar.withDensity w).map (coordinateRotate θ n) =
      sourceSamplingHaar.withDensity (fun y => w (coordinateRotate θ (-n) y)) := by
  let R := coordinateRotate θ n
  let R' := coordinateRotate θ (-n)
  have hR := coordinateRotate_preserving θ n
  have hR' := coordinateRotate_preserving θ (-n)
  ext A hA
  rw [Measure.map_apply hR.measurable hA,withDensity_apply _ (hR.measurable hA),withDensity_apply _ hA]
  rw [← lintegral_indicator (hR.measurable hA),← lintegral_indicator hA]
  have hm : Measurable (A.indicator (fun y => w (R' y))) := (hw.comp hR'.measurable).indicator hA
  calc
    _ = ∫⁻ x, A.indicator (fun y => w (R' y)) (R x) ∂sourceSamplingHaar := by
      apply lintegral_congr_ae
      filter_upwards [sourceSamplingHaar_cube] with x hx
      change (if R x ∈ A then w x else 0) = (if R x ∈ A then w (R' (R x)) else 0)
      rw [show R' (R x) = x from coordinateRotate_neg_cube θ x n hx]
    _ = _ := hR.lintegral_comp hm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_SecondMarginal
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

/-- The actual second marginal of one orbit summand, obtained by weighted
Haar transport and not supplied as an assumption. -/
theorem sourceSamplingSummand_second_density (I : Finset SourceCoordinate) (stage : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    (sourceSamplingSummand I stage θ n).map Prod.snd =
      sourceSamplingHaar.withDensity (fun y => ENNReal.ofReal
        (sourceSamplingWeight I stage θ n (coordinateRotate θ (-n) y))) := by
  unfold sourceSamplingSummand
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  rw [Measure.map_map measurable_snd hp]
  exact sourceSamplingHaar_rotate_withDensity θ n _
    (sourceSamplingWeight_measurable I stage θ n).ennreal_ofReal

/-- The actual second marginal is the second-oriented empirical density. -/
theorem sourceSamplingUntrimmed_second_density (I : Finset SourceCoordinate) (stage : ℕ)
    (θ : SourceCoordinate → ℝ) :
    (sourceSamplingUntrimmed I stage θ).map Prod.snd =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingEmpiricalDensity stage true (fun i => decide (i ∈ I))
          (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) θ x)) := by
  let S := sourceSamplingPowers stage
  let c : ℝ≥0∞ := ENNReal.ofReal (1/((sourceSamplingPowers stage).card : ℝ))
  let w (n : ℤ) := fun x => sourceSamplingWeight I stage θ n (coordinateRotate θ (-n) x)
  have hrep : (fun x => ENNReal.ofReal (sourceSamplingEmpiricalDensity stage true (fun i => decide (i ∈ I))
        (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) θ x)) =ᵐ[sourceSamplingHaar]
      (fun x => c*(∑ n ∈ S, ENNReal.ofReal (w n x))) := by
    filter_upwards [sourceSamplingHaar_cube] with x hx
    have hw (n : ℤ) : sourceSamplingProduct stage true (fun i => decide (i ∈ I))
        (fun _ => Set.Icc 0 1) (fun _ => Set.Icc 0 1) n θ x = w n x := by
      apply Finset.prod_congr rfl
      intro i _
      have hx' : x i ∈ Set.Icc (0 : ℝ) 1 := ⟨(hx i).1,(hx i).2.le⟩
      have hz : Int.fract (x i-Int.fract ((n : ℝ)*θ i)) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
      simp only [samplingOrientedWeight,ite_true,hz,hx',and_self]
      rw [coordinateRotate_neg_phase]
    simp only [sourceSamplingEmpiricalDensity,hw]
    rw [div_eq_mul_inv,mul_comm,← one_div,
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_sum_of_nonneg (fun n _ => (sourceSamplingWeight_bounds I stage θ n (coordinateRotate θ (-n) x)).1)]
  rw [withDensity_congr_ae hrep]
  ext A hA
  rw [Measure.map_apply measurable_snd hA]
  unfold sourceSamplingUntrimmed
  rw [Measure.smul_apply,Measure.finsetSum_apply,withDensity_apply _ hA]
  have hterm (n : ℤ) : sourceSamplingSummand I stage θ n (Prod.snd ⁻¹' A) =
      ∫⁻ x in A, ENNReal.ofReal (w n x) ∂sourceSamplingHaar := by
    rw [← Measure.map_apply measurable_snd hA,sourceSamplingSummand_second_density]
    exact withDensity_apply _ hA
  simp only [hterm,smul_eq_mul]
  rw [lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  congr 1
  exact (lintegral_finsetSum S (fun n _ =>
    ((sourceSamplingWeight_measurable I stage θ n).comp (coordinateRotate_preserving θ (-n)).measurable).ennreal_ofReal)).symm

/-- Uniform L2 densities for the actual untrimmed second marginals. -/
theorem sourceSamplingUntrimmed_second_L2 (I : Finset SourceCoordinate) :
    ∀ᵐ θ ∂sourceAngleLaw, ∃ C : ℝ, ∀ stage,
      ∃ f : (SourceCoordinate → ℝ) → ℝ,
        (sourceSamplingUntrimmed I stage θ).map Prod.snd = sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        MemLp f 2 sourceSamplingHaar ∧ (∫ x, f x^2 ∂sourceSamplingHaar) ≤ C := by
  filter_upwards [sourceSamplingEmpiricalDensity_uniform true (fun i => decide (i ∈ I))
    (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 1)] with θ hθ
  obtain ⟨C,hC⟩ := hθ
  refine ⟨C,fun stage => ⟨_,sourceSamplingUntrimmed_second_density I stage θ,(hC stage).1,(hC stage).2⟩⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TestedMarginals
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

theorem sourceSamplingEndpoint_measurable (r : Bool) : Measurable (sourceSamplingEndpoint r) := by
  cases r
  · exact measurable_fst
  · exact measurable_snd

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_RationalTests
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Both actual untested marginal densities are uniformly L2 bounded on one
conull event, simultaneously for all finite I. -/
theorem sourceSampling_both_marginals_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (r : Bool),
      ∃ C : ℝ, ∀ stage, ∃ f : (SourceCoordinate → ℝ) → ℝ,
        (sourceSamplingUntrimmed I stage θ).map (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        MemLp f 2 sourceSamplingHaar ∧ (∫ x, f x^2 ∂sourceSamplingHaar) ≤ C := by
  apply ae_all_iff.mpr
  intro I
  apply ae_all_iff.mpr
  intro r
  cases r
  · exact sourceSamplingUntrimmed_first_L2 I
  · exact sourceSamplingUntrimmed_second_L2 I

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_OrderedRestriction
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingTrimmed_le (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : sourceSamplingTrimmed I s θ ≤ sourceSamplingUntrimmed I s θ :=
  Measure.restrict_le_self

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_SubmeasureL2Density
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A finite submeasure of an L2 density has an actual nonnegative L2
Radon--Nikodym density, with no increase in its squared integral. -/
theorem submeasure_L2_density {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [SigmaFinite μ] [IsFiniteMeasure ν] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (hν : ν ≤ μ.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∀ᵐ x ∂μ, g x ≤ |f x|) ∧ MemLp g 2 μ ∧
      (∫ x, g x ^ 2 ∂μ) ≤ ∫ x, f x ^ 2 ∂μ := by
  let g := fun x => (ν.rnDeriv μ x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans (withDensity_absolutelyContinuous _ _)
  have hderiv : ν.rnDeriv μ ≤ᵐ[μ] (fun x => ENNReal.ofReal (f x)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ)
    intro A hA _
    calc
      _ ≤ ν A := Measure.setLIntegral_rnDeriv_le A
      _ ≤ (μ.withDensity (fun x => ENNReal.ofReal (f x))) A := hν A
      _ = _ := withDensity_apply _ hA
  have hle : ∀ᵐ x ∂μ, g x ≤ |f x| := by
    filter_upwards [hderiv] with x hx
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hx.trans (ENNReal.ofReal_le_ofReal (le_abs_self (f x))))
    simpa only [ENNReal.toReal_ofReal (abs_nonneg (f x))] using hh
  have hlp : MemLp g 2 μ := hf.mono hg.aestronglyMeasurable (by
    filter_upwards [hle] with x hx
    change |g x| ≤ |f x|
    rw [abs_of_nonneg (show 0 ≤ g x from ENNReal.toReal_nonneg)]
    exact hx)
  refine ⟨g,hg,fun x => ENNReal.toReal_nonneg,?_,hle,hlp,?_⟩
  · rw [← Measure.withDensity_rnDeriv_eq ν μ hac]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_ne_top ν μ] with x hx
    exact (ENNReal.ofReal_toReal hx).symm
  · apply integral_mono_ae hlp.integrable_sq hf.integrable_sq
    filter_upwards [hle] with x hx
    have hg0 : 0 ≤ g x := ENNReal.toReal_nonneg
    nlinarith [sq_abs (f x)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TrimmedMarginals
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Each actual trimmed marginal is dominated by the actual untrimmed
marginal, for both orientations. -/
theorem sourceSamplingTrimmed_marginal_le (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (r : Bool) :
    (sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r) ≤
      (sourceSamplingUntrimmed I s θ).map (sourceSamplingEndpoint r) :=
  Measure.map_mono (sourceSamplingTrimmed_le I s θ) (sourceSamplingEndpoint_measurable r)

/-- The actual Radon--Nikodym densities after trimming have the same uniform
squared L2 bound, on a single event for every finite I and both endpoints. -/
theorem sourceSamplingTrimmed_marginals_event_oai : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ (I : Finset SourceCoordinate) (r : Bool), ∃ C : ℝ, ∀ s : ℕ,
      ∃ g : (SourceCoordinate → ℝ) → ℝ,
        Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        (sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
        MemLp g 2 sourceSamplingHaar ∧ (∫ x, g x^2 ∂sourceSamplingHaar) ≤ C := by
  filter_upwards [sourceSampling_both_marginals_event] with θ hθ
  intro I r
  obtain ⟨C,hC⟩ := hθ I r
  refine ⟨C,fun s => ?_⟩
  obtain ⟨f,hf,hLp,hbound⟩ := hC s
  have hsub := sourceSamplingTrimmed_marginal_le I s θ r
  rw [hf] at hsub
  obtain ⟨g,hg,hg0,hgμ,hle,hgLp,hgint⟩ := submeasure_L2_density sourceSamplingHaar
    ((sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r)) f hLp hsub
  exact ⟨g,hg,hg0,hgμ,hgLp,hgint.trans hbound⟩

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event_oai := @OAI.FiniteFactor.sourceSamplingTrimmed_marginals_event_oai
