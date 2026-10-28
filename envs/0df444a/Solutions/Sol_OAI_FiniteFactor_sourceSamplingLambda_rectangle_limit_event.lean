-- Prove2me | solution 1 for OAI.FiniteFactor.sourceSamplingLambda_rectangle_limit_event
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:44:46.380985+00:00
-- url     : https://prove2.me/submissions/05baac10-bd21-491d-ad26-9a4757903638

import Mathlib
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceSamplingSquaredError_ae

section
-- module Solutions.OAIQ3_FF.Compat
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_BlockLimit
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
namespace CouplingParameters

theorem mem_blockPrefix (m : ℕ → ℕ) (n : ℕ) (i : BlockCoordinate m) :
    i ∈ blockPrefix m n ↔ i.1 < n := by simp [blockPrefix]

end CouplingParameters
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
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_SelfMoment
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceSamplingCutoff_le_half (s : ℕ) : sourceSamplingCutoff s ≤ 1/2 := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  have hp := sourceBlockSize_pos s
  calc
    sourceSamplingCutoff s ≤ (sourceBlockSize s : ℝ)^(-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = 1/(sourceBlockSize s : ℝ) := by rw [Real.rpow_neg_one,one_div]
    _ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)

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

theorem coordinateRotate_phase (θ x : SourceCoordinate → ℝ) (n : ℤ) (i : SourceCoordinate) :
    coordinateRotate θ n x i = Int.fract (x i+Int.fract ((n : ℝ)*θ i)) := by
  unfold coordinateRotate
  have he : x i+(n : ℝ)*θ i = (x i+Int.fract ((n : ℝ)*θ i)) + (⌊(n : ℝ)*θ i⌋ : ℝ) := by
    linarith [Int.fract_add_floor ((n : ℝ)*θ i)]
  rw [he,Int.fract_add_intCast]

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
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TestedTransport
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

theorem sourceSamplingRectangle_measurable (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    MeasurableSet (sourceSamplingRectangle E G) := by
  simp only [sourceSamplingRectangle,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact ((hE i).preimage ((measurable_pi_apply i).comp measurable_fst)).inter
    ((hG i).preimage ((measurable_pi_apply i).comp measurable_snd))

theorem sourceSamplingProduct_first_indicator (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ)
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ x : SourceCoordinate → ℝ) (n : ℤ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ x =
      if (x,coordinateRotate θ n x) ∈ sourceSamplingRectangle E G
      then sourceSamplingWeight I stage θ n x else 0 := by
  have hy (i) : coordinateRotate θ n x i ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  have he : (∀ i ∈ sourceSamplingPrefix stage, x i ∈ E i ∧ coordinateRotate θ n x i ∈ G i) ↔
      (x,coordinateRotate θ n x) ∈ sourceSamplingRectangle E G := by
    constructor
    · intro h i
      by_cases hi : i ∈ sourceSamplingPrefix stage
      · exact h i hi
      · exact ⟨(houtside i hi).1 (hx i),(houtside i hi).2 (hy i)⟩
    · intro h i _
      exact h i
  unfold sourceSamplingProduct samplingOrientedWeight samplingTestedFirstWeight
  simp only [Bool.false_eq_true,ite_false,← coordinateRotate_phase]
  simp only [Finset.prod_ite_zero,he]
  rfl

/-- Inverse rotation exchanges the two actual tested product orientations. -/
theorem sourceSamplingProduct_second_inverse (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ) (θ y : SourceCoordinate → ℝ) (n : ℤ)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1) :
    sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ
      (coordinateRotate θ (-n) y) =
    sourceSamplingProduct stage true (fun i => decide (i ∈ I)) E G n θ y := by
  have hinv : coordinateRotate θ n (coordinateRotate θ (-n) y) = y := by
    simpa only [neg_neg] using coordinateRotate_neg_cube θ y (-n) hy
  apply Finset.prod_congr rfl
  intro i _
  have hi := congrFun hinv i
  rw [coordinateRotate_phase] at hi
  simp only [samplingOrientedWeight,Bool.false_eq_true,ite_false,ite_true,samplingTestedFirstWeight,hi]
  rw [coordinateRotate_neg_phase]

/-- The restricted orbit-pair summand is exactly the pushforward of its
first tested product, with no assumed marginal law. -/
theorem sourceSamplingSummand_restrict_rectangle (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    (sourceSamplingSummand I stage θ n).restrict (sourceSamplingRectangle E G) =
      (sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ x))).map
          (fun x => (x,coordinateRotate θ n x)) := by
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  have hR := sourceSamplingRectangle_measurable E G hE hG
  unfold sourceSamplingSummand sourceSamplingWeightedMeasure
  rw [Measure.restrict_map hp hR,restrict_withDensity (hp hR),← withDensity_indicator (hp hR)]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [sourceSamplingHaar_cube] with x hx
  rw [sourceSamplingProduct_first_indicator I stage E G houtside θ x n hx]
  change (if (x,coordinateRotate θ n x) ∈ sourceSamplingRectangle E G
    then ENNReal.ofReal (sourceSamplingWeight I stage θ n x) else 0) = _
  split_ifs <;> simp

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

/-- Both actual rectangle-restricted marginal measures for a single power. -/
theorem sourceSamplingSummand_tested_marginal (I : Finset SourceCoordinate) (stage : ℕ)
    (r : Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    ((sourceSamplingSummand I stage θ n).restrict (sourceSamplingRectangle E G)).map
        (sourceSamplingEndpoint r) =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingProduct stage r (fun i => decide (i ∈ I)) E G n θ x)) := by
  rw [sourceSamplingSummand_restrict_rectangle I stage E G hE hG houtside θ n]
  have hp : Measurable (fun x : SourceCoordinate → ℝ => (x,coordinateRotate θ n x)) :=
    measurable_id.prodMk (coordinateRotate_preserving θ n).measurable
  rw [Measure.map_map (sourceSamplingEndpoint_measurable r) hp]
  cases r
  · exact Measure.map_id
  · change (sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ x))).map
      (coordinateRotate θ n) = _
    have hw : Measurable (fun x => ENNReal.ofReal
        (sourceSamplingProduct stage false (fun i => decide (i ∈ I)) E G n θ x)) :=
      (((sourceSamplingProduct_measurable stage false (fun i => decide (i ∈ I)) E G hE hG n).comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal)
    rw [sourceSamplingHaar_rotate_withDensity θ n _ hw]
    apply withDensity_congr_ae
    filter_upwards [sourceSamplingHaar_cube] with y hy
    rw [sourceSamplingProduct_second_inverse I stage E G θ y n hy]

/-- Averaging commutes with rectangle restriction and either endpoint map.
The density is the previously estimated empirical function, exactly. -/
theorem sourceSamplingUntrimmed_tested_marginal (I : Finset SourceCoordinate) (stage : ℕ)
    (r : Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) :
    ((sourceSamplingUntrimmed I stage θ).restrict (sourceSamplingRectangle E G)).map
        (sourceSamplingEndpoint r) =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
        (sourceSamplingEmpiricalDensity stage r (fun i => decide (i ∈ I)) E G θ x)) := by
  let S := sourceSamplingPowers stage
  let c : ℝ≥0∞ := ENNReal.ofReal (1/((sourceSamplingPowers stage).card : ℝ))
  let w := fun n => sourceSamplingProduct stage r (fun i => decide (i ∈ I)) E G n θ
  have hrep : (fun x => ENNReal.ofReal (sourceSamplingEmpiricalDensity stage r
      (fun i => decide (i ∈ I)) E G θ x)) =
      (fun x => c*∑ n ∈ S, ENNReal.ofReal (w n x)) := by
    funext x
    simp only [sourceSamplingEmpiricalDensity]
    rw [div_eq_mul_inv,mul_comm,← one_div,ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun n _ => (sourceSamplingProduct_bounds stage r
        (fun i => decide (i ∈ I)) E G n θ x).1)]
  rw [hrep]
  have hf := sourceSamplingEndpoint_measurable r
  have hR := sourceSamplingRectangle_measurable E G hE hG
  ext A hA
  rw [Measure.map_apply hf hA,Measure.restrict_apply (hf hA)]
  unfold sourceSamplingUntrimmed
  rw [Measure.smul_apply,Measure.finsetSum_apply,withDensity_apply _ hA]
  have hterm (n : ℤ) : sourceSamplingSummand I stage θ n
      (sourceSamplingEndpoint r ⁻¹' A ∩ sourceSamplingRectangle E G) =
      ∫⁻ x in A, ENNReal.ofReal (w n x) ∂sourceSamplingHaar := by
    rw [← Measure.restrict_apply (hf hA),← Measure.map_apply hf hA,
      sourceSamplingSummand_tested_marginal I stage r E G hE hG houtside θ n]
    exact withDensity_apply _ hA
  simp only [hterm,smul_eq_mul]
  rw [lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  congr 1
  exact (lintegral_finsetSum S (fun n _ =>
    (((sourceSamplingProduct_measurable stage r (fun i => decide (i ∈ I)) E G hE hG n).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal))).symm

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

theorem sourceSamplingRationalTests_outside (T : SourceSamplingRationalTest) (stage : ℕ)
    (hK : T.1 ⊆ sourceSamplingPrefix stage) :
    ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ sourceSamplingRationalX T i ∧
      Set.Ico (0 : ℝ) 1 ⊆ sourceSamplingRationalY T i := by
  intro i hi
  have hnot : i ∉ T.1 := fun h => hi (hK h)
  simp only [sourceSamplingRationalX,sourceSamplingRationalY,sourceSamplingRationalEndpoints,
    dite_eq_right hnot,Rat.cast_zero,Rat.cast_one]
  exact ⟨Set.Ico_subset_Icc_self,Set.Ico_subset_Icc_self⟩

theorem sourceSamplingPrefix_eventually_covers (K : Finset SourceCoordinate) :
    ∀ᶠ stage : ℕ in atTop, K ⊆ sourceSamplingPrefix stage := by
  filter_upwards [eventually_ge_atTop (K.sup (fun i => i.1))] with stage hstage
  intro i hi
  apply (CouplingParameters.mem_blockPrefix sourceBlockSize (stage+1) i).mpr
  exact Nat.lt_succ_of_le ((Finset.le_sup (f := fun i => i.1) hi).trans hstage)

/-- A concrete single conull event for every finite I, both orientations, and
all rational cylinder tests. It includes the actual tested measure identity
at every admissible stage, as well as the full-error convergence and L2 bound. -/
theorem sourceSampling_rational_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (r : Bool)
      (T : SourceSamplingRationalTest),
      Tendsto (fun stage => sourceSamplingSquaredError stage r (fun i => decide (i ∈ I))
        (sourceSamplingRationalX T) (sourceSamplingRationalY T) θ) atTop (𝓝 0) ∧
      ∃ C : ℝ, ∀ stage,
        MemLp (sourceSamplingEmpiricalDensity stage r (fun i => decide (i ∈ I))
          (sourceSamplingRationalX T) (sourceSamplingRationalY T) θ) 2 sourceSamplingHaar ∧
        (∫ x, sourceSamplingEmpiricalDensity stage r (fun i => decide (i ∈ I))
          (sourceSamplingRationalX T) (sourceSamplingRationalY T) θ x ^ 2 ∂sourceSamplingHaar) ≤ C ∧
        (T.1 ⊆ sourceSamplingPrefix stage →
          ((sourceSamplingUntrimmed I stage θ).restrict
            (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).map
              (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal
            (sourceSamplingEmpiricalDensity stage r (fun i => decide (i ∈ I))
              (sourceSamplingRationalX T) (sourceSamplingRationalY T) θ x))) := by
  apply ae_all_iff.mpr
  intro I
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro T
  filter_upwards [sourceSamplingSquaredError_ae r (fun i => decide (i ∈ I))
    (fun i => (sourceSamplingRationalEndpoints T i).1.1)
    (fun i => (sourceSamplingRationalEndpoints T i).1.2)
    (fun i => (sourceSamplingRationalEndpoints T i).2.1)
    (fun i => (sourceSamplingRationalEndpoints T i).2.2),
    sourceSamplingEmpiricalDensity_uniform r (fun i => decide (i ∈ I))
    (fun i => (sourceSamplingRationalEndpoints T i).1.1)
    (fun i => (sourceSamplingRationalEndpoints T i).1.2)
    (fun i => (sourceSamplingRationalEndpoints T i).2.1)
    (fun i => (sourceSamplingRationalEndpoints T i).2.2)] with θ he hu
  obtain ⟨C,hC⟩ := hu
  refine ⟨he.2,C,fun stage => ⟨(hC stage).1,(hC stage).2,?_⟩⟩
  intro hK
  exact sourceSamplingUntrimmed_tested_marginal I stage r _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
    (sourceSamplingRationalTests_outside T stage hK) θ

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_DiagonalLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingWidth_tendsto : Tendsto sourceSamplingWidth atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3/5)).comp
    (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  convert hh using 1
  funext stage
  simp only [sourceSamplingWidth,Function.comp_apply]
  congr 1; norm_num

theorem sourceSamplingCutoff_tendsto : Tendsto sourceSamplingCutoff atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).comp
    (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  exact hh

theorem sampling_interval_small_displacement (s a c t : ℝ)
    (_ha : s ≠ a) (hc : s ≠ c) (ht : 0 ≤ t)
    (hta : t < |s-a|) (htc : t < |s-c|) :
    s+t ∈ Set.Icc a c ↔ s ∈ Set.Icc a c := by
  have hleft : a ≤ s+t ↔ a ≤ s := by
    by_cases h : a ≤ s
    · constructor
      · exact fun _ => h
      · intro _; linarith
    · rw [abs_of_neg (by linarith : s-a < 0)] at hta
      constructor <;> intro hh <;> linarith
  have hright : s+t ≤ c ↔ s ≤ c := by
    by_cases h : s ≤ c
    · have hsc : s < c := lt_of_le_of_ne h hc
      rw [abs_of_neg (by linarith : s-c < 0)] at htc
      constructor <;> intro hh <;> linarith
    · constructor <;> intro hh <;> linarith
  exact and_congr hleft hright

/-- Away from the interval endpoints, a sufficiently short retained diagonal
step has exactly the same interval test as its starting coordinate. -/
theorem samplingTestedFirstDensity_diagonal_exact (h α s a c : ℝ) (E : Set ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (hcut : α ≤ samplingDistance s)
    (ha : s ≠ a) (hc : s ≠ c) (hha : h < |s-a|) (hhc : h < |s-c|) :
    samplingTestedFirstDensity false h α E (Set.Icc a c) s =
      if s ∈ E ∧ s ∈ Set.Icc a c then 1 else 0 := by
  have he (t : ℝ) : samplingTestedFirstWeight false h α E (Set.Icc a c) s t =
      if s ∈ E ∧ s ∈ Set.Icc a c then samplingWeight false h α s t else 0 := by
    by_cases hw : samplingWeight false h α s t = 0
    · simp [samplingTestedFirstWeight,hw]
    · have ho := samplingWeight_orders false h α s t hh hh1 hα hs hw
      have hsp : 0 < t ∧ t < h*samplingDistance s := by
        unfold samplingWeight at hw
        simp only [Bool.false_eq_true,ite_false] at hw
        split_ifs at hw with hcond
        · exact hcond.2
        · exact False.elim (hw rfl)
      have hd : samplingDistance s ≤ 1 := (min_le_right s (1-s)).trans (by linarith [hs.1])
      have hth : t < h := hsp.2.trans_le (by nlinarith)
      have hmem := sampling_interval_small_displacement s a c t ha hc hsp.1.le
        (hth.trans hha) (hth.trans hhc)
      simp only [samplingTestedFirstWeight,ho.1,hmem]
  unfold samplingTestedFirstDensity
  simp_rw [he]
  by_cases htest : s ∈ E ∧ s ∈ Set.Icc a c
  · simp only [ite_eq_left htest]
    simpa only [Bool.false_eq_true,ite_false,ite_eq_left hcut] using
      samplingWeight_first_integral false h α s hh hh1 hα hs
  · simp only [ite_eq_right htest,integral_zero]

/-- At each interior starting point away from the two tested endpoints, the
actual diagonal density eventually equals the uniform diagonal test. -/
theorem sourceSampling_diagonal_eventually (s a c : ℝ) (E : Set ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ha : s ≠ a) (hc : s ≠ c) :
    ∀ᶠ stage in atTop,
      samplingTestedFirstDensity false (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s = if s ∈ E ∧ s ∈ Set.Icc a c then 1 else 0 := by
  have hd : 0 < samplingDistance s := lt_min hs.1 (by linarith [hs.2])
  have hcut := sourceSamplingCutoff_tendsto.eventually (gt_mem_nhds hd)
  have hwa := sourceSamplingWidth_tendsto.eventually (gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr ha)))
  have hwc := sourceSamplingWidth_tendsto.eventually (gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr hc)))
  filter_upwards [hcut,hwa,hwc] with stage hcut hwa hwc
  have hp := sourceSampling_parameters stage
  exact samplingTestedFirstDensity_diagonal_exact _ _ s a c E hp.1 hp.2.1 hp.2.2
    ⟨hs.1.le,hs.2⟩ hcut.le ha hc hwa hwc

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_DiagonalIntegral
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- The actual one-coordinate diagonal model converges to uniform diagonal
mass on every measurable first test and closed-interval second test. -/
theorem sourceSampling_diagonal_integral_tendsto (E : Set ℝ) (hE : MeasurableSet E) (a c : ℝ) :
    Tendsto (fun stage => ∫ s,
      samplingTestedFirstDensity false (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s ∂unitIntervalMeasure)
      atTop (𝓝 ((unitIntervalMeasure (E ∩ Set.Icc a c)).toReal)) := by
  have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  let f : ℝ → ℝ := (E ∩ Set.Icc a c).indicator (fun _ => 1)
  have hlim : ∀ᵐ s ∂unitIntervalMeasure,
      Tendsto (fun stage => samplingTestedFirstDensity false
        (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E (Set.Icc a c) s)
        atTop (𝓝 (f s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico,unitIntervalMeasure.ae_ne 0,
      unitIntervalMeasure.ae_ne a,unitIntervalMeasure.ae_ne c] with s hs hs0 hsa hsc
    have hh := sourceSampling_diagonal_eventually s a c E ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),hs.2⟩ hsa hsc
    have he : (fun stage => samplingTestedFirstDensity false (sourceSamplingWidth stage)
        (sourceSamplingCutoff stage) E (Set.Icc a c) s) =ᶠ[atTop] (fun _ => f s) := by
      filter_upwards [hh] with stage hstage
      simpa only [f,Set.indicator_apply,Set.mem_inter_iff] using hstage
    exact tendsto_const_nhds.congr' he.symm
  have hm (stage : ℕ) : AEStronglyMeasurable
      (samplingTestedFirstDensity false (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c)) unitIntervalMeasure := (samplingTestedFirstDensity_measurable false
    (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E (Set.Icc a c) hE measurableSet_Icc).aestronglyMeasurable
  have hb (stage : ℕ) : ∀ᵐ s ∂unitIntervalMeasure,
      ‖samplingTestedFirstDensity false (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    have hp := sourceSampling_parameters stage
    have h := samplingTestedFirstDensity_bounds false _ _ E (Set.Icc a c)
      hp.1 hp.2.1 hp.2.2 hE measurableSet_Icc s hs
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2
  have ht := tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ)) hm (integrable_const 1) hb hlim
  have hf : (∫ s, f s ∂unitIntervalMeasure) = (unitIntervalMeasure (E ∩ Set.Icc a c)).toReal := by
    rw [integral_indicator (hE.inter measurableSet_Icc)]
    simp [measureReal_def]
  rwa [hf] at ht

/-- Triangular tested factors are independent of the sampling width and cutoff. -/
theorem samplingTestedFirstDensity_triangular_parameters (h α h' α' s : ℝ) (E G : Set ℝ) :
    samplingTestedFirstDensity true h α E G s = samplingTestedFirstDensity true h' α' E G s := by
  unfold samplingTestedFirstDensity samplingTestedFirstWeight samplingWeight
  simp only [ite_true]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CutoffMass
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

/-- Exact whole-circle first density, including the retained cutoff. -/
theorem samplingTestedFirstDensity_whole (b : Bool) (h α s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedFirstDensity b h α (Set.Icc 0 1) (Set.Icc 0 1) s =
      if b then 1-s else if α ≤ samplingDistance s then 1 else 0 := by
  have he : samplingTestedFirstDensity b h α (Set.Icc 0 1) (Set.Icc 0 1) s =
      ∫ t, samplingWeight b h α s t ∂unitIntervalMeasure := by
    apply integral_congr_ae
    filter_upwards [] with t
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1,hs.2.le⟩
    have ht' : Int.fract (s+t) ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
    simp only [samplingTestedFirstWeight,hs',ht',and_self,ite_true]
  exact he.trans (samplingWeight_first_integral b h α s hh hh1 hα hs)

/-- The exact lost mass of one untested diagonal coordinate is 2α. -/
theorem sampling_diagonal_whole_mass (h α : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hα1 : α ≤ 1/2) :
    (∫ s, samplingTestedFirstDensity false h α (Set.Icc 0 1) (Set.Icc 0 1) s ∂unitIntervalMeasure) = 1-2*α := by
  have he : samplingTestedFirstDensity false h α (Set.Icc 0 1) (Set.Icc 0 1) =ᵐ[unitIntervalMeasure]
      (Set.Icc α (1-α)).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    rw [samplingTestedFirstDensity_whole false h α s hh hh1 hα hs]
    have hc : α ≤ samplingDistance s ↔ s ∈ Set.Icc α (1-α) := by
      simp only [samplingDistance,le_min_iff,Set.mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    simp only [Bool.false_eq_true,ite_false,hc,Set.indicator_apply]
  rw [integral_congr_ae he,integral_indicator measurableSet_Icc,integral_const]
  have hsub : Set.Icc α (1-α) ⊆ Set.Ico (0 : ℝ) 1 := by
    intro s hs
    exact ⟨hα.le.trans hs.1,hs.2.trans_lt (by linarith)⟩
  simp only [measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    smul_eq_mul,mul_one]
  unfold unitIntervalMeasure
  rw [Measure.restrict_apply measurableSet_Icc,Set.inter_eq_left.mpr hsub,Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

/-- The total cutoff budget tends to zero despite the growing dimension. -/
theorem sourceSampling_cutoff_budget_tendsto :
    Tendsto (fun stage => 2*((sourceSamplingPrefix stage).card : ℝ)*sourceSamplingCutoff stage)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun stage => (101/50 : ℝ)*(sourceBlockSize stage : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)).const_mul (101/50 : ℝ)
  apply squeeze_zero (fun stage => by have := (sourceSampling_parameters stage).2.2; positivity) _ ht
  intro stage
  have hm := sourceBlockSize_pos stage
  calc
    _ ≤ 2*((101/100 : ℝ)*sourceBlockSize stage)*sourceSamplingCutoff stage := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sourceSamplingPrefix_card_bound stage) (by norm_num))
        (sourceSampling_parameters stage).2.2.le
    _ = (101/50 : ℝ)*(sourceBlockSize stage : ℝ)⁻¹ := by
      simp only [sourceSamplingCutoff,Real.rpow_neg hm.le,Real.rpow_two]
      field_simp
      ring

/-- Any subset of untested coordinates retains asymptotically all its mass.
The estimate uses its actual varying cardinality, bounded by the prefix. -/
theorem sourceSampling_untested_mass_tendsto (k : ℕ → ℕ)
    (hk : ∀ stage, k stage ≤ (sourceSamplingPrefix stage).card) :
    Tendsto (fun stage => (1-2*sourceSamplingCutoff stage)^(k stage)) atTop (𝓝 1) := by
  have he : ∀ stage, |(1-2*sourceSamplingCutoff stage)^(k stage)-1| ≤
      2*((sourceSamplingPrefix stage).card : ℝ)*sourceSamplingCutoff stage := by
    intro stage
    have hα := (sourceSampling_parameters stage).2.2
    have hα1 := sourceSamplingCutoff_le_half stage
    have hlo : 0 ≤ 1-2*sourceSamplingCutoff stage := by linarith
    have hup : (1-2*sourceSamplingCutoff stage)^(k stage) ≤ 1 := pow_le_one₀ hlo (by linarith)
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(2*sourceSamplingCutoff stage) by linarith) (k stage)
    have hk' : (k stage : ℝ) ≤ (sourceSamplingPrefix stage).card := by exact_mod_cast hk stage
    rw [abs_of_nonpos (by linarith)]
    have hm := mul_le_mul_of_nonneg_right hk' (show 0 ≤ 2*sourceSamplingCutoff stage by positivity)
    simp only [mul_neg,← sub_eq_add_neg] at hb
    nlinarith
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun stage => abs_nonneg _) he sourceSampling_cutoff_budget_tendsto

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_RectangleError
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

/-- The elementary probability-space Cauchy--Schwarz bound, proved by
integrating the nonnegative square centered at the mean. -/
theorem sampling_integral_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x^2) μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, f x^2 ∂μ := by
  let c := ∫ x, f x ∂μ
  have he : (fun x => (f x-c)^2) = (fun x => f x^2-2*c*f x+c^2) := by funext x; ring
  have hh : 0 ≤ ∫ x, (f x-c)^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hi : Integrable (fun x => f x^2-2*c*f x) μ := hf2.sub (hf.const_mul (2*c))
  have hc : Integrable (fun _x : Ω => c^2) μ := integrable_const _
  rw [he,integral_add hi hc,integral_sub hf2 (hf.const_mul (2*c)),integral_const_mul] at hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hh
  change c^2 ≤ _
  change 0 ≤ (∫ x, f x^2 ∂μ)-2*c*c+c^2 at hh
  nlinarith

/-- Actual rectangle mass equals the integral of the first tested empirical
density at every admissible stage. -/
theorem sourceSamplingUntrimmed_rectangle_mass (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) :
    ((sourceSamplingUntrimmed I stage θ) (sourceSamplingRectangle E G)).toReal =
      ∫ x, sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I)) E G θ x
        ∂sourceSamplingHaar := by
  let z := sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I)) E G θ
  have hm := sourceSamplingEmpiricalDensity_measurable stage false (fun i => decide (i ∈ I)) E G hE hG θ
  have hb := sourceSamplingEmpiricalDensity_bounds stage false (fun i => decide (i ∈ I)) E G θ
  have hi : Integrable z sourceSamplingHaar :=
    sampling_integrable_bounded sourceSamplingHaar z hm _ (fun x => by
      rw [abs_of_nonneg (hb x).1]; exact (hb x).2)
  have hh := congrArg (fun ν : Measure (SourceCoordinate → ℝ) => ν Set.univ)
    (sourceSamplingUntrimmed_tested_marginal I stage false E G hE hG houtside θ)
  rw [Measure.map_apply (sourceSamplingEndpoint_measurable false) MeasurableSet.univ,
    Set.preimage_univ,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  rw [hh,← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => (hb x).1)),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (hb x).1))]

/-- Full squared sampling error bounds the squared discrepancy of the actual
rectangle mass and the ideal product integral. -/
theorem sourceSamplingUntrimmed_rectangle_error (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (houtside : ∀ i ∉ sourceSamplingPrefix stage,
      Set.Ico (0 : ℝ) 1 ⊆ E i ∧ Set.Ico (0 : ℝ) 1 ⊆ G i)
    (θ : SourceCoordinate → ℝ) :
    (((sourceSamplingUntrimmed I stage θ) (sourceSamplingRectangle E G)).toReal -
      ∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I)) E G x ∂sourceSamplingHaar)^2 ≤
    sourceSamplingSquaredError stage false (fun i => decide (i ∈ I)) E G θ := by
  rw [sourceSamplingUntrimmed_rectangle_mass I stage E G hE hG houtside θ]
  let z := sourceSamplingEmpiricalDensity stage false (fun i => decide (i ∈ I)) E G θ
  let g := sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I)) E G
  let C := (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card
  have hzm := sourceSamplingEmpiricalDensity_measurable stage false (fun i => decide (i ∈ I)) E G hE hG θ
  have hgm := sourceSamplingIdealDensity_measurable stage false (fun i => decide (i ∈ I)) E G hE hG
  have hzb := sourceSamplingEmpiricalDensity_bounds stage false (fun i => decide (i ∈ I)) E G θ
  have hgb := sourceSamplingIdealDensity_bounds stage false (fun i => decide (i ∈ I)) E G hE hG
  have hzi : Integrable z sourceSamplingHaar := sampling_integrable_bounded sourceSamplingHaar z hzm C
    (fun x => by rw [abs_of_nonneg (hzb x).1]; exact (hzb x).2)
  have hgi : Integrable g sourceSamplingHaar := sampling_integrable_bounded sourceSamplingHaar g hgm C
    (fun x => by rw [abs_of_nonneg (hgb x).1]; exact (hgb x).2)
  have hei : Integrable (fun x => (z x-g x)^2) sourceSamplingHaar := by
    apply sampling_integrable_bounded sourceSamplingHaar _ ((hzm.sub hgm).pow_const 2) (C^2)
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    have hz' : 0 ≤ z x ∧ z x ≤ C := hzb x
    have hg' : 0 ≤ g x ∧ g x ≤ C := hgb x
    change (z x-g x)^2 ≤ C^2
    nlinarith [sq_nonneg (z x+g x),mul_nonneg (show 0 ≤ C-(z x-g x) by linarith)
      (show 0 ≤ C+(z x-g x) by linarith)]
  have hh := sampling_integral_square_le sourceSamplingHaar (fun x => z x-g x) (hzi.sub hgi) hei
  rw [integral_sub hzi hgi] at hh
  exact hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_RectangleApproximation
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

/-- Actual rational rectangle masses approach their ideal product integrals
on a single conull event. This is the stochastic approximation step; the
identification of the ideal limiting law is a separate obligation. -/
theorem sourceSampling_rectangle_approximation_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest),
      Tendsto (fun stage =>
        ((sourceSamplingUntrimmed I stage θ)
          (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal -
        ∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I))
          (sourceSamplingRationalX T) (sourceSamplingRationalY T) x ∂sourceSamplingHaar)
      atTop (𝓝 0) := by
  filter_upwards [sourceSampling_rational_event] with θ hθ
  intro I T
  have he := (hθ I false T).1
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp he
  simp only [Real.sqrt_zero] at hs
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall (fun stage => abs_nonneg _)) _ hs
  filter_upwards [sourceSamplingPrefix_eventually_covers T.1] with stage hstage
  exact Real.abs_le_sqrt (sourceSamplingUntrimmed_rectangle_error I stage
    (sourceSamplingRationalX T) (sourceSamplingRationalY T)
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
    (sourceSamplingRationalTests_outside T stage hstage) θ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_IdealRectangleLimit
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

/-- Exact finite-coordinate factorization of the first ideal integral. -/
theorem sourceSamplingIdealDensity_integral (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I)) E G x ∂sourceSamplingHaar) =
      ∏ i ∈ sourceSamplingPrefix stage, ∫ s,
        samplingTestedFirstDensity (decide (i ∈ I)) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (E i) (G i) s ∂unitIntervalMeasure := by
  exact integral_infinitePi_finset_prod _ _ _ (fun i =>
    samplingTestedFirstDensity_measurable (decide (i ∈ I)) _ _ (E i) (G i) (hE i) (hG i))

/-- Tests and triangular coordinates occupy a fixed finite set. Every other
prefix coordinate contributes its exact retained mass, 1-2α. -/
theorem sourceSamplingIdeal_rectangle_split (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (stage : ℕ) (hK : I ∪ T.1 ⊆ sourceSamplingPrefix stage) :
    (∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I))
      (sourceSamplingRationalX T) (sourceSamplingRationalY T) x ∂sourceSamplingHaar) =
    (∏ i ∈ I ∪ T.1, ∫ s,
      samplingTestedFirstDensity (decide (i ∈ I)) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure) *
    (1-2*sourceSamplingCutoff stage)^((sourceSamplingPrefix stage \ (I ∪ T.1)).card) := by
  rw [sourceSamplingIdealDensity_integral I stage (sourceSamplingRationalX T) (sourceSamplingRationalY T) (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)]
  let F := fun i => ∫ s, samplingTestedFirstDensity (decide (i ∈ I)) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure
  have hf (i : SourceCoordinate) (hi : i ∈ sourceSamplingPrefix stage \ (I ∪ T.1)) :
      F i = 1-2*sourceSamplingCutoff stage := by
    have hnot := (Finset.mem_sdiff.mp hi).2
    have hI : i ∉ I := fun h => hnot (Finset.mem_union_left _ h)
    have hT : i ∉ T.1 := fun h => hnot (Finset.mem_union_right _ h)
    simp only [F,decide_eq_false hI,sourceSamplingRationalX,sourceSamplingRationalY,
      sourceSamplingRationalEndpoints,dite_eq_right hT,Rat.cast_zero,Rat.cast_one]
    have hp := sourceSampling_parameters stage
    exact sampling_diagonal_whole_mass _ _ hp.1 hp.2.1 hp.2.2 (sourceSamplingCutoff_le_half stage)
  have hp := Finset.prod_sdiff hK (f := F)
  rw [Finset.prod_congr rfl hf,Finset.prod_const] at hp
  simpa only [mul_comm] using hp.symm

/-- The deterministic ideal product limit includes all growing-prefix cutoff
losses and has exactly the tested diagonal-coordinate limits. -/
theorem sourceSamplingIdeal_rectangle_tendsto (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) :
    Tendsto (fun stage => ∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I))
      (sourceSamplingRationalX T) (sourceSamplingRationalY T) x ∂sourceSamplingHaar)
      atTop (𝓝 (sourceSamplingLimitRectangleMass I T)) := by
  let F := fun stage i => ∫ s, samplingTestedFirstDensity (decide (i ∈ I)) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure
  have hcoord (i : SourceCoordinate) : Tendsto (fun stage => F stage i) atTop
      (𝓝 (if i ∈ I then ∫ s, samplingTestedFirstDensity true (sourceSamplingWidth 0) (sourceSamplingCutoff 0)
        (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure
      else (unitIntervalMeasure (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i)).toReal)) := by
    by_cases hi : i ∈ I
    · simp only [ite_eq_left hi,F,decide_eq_true hi]
      have he (stage : ℕ) : (∫ s, samplingTestedFirstDensity true (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure) =
        ∫ s, samplingTestedFirstDensity true (sourceSamplingWidth 0) (sourceSamplingCutoff 0)
          (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun s => samplingTestedFirstDensity_triangular_parameters _ _ _ _ _ _ _)
      simp_rw [he]
      exact tendsto_const_nhds
    · simp only [ite_eq_right hi,F,decide_eq_false hi]
      exact sourceSampling_diagonal_integral_tendsto _ measurableSet_Icc _ _
  have hfixed := tendsto_finsetProd (I ∪ T.1) (fun i _ => hcoord i)
  have htail := sourceSampling_untested_mass_tendsto
    (fun stage => (sourceSamplingPrefix stage \ (I ∪ T.1)).card)
    (fun stage => Finset.card_le_card Finset.sdiff_subset)
  have hall := hfixed.mul htail
  simp only [mul_one] at hall
  apply hall.congr'
  filter_upwards [sourceSamplingPrefix_eventually_covers (I ∪ T.1)] with stage hstage
  exact (sourceSamplingIdeal_rectangle_split I T stage hstage).symm

/-- Actual untrimmed rational rectangle masses converge to the explicit
triangular/diagonal product value on one conull event for all I and tests. -/
theorem sourceSampling_rectangle_limit_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest),
      Tendsto (fun stage => ((sourceSamplingUntrimmed I stage θ)
        (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal)
        atTop (𝓝 (sourceSamplingLimitRectangleMass I T)) := by
  filter_upwards [sourceSampling_rectangle_approximation_event] with θ hθ
  intro I T
  have hh := (hθ I T).add (sourceSamplingIdeal_rectangle_tendsto I T)
  simpa only [sub_add_cancel,zero_add] using hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TriangleLaw
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal Topology
noncomputable section

/-- The actual triangular phase weight is precisely the order indicator
of the rotated endpoint, on the Haar representatives. -/
theorem samplingWeight_triangular_order (h α s t : ℝ)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingWeight true h α s t = if s < Int.fract (s+t) then 1 else 0 := by
  by_cases hst : s+t < 1
  · have hf : Int.fract (s+t) = s+t := Int.fract_eq_self.mpr ⟨by linarith [hs.1,ht.1],hst⟩
    simp only [samplingWeight,ite_true,hf]
    have he : (0 < t ∧ t < 1-s) ↔ s < s+t := by
      constructor
      · intro h; linarith [h.1]
      · intro h; constructor <;> linarith
    simp only [he]
  · have hf : ⌊s+t⌋ = (1 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith [hs.2,ht.2]⟩
    have hn : ¬ (0 < t ∧ t < 1-s) := by intro h; linarith [h.2]
    have ho : ¬ s < Int.fract (s+t) := by rw [Int.fract,hf]; norm_num; linarith [ht.2]
    simp only [samplingWeight,ite_true,ite_eq_right hn,ite_eq_right ho]

/-- The first tested triangular density is its actual vertical section of
Lebesgue measure on 0≤x<y<1. No triangular marginal identity is assumed. -/
theorem samplingTestedFirstDensity_triangular_section (h α s : ℝ) (E G : Set ℝ)
    (hG : MeasurableSet G) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    samplingTestedFirstDensity true h α E G s =
      ∫ y, (if s ∈ E ∧ y ∈ G ∧ s < y then (1 : ℝ) else 0) ∂unitIntervalMeasure := by
  let F := fun y : ℝ => if s ∈ E ∧ y ∈ G ∧ s < y then (1 : ℝ) else 0
  have hm : Measurable F := by
    apply Measurable.ite _ measurable_const measurable_const
    by_cases htest : s ∈ E
    · simp only [htest,true_and]
      change MeasurableSet (G ∩ {y : ℝ | s < y})
      exact hG.inter (measurableSet_lt measurable_const measurable_id)
    · simp [htest]
  have hp : MeasurePreserving (fun t : ℝ => Int.fract (s+t)) unitIntervalMeasure unitIntervalMeasure := by
    simpa only [add_comm] using unitInterval_rotate_preserving s
  have he : samplingTestedFirstWeight true h α E G s =ᵐ[unitIntervalMeasure]
      (fun t => F (Int.fract (s+t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    rw [samplingTestedFirstWeight,samplingWeight_triangular_order h α s t hs ht]
    simp only [F]
    split_ifs <;> simp_all
  rw [samplingTestedFirstDensity,integral_congr_ae he]
  rw [← integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable,hp.map_eq]

/-- The two-dimensional tested source integral equals the genuine triangular
restriction of product Lebesgue measure. -/
theorem samplingTestedFirstDensity_triangular_mass (h α : ℝ) (E G : Set ℝ)
    (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, samplingTestedFirstDensity true h α E G s ∂unitIntervalMeasure) =
      ((unitIntervalMeasure.prod unitIntervalMeasure)
        {p : ℝ × ℝ | p.1 ∈ E ∧ p.2 ∈ G ∧ p.1 < p.2}).toReal := by
  let A := {p : ℝ × ℝ | p.1 ∈ E ∧ p.2 ∈ G ∧ p.1 < p.2}
  have hA : MeasurableSet A := (hE.preimage measurable_fst).inter
    ((hG.preimage measurable_snd).inter (measurableSet_lt measurable_fst measurable_snd))
  have hm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) (unitIntervalMeasure.prod unitIntervalMeasure) :=
    (integrable_const (1 : ℝ)).indicator hA
  calc
    _ = ∫ s, ∫ y, A.indicator (fun _ => (1 : ℝ)) (s,y) ∂unitIntervalMeasure ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
      simpa only [A,Set.indicator_apply,Set.mem_ofPred_eq] using
        samplingTestedFirstDensity_triangular_section h α s E G hG hs
    _ = ∫ p, A.indicator (fun _ => (1 : ℝ)) p ∂unitIntervalMeasure.prod unitIntervalMeasure :=
      (integral_prod _ hi).symm
    _ = _ := by rw [integral_indicator hA]; simp [measureReal_def,A]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LimitMeasure
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingTriangleSet_measurable (I : Finset SourceCoordinate) :
    MeasurableSet (sourceSamplingTriangleSet I) := by
  simp only [sourceSamplingTriangleSet,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt (measurable_fst.comp (measurable_pi_apply i))
    (measurable_snd.comp (measurable_pi_apply i))

theorem sourceSamplingLimitMap_measurable (I : Finset SourceCoordinate) :
    Measurable (sourceSamplingLimitMap I) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval (fun i => measurable_fst.comp (measurable_pi_apply i))
  · apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ I
    · simpa only [hi,ite_true,Function.comp_def] using measurable_snd.comp (measurable_pi_apply i)
    · simpa only [hi,ite_false,Function.comp_def] using measurable_fst.comp (measurable_pi_apply i)

theorem sourceSamplingPairHaar_cube : ∀ᵐ p ∂sourceSamplingPairHaar,
    ∀ i, (p i).1 ∈ Set.Ico (0 : ℝ) 1 ∧ (p i).2 ∈ Set.Ico (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  have hp : ∀ᵐ z ∂unitIntervalMeasure.prod unitIntervalMeasure,
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ Set.Ico (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ico.prod measurableSet_Ico)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    exact ⟨hx,hy⟩
  have hh : ∀ᵐ z ∂sourceSamplingPairHaar.map (fun p => p i),
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact hp
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hh

/-- The finite rectangle formula for the source limit, written using actual
Lebesgue triangular and diagonal masses. -/
theorem sourceSamplingLimitRectangleMass_formula (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) :
    sourceSamplingLimitRectangleMass I T = ∏ i ∈ I ∪ T.1,
      if i ∈ I then ((unitIntervalMeasure.prod unitIntervalMeasure)
        {p : ℝ × ℝ | p.1 ∈ sourceSamplingRationalX T i ∧
          p.2 ∈ sourceSamplingRationalY T i ∧ p.1 < p.2}).toReal
      else (unitIntervalMeasure (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i)).toReal := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ I
  · simp only [ite_eq_left hi]
    exact samplingTestedFirstDensity_triangular_mass _ _ _ _ measurableSet_Icc measurableSet_Icc
  · simp only [ite_eq_right hi]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LambdaRectangles
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingLambdaTest_measurable (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (i : SourceCoordinate) : MeasurableSet {p | sourceSamplingLambdaTest I T i p} := by
  by_cases hi : i ∈ I
  · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
    exact (measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter (measurableSet_lt measurable_fst measurable_snd))
  · simp only [sourceSamplingLambdaTest,ite_eq_right hi]
    exact (measurableSet_Icc.preimage measurable_fst).inter (measurableSet_Icc.preimage measurable_fst)

/-- The finite coordinate conditions are equivalent to restriction by the
triangle and the full cylinder rectangle on the conull Haar cube. -/
theorem sourceSamplingLambdaTest_iff (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (p : SourceCoordinate → ℝ × ℝ)
    (hp : ∀ i, (p i).1 ∈ Set.Ico (0 : ℝ) 1 ∧ (p i).2 ∈ Set.Ico (0 : ℝ) 1) :
    (∀ i ∈ I ∪ T.1, sourceSamplingLambdaTest I T i (p i)) ↔
      sourceSamplingLimitMap I p ∈ sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T) ∧
      p ∈ sourceSamplingTriangleSet I := by
  constructor
  · intro h
    constructor
    · intro i
      by_cases hi : i ∈ I
      · have hh := h i (Finset.mem_union_left _ hi)
        simp only [sourceSamplingLambdaTest,ite_eq_left hi] at hh
        exact ⟨hh.1,by simpa only [sourceSamplingLimitMap,ite_eq_left hi] using hh.2.1⟩
      · by_cases ht : i ∈ T.1
        · have hh := h i (Finset.mem_union_right _ ht)
          simpa only [sourceSamplingLambdaTest,sourceSamplingLimitMap,ite_eq_right hi] using hh
        · have hx : (p i).1 ∈ Set.Icc (0 : ℝ) 1 := ⟨(hp i).1.1,(hp i).1.2.le⟩
          simpa only [sourceSamplingLimitMap,ite_eq_right hi,sourceSamplingRationalX,sourceSamplingRationalY,
            sourceSamplingRationalEndpoints,dite_eq_right ht,Rat.cast_zero,Rat.cast_one] using And.intro hx hx
    · intro i hi
      have hh := h i (Finset.mem_union_left _ hi)
      simp only [sourceSamplingLambdaTest,ite_eq_left hi] at hh
      exact hh.2.2
  · rintro ⟨hrect,htri⟩ i _
    have hh := hrect i
    by_cases hi : i ∈ I
    · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
      exact ⟨hh.1,by simpa only [sourceSamplingLimitMap,ite_eq_left hi] using hh.2,htri i hi⟩
    · simpa only [sourceSamplingLambdaTest,sourceSamplingLimitMap,ite_eq_right hi] using hh

/-- The constructed infinite-coordinate measure has exactly the rectangle
values previously obtained as sampling limits. -/
theorem sourceSamplingLambda_rectangle (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) :
    ((sourceSamplingLambda I)
      (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal =
      sourceSamplingLimitRectangleMass I T := by
  let R := sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T)
  let C := sourceSamplingLimitMap I ⁻¹' R ∩ sourceSamplingTriangleSet I
  have hR : MeasurableSet R := sourceSamplingRectangle_measurable _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
  have hmap := sourceSamplingLimitMap_measurable I
  have hC : MeasurableSet C := (hmap hR).inter (sourceSamplingTriangleSet_measurable I)
  have he : C.indicator (fun _ => (1 : ℝ)) =ᵐ[sourceSamplingPairHaar]
      (fun p => ∏ i ∈ I ∪ T.1, if sourceSamplingLambdaTest I T i (p i) then (1 : ℝ) else 0) := by
    filter_upwards [sourceSamplingPairHaar_cube] with p hp
    simp only [Finset.prod_ite_zero,Finset.prod_const_one,
      sourceSamplingLambdaTest_iff I T p hp,Set.indicator_apply]
    rfl
  rw [sourceSamplingLambda,Measure.map_apply hmap hR,Measure.restrict_apply (hmap hR)]
  change (sourceSamplingPairHaar C).toReal = _
  calc
    _ = ∫ p, C.indicator (fun _ => (1 : ℝ)) p ∂sourceSamplingPairHaar := by
      rw [integral_indicator hC]; simp [measureReal_def]
    _ = ∫ p, ∏ i ∈ I ∪ T.1, if sourceSamplingLambdaTest I T i (p i) then (1 : ℝ) else 0
        ∂sourceSamplingPairHaar := integral_congr_ae he
    _ = ∏ i ∈ I ∪ T.1, ∫ z, (if sourceSamplingLambdaTest I T i z then (1 : ℝ) else 0)
        ∂unitIntervalMeasure.prod unitIntervalMeasure :=
      integral_infinitePi_finset_prod _ _ _ (fun i =>
        Measurable.ite (sourceSamplingLambdaTest_measurable I T i) measurable_const measurable_const)
    _ = _ := by
      rw [sourceSamplingLimitRectangleMass_formula]
      apply Finset.prod_congr rfl
      intro i _
      have hA := sourceSamplingLambdaTest_measurable I T i
      have hh : (∫ z, (if sourceSamplingLambdaTest I T i z then (1 : ℝ) else 0)
          ∂unitIntervalMeasure.prod unitIntervalMeasure) =
          ((unitIntervalMeasure.prod unitIntervalMeasure) {z | sourceSamplingLambdaTest I T i z}).toReal := by
        change (∫ z, {z | sourceSamplingLambdaTest I T i z}.indicator (fun _ => (1 : ℝ)) z
          ∂unitIntervalMeasure.prod unitIntervalMeasure) = _
        rw [integral_indicator hA]; simp [measureReal_def]
      rw [hh]
      by_cases hi : i ∈ I
      · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
      · simp only [sourceSamplingLambdaTest,ite_eq_right hi]
        have heq : {z : ℝ × ℝ | z.1 ∈ sourceSamplingRationalX T i ∧ z.1 ∈ sourceSamplingRationalY T i} =
            (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i) ×ˢ Set.univ := by ext z; simp
        rw [heq,Measure.prod_prod]
        simp

/-- Actual untrimmed measures converge to the actual source limiting measure
on every rational cylinder rectangle, on a single conull event. -/
theorem sourceSamplingLambda_rectangle_limit_event_oai :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest),
      Tendsto (fun stage => ((sourceSamplingUntrimmed I stage θ)
        (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal)
        atTop (𝓝 (((sourceSamplingLambda I)
          (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal)) := by
  filter_upwards [sourceSampling_rectangle_limit_event] with θ hθ
  intro I T
  rw [sourceSamplingLambda_rectangle]
  exact hθ I T

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceSamplingLambda_rectangle_limit_event_oai := @OAI.FiniteFactor.sourceSamplingLambda_rectangle_limit_event_oai
