-- Prove2me | solution 1 for OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:55:01.60625+00:00
-- url     : https://prove2.me/submissions/cad3599b-8993-4263-be10-c02d324873a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_constrainedFieldValue_magneticBias
import Theorems.Thm_OAI_InvariantIsing_fieldBiasMean_magneticBias

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianTransformLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact one-step Gaussian operator laws used to propagate the radial
comparison through the finite Ising field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_gaussian_integral_reflect (v : ℝ≥0) (z : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (hEven : Function.Even F) :
    (∫ u, F u ∂gaussianReal (-z) v) = ∫ u, F u ∂gaussianReal z v := by
  have hm : (gaussianReal z v).map (fun u => -u) = gaussianReal (-z) v :=
    gaussianReal_map_neg

  rw [← hm, integral_map measurable_neg.aemeasurable hF.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall hEven)

lemma gaussianOperator_even (ζ : ℝ) (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hEven : Function.Even F) :
    Function.Even (gaussianOperator ζ v F) := by
  intro z
  by_cases hζ : ζ = 0
  · subst ζ
    rw [gaussianOperator_eq_gaussian_integral v hF,
      gaussianOperator_eq_gaussian_integral v hF,
      field_gaussian_integral_reflect v z hF hEven]
  · rw [gaussianOperator_eq_gaussian_exp_integral hζ v hF,
      gaussianOperator_eq_gaussian_exp_integral hζ v hF,
      field_gaussian_integral_reflect v z (hF.const_mul ζ).exp
        (fun u => by rw [hEven u])]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMajorantGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp one-step Gaussian estimate for the entropy-domain majorant. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace InvariantIsing

/-- Jensen at exponent zero, under the same actual moment assumptions. -/
lemma mean_le_log_moment_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {F : Ω → ℝ} (hi : Integrable F μ)
    {d : ℝ} (hd : 0 < d) (he : Integrable (fun x => Real.exp (d * F x)) μ) :
    (∫ x, F x ∂μ) ≤ d⁻¹ * Real.log (∫ x, Real.exp (d * F x) ∂μ) := by
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all μ (fun x => mem_univ (d * F x))) (hi.const_mul d) he
  have hl := Real.log_le_log (Real.exp_pos _) hj
  rw [Real.log_exp, integral_const_mul] at hl
  have ht := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hd.le)
  have heq : d⁻¹ * (d * ∫ x, F x ∂μ) = ∫ x, F x ∂μ := by field_simp
  rwa [heq] at ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldScalarOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial order of the actual scalar backward values and physical spin
means, with covariance increments fixed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarValue_even (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (he : Function.Even F) :
    Function.Even (fieldScalarValue L F) := by
  induction L with
  | nil => exact he
  | cons av L ih =>
    have ht (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hr := fieldScalarValue_regular L ht hF hG
    exact gaussianOperator_even av.1 av.2 hr.1 (ih ht)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightChart
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate charts for the exact finite field functional. The charts
use its original Gaussian increments and change a single covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_value (h : FieldStep) (z : ℝ) :
    fieldScalarValue (fieldAllIncrements h) (fun y => Real.log (Real.cosh y)) z -
      h.height (Fin.last h.depth) / 2 = fieldValue h z := by
  unfold fieldScalarValue fieldAllIncrements fieldValue
  rw [← List.foldr_map (f := fun av : ℝ × ℝ≥0 => (av.1, (av.2 : ℝ)))
    (g := fun av f => gaussianOperator av.1 av.2 f), List.map_ofFn]
  rfl

lemma fieldAllIncrements_root (h : FieldStep) :
    fieldAllIncrements h = (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
      scalarFieldIncrements h := by
  unfold fieldAllIncrements scalarFieldIncrements
  rw [List.ofFn_succ]
  congr 1
  apply Prod.ext
  · exact h.first
  · apply Subtype.ext
    simp [fieldIncrement]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldBias
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical mean spin is the bias derivative of the actual finite
field functional, including its zero-exponent root Gaussian step. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldValue_root (h : FieldStep) (b : ℝ) :
    fieldValue h b =
      gaussianOperator 0 (h.height 0)
        (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b -
      h.height (Fin.last h.depth) / 2 := by
  rw [← fieldAllIncrements_value h b, fieldAllIncrements_root]
  rfl

lemma hasDerivAt_fieldValue_bias (h : FieldStep) (b : ℝ) :
    HasDerivAt (fieldValue h) (fieldBiasMean h b) b := by
  have hL := scalarFieldIncrements_positive h
  have hF := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have hD := fieldScalarMean_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth hm field_abs_tanh_le_one
  have hd := hasDerivAt_gaussianOperator 0
    (NNReal.mk (h.height 0) (h.nonneg 0)) hF.1 hF.2 hD.1 zero_le_one hD.2
    (hasDerivAt_fieldScalarLogCosh (scalarFieldIncrements h) hL) b
  refine ((hd.sub_const (h.height (Fin.last h.depth) / 2)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    exact fieldValue_root h z
  · rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldLowerBound
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear bias coercivity for the finite magnetic field functional.
The lower estimate is preserved by the actual Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma affine_le_gaussianOperator {F : ℝ → ℝ} (hF : Measurable F)
    (hG : HasLinearGrowth F) {a : ℝ} (ha : 0 ≤ a) (v : ℝ≥0)
    (m c : ℝ) (hl : ∀ z, m * z + c ≤ F z) (z : ℝ) :
    m * z + c ≤ gaussianOperator a v F z := by
  have hi : Integrable (fun u : ℝ => u) (gaussianReal z v) := IsGaussian.integrable_id
  have hmean : m * z + c ≤ ∫ u, F u ∂gaussianReal z v := by
    calc
      _ = ∫ u, m * u + c ∂gaussianReal z v := by
        rw [integral_add (hi.const_mul m) (integrable_const c),
          integral_const_mul, integral_id_gaussianReal, integral_const]
        simp
      _ ≤ _ := integral_mono ((hi.const_mul m).add (integrable_const c))
        (field_gaussian_linear_integrable v z hF hG) hl
  by_cases ha0 : a = 0
  · subst a
    rwa [gaussianOperator_eq_gaussian_integral v hF]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [gaussianOperator_eq_gaussian_exp_integral ha0 v hF]
    exact hmean.trans (mean_le_log_moment_div (gaussianReal z v)
      (field_gaussian_linear_integrable v z hF hG) hap
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG a))

lemma affine_le_fieldScalarValue (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (m c : ℝ) (hl : ∀ z, m * z + c ≤ F z) (z : ℝ) :
    m * z + c ≤ fieldScalarValue L F z := by
  induction L generalizing z with
  | nil => exact hl z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htail := fieldScalarValue_regular L ht hF hG
    exact affine_le_gaussianOperator htail.1 htail.2 (hL av (List.mem_cons_self)).le
      av.2 m c (ih ht) z

lemma signed_bias_le_logcosh (b : ℝ) :
    b - Real.log 2 ≤ Real.log (Real.cosh b) := by
  have he : Real.exp b ≤ 2 * Real.cosh b := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-b)]
  have hl := Real.log_le_log (Real.exp_pos b) he
  rw [Real.log_exp, Real.log_mul (by norm_num) (Real.cosh_pos b).ne'] at hl
  linarith

lemma fieldValue_bias_lower (h : FieldStep) (b : ℝ) :
    |b| - Real.log 2 - h.height (Fin.last h.depth) / 2 ≤ fieldValue h b := by
  have hL := scalarFieldIncrements_positive h
  have hF := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hplus : ∀ z, (1 : ℝ) * z + -Real.log 2 ≤
      fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) z := by
    apply affine_le_fieldScalarValue _ hL measurable_logCosh logCosh_linearGrowth
    intro z
    simpa only [one_mul, sub_eq_add_neg] using signed_bias_le_logcosh z
  have hminus : ∀ z, (-1 : ℝ) * z + -Real.log 2 ≤
      fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) z := by
    apply affine_le_fieldScalarValue _ hL measurable_logCosh logCosh_linearGrowth
    intro z
    simpa only [Real.cosh_neg, neg_mul, one_mul, sub_eq_add_neg]
      using signed_bias_le_logcosh (-z)
  have hp := affine_le_gaussianOperator hF.1 hF.2 (show (0:ℝ) ≤ 0 from le_rfl)
    (NNReal.mk (h.height 0) (h.nonneg 0)) 1 (-Real.log 2) hplus b
  have hm := affine_le_gaussianOperator hF.1 hF.2 (show (0:ℝ) ≤ 0 from le_rfl)
    (NNReal.mk (h.height 0) (h.nonneg 0)) (-1) (-Real.log 2) hminus b
  change 1 * b + -Real.log 2 ≤ gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b at hp
  change -1 * b + -Real.log 2 ≤ gaussianOperator 0 (h.height 0)
    (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) b at hm
  rw [fieldValue_root]
  rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonpos hb]
    linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldMinimum
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite prescribed-magnetization functional has an attained bias
minimum at every interior magnetization. No optimizer or concavity premise
is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticBiasObjective_lower (h : FieldStep) (s b : ℝ) :
    (1 - |s|) * |b| - Real.log 2 - h.height (Fin.last h.depth) / 2 ≤
      magneticBiasObjective h s b := by
  have hp : b * s ≤ |b| * |s| := by
    simpa only [abs_mul] using le_abs_self (b * s)
  have hl := fieldValue_bias_lower h b
  unfold magneticBiasObjective
  nlinarith

lemma magneticBiasObjective_bddBelow (h : FieldStep) {s : ℝ} (hs : |s| ≤ 1) :
    BddBelow (Set.range (magneticBiasObjective h s)) := by
  refine ⟨-Real.log 2 - h.height (Fin.last h.depth) / 2, ?_⟩
  rintro _ ⟨b, rfl⟩
  have hp : 0 ≤ (1 - |s|) * |b| := mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg b)
  linarith [magneticBiasObjective_lower h s b]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldCurvature
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict bias convexity follows from the positive terminal curvature
and the nonnegative conditional variance terms in the actual recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_pos (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (ha : Measurable a)
    {B : ℝ} (haB : ∀ z, |a z| ≤ B) (hap : ∀ z, 0 < a z) (z : ℝ) :
    0 < fieldSpinTransition ζ v F a z := by
  have hw := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v)
    hF hG ζ
  let μ := (gaussianReal z v).tilted (fun u => ζ * F u)
  have : IsProbabilityMeasure μ := MeasureTheory.isProbabilityMeasure_tilted hw
  have hi : Integrable a μ := (integrable_const B).mono' ha.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using haB u))
  have hs : Function.support a = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hap u).ne'
  change 0 < ∫ u, a u ∂μ
  apply (integral_pos_iff_support_of_nonneg (fun u => (hap u).le) hi).mpr
  rw [hs, measure_univ]
  exact (zero_lt_one : (0 : ENNReal) < 1)

lemma fieldScalarLogCoshSecond_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    0 < fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
      (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => exact one_div_pos.mpr (sq_pos_of_pos (Real.cosh_pos z))
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hs := fieldScalarLogCoshSecond_regular L ht
    have hp := fieldSpinTransition_pos av.1 av.2 hv.1 hv.2 hs.1 hs.2 (ih ht) z
    have hm : Measurable Real.tanh := by
      change Measurable (fun z : ℝ => Real.tanh z)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hc := fieldSpinTransition_square_le av.1 av.2 hv.1 hv.2 ha.1 ha.2 z
    have hζ := (hL av List.mem_cons_self).le
    change 0 < fieldSpinTransition av.1 av.2 _ _ z + av.1 *
      (fieldSpinTransition av.1 av.2 _ _ z - (fieldScalarMean (av :: L) _ _ z) ^ 2)
    exact add_pos_of_pos_of_nonneg hp (mul_nonneg hζ (sub_nonneg.mpr hc))

lemma fieldBiasCurvature_pos (h : FieldStep) (b : ℝ) : 0 < fieldBiasCurvature h b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hs := fieldScalarLogCoshSecond_regular (scalarFieldIncrements h) hL
  exact fieldSpinTransition_pos 0 _ hv.1 hv.2 hs.1 hs.2
    (fieldScalarLogCoshSecond_pos (scalarFieldIncrements h) hL) b

lemma hasDerivAt_fieldBiasMean (h : FieldStep) (b : ℝ) :
    HasDerivAt (fieldBiasMean h) (fieldBiasCurvature h b) b := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have ha := fieldScalarMean_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth hm field_abs_tanh_le_one
  have hs := fieldScalarLogCoshSecond_regular (scalarFieldIncrements h) hL
  have hd := hasDerivAt_fieldSpinTransition 0
    (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 hv.2 ha.1 ha.1 hs.1
    zero_le_one zero_le_one ha.2 ha.2 hs.2
    (hasDerivAt_fieldScalarLogCosh (scalarFieldIncrements h) hL)
    (hasDerivAt_fieldScalarLogCoshMean (scalarFieldIncrements h) hL) b
  simpa only [zero_mul, add_zero, fieldBiasMean, fieldBiasCurvature] using hd

lemma strictMono_fieldBiasMean (h : FieldStep) : StrictMono (fieldBiasMean h) := by
  apply strictMono_of_deriv_pos
  intro b
  rw [(hasDerivAt_fieldBiasMean h b).deriv]
  exact fieldBiasCurvature_pos h b

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldParameter
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bias infimum is finite and concave in the prescribed magnetization.
Its actual minimizing bias supplies the supporting slope. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma constrainedFieldValue_le_trial (h : FieldStep) {s : ℝ} (hs : |s| ≤ 1) (b : ℝ) :
    constrainedFieldValue h s ≤ fieldValue h b - b * s :=
  csInf_le (magneticBiasObjective_bddBelow h hs) ⟨b, rfl⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldSymmetry
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin-flip symmetry of the actual bias optimization and recovery of
the zero-magnetization scalar field functional. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldValue_bias_even (h : FieldStep) : Function.Even (fieldValue h) := by
  have hL := scalarFieldIncrements_positive h
  have hv := fieldScalarValue_regular (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth
  have he := fieldScalarValue_even (scalarFieldIncrements h) hL
    measurable_logCosh logCosh_linearGrowth (fun z => by simp only [Real.cosh_neg])
  have hr := gaussianOperator_even 0 (NNReal.mk (h.height 0) (h.nonneg 0)) hv.1 he
  intro b
  rw [fieldValue_root, fieldValue_root]
  exact congrArg (fun x => x - h.height (Fin.last h.depth) / 2) (hr b)

lemma fieldBiasMean_zero (h : FieldStep) : fieldBiasMean h 0 = 0 := by
  have hp := hasDerivAt_fieldValue_bias h 0
  have hp' : HasDerivAt (fieldValue h) (fieldBiasMean h 0) (-0) := by simpa using hp
  have hn := hp'.comp 0 (hasDerivAt_neg (0 : ℝ))
  have hn' : HasDerivAt (fieldValue h) (-fieldBiasMean h 0) 0 := by
    refine (hn.congr_of_eventuallyEq (Filter.Eventually.of_forall fun b => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      exact (fieldValue_bias_even h b).symm
    · ring
  linarith [hp.unique hn']

@[simp] lemma magneticBias_zero (h : FieldStep) : magneticBias h 0 = 0 := by
  apply (strictMono_fieldBiasMean h).injective
  rw [fieldBiasMean_magneticBias h (by norm_num), fieldBiasMean_zero]

@[simp] lemma constrainedFieldValue_zero_magnetization (h : FieldStep) :
    constrainedFieldValue h 0 = fieldValue h 0 := by
  rw [constrainedFieldValue_magneticBias h (by norm_num), magneticBias_zero]
  simp only [mul_zero, sub_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticVariational
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prescribed-magnetization variational expression in (7.3)--(7.4).
One common covariance path is used for every field group. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma magneticGroupValue_zero {A : Type*} [Fintype A] (γ : A → ℝ)
    (hγ : ∑ a, γ a = 1) (h : FieldStep) :
    magneticGroupValue γ (fun _ => 0) h = fieldValue h 0 := by
  simp only [magneticGroupValue, constrainedFieldValue_zero_magnetization,
    ← Finset.sum_mul, hγ, one_mul]

lemma magneticGroupValue_le {A : Type*} [Fintype A] (γ m : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hm : ∀ a, |m a| ≤ 1) (h : FieldStep) :
    magneticGroupValue γ m h ≤ fieldValue h 0 := by
  calc
    _ ≤ ∑ a, γ a * fieldValue h 0 := Finset.sum_le_sum (fun a _ =>
      mul_le_mul_of_nonneg_left (by
        simpa only [zero_mul, sub_zero] using constrainedFieldValue_le_trial h (hm a) 0) (hγ a))
    _ = _ := by rw [← Finset.sum_mul, hγsum, one_mul]

lemma magneticEntropyFunctional_le {A : Type*} [Fintype A] (γ m : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) (hm : ∀ a, |m a| ≤ 1)
    (p : OverlapPath) : magneticEntropyFunctional γ m p ≤ entropyFunctional p := by
  apply iSup_le
  intro h
  apply (show ((magneticGroupValue γ m h + fieldPairing p h / 2 : ℝ) : EReal) ≤
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal) from
    EReal.coe_le_coe (add_le_add (magneticGroupValue_le γ m hγ hγsum hm h) le_rfl)).trans
  exact le_iSup (fun h : FieldStep => ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) h

lemma magneticEntropyFunctional_zero {A : Type*} [Fintype A] (γ : A → ℝ)
    (hγ : ∑ a, γ a = 1) (p : OverlapPath) :
    magneticEntropyFunctional γ (fun _ => 0) p = entropyFunctional p := by
  simp only [magneticEntropyFunctional, magneticGroupValue_zero γ hγ, entropyFunctional]

lemma magneticVariationalFunctional_zero {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ : A → ℝ) (hγ : ∑ a, γ a = 1) :
    magneticVariationalFunctional R γ (fun _ => 0) = variationalFunctional R := by
  simp only [magneticVariationalFunctional, magneticEntropyFunctional_zero γ hγ,
    variationalFunctional]

lemma magneticVariationalFunctional_le {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ m : A → ℝ) (hγ : ∀ a, 0 ≤ γ a)
    (hγsum : ∑ a, γ a = 1) (hm : ∀ a, |m a| ≤ 1) :
    magneticVariationalFunctional R γ m ≤ variationalFunctional R := by
  apply iInf_mono
  intro p
  exact add_le_add (magneticEntropyFunctional_le γ m hγ hγsum hm p) le_rfl

lemma finiteMagneticFunctional_lower {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c : A → ℝ) (hγ : ∑ a, γ a = 1) :
    variationalFunctional R ≤ finiteMagneticFunctional R γ c := by
  have hh := le_iSup (fun m : RationalMagnetization A =>
    ((∑ a, γ a * c a * (m.val a : ℝ) : ℝ) : EReal) +
      magneticVariationalFunctional R γ (fun a => (m.val a : ℝ)))
    (⟨fun _ => 0, by intro a; norm_num⟩ : RationalMagnetization A)
  simpa only [Rat.cast_zero, mul_zero, Finset.sum_const_zero, EReal.coe_zero, zero_add,
    magneticVariationalFunctional_zero R γ hγ, finiteMagneticFunctional] using hh

lemma finiteMagneticFunctional_upper {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1) :
    finiteMagneticFunctional R γ c ≤ variationalFunctional R +
      ((∑ a, γ a * |c a| : ℝ) : EReal) := by
  apply iSup_le
  intro m
  have hcm : (∑ a, γ a * c a * (m.val a : ℝ)) ≤ ∑ a, γ a * |c a| := by
    apply Finset.sum_le_sum
    intro a _
    calc
      γ a * c a * (m.val a : ℝ) = γ a * (c a * (m.val a : ℝ)) := by ring
      _ ≤ γ a * |c a * (m.val a : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (hγ a)
      _ ≤ γ a * |c a| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_right (abs_nonneg _) (m.property a).le) (hγ a)
  have hv := magneticVariationalFunctional_le R γ (fun a => (m.val a : ℝ))
    hγ hγsum (fun a => (m.property a).le)
  exact (add_le_add (EReal.coe_le_coe hcm) hv).trans_eq (add_comm _ _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticVariationalContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Field-alphabet stability of the magnetic variational formula. These
bounds are uniform over all rational interior magnetizations. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma finiteMagneticFunctional_ne_top_bot_oai {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ c : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hRtop : variationalFunctional R ≠ ⊤) (hRbot : variationalFunctional R ≠ ⊥) :
    finiteMagneticFunctional R γ c ≠ ⊤ ∧ finiteMagneticFunctional R γ c ≠ ⊥ := by
  constructor
  · exact ne_top_of_le_ne_top (EReal.add_ne_top hRtop (EReal.coe_ne_top _))
      (finiteMagneticFunctional_upper R γ c hγ hγsum)
  · exact ne_bot_of_le_ne_bot hRbot (finiteMagneticFunctional_lower R γ c hγsum)

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot_oai.{u_1} := @OAI.InvariantIsing.finiteMagneticFunctional_ne_top_bot_oai.{u_1}
