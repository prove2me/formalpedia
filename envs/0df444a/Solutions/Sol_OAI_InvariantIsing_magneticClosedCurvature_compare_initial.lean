-- Prove2me | solution 1 for OAI.InvariantIsing.magneticClosedCurvature_compare_initial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:29:12.897901+00:00
-- url     : https://prove2.me/submissions/00e44d86-64af-4ca2-bc20-701e9b229173

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004
import Theorems.Thm_OAI_InvariantIsing_closedMagneticScalarCurvature_hasDerivAt_time

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the scalar Gaussian step at zero variance. The payoff
has a uniform linear envelope; the physical-spin observable is bounded.
This is the dominated-convergence input for closed height cones. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_shift_linear_envelope {E : Type*} [TopologicalSpace E]
    {U : E → ℝ → ℝ} {s x : E → ℝ} (hs : Continuous s) (hx : Continuous x)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (t₀ : E) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ᶠ t in 𝓝 t₀, ∀ u, |U t (x t + Real.sqrt (s t) * u)| ≤ A + B * ‖u‖ := by
  let X := |x t₀| + 1
  let R := |Real.sqrt (s t₀)| + 1
  have hX0 : |x t₀| < X := by dsimp only [X]; linarith
  have hR0 : |Real.sqrt (s t₀)| < R := by dsimp only [R]; linarith
  have hxB : ∀ᶠ t in 𝓝 t₀, |x t| < X :=
    (isOpen_lt hx.abs continuous_const).mem_nhds hX0
  have hsB : ∀ᶠ t in 𝓝 t₀, |Real.sqrt (s t)| < R :=
    (isOpen_lt (Real.continuous_sqrt.comp hs).abs continuous_const).mem_nhds
      hR0
  refine ⟨C + L * X, L * R, by dsimp only [X] <;> positivity,
    by dsimp only [R] <;> positivity, ?_⟩
  filter_upwards [hxB, hsB] with t ht hs'
  intro u
  have harg : |x t + Real.sqrt (s t) * u| ≤ X + R * |u| :=
    (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
  calc
    _ ≤ C + L * (X + R * |u|) := (hB t _).trans (by gcongr)
    _ = C + L * X + L * R * ‖u‖ := by rw [Real.norm_eq_abs]; ring

lemma continuous_field_gaussian_weighted {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U A : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2))
    (hA : Continuous (fun p : E × ℝ => A p.1 p.2))
    (hs : Continuous s) (hx : Continuous x) {C L M : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (_hM : 0 ≤ M)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (haB : ∀ t y, |A t y| ≤ M) (ζ : ℝ) :
    Continuous (fun t => ∫ u, Real.exp (ζ * U t (x t + Real.sqrt (s t) * u)) *
      A t (x t + Real.sqrt (s t) * u) ∂gaussianReal 0 1) := by
  let q := fun p : E × ℝ => (p.1, x p.1 + Real.sqrt (s p.1) * p.2)
  have hq : Continuous q := continuous_fst.prodMk ((hx.comp continuous_fst).add
    (((Real.continuous_sqrt.comp hs).comp continuous_fst).mul continuous_snd))
  have hF : Continuous (fun p : E × ℝ =>
      Real.exp (ζ * U p.1 (x p.1 + Real.sqrt (s p.1) * p.2)) *
        A p.1 (x p.1 + Real.sqrt (s p.1) * p.2)) :=
    (Real.continuous_exp.comp ((hU.comp hq).const_mul ζ)).mul (hA.comp hq)
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨D, B, _hD, _hBB, hb⟩ := field_shift_linear_envelope hs hx hC hL hB t₀
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (|ζ| * D) * Real.exp ((|ζ| * B) * ‖u‖) * M)
  · exact Eventually.of_forall (fun t =>
      (hF.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
  · filter_upwards [hb] with t ht
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have harg : ζ * U t (x t + Real.sqrt (s t) * u) ≤
        |ζ| * D + (|ζ| * B) * ‖u‖ := by
      calc
        _ ≤ |ζ * U t (x t + Real.sqrt (s t) * u)| := le_abs_self _
        _ = |ζ| * |U t (x t + Real.sqrt (s t) * u)| := abs_mul _ _
        _ ≤ |ζ| * (D + B * ‖u‖) := mul_le_mul_of_nonneg_left (ht u) (abs_nonneg _)
        _ = _ := by ring
    rw [← Real.exp_add]
    exact mul_le_mul (Real.exp_le_exp.mpr harg) (haB t _)
      (abs_nonneg _) (Real.exp_pos _).le
  · exact (((gaussianReal_exponentialNormMoments 0 1) (|ζ| * B)).const_mul
      (Real.exp (|ζ| * D))).mul_const M
  · exact ae_of_all _ (fun u =>
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt)

lemma continuous_field_gaussian_tilt_average {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U A : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2))
    (hA : Continuous (fun p : E × ℝ => A p.1 p.2))
    (hs : Continuous s) (hx : Continuous x) {C L M : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (haB : ∀ t y, |A t y| ≤ M) (ζ : ℝ) :
    Continuous (fun t => gaussianTiltAverage (s t) ζ (U t) (A t) (x t)) := by
  have hn := continuous_field_gaussian_weighted hU hA hs hx hC hL hM hB haB ζ
  have hd := continuous_field_gaussian_weighted (A := fun _ _ => 1) hU
    (show Continuous (fun _ : E × ℝ => (1 : ℝ)) from continuous_const)
    hs hx hC hL zero_le_one hB (fun _ _ => by norm_num) ζ
  simp only [mul_one] at hd
  have hp (t : E) : 0 < ∫ u, Real.exp (ζ * U t (x t + Real.sqrt (s t) * u))
      ∂gaussianReal 0 1 := by
    apply IsingPerceptron.integral_exp_pos
    have hm : Measurable (U t) :=
      (hU.comp (continuous_const.prodMk continuous_id)).measurable
    have hg : HasLinearGrowth (U t) :=
      ⟨C, L, hC, hL, by simpa only [Real.norm_eq_abs] using hB t⟩
    exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
      (hm.comp (by fun_prop)) ((hg.add_left (x t)).scale_argument (Real.sqrt (s t))) ζ
  simp only [gaussianTiltAverage_eq_div]
  convert hn.div hd (fun t => (hp t).ne') using 1
  all_goals try with_reducible_and_instances rfl

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear identities for the actual tilted scalar transition. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_const_mul (ζ : ℝ) (v : ℝ≥0) (F a : ℝ → ℝ)
    (c z : ℝ) :
    fieldSpinTransition ζ v F (fun u => c * a u) z = c * fieldSpinTransition ζ v F a z := by
  exact integral_const_mul c _

lemma fieldSpinTransition_add (ζ : ℝ) (v : ℝ≥0) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (z : ℝ) :
    fieldSpinTransition ζ v F (fun u => a u + b u) z =
      fieldSpinTransition ζ v F a z + fieldSpinTransition ζ v F b z := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted he
  exact integral_add
    (Integrable.of_bound ha.aestronglyMeasurable A
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using haB u))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hbB u))

lemma fieldSpinTransition_const (ζ : ℝ) (v : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (c z : ℝ) :
    fieldSpinTransition ζ v F (fun _ => c) z = c := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  have : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    MeasureTheory.isProbabilityMeasure_tilted he
  simp only [fieldSpinTransition, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldLowerBound
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldCurvature
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticMinimumCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Necessary derivative signs at minima, for the inverse-coordinate
parabolic comparison on the closed mean-spin interval. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma second_derivative_nonneg_at_local_min {f f' : ℝ → ℝ} {a c : ℝ}
    (hm : IsLocalMin f a)
    (hf : ∀ᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' c a) : 0 ≤ c := by
  have hfa := hf.self_of_nhds
  have hz : f' a = 0 := hm.hasDerivAt_eq_zero hfa
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp hf').2
  have hd' : Tendsto (fun x : ℝ => f' x / (2 * (x - a)))
      (𝓝[>] a) (𝓝 (c / 2)) := by
    have hh := hd.div_const 2
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    rw [slope_def_field, hz, sub_zero, mul_comm (2 : ℝ) (x - a), div_mul_eq_div_div]
  have hnum : ∀ᶠ x in 𝓝[>] a, HasDerivAt (fun y => f y - f a) (f' x) x := by
    filter_upwards [hf.filter_mono nhdsWithin_le_nhds] with x hx
    exact hx.sub_const (f a)
  have hden : ∀ᶠ x in 𝓝[>] a,
      HasDerivAt (fun y : ℝ => (y - a) ^ 2) (2 * (x - a)) x := by
    filter_upwards [] with x
    refine (((hasDerivAt_id x).sub_const a).pow 2).congr_deriv (Eq.symm ?_)
    · simp
  have hne : ∀ᶠ x in 𝓝[>] a, 2 * (x - a) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hx.ne')
  have hn0 : Tendsto (fun x => f x - f a) (𝓝[>] a) (𝓝 0) := by
    simpa only [sub_self] using (hfa.continuousAt.sub_const (f a)).mono_left
      nhdsWithin_le_nhds
  have hd0 : Tendsto (fun x : ℝ => (x - a) ^ 2) (𝓝[>] a) (𝓝 0) := by
    have hh : ContinuousAt (fun x : ℝ => (x - a) ^ 2) a := by fun_prop
    simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] using
      hh.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := HasDerivAt.lhopital_zero_nhdsGT hnum hden hne hn0 hd0 hd'
  have hnon : ∀ᶠ x in 𝓝[>] a, 0 ≤ (f x - f a) / (x - a) ^ 2 := by
    filter_upwards [hm.filter_mono nhdsWithin_le_nhds] with x hx
    exact div_nonneg (sub_nonneg.mpr hx) (sq_nonneg _)
  have : 0 ≤ c / 2 := ge_of_tendsto hlim hnon
  linarith

lemma derivativeWithin_nonpos_at_left_min {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivWithinAt f d (Iic a) a)
    (hm : ∀ᶠ x in 𝓝[<] a, f a ≤ f x) : d ≤ 0 := by
  have hl : Tendsto (slope f a) (𝓝[<] a) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : a ∉ Iio a)).mp
      (hf.mono Iio_subset_Iic_self)
  apply le_of_tendsto hl
  filter_upwards [hm, self_mem_nhdsWithin] with x hx hxa
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx) (sub_nonpos.mpr hxa.le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticParabolicMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Minimum comparison on the closed mean-spin interval. Diffusion and
drift may degenerate at the two endpoints, where both coefficients vanish. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma parabolic_minimum_nonneg {T : ℝ} (hT : 0 ≤ T)
    (W Wt Wx Wxx A B C : ℝ × ℝ → ℝ)
    (hW : ContinuousOn W (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ W (0, x))
    (hdt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => W (q, x)) (Wt (t, x)) (Iic t) t)
    (hdx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => W (t, y)) (Wx (t, x)) x)
    (hdxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Wx (t, y)) (Wxx (t, x)) x)
    (hA : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ A p)
    (hC : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, C p < 0)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) T,
      A (t, -1) = 0 ∧ B (t, -1) = 0 ∧ A (t, 1) = 0 ∧ B (t, 1) = 0)
    (hPDE : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      A p * Wxx p + B p * Wx p + C p * W p ≤ Wt p) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ W p := by
  intro p hp
  by_contra hn
  have hpneg : W p < 0 := lt_of_not_ge hn
  obtain ⟨q, hq, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    ⟨(0, 0), by exact ⟨⟨le_rfl, hT⟩, by constructor <;> norm_num⟩⟩ hW
  have hqneg : W q < 0 := (hmin hp).trans_lt hpneg
  have hqt : 0 < q.1 := by
    have hqn : q.1 ≠ 0 := by
      intro he
      have hh := hinit q.2 hq.2
      have hqe : q = (0, q.2) := Prod.ext he rfl
      rw [hqe] at hqneg
      linarith
    exact lt_of_le_of_ne hq.1.1 (Ne.symm hqn)
  have htime : ∀ᶠ t in 𝓝[<] q.1, W q ≤ W (t, q.2) := by
    have hn0 : ∀ᶠ t in 𝓝[<] q.1, 0 < t :=
      (show ∀ᶠ t : ℝ in 𝓝 q.1, 0 < t from Ioi_mem_nhds hqt).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hn0, self_mem_nhdsWithin] with t ht0 htt
    exact hmin ⟨⟨ht0.le, htt.le.trans hq.1.2⟩, hq.2⟩
  have htderiv : Wt q ≤ 0 := derivativeWithin_nonpos_at_left_min
    (hdt q.1 ⟨hqt, hq.1.2⟩ q.2 hq.2) htime
  have hqC : 0 < C q * W q := mul_pos_of_neg_of_neg (hC q hq) hqneg
  have hqp : q ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1 := ⟨⟨hqt, hq.1.2⟩, hq.2⟩
  by_cases hleft : q.2 = -1
  · have hb := hboundary q.1 hq.1
    have hpde := hPDE q hqp
    have hqe : q = (q.1, -1) := Prod.ext rfl hleft
    rw [hqe, hb.1, hb.2.1, zero_mul, zero_mul, zero_add, zero_add] at hpde
    rw [hqe] at htderiv hqC
    linarith
  by_cases hright : q.2 = 1
  · have hb := hboundary q.1 hq.1
    have hpde := hPDE q hqp
    have hqe : q = (q.1, 1) := Prod.ext rfl hright
    rw [hqe, hb.2.2.1, hb.2.2.2, zero_mul, zero_mul, zero_add, zero_add] at hpde
    rw [hqe] at htderiv hqC
    linarith
  have hqi : q.2 ∈ Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hq.2.1 (Ne.symm hleft), lt_of_le_of_ne hq.2.2 hright⟩
  have hm : IsLocalMin (fun x => W (q.1, x)) q.2 := by
    filter_upwards [isOpen_Ioo.mem_nhds hqi] with x hx
    exact hmin ⟨hq.1, ⟨hx.1.le, hx.2.le⟩⟩
  have hx0 : Wx q = 0 := hm.hasDerivAt_eq_zero (hdx q.1 hq.1 q.2 hqi)
  have hxx : 0 ≤ Wxx q := by
    apply second_derivative_nonneg_at_local_min hm ?_ (hdxx q.1 hq.1 q.2 hqi)
    filter_upwards [isOpen_Ioo.mem_nhds hqi] with x hx
    exact hdx q.1 hq.1 x hx
  have hprod : 0 ≤ A q * Wxx q := mul_nonneg (hA q hq) hxx
  have hpde := hPDE q hqp
  rw [hx0, mul_zero, add_zero] at hpde
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticParabolicComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponential damping removes the sign restriction on the bounded
zeroth-order coefficient in the degenerate closed-interval comparison. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma parabolic_minimum_nonneg_bounded {T M : ℝ} (hT : 0 ≤ T)
    (W Wt Wx Wxx A B C : ℝ × ℝ → ℝ)
    (hW : ContinuousOn W (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ W (0, x))
    (hdt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => W (q, x)) (Wt (t, x)) (Iic t) t)
    (hdx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => W (t, y)) (Wx (t, x)) x)
    (hdxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Wx (t, y)) (Wxx (t, x)) x)
    (hA : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ A p)
    (hC : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, C p ≤ M)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) T,
      A (t, -1) = 0 ∧ B (t, -1) = 0 ∧ A (t, 1) = 0 ∧ B (t, 1) = 0)
    (hPDE : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      A p * Wxx p + B p * Wx p + C p * W p ≤ Wt p) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ W p := by
  let E : ℝ × ℝ → ℝ := fun p => Real.exp (-(M + 1) * p.1)
  let V := fun p => E p * W p
  let Vt := fun p => E p * (Wt p - (M + 1) * W p)
  let Vx := fun p => E p * Wx p
  let Vxx := fun p => E p * Wxx p
  have hV : ContinuousOn V (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1) :=
    ((by fun_prop : Continuous E).continuousOn).mul hW
  have hVi : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ V (0, x) := by
    intro x hx
    simpa [V, E] using hinit x hx
  have hVt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => V (q, x)) (Vt (t, x)) (Iic t) t := by
    intro t ht x hx
    have he := (((hasDerivAt_id t).const_mul (-(M + 1))).exp).hasDerivWithinAt (s := Iic t)
    convert (config := {transparency := .instances, preTransparency := .instances}) he.mul (hdt t ht x hx) using 1
    · rfl
    · simp only [Vt, E, id_eq]
      ring
  have hVx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => V (t, y)) (Vx (t, x)) x := by
    intro t ht x hx
    exact (hdx t ht x hx).const_mul (Real.exp (-(M + 1) * t))
  have hVxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Vx (t, y)) (Vxx (t, x)) x := by
    intro t ht x hx
    exact (hdxx t ht x hx).const_mul (Real.exp (-(M + 1) * t))
  have hCn : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, C p - (M + 1) < 0 := by
    intro p hp
    linarith [hC p hp]
  have hVpde : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      A p * Vxx p + B p * Vx p + (C p - (M + 1)) * V p ≤ Vt p := by
    intro p hp
    have hh := mul_le_mul_of_nonneg_left (hPDE p hp) (Real.exp_pos (-(M + 1) * p.1)).le
    dsimp only [Vxx, Vx, V, Vt, E]
    nlinarith
  have hv := parabolic_minimum_nonneg hT V Vt Vx Vxx A B
    (fun p => C p - (M + 1)) hV hVi hVt hVx hVxx hA hCn hboundary hVpde
  intro p hp
  exact nonneg_of_mul_nonneg_right (hv p hp) (Real.exp_pos (-(M + 1) * p.1))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticParabolicNegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison only needs a bound for the zeroth-order coefficient on the
negative set of the proposed difference. This avoids division estimates
between two different inverse curvatures at the degenerate endpoints. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma parabolic_minimum_nonneg_bounded_on_negative {T M : ℝ} (hT : 0 ≤ T)
    (W Wt Wx Wxx A B C : ℝ × ℝ → ℝ)
    (hW : ContinuousOn W (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ W (0, x))
    (hdt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => W (q, x)) (Wt (t, x)) (Iic t) t)
    (hdx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => W (t, y)) (Wx (t, x)) x)
    (hdxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Wx (t, y)) (Wxx (t, x)) x)
    (hA : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ A p)
    (hC : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, W p < 0 → C p ≤ M)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) T,
      A (t, -1) = 0 ∧ B (t, -1) = 0 ∧ A (t, 1) = 0 ∧ B (t, 1) = 0)
    (hPDE : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      A p * Wxx p + B p * Wx p + C p * W p ≤ Wt p) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ W p := by
  apply parabolic_minimum_nonneg_bounded hT W Wt Wx Wxx A B
    (fun p => min (C p) M) hW hinit hdt hdx hdxx hA
    (fun p _ => min_le_right _ _) hboundary
  intro p hp
  by_cases hn : W p < 0
  · have hc := hC p ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩ hn
    simpa only [min_eq_left hc] using hPDE p hp
  · have hm := mul_le_mul_of_nonneg_right (min_le_left (C p) M) (le_of_not_gt hn)
    linarith [hPDE p hp]

lemma inverse_curvature_difference_coefficient_bound
    {a b d ζ A K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a)
    (hA : a ≤ A) (hζ : 0 ≤ ζ) (hd : |a * d| ≤ K) :
    (b + a) * (d / 2 + ζ) ≤ K + 2 * A * ζ := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hd
  have hdiff : (b + a) * d / 2 ≤ K := by
    by_cases hd0 : 0 ≤ d
    · have hp := mul_nonneg (sub_nonneg.mpr hba) hd0
      nlinarith [(le_abs_self (a * d)).trans hd]
    · have hp := mul_nonpos_of_nonneg_of_nonpos (add_nonneg hb ha) (le_of_not_ge hd0)
      linarith
  have hterm := mul_le_mul_of_nonneg_right (show b + a ≤ 2 * A by linarith) hζ
  nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticBoundedInverseComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exponent comparison for the one-dimensional inverse-curvature equation with an arbitrary finite curvature cap.
The coefficient bound is required only where the proposed order fails. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

theorem inverse_curvature_parabolic_comparison_bound {T ζ η K A : ℝ}
    (hT : 0 ≤ T) (hη : 0 ≤ η) (hζη : ζ ≤ η)
    (a aTime ax axx b bTime bx bxx : ℝ × ℝ → ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hb : ContinuousOn b (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ s ∈ Icc (-1 : ℝ) 1, a (0, s) ≤ b (0, s))
    (hat : ∀ t ∈ Ioc (0 : ℝ) T, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun u => a (u, s)) (aTime (t, s)) (Iic t) t)
    (hbt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun u => b (u, s)) (bTime (t, s)) (Iic t) t)
    (hax : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u => a (t, u)) (ax (t, s)) s)
    (hbx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u => b (t, u)) (bx (t, s)) s)
    (haxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u => ax (t, u)) (axx (t, s)) s)
    (hbxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u => bx (t, u)) (bxx (t, s)) s)
    (ha0 : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ a p)
    (hb0 : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ b p)
    (ha1 : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, a p ≤ A)
    (hbound : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, |a p * axx p| ≤ K)
    (hend : ∀ t ∈ Icc (0 : ℝ) T, a (t, -1) = 0 ∧ b (t, -1) = 0 ∧
      a (t, 1) = 0 ∧ b (t, 1) = 0)
    (hpa : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      aTime p = a p ^ 2 / 2 * axx p + ζ * a p ^ 2)
    (hpb : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1,
      bTime p = b p ^ 2 / 2 * bxx p + η * b p ^ 2) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, a p ≤ b p := by
  have h := parabolic_minimum_nonneg_bounded_on_negative (M := K + 2 * A * η) hT
    (fun p => b p - a p) (fun p => bTime p - aTime p) (fun p => bx p - ax p)
    (fun p => bxx p - axx p) (fun p => b p ^ 2 / 2) (fun _ => 0)
    (fun p => (b p + a p) * (axx p / 2 + η))
    (hb.sub ha) (fun s hs => sub_nonneg.mpr (hinit s hs))
    (fun t ht s hs => (hbt t ht s hs).sub (hat t ht s hs))
    (fun t ht s hs => (hbx t ht s hs).sub (hax t ht s hs))
    (fun t ht s hs => (hbxx t ht s hs).sub (haxx t ht s hs))
    (fun p hp => div_nonneg (sq_nonneg _) (by norm_num))
    (fun p hp hn => by
      exact inverse_curvature_difference_coefficient_bound
        (ha0 p hp) (hb0 p hp) (by linarith) (ha1 p hp) hη (hbound p hp))
    (fun t ht => by
      obtain ⟨haL, hbL, haR, hbR⟩ := hend t ht
      simp only [hbL, hbR, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_div, and_self]) ?_
  · intro p hp
    exact sub_nonneg.mp (h p hp)
  · intro p hp
    rw [hpb p hp, hpa p hp]
    have hn := mul_nonneg (sub_nonneg.mpr hζη) (sq_nonneg (a p))
    nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticInverseVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local inverse-mean-coordinate calculus used by the prescribed-spin
field comparison. These identities derive the change of curvature and
the second derivative of a pulled-back field variation. -/

noncomputable section
open Filter IsingPerceptron
open scoped Topology

namespace InvariantIsing

lemma inverse_mean_pullback_derivative {V Z : ℝ → ℝ} {u c v : ℝ}
    (hZ : HasDerivAt Z (1 / c) u) (hV : HasDerivAt V v (Z u)) :
    HasDerivAt (fun q => V (Z q)) (v / c) u := by
  convert hV.comp u hZ using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | simp [div_eq_mul_inv]

/-- The spatial derivative of the first inverse-coordinate derivative.
This is the local formula behind `delta a = a^2 delta F_uu`. -/
lemma inverse_mean_pullback_quotient {Z V₁ C : ℝ → ℝ} {u c v v₂ d : ℝ}
    (hc : c ≠ 0) (hZ : HasDerivAt Z (1 / c) u)
    (hv : V₁ (Z u) = v) (hcv : C (Z u) = c)
    (hV : HasDerivAt V₁ v₂ (Z u)) (hC : HasDerivAt C d (Z u)) :
    HasDerivAt (fun q => V₁ (Z q) / C (Z q))
      (v₂ / c ^ 2 - v * d / c ^ 3) u := by
  have hn := inverse_mean_pullback_derivative hZ hV
  have hd := inverse_mean_pullback_derivative hZ hC
  have hq := hn.div hd (by rwa [hcv])
  convert hq using 1
  all_goals try with_reducible_and_instances rfl
  rw [hv, hcv]
  field_simp [hc]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCurvatureBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical curvature is bounded by the remaining spin variance.
Consequently its mean-coordinate representative vanishes at both endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldCurvatureTransform_le_spin_variance {ζ : ℝ} (hζ : ζ ≤ 1) (v : ℝ≥0)
    {F M Q : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q)
    {K C : ℝ} (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C)
    (hbound : ∀ y, Q y + (M y) ^ 2 ≤ 1) (z : ℝ) :
    fieldCurvatureTransform ζ v F M Q z ≤ 1 - (fieldSpinTransition ζ v F M z) ^ 2 := by
  have bM2 : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have hle := fieldSpinTransition_mono_test ζ v F (hQ.add (hM.pow_const 2))
    measurable_const
    (fun y => (abs_add_le _ _).trans (add_le_add (bQ y) (bM2 y)))
    (fun _ => by norm_num : ∀ y : ℝ, |(1 : ℝ)| ≤ 1) hbound z
  change fieldSpinTransition ζ v F (fun y => Q y + M y ^ 2) z ≤
    fieldSpinTransition ζ v F (fun _ => 1) z at hle
  rw [fieldSpinTransition_add ζ v hF hG hQ (hM.pow_const 2) bQ bM2,
    fieldSpinTransition_const ζ v hF hG] at hle
  have hvar := fieldSpinTransition_square_le ζ v hF hG hM bM z
  have hc : ζ * (fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2) ≤
      fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
      (fieldSpinTransition ζ v F M z) ^ 2 := by
    exact mul_le_of_le_one_left (sub_nonneg.mpr hvar) hζ
  unfold fieldCurvatureTransform
  linarith

lemma field_logCosh_spin_variance (z : ℝ) :
    1 / (Real.cosh z) ^ 2 + (Real.tanh z) ^ 2 = 1 := by
  have hc := (Real.cosh_pos z).ne'
  have hr := Real.cosh_sq_sub_sinh_sq z
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc]
  nlinarith

lemma fieldScalarLogCoshSecond_le_spin_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (z : ℝ) :
    fieldScalarSecond L (fun y => Real.log (Real.cosh y)) Real.tanh
      (fun y => 1 / (Real.cosh y) ^ 2) z ≤
      1 - (fieldScalarMean L (fun y => Real.log (Real.cosh y)) Real.tanh z) ^ 2 := by
  induction L generalizing z with
  | nil =>
    change 1 / (Real.cosh z) ^ 2 ≤ 1 - (Real.tanh z) ^ 2
    linarith [field_logCosh_spin_variance z]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hb : ∀ y, fieldScalarSecond L (fun y => Real.log (Real.cosh y)) Real.tanh
        (fun y => 1 / (Real.cosh y) ^ 2) y +
        (fieldScalarMean L (fun y => Real.log (Real.cosh y)) Real.tanh y) ^ 2 ≤ 1 := by
      intro y
      linarith [ih ht htζ y]
    exact fieldCurvatureTransform_le_spin_variance (hζ av List.mem_cons_self) av.2
      hv.1 hv.2 ha.1 hq.1 ha.2 hq.2 hb z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCenteredMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered bounded-spin moments used to control the coefficients of the
inverse-mean diffusion. These estimates apply to the actual tilted Gaussian
law, including zero covariance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

private lemma magnetic_bounded_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)

lemma magnetic_spin_mean_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : ∀ x, |M x| ≤ 1) : |∫ x, M x ∂μ| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := M) (C := 1)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hM x)
  simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

lemma magnetic_centered_spin_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : ∀ x, |M x| ≤ 1) (x : ℝ) :
    |M x - ∫ y, M y ∂μ| ≤ 2 := by
  exact (abs_sub _ _).trans (by linarith [hM x, magnetic_spin_mean_bound μ hM])

lemma magnetic_centered_power_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) (k : ℕ) :
    Integrable (fun x => (M x - ∫ y, M y ∂μ) ^ k) μ := by
  apply magnetic_bounded_integrable μ ((hM.sub measurable_const).pow_const k)
  intro x
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (magnetic_centered_spin_bound μ bM x) k

lemma magnetic_centered_second (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) =
      (∫ x, (M x) ^ 2 ∂μ) - (∫ x, M x ∂μ) ^ 2 := by
  have h1 := magnetic_bounded_integrable μ hM bM
  have h2 : Integrable (fun x => (M x) ^ 2) μ :=
    magnetic_bounded_integrable μ (C := 1) (hM.pow_const 2) (fun x => by
      rw [abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) 2)
  let m := ∫ x, M x ∂μ
  calc
    _ = ∫ x, ((M x) ^ 2 - (2 * m) * M x) + m ^ 2 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [m] <;> ring
    _ = _ := by
      rw [integral_add (f := fun x => (M x) ^ 2 - (2 * m) * M x)
          (g := fun _ => m ^ 2) (h2.sub (h1.const_mul _)) (integrable_const _),
        integral_sub (f := fun x => (M x) ^ 2) (g := fun x => (2 * m) * M x)
          h2 (h1.const_mul _), integral_const_mul, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      dsimp only [m]
      ring

lemma magnetic_centered_second_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    0 ≤ (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) ∧
      (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) ≤ 1 := by
  constructor
  · exact integral_nonneg fun _ => sq_nonneg _
  · rw [magnetic_centered_second μ hM bM]
    have hi := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => (M x) ^ 2) (C := 1) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) 2)
    simp only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at hi
    linarith [le_abs_self (∫ x, (M x) ^ 2 ∂μ), sq_nonneg (∫ x, M x ∂μ)]

lemma magnetic_centered_third (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    (∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ) =
      (∫ x, (M x) ^ 3 ∂μ) - 3 * (∫ x, M x ∂μ) * (∫ x, (M x) ^ 2 ∂μ) +
        2 * (∫ x, M x ∂μ) ^ 3 := by
  have hp (k : ℕ) : Integrable (fun x => (M x) ^ k) μ :=
    magnetic_bounded_integrable μ (C := 1) (hM.pow_const k) (fun x => by
      rw [abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) k)
  have h1 := magnetic_bounded_integrable μ hM bM
  let m := ∫ x, M x ∂μ
  calc
    _ = ∫ x, (((M x) ^ 3 - (3 * m) * (M x) ^ 2) + (3 * m ^ 2) * M x) - m ^ 3 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [m] <;> ring
    _ = _ := by
      rw [integral_sub (f := fun x => ((M x) ^ 3 - (3 * m) * (M x) ^ 2) + (3 * m ^ 2) * M x)
          (g := fun _ => m ^ 3) (((hp 3).sub ((hp 2).const_mul _)).add (h1.const_mul _))
          (integrable_const _),
        integral_add (f := fun x => (M x) ^ 3 - (3 * m) * (M x) ^ 2)
          (g := fun x => (3 * m ^ 2) * M x) ((hp 3).sub ((hp 2).const_mul _)) (h1.const_mul _),
        integral_sub (f := fun x => (M x) ^ 3) (g := fun x => (3 * m) * (M x) ^ 2)
          (hp 3) ((hp 2).const_mul _), integral_const_mul,
        integral_const_mul, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      dsimp only [m]
      ring

lemma magnetic_centered_fourth (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    (∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ) =
      (∫ x, (M x) ^ 4 ∂μ) - 4 * (∫ x, M x ∂μ) * (∫ x, (M x) ^ 3 ∂μ) +
        6 * (∫ x, M x ∂μ) ^ 2 * (∫ x, (M x) ^ 2 ∂μ) -
        3 * (∫ x, M x ∂μ) ^ 4 := by
  have hp (k : ℕ) : Integrable (fun x => (M x) ^ k) μ :=
    magnetic_bounded_integrable μ (C := 1) (hM.pow_const k) (fun x => by
      rw [abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) k)
  have h1 := magnetic_bounded_integrable μ hM bM
  let m := ∫ x, M x ∂μ
  calc
    _ = ∫ x, ((((M x) ^ 4 - (4 * m) * (M x) ^ 3) + (6 * m ^ 2) * (M x) ^ 2) -
        (4 * m ^ 3) * M x) + m ^ 4 ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [m] <;> ring
    _ = _ := by
      rw [integral_add
          (f := fun x => (((M x) ^ 4 - (4 * m) * (M x) ^ 3) + (6 * m ^ 2) * (M x) ^ 2) - (4 * m ^ 3) * M x)
          (g := fun _ => m ^ 4)
          ((((hp 4).sub ((hp 3).const_mul _)).add ((hp 2).const_mul _)).sub (h1.const_mul _))
          (integrable_const _),
        integral_sub (f := fun x => ((M x) ^ 4 - (4 * m) * (M x) ^ 3) + (6 * m ^ 2) * (M x) ^ 2)
          (g := fun x => (4 * m ^ 3) * M x)
          (((hp 4).sub ((hp 3).const_mul _)).add ((hp 2).const_mul _)) (h1.const_mul _),
        integral_add (f := fun x => (M x) ^ 4 - (4 * m) * (M x) ^ 3)
          (g := fun x => (6 * m ^ 2) * (M x) ^ 2)
          ((hp 4).sub ((hp 3).const_mul _)) ((hp 2).const_mul _),
        integral_sub (f := fun x => (M x) ^ 4) (g := fun x => (4 * m) * (M x) ^ 3)
          (hp 4) ((hp 3).const_mul _), integral_const_mul,
        integral_const_mul, integral_const_mul, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      dsimp only [m]
      ring

lemma magnetic_weighted_centered_second (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M Q : ℝ → ℝ} (hM : Measurable M) (hQ : Measurable Q)
    (bM : ∀ x, |M x| ≤ 1) {C : ℝ} (bQ : ∀ x, |Q x| ≤ C) :
    (∫ x, Q x * (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) =
      (∫ x, Q x * (M x) ^ 2 ∂μ) -
        2 * (∫ x, M x ∂μ) * (∫ x, Q x * M x ∂μ) +
        (∫ x, M x ∂μ) ^ 2 * (∫ x, Q x ∂μ) := by
  have hiQ := magnetic_bounded_integrable μ hQ bQ
  have hiQM (k : ℕ) : Integrable (fun x => Q x * (M x) ^ k) μ :=
    hiQ.mul_bdd (hM.pow_const k).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bM x) k)
  let m := ∫ x, M x ∂μ
  calc
    _ = ∫ x, (Q x * (M x) ^ 2 - (2 * m) * (Q x * (M x) ^ 1)) +
        m ^ 2 * Q x ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp only [m] <;> ring
    _ = _ := by
      rw [integral_add (f := fun x => Q x * (M x) ^ 2 - (2 * m) * (Q x * (M x) ^ 1))
          (g := fun x => m ^ 2 * Q x) ((hiQM 2).sub ((hiQM 1).const_mul _)) (hiQ.const_mul _),
        integral_sub (f := fun x => Q x * (M x) ^ 2) (g := fun x => (2 * m) * (Q x * (M x) ^ 1))
          (hiQM 2) ((hiQM 1).const_mul _), integral_const_mul,
        integral_const_mul]
      simp only [pow_one]
      dsimp only [m]

lemma magnetic_centered_third_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    |∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ| ≤
      2 * ∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ := by
  have h3 := magnetic_centered_power_integrable μ hM bM 3
  have h2 := magnetic_centered_power_integrable μ hM bM 2
  calc
    _ ≤ ∫ x, |(M x - ∫ y, M y ∂μ) ^ 3| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, 2 * (M x - ∫ y, M y ∂μ) ^ 2 ∂μ := by
      apply integral_mono h3.abs (h2.const_mul 2)
      intro x
      change |(M x - ∫ y, M y ∂μ) ^ 3| ≤ 2 * (M x - ∫ y, M y ∂μ) ^ 2
      rw [abs_pow, pow_succ _ 2]
      have hp := mul_le_mul_of_nonneg_left (magnetic_centered_spin_bound μ bM x)
        (sq_nonneg |M x - ∫ y, M y ∂μ|)
      nlinarith [sq_abs (M x - ∫ y, M y ∂μ)]
    _ = _ := integral_const_mul _ _

lemma magnetic_centered_fourth_cumulant_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ → ℝ} (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) :
    |(∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ) -
        3 * (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) ^ 2| ≤
      7 * ∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ := by
  let V := ∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ
  have hV := magnetic_centered_second_bounds μ hM bM
  have h4 : (∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ) ≤ 4 * V := by
    calc
      _ ≤ ∫ x, 4 * (M x - ∫ y, M y ∂μ) ^ 2 ∂μ := by
        apply integral_mono (magnetic_centered_power_integrable μ hM bM 4)
          ((magnetic_centered_power_integrable μ hM bM 2).const_mul 4)
        intro x
        have hs := pow_le_pow_left₀ (abs_nonneg _) (magnetic_centered_spin_bound μ bM x) 2
        rw [sq_abs] at hs
        nlinarith [sq_nonneg (M x - ∫ y, M y ∂μ),
          mul_nonneg (sq_nonneg (M x - ∫ y, M y ∂μ)) (sub_nonneg.mpr hs)]
      _ = _ := integral_const_mul _ _
  have h4pos : 0 ≤ ∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ :=
    integral_nonneg fun _ => by positivity
  calc
    _ ≤ |∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ| + |3 * V ^ 2| := abs_sub _ _
    _ = (∫ x, (M x - ∫ y, M y ∂μ) ^ 4 ∂μ) + 3 * V ^ 2 := by
      rw [abs_of_nonneg h4pos, abs_of_nonneg (by positivity)]
    _ ≤ 7 * V := by dsimp only [V] at * <;> nlinarith

lemma magnetic_weighted_centered_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M Q : ℝ → ℝ} (hM : Measurable M) (hQ : Measurable Q)
    (bM : ∀ x, |M x| ≤ 1) {C : ℝ} (bQ : ∀ x, |Q x| ≤ C)
    (hQpos : ∀ x, 0 ≤ Q x) :
    |(∫ x, Q x * M x ∂μ) - (∫ x, Q x ∂μ) * (∫ x, M x ∂μ)| ≤
      2 * ∫ x, Q x ∂μ := by
  let m := ∫ x, M x ∂μ
  have hi := magnetic_bounded_integrable μ hQ bQ
  have hip : Integrable (fun x => Q x * M x) μ :=
    magnetic_bounded_integrable μ (hQ.mul hM) (fun x => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (bM x) (abs_nonneg _)).trans (by simpa using bQ x))
  have hic : Integrable (fun x => Q x * (M x - m)) μ := by
    convert hip.sub (hi.mul_const m) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change Q x * (M x - m) = Q x * M x - Q x * m
    ring
  have he : (∫ x, Q x * M x ∂μ) - (∫ x, Q x ∂μ) * m =
      ∫ x, Q x * (M x - m) ∂μ := by
    rw [show (fun x => Q x * (M x - m)) = fun x => Q x * M x - Q x * m by
      funext x; ring, integral_sub hip (hi.mul_const m), integral_mul_const]
  change |(∫ x, Q x * M x ∂μ) - (∫ x, Q x ∂μ) * m| ≤ _
  rw [he]
  calc
    _ ≤ ∫ x, |Q x * (M x - m)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, 2 * Q x ∂μ := by
      apply integral_mono hic.abs (hi.const_mul 2)
      intro x
      change |Q x * (M x - m)| ≤ 2 * Q x
      rw [abs_mul, abs_of_nonneg (hQpos x)]
      have hb := mul_le_mul_of_nonneg_left (magnetic_centered_spin_bound μ bM x) (hQpos x)
      dsimp only [m]
      linarith
    _ = _ := integral_const_mul _ _

lemma magnetic_nonnegative_spin_variance_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Q : ℝ → ℝ} (hQ : Measurable Q) (hQpos : ∀ x, 0 ≤ Q x) (hQle : ∀ x, Q x ≤ 1) :
    0 ≤ (∫ x, (Q x) ^ 2 ∂μ) - (∫ x, Q x ∂μ) ^ 2 ∧
      (∫ x, (Q x) ^ 2 ∂μ) - (∫ x, Q x ∂μ) ^ 2 ≤ ∫ x, Q x ∂μ := by
  have bQ : ∀ x, |Q x| ≤ 1 := fun x => by rw [abs_of_nonneg (hQpos x)]; exact hQle x
  have hiQ := magnetic_bounded_integrable μ hQ bQ
  have hiQ2 : Integrable (fun x => (Q x) ^ 2) μ :=
    magnetic_bounded_integrable μ (C := 1) (hQ.pow_const 2) (fun x => by
      rw [abs_pow]; simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (bQ x) 2)
  constructor
  · rw [← magnetic_centered_second μ hQ bQ]
    exact integral_nonneg fun _ => sq_nonneg _
  · have hle : (∫ x, (Q x) ^ 2 ∂μ) ≤ ∫ x, Q x ∂μ :=
      integral_mono hiQ2 hiQ (fun x => by nlinarith [hQpos x, hQle x])
    linarith [sq_nonneg (∫ x, Q x ∂μ)]

lemma magnetic_weighted_variance_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M Q : ℝ → ℝ} (hM : Measurable M) (hQ : Measurable Q)
    (bM : ∀ x, |M x| ≤ 1) {C : ℝ} (bQ : ∀ x, |Q x| ≤ C)
    (hQpos : ∀ x, 0 ≤ Q x) :
    |(∫ x, Q x * (M x - ∫ y, M y ∂μ) ^ 2 ∂μ) -
      (∫ x, Q x ∂μ) * (∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ)| ≤
      5 * ∫ x, Q x ∂μ := by
  let m := ∫ x, M x ∂μ
  let q := ∫ x, Q x ∂μ
  let V := ∫ x, (M x - m) ^ 2 ∂μ
  have hq : 0 ≤ q := integral_nonneg hQpos
  have hV := magnetic_centered_second_bounds μ hM bM
  have hiQ := magnetic_bounded_integrable μ hQ bQ
  have hib : ∀ x, |Q x * (M x - m) ^ 2| ≤ C * 4 := by
    intro x
    rw [abs_mul, abs_pow]
    have hc : 0 ≤ C := (abs_nonneg _).trans (bQ 0)
    have hs := pow_le_pow_left₀ (abs_nonneg _) (magnetic_centered_spin_bound μ bM x) 2
    exact mul_le_mul (bQ x) (by change |M x - ∫ y, M y ∂μ| ^ 2 ≤ 4; exact hs.trans_eq (by norm_num)) (by positivity) hc
  have hi : Integrable (fun x => Q x * (M x - m) ^ 2) μ :=
    magnetic_bounded_integrable μ (hQ.mul ((hM.sub measurable_const).pow_const 2)) hib
  have hip : 0 ≤ ∫ x, Q x * (M x - m) ^ 2 ∂μ :=
    integral_nonneg fun x => mul_nonneg (hQpos x) (sq_nonneg _)
  have hi4 : (∫ x, Q x * (M x - m) ^ 2 ∂μ) ≤ 4 * q := by
    calc
      _ ≤ ∫ x, 4 * Q x ∂μ := by
        apply integral_mono hi (hiQ.const_mul 4)
        intro x
        have hs := pow_le_pow_left₀ (abs_nonneg _) (magnetic_centered_spin_bound μ bM x) 2
        rw [sq_abs] at hs
        dsimp only [m]
        nlinarith [mul_nonneg (hQpos x) (sub_nonneg.mpr hs)]
      _ = _ := integral_const_mul _ _
  change |(∫ x, Q x * (M x - m) ^ 2 ∂μ) - q * V| ≤ 5 * q
  calc
    _ ≤ |∫ x, Q x * (M x - m) ^ 2 ∂μ| + |q * V| := abs_sub _ _
    _ = (∫ x, Q x * (M x - m) ^ 2 ∂μ) + q * V := by
      rw [abs_of_nonneg hip, abs_of_nonneg (mul_nonneg hq hV.1)]
    _ ≤ _ := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hV.2)]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCoerciveRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-dimensional coercivity argument needed for the inverse mean
of a finite Gaussian slab. -/

noncomputable section
open Set Filter
open scoped Topology

namespace InvariantIsing

lemma exists_mean_root_of_linear_lower {F M : ℝ → ℝ} {C s : ℝ}
    (dF : ∀ z, HasDerivAt F (M z) z) (hl : ∀ z, |z| - C ≤ F z)
    (hs : |s| < 1) : ∃ z, M z = s := by
  let δ := 1 - |s|
  let R := (|F 0| + |C| + 1) / δ
  have hδ : 0 < δ := sub_pos.mpr hs
  have hR : 0 ≤ R := div_nonneg (by positivity) hδ.le
  have he : δ * R = |F 0| + |C| + 1 := by
    dsimp only [R]
    field_simp
  let G := fun z => F z - z * s
  have hG : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((dF z).sub ((hasDerivAt_id z).mul_const s)).continuousAt
  have hlow (z : ℝ) : δ * |z| - C ≤ G z := by
    have hz : z * s ≤ |z| * |s| := by
      simpa only [abs_mul] using le_abs_self (z * s)
    dsimp only [δ, G]
    nlinarith [hl z]
  obtain ⟨b, hb, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩) hG.continuousOn
  have hglobal (c : ℝ) : G b ≤ G c := by
    by_cases hc : c ∈ Icc (-R) R
    · exact hmin hc
    have hcr : R ≤ |c| := by
      by_contra hn
      have hlt : |c| < R := lt_of_not_ge hn
      exact hc ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩
    have hlarge : F 0 ≤ G c := by
      have hm := mul_le_mul_of_nonneg_left hcr hδ.le
      have hcabs := le_abs_self C
      have hfabs := le_abs_self (F 0)
      linarith [hlow c]
    have hz := hmin (show (0 : ℝ) ∈ Icc (-R) R by constructor <;> linarith)
    change G b ≤ G 0 at hz
    have hz' : G b ≤ F 0 := by
      simpa only [G, zero_mul, sub_zero] using hz
    exact hz'.trans hlarge
  have hlocal : IsLocalMin G b := Eventually.of_forall hglobal
  have hd : HasDerivAt G (M b - s) b := by
    refine ((dF b).sub ((hasDerivAt_id b).mul_const s)).congr_deriv (Eq.symm ?_)
    · simp only [one_mul]
  exact ⟨b, sub_eq_zero.mp (hlocal.hasDerivAt_eq_zero hd)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRelativeThird
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative third-derivative control through a physical tilted Gaussian
step. Unlike a uniform derivative bound, this remains useful at spin endpoints. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldThirdTransform_centered (ζ : ℝ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (bM : ∀ x, |M x| ≤ 1) (z : ℝ) :
    fieldThirdTransform ζ v F M Q R z =
      fieldSpinTransition ζ v F R z +
      3 * ζ * (fieldSpinTransition ζ v F (fun x => Q x * M x) z -
        fieldSpinTransition ζ v F Q z * fieldSpinTransition ζ v F M z) +
      ζ ^ 2 * fieldSpinTransition ζ v F
        (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 3) z := by
  let μ := (gaussianReal z v).tilted (fun x => ζ * F x)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)
  have hQM : fieldSpinTransition ζ v F (fun x => 2 * M x * Q x) z =
      2 * fieldSpinTransition ζ v F (fun x => Q x * M x) z := by
    change (∫ x, 2 * M x * Q x ∂μ) = 2 * ∫ x, Q x * M x ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hM3 : fieldSpinTransition ζ v F (fun x => (M x) ^ 2 * M x) z =
      fieldSpinTransition ζ v F (fun x => (M x) ^ 3) z := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hc := magnetic_centered_third μ hM bM
  change fieldSpinTransition ζ v F (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 3) z =
    fieldSpinTransition ζ v F (fun x => (M x) ^ 3) z -
      3 * fieldSpinTransition ζ v F M z * fieldSpinTransition ζ v F (fun x => (M x) ^ 2) z +
      2 * (fieldSpinTransition ζ v F M z) ^ 3 at hc
  rw [hc]
  unfold fieldThirdTransform fieldCurvatureTransform
  rw [hQM, hM3]
  ring

theorem fieldThirdTransform_relative_bound {ζ : ℝ} (hζ : 0 ≤ ζ) (v : ℝ≥0)
    {F M Q R : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    (bM : ∀ x, |M x| ≤ 1) {B C : ℝ} (bQ : ∀ x, |Q x| ≤ B)
    (hQpos : ∀ x, 0 ≤ Q x) (hC : 0 ≤ C)
    (bR : ∀ x, |R x| ≤ C * Q x) (z : ℝ) :
    |fieldThirdTransform ζ v F M Q R z| ≤
      (C + 8 * ζ) * fieldCurvatureTransform ζ v F M Q z := by
  let μ := (gaussianReal z v).tilted (fun x => ζ * F x)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)
  let q := ∫ x, Q x ∂μ
  let V := ∫ x, (M x - ∫ y, M y ∂μ) ^ 2 ∂μ
  have hq : 0 ≤ q := integral_nonneg hQpos
  have hV : 0 ≤ V := integral_nonneg fun _ => sq_nonneg _
  have hiQ : Integrable Q μ := Integrable.of_bound hQ.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bQ x)
  have hiR : Integrable R μ := (hiQ.const_mul C).mono' hR.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bR x)
  have hRb : |∫ x, R x ∂μ| ≤ C * q := by
    calc
      _ ≤ ∫ x, |R x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, C * Q x ∂μ := integral_mono hiR.abs (hiQ.const_mul C) bR
      _ = _ := integral_const_mul _ _
  have hCov := magnetic_weighted_centered_bound μ hM hQ bM bQ hQpos
  have hThird := magnetic_centered_third_bound μ hM bM
  have hcurv : fieldCurvatureTransform ζ v F M Q z = q + ζ * V := by
    dsimp only [q, V]
    rw [magnetic_centered_second μ hM bM]
    rfl
  rw [fieldThirdTransform_centered ζ v hF hG hM bM, hcurv]
  change |(∫ x, R x ∂μ) + 3 * ζ * ((∫ x, Q x * M x ∂μ) - q * (∫ x, M x ∂μ)) +
    ζ ^ 2 * (∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ)| ≤ (C + 8 * ζ) * (q + ζ * V)
  calc
    _ ≤ |∫ x, R x ∂μ| + 3 * ζ * |(∫ x, Q x * M x ∂μ) - q * (∫ x, M x ∂μ)| +
        ζ ^ 2 * |∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ| := by
      have ha := abs_add_le ((∫ x, R x ∂μ) + 3 * ζ *
        ((∫ x, Q x * M x ∂μ) - q * (∫ x, M x ∂μ)))
        (ζ ^ 2 * (∫ x, (M x - ∫ y, M y ∂μ) ^ 3 ∂μ))
      have hb := abs_add_le (∫ x, R x ∂μ)
        (3 * ζ * ((∫ x, Q x * M x ∂μ) - q * (∫ x, M x ∂μ)))
      rw [abs_mul, abs_of_nonneg (sq_nonneg ζ)] at ha
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * ζ)] at hb
      linarith
    _ ≤ C * q + 3 * ζ * (2 * q) + ζ ^ 2 * (2 * V) := by
      exact add_le_add (add_le_add hRb (mul_le_mul_of_nonneg_left hCov (by positivity)))
        (mul_le_mul_of_nonneg_left hThird (sq_nonneg ζ))
    _ ≤ (C + 8 * ζ) * (q + ζ * V) := by
      have h1 := mul_nonneg hζ hq
      have h2 := mul_nonneg (mul_nonneg hC hζ) hV
      have h3 := mul_nonneg (sq_nonneg ζ) hV
      nlinarith

lemma magneticThirdRatioCap_nonneg (L : List (ℝ × ℝ≥0)) :
    0 ≤ magneticThirdRatioCap L := by
  induction L with
  | nil => norm_num [magneticThirdRatioCap]
  | cons av L ih => exact add_nonneg ih (mul_nonneg (by norm_num) (abs_nonneg _))

lemma field_logCosh_third_relative (z : ℝ) :
    |-2 * Real.tanh z / (Real.cosh z) ^ 2| ≤ 2 * (1 / (Real.cosh z) ^ 2) := by
  have hp : 0 < (Real.cosh z) ^ 2 := sq_pos_of_pos (Real.cosh_pos z)
  calc
    _ = 2 * |Real.tanh z| * (1 / (Real.cosh z) ^ 2) := by
      rw [abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos hp]
      ring
    _ ≤ 2 * 1 * (1 / (Real.cosh z) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (field_abs_tanh_le_one z) (by norm_num))
        (one_div_nonneg.mpr hp.le)
    _ = _ := by ring

theorem fieldScalarLogCoshThird_relative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    |fieldScalarThird L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2)
        (fun x => -2 * Real.tanh x / (Real.cosh x) ^ 2) z| ≤
      magneticThirdRatioCap L * fieldScalarSecond L
        (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => exact field_logCosh_third_relative z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hr := fieldScalarThird_regular L ht measurable_logCosh logCosh_linearGrowth
      hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
      field_tanh_second_bound field_logCosh_third_bound
    have hp := (hL av List.mem_cons_self).le
    have he := fieldThirdTransform_relative_bound hp av.2 hv.1 hv.2 ha.1 hq.1 hr.1
      ha.2 hq.2 (fun x => (fieldScalarLogCoshSecond_pos L ht x).le)
      (magneticThirdRatioCap_nonneg L) (ih ht) z
    simpa only [fieldScalarThird, fieldScalarSecond, fieldScalarMean, magneticThirdRatioCap,
      abs_of_nonneg hp, fieldCurvatureTransform] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFourthCumulant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fourth-derivative recursion in centered-cumulant form. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldFourthTransform_centered (ζ : ℝ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R)
    (bM : ∀ x, |M x| ≤ 1) {C D : ℝ}
    (bQ : ∀ x, |Q x| ≤ C) (bR : ∀ x, |R x| ≤ D) (z : ℝ) :
    fieldFourthTransform ζ v F M Q R S z =
      fieldSpinTransition ζ v F S z +
      4 * ζ * (fieldSpinTransition ζ v F (fun x => R x * M x) z -
        fieldSpinTransition ζ v F R z * fieldSpinTransition ζ v F M z) +
      3 * ζ * (fieldSpinTransition ζ v F (fun x => (Q x) ^ 2) z -
        (fieldSpinTransition ζ v F Q z) ^ 2) +
      6 * ζ ^ 2 * (fieldSpinTransition ζ v F
          (fun x => Q x * (M x - fieldSpinTransition ζ v F M z) ^ 2) z -
        fieldSpinTransition ζ v F Q z * fieldSpinTransition ζ v F
          (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 2) z) +
      ζ ^ 3 * (fieldSpinTransition ζ v F
          (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 4) z -
        3 * (fieldSpinTransition ζ v F
          (fun x => (M x - fieldSpinTransition ζ v F M z) ^ 2) z) ^ 2) := by
  let μ := (gaussianReal z v).tilted (fun x => ζ * F x)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)
  let T := fun a : ℝ → ℝ => fieldSpinTransition ζ v F a z
  have bRM : ∀ x, |R x * M x| ≤ D := by
    intro x
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (bM x) (abs_nonneg _)).trans (by simpa using bR x)
  have bQ2 : ∀ x, |(Q x) ^ 2| ≤ C ^ 2 := by
    intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bQ x) 2
  have hRMQ : T (fun x => R x * M x + Q x * Q x) =
      T (fun x => R x * M x) + T (fun x => (Q x) ^ 2) := by
    change fieldSpinTransition ζ v F (fun x => R x * M x + Q x * Q x) z = _
    simp only [← pow_two]
    exact fieldSpinTransition_add ζ v hF hG (hR.mul hM) (hQ.pow_const 2) bRM bQ2 z
  have h2QR : T (fun x => 2 * Q x * Q x + 2 * M x * R x) =
      2 * T (fun x => (Q x) ^ 2) + 2 * T (fun x => R x * M x) := by
    have he : (fun x => 2 * Q x * Q x + 2 * M x * R x) =
        fun x => 2 * ((Q x) ^ 2 + R x * M x) := by funext x; ring
    rw [he]
    change fieldSpinTransition ζ v F (fun x => 2 * ((Q x) ^ 2 + R x * M x)) z = _
    rw [fieldSpinTransition_const_mul]
    have hadd := fieldSpinTransition_add ζ v hF hG (hQ.pow_const 2) (hR.mul hM) bQ2 bRM z
    change fieldSpinTransition ζ v F (fun x => (Q x) ^ 2 + R x * M x) z =
      fieldSpinTransition ζ v F (fun x => (Q x) ^ 2) z +
        fieldSpinTransition ζ v F (fun x => R x * M x) z at hadd
    rw [hadd]
    dsimp only [T]
    ring
  have h2MQ : T (fun x => 2 * M x * Q x) = 2 * T (fun x => Q x * M x) := by
    change (∫ x, 2 * M x * Q x ∂μ) = 2 * ∫ x, Q x * M x ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have h3M2Q : T (fun x => 3 * (M x) ^ 2 * Q x) = 3 * T (fun x => Q x * (M x) ^ 2) := by
    change (∫ x, 3 * (M x) ^ 2 * Q x ∂μ) = 3 * ∫ x, Q x * (M x) ^ 2 ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have h2MQM : T (fun x => (2 * M x * Q x) * M x) = 2 * T (fun x => Q x * (M x) ^ 2) := by
    change (∫ x, (2 * M x * Q x) * M x ∂μ) = 2 * ∫ x, Q x * (M x) ^ 2 ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hQMM : T (fun x => (Q x * M x) * M x) = T (fun x => Q x * (M x) ^ 2) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hM3 : T (fun x => (M x) ^ 2 * M x) = T (fun x => (M x) ^ 3) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hM4 : T (fun x => ((M x) ^ 2 * M x) * M x) = T (fun x => (M x) ^ 4) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hc2 := magnetic_centered_second μ hM bM
  have hc4 := magnetic_centered_fourth μ hM bM
  have hqc2 := magnetic_weighted_centered_second μ hM hQ bM bQ
  change T (fun x => (M x - T M) ^ 2) = T (fun x => (M x) ^ 2) - (T M) ^ 2 at hc2
  change T (fun x => (M x - T M) ^ 4) = T (fun x => (M x) ^ 4) -
    4 * T M * T (fun x => (M x) ^ 3) + 6 * (T M) ^ 2 * T (fun x => (M x) ^ 2) -
    3 * (T M) ^ 4 at hc4
  change T (fun x => Q x * (M x - T M) ^ 2) = T (fun x => Q x * (M x) ^ 2) -
    2 * T M * T (fun x => Q x * M x) + (T M) ^ 2 * T Q at hqc2
  change _ = T S + 4 * ζ * (T (fun x => R x * M x) - T R * T M) +
    3 * ζ * (T (fun x => (Q x) ^ 2) - (T Q) ^ 2) +
    6 * ζ ^ 2 * (T (fun x => Q x * (M x - T M) ^ 2) -
      T Q * T (fun x => (M x - T M) ^ 2)) +
    ζ ^ 3 * (T (fun x => (M x - T M) ^ 4) -
      3 * (T (fun x => (M x - T M) ^ 2)) ^ 2)
  rw [hc2, hc4, hqc2]
  unfold fieldFourthTransform fieldTiltSpatial fieldCurvatureTransform fieldThirdTransform
  change T S + ζ * (T (fun x => R x * M x) - T R * T M) +
    ζ * ((T (fun x => R x * M x + Q x * Q x) +
      ζ * (T (fun x => (Q x * M x) * M x) - T (fun x => Q x * M x) * T M)) -
      ((T R + ζ * (T (fun x => Q x * M x) - T Q * T M)) * T M +
        T Q * (T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2)))) +
    ζ * ((T (fun x => 2 * Q x * Q x + 2 * M x * R x) +
      ζ * (T (fun x => (2 * M x * Q x) * M x) - T (fun x => 2 * M x * Q x) * T M) +
      ζ * ((T (fun x => 3 * (M x) ^ 2 * Q x) +
        ζ * (T (fun x => ((M x) ^ 2 * M x) * M x) - T (fun x => (M x) ^ 2 * M x) * T M)) -
        ((T (fun x => 2 * M x * Q x) +
          ζ * (T (fun x => (M x) ^ 2 * M x) - T (fun x => (M x) ^ 2) * T M)) * T M +
          T (fun x => (M x) ^ 2) * (T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2))))) -
      2 * ((T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2)) *
        (T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2)) +
        T M * ((T R + ζ * (T (fun x => Q x * M x) - T Q * T M)) +
          ζ * ((T (fun x => 2 * M x * Q x) +
            ζ * (T (fun x => (M x) ^ 2 * M x) - T (fun x => (M x) ^ 2) * T M)) -
            2 * T M * (T Q + ζ * (T (fun x => (M x) ^ 2) - (T M) ^ 2)))))) = _
  rw [hRMQ, h2QR, h2MQ, h3M2Q, h2MQM, hQMM, hM4, hM3]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRelativeFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A relative fourth-derivative bound, uniform in the spatial bias.
The centered fourth cumulant costs only one spin variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magnetic_relative_centered_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M Q A : ℝ → ℝ} (hM : Measurable M) (hQ : Measurable Q) (hA : Measurable A)
    (bM : ∀ x, |M x| ≤ 1) {B C : ℝ} (bQ : ∀ x, |Q x| ≤ B)
    (bA : ∀ x, |A x| ≤ C * Q x) :
    |(∫ x, A x * M x ∂μ) - (∫ x, A x ∂μ) * (∫ x, M x ∂μ)| ≤
      2 * C * ∫ x, Q x ∂μ := by
  let m := ∫ x, M x ∂μ
  have hiQ : Integrable Q μ := Integrable.of_bound hQ.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bQ x)
  have hiA : Integrable A μ := (hiQ.const_mul C).mono' hA.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bA x)
  have hiAM : Integrable (fun x => A x * M x) μ := hiA.mul_bdd hM.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bM x)
  have he : (∫ x, A x * M x ∂μ) - (∫ x, A x ∂μ) * m =
      ∫ x, A x * (M x - m) ∂μ := by
    rw [show (fun x => A x * (M x - m)) = fun x => A x * M x - A x * m by
      funext x; ring, integral_sub hiAM (hiA.mul_const m), integral_mul_const]
  have hi : Integrable (fun x => A x * (M x - m)) μ := by
    convert hiAM.sub (hiA.mul_const m) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change A x * (M x - m) = A x * M x - A x * m
    ring
  change |(∫ x, A x * M x ∂μ) - (∫ x, A x ∂μ) * m| ≤ _
  rw [he]
  calc
    _ ≤ ∫ x, |A x * (M x - m)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (2 * C) * Q x ∂μ := by
      apply integral_mono hi.abs (hiQ.const_mul _)
      intro x
      change |A x * (M x - m)| ≤ 2 * C * Q x
      rw [abs_mul]
      calc
        _ ≤ |A x| * 2 := mul_le_mul_of_nonneg_left
          (magnetic_centered_spin_bound μ bM x) (abs_nonneg _)
        _ ≤ (C * Q x) * 2 := mul_le_mul_of_nonneg_right (bA x) (by norm_num)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

private lemma magnetic_abs_five (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  linarith

theorem fieldFourthTransform_relative_bound {ζ : ℝ} (hζ : 0 ≤ ζ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R) (hS : Measurable S)
    (bM : ∀ x, |M x| ≤ 1) (hQpos : ∀ x, 0 ≤ Q x) (hQle : ∀ x, Q x ≤ 1)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (bR : ∀ x, |R x| ≤ C * Q x) (bS : ∀ x, |S x| ≤ D * Q x) (z : ℝ) :
    |fieldFourthTransform ζ v F M Q R S z| ≤
      (D + 8 * ζ * C + 3 * ζ + 37 * ζ ^ 2) * fieldCurvatureTransform ζ v F M Q z := by
  let μ := (gaussianReal z v).tilted (fun x => ζ * F x)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)
  let T := fun A : ℝ → ℝ => ∫ x, A x ∂μ
  let m := T M
  let q := T Q
  let V := T (fun x => (M x - m) ^ 2)
  let rc := T (fun x => R x * M x) - T R * m
  let qv := T (fun x => (Q x) ^ 2) - q ^ 2
  let qc := T (fun x => Q x * (M x - m) ^ 2) - q * V
  let mc := T (fun x => (M x - m) ^ 4) - 3 * V ^ 2
  have bQ : ∀ x, |Q x| ≤ 1 := fun x => by rw [abs_of_nonneg (hQpos x)]; exact hQle x
  have bRb : ∀ x, |R x| ≤ C := fun x => (bR x).trans
    (mul_le_of_le_one_right hC (hQle x))
  have hiQ : Integrable Q μ := Integrable.of_bound hQ.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bQ x)
  have hiS : Integrable S μ := (hiQ.const_mul D).mono' hS.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bS x)
  have hSb : |T S| ≤ D * q := by
    calc
      _ ≤ ∫ x, |S x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, D * Q x ∂μ := integral_mono hiS.abs (hiQ.const_mul D) bS
      _ = _ := integral_const_mul _ _
  have hrc : |rc| ≤ 2 * C * q := magnetic_relative_centered_bound μ hM hQ hR bM bQ bR
  have hqv0 := magnetic_nonnegative_spin_variance_bound μ hQ hQpos hQle
  have hqv : |qv| ≤ q := by rw [abs_of_nonneg hqv0.1]; exact hqv0.2
  have hqc : |qc| ≤ 5 * q := magnetic_weighted_variance_bound μ hM hQ bM bQ hQpos
  have hmc : |mc| ≤ 7 * V := magnetic_centered_fourth_cumulant_bound μ hM bM
  have hq : 0 ≤ q := integral_nonneg hQpos
  have hV : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have hcurv : fieldCurvatureTransform ζ v F M Q z = q + ζ * V := by
    dsimp only [q, V, m, T]
    rw [magnetic_centered_second μ hM bM]
    rfl
  have he := fieldFourthTransform_centered ζ v (S := S) hF hG hM hQ hR bM bQ bRb z
  change fieldFourthTransform ζ v F M Q R S z =
    T S + 4 * ζ * rc + 3 * ζ * qv + 6 * ζ ^ 2 * qc + ζ ^ 3 * mc at he
  rw [he, hcurv]
  have h4 : |4 * ζ * rc| ≤ 4 * ζ * (2 * C * q) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * ζ)]
    exact mul_le_mul_of_nonneg_left hrc (by positivity)
  have h3 : |3 * ζ * qv| ≤ 3 * ζ * q := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * ζ)]
    exact mul_le_mul_of_nonneg_left hqv (by positivity)
  have h6 : |6 * ζ ^ 2 * qc| ≤ 6 * ζ ^ 2 * (5 * q) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 * ζ ^ 2)]
    exact mul_le_mul_of_nonneg_left hqc (by positivity)
  have h7 : |ζ ^ 3 * mc| ≤ ζ ^ 3 * (7 * V) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ζ ^ 3)]
    exact mul_le_mul_of_nonneg_left hmc (by positivity)
  calc
    _ ≤ |T S| + |4 * ζ * rc| + |3 * ζ * qv| + |6 * ζ ^ 2 * qc| + |ζ ^ 3 * mc| :=
      magnetic_abs_five _ _ _ _ _
    _ ≤ D * q + 4 * ζ * (2 * C * q) + 3 * ζ * q + 6 * ζ ^ 2 * (5 * q) + ζ ^ 3 * (7 * V) := by
      linarith
    _ ≤ (D + 8 * ζ * C + 3 * ζ + 37 * ζ ^ 2) * (q + ζ * V) := by
      let L := D + 8 * ζ * C + 3 * ζ + 30 * ζ ^ 2
      let K := D + 8 * ζ * C + 3 * ζ + 37 * ζ ^ 2
      have hLK : L ≤ K := by dsimp only [L, K] <;> nlinarith [sq_nonneg ζ]
      have h7K : 7 * ζ ^ 2 ≤ K := by
        dsimp only [K]
        nlinarith [sq_nonneg ζ, mul_nonneg hζ hC]
      have h1 := mul_le_mul_of_nonneg_right hLK hq
      have h2 := mul_le_mul_of_nonneg_right h7K (mul_nonneg hζ hV)
      dsimp only [L, K] at h1 h2
      nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFiniteFourth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative fourth derivatives for the actual finite Ising field recursion,
and the bounded coefficients needed for inverse-coordinate comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticFourthRatioCap_nonneg (L : List (ℝ × ℝ≥0)) :
    0 ≤ magneticFourthRatioCap L := by
  induction L with
  | nil => norm_num [magneticFourthRatioCap]
  | cons av L ih =>
    change 0 ≤ magneticFourthRatioCap L + 8 * |av.1| * magneticThirdRatioCap L +
      3 * |av.1| + 37 * av.1 ^ 2
    have ht := magneticThirdRatioCap_nonneg L
    positivity

lemma field_logCosh_fourth_relative (z : ℝ) :
    |fieldLogCoshFourth z| ≤ 6 * (1 / (Real.cosh z) ^ 2) := by
  let q := 1 / (Real.cosh z) ^ 2
  have hq : 0 ≤ q := by dsimp only [q] <;> positivity
  have hq1 : q ≤ 1 := (le_abs_self q).trans (field_tanh_second_bound z)
  have hm2 : (Real.tanh z) ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (field_abs_tanh_le_one z) 2
    simpa only [sq_abs, one_pow] using h
  change |-2 * q ^ 2 + 4 * (Real.tanh z) ^ 2 * q| ≤ 6 * q
  have h1 : |-2 * q ^ 2| ≤ 2 * q := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg q)]
    nlinarith
  have h2 : |4 * (Real.tanh z) ^ 2 * q| ≤ 4 * q := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hm2)]
  exact (abs_add_le _ _).trans (by linarith)

theorem fieldScalarLogCoshFourth_relative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1) (z : ℝ) :
    |fieldScalarFourth L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2)
        (fun x => -2 * Real.tanh x / (Real.cosh x) ^ 2) fieldLogCoshFourth z| ≤
      magneticFourthRatioCap L * fieldScalarSecond L
        (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) z := by
  induction L generalizing z with
  | nil => exact field_logCosh_fourth_relative z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hm : Measurable Real.tanh := by
      change Measurable (fun x : ℝ => Real.tanh x)
      simp only [Real.tanh_eq]
      fun_prop
    have ha := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      hm field_abs_tanh_le_one
    have hq := fieldScalarLogCoshSecond_regular L ht
    have hr := fieldScalarThird_regular L ht measurable_logCosh logCosh_linearGrowth
      hm (by fun_prop) (by fun_prop) zero_le_one field_abs_tanh_le_one
      field_tanh_second_bound field_logCosh_third_bound
    have hterminal : Measurable fieldLogCoshFourth := by
      unfold fieldLogCoshFourth
      fun_prop
    have hs := fieldScalarFourth_regular L ht measurable_logCosh logCosh_linearGrowth
      hm (by fun_prop) (by fun_prop) hterminal zero_le_one field_abs_tanh_le_one
      field_tanh_second_bound field_logCosh_third_bound field_logCosh_fourth_bound
    have hq1 (x : ℝ) : fieldScalarSecond L (fun x => Real.log (Real.cosh x)) Real.tanh
        (fun x => 1 / (Real.cosh x) ^ 2) x ≤ 1 := by
      have hh := fieldScalarLogCoshSecond_le_spin_variance L ht htζ x
      linarith [sq_nonneg (fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh x)]
    have hp := (hL av List.mem_cons_self).le
    have he := fieldFourthTransform_relative_bound hp av.2 hv.1 hv.2 ha.1 hq.1 hr.1 hs.1
      ha.2 (fun x => (fieldScalarLogCoshSecond_pos L ht x).le) hq1
      (magneticThirdRatioCap_nonneg L) (magneticFourthRatioCap_nonneg L)
      (fieldScalarLogCoshThird_relative L ht) (ih ht htζ) z
    simpa only [fieldScalarFourth, fieldScalarSecond, fieldScalarMean, magneticFourthRatioCap,
      abs_of_nonneg hp, fieldCurvatureTransform] using he

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual scalar curvature satisfies the differentiated heat equation.
The computation uses only four derivatives of the finite scalar value. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticHeatCurvature_eq (P : MagneticContinuationJet) (F : ℝ → ℝ)
    (hF : Measurable F) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatCurvature P F ζ q =
      fieldCurvatureTransform ζ (Real.toNNReal q.1) F P.value P.first q.2 := by
  unfold magneticHeatCurvature fieldCurvatureTransform
  rw [field_gaussianTiltAverage_eq_transition q.1 ζ hF P.mFirst,
    field_gaussianTiltAverage_eq_transition q.1 ζ (a := fun y => (P.value y) ^ 2)
      hF (P.mValue.pow_const 2),
    field_gaussianTiltAverage_eq_transition q.1 ζ hF P.mValue]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint heat derivatives of the mean spin and of a bounded continuation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticHeatMean_eq (P : MagneticContinuationJet) (F : ℝ → ℝ)
    (hF : Measurable F) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatMean P F ζ q =
      fieldSpinTransition ζ (Real.toNNReal q.1) F P.value q.2 := by
  exact congrFun (field_gaussianTiltAverage_eq_transition q.1 ζ hF P.mValue) q.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarSlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-tail Gaussian slabs have a unique bias at every
interior prescribed magnetization. These are the inverse coordinates used
in the finite-step parabolic comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabMean_eq (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v z : ℝ) :
    magneticScalarSlabMean L ζ v z =
      magneticHeatMean (magneticLogCoshMeanJet L hL)
        (fieldScalarValue L (fun x => Real.log (Real.cosh x))) ζ (v, z) := by
  exact (magneticHeatMean_eq (magneticLogCoshMeanJet L hL) _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1 ζ (v, z)).symm

lemma magneticScalarSlab_lower (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    |z| - Real.log 2 ≤ gaussianOperator ζ (Real.toNNReal v)
      (fieldScalarValue L (fun x => Real.log (Real.cosh x))) z := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hp : ∀ x, 1 * x + -Real.log 2 ≤
      fieldScalarValue L (fun y => Real.log (Real.cosh y)) x := by
    apply affine_le_fieldScalarValue L hL measurable_logCosh logCosh_linearGrowth
    intro x
    simpa only [one_mul, sub_eq_add_neg] using signed_bias_le_logcosh x
  have hm : ∀ x, (-1) * x + -Real.log 2 ≤
      fieldScalarValue L (fun y => Real.log (Real.cosh y)) x := by
    apply affine_le_fieldScalarValue L hL measurable_logCosh logCosh_linearGrowth
    intro x
    simpa only [Real.cosh_neg, neg_mul, one_mul, sub_eq_add_neg]
      using signed_bias_le_logcosh (-x)
  have hplus := affine_le_gaussianOperator hF.1 hF.2 hζ (Real.toNNReal v)
    1 (-Real.log 2) hp z
  have hminus := affine_le_gaussianOperator hF.1 hF.2 hζ (Real.toNNReal v)
    (-1) (-Real.log 2) hm z
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    simpa only [one_mul, sub_eq_add_neg] using hplus
  · rw [abs_of_nonpos hz]
    simpa only [neg_mul, one_mul, sub_eq_add_neg] using hminus

lemma magneticScalarSlab_value_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v z : ℝ) :
    HasDerivAt
      (gaussianOperator ζ (Real.toNNReal v)
        (fieldScalarValue L (fun x => Real.log (Real.cosh x))))
      (magneticScalarSlabMean L ζ v z) z := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  obtain ⟨K, hK, bK⟩ := P.bValue
  exact hasDerivAt_gaussianOperator ζ (Real.toNNReal v) hF.1 hF.2 P.mValue hK bK
    (hasDerivAt_fieldScalarLogCosh L hL) z

lemma magneticScalarSlab_curvature_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    0 < fieldCurvatureTransform ζ (Real.toNNReal v)
      (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
      (magneticLogCoshMeanJet L hL).value (magneticLogCoshMeanJet L hL).first z := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  obtain ⟨K, _, bK⟩ := P.bFirst
  have hpos : ∀ x, 0 < P.first x := fieldScalarLogCoshSecond_pos L hL
  have hp := fieldSpinTransition_pos ζ (Real.toNNReal v) hF.1 hF.2 P.mFirst bK hpos z
  obtain ⟨D, _, bD⟩ := P.bValue
  have hs := fieldSpinTransition_square_le ζ (Real.toNNReal v) hF.1 hF.2 P.mValue bD z
  exact add_pos_of_pos_of_nonneg hp (mul_nonneg hζ (sub_nonneg.mpr hs))

lemma magneticScalarSlabMean_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v z : ℝ) :
    HasDerivAt (magneticScalarSlabMean L ζ v)
      (fieldCurvatureTransform ζ (Real.toNNReal v)
        (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
        (magneticLogCoshMeanJet L hL).value (magneticLogCoshMeanJet L hL).first z) z := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  obtain ⟨K, hK, bK⟩ := P.bValue
  obtain ⟨C, _, bC⟩ := P.bFirst
  have hd := hasDerivAt_fieldSpinTransition ζ (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mValue P.mFirst hK hK bK bK bC
    (hasDerivAt_fieldScalarLogCosh L hL) P.dValue z
  change HasDerivAt (fieldSpinTransition ζ (Real.toNNReal v) _ P.value)
    (fieldCurvatureTransform ζ (Real.toNNReal v) _ P.value P.first z) z
  simpa only [fieldCurvatureTransform, pow_two] using hd

lemma magneticScalarSlabMean_strictMono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v : ℝ) :
    StrictMono (magneticScalarSlabMean L ζ v) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(magneticScalarSlabMean_hasDerivAt L hL ζ v z).deriv]
  exact magneticScalarSlab_curvature_pos L hL hζ v z

lemma magneticScalarSlabMean_bias (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    magneticScalarSlabMean L ζ v (magneticScalarSlabBias L ζ v s) = s := by
  apply Function.invFun_eq
  exact exists_mean_root_of_linear_lower (magneticScalarSlab_value_hasDerivAt L hL ζ v)
    (magneticScalarSlab_lower L hL hζ v) hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial and variance derivatives of the genuine finite-tail inverse
curvature. The minimizing bias is constructed by coercivity, and no
inverse-regularity assumption remains in these statements. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabBias_continuousAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    ContinuousAt (magneticScalarSlabBias L ζ v) s := by
  have hmono := magneticScalarSlabMean_strictMono L hL hζ v
  apply tendsto_order.2
  constructor
  · intro l hl
    have hlt : magneticScalarSlabMean L ζ v l < s := by
      rw [← magneticScalarSlabMean_bias L hL hζ hs v]
      exact hmono hl
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2,
      Ioi_mem_nhds hlt] with t ht hlt'
    apply hmono.lt_iff_lt.mp
    rw [magneticScalarSlabMean_bias L hL hζ (abs_lt.mpr ht) v]
    exact hlt'
  · intro u hu
    have htu : s < magneticScalarSlabMean L ζ v u := by
      rw [← magneticScalarSlabMean_bias L hL hζ hs v]
      exact hmono hu
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2,
      Iio_mem_nhds htu] with t ht htu'
    apply hmono.lt_iff_lt.mp
    rw [magneticScalarSlabMean_bias L hL hζ (abs_lt.mpr ht) v]
    exact htu'

lemma magneticScalarSlabBias_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    let z := magneticScalarSlabBias L ζ v s
    let P := magneticLogCoshMeanJet L hL
    let F := fieldScalarValue L (fun x => Real.log (Real.cosh x))
    HasDerivAt (magneticScalarSlabBias L ζ v)
      (fieldCurvatureTransform ζ (Real.toNNReal v) F P.value P.first z)⁻¹ s := by
  apply HasDerivAt.of_local_left_inverse
    (magneticScalarSlabBias_continuousAt_spin L hL hζ hs v)
    (magneticScalarSlabMean_hasDerivAt L hL ζ v _)
    (magneticScalarSlab_curvature_pos L hL hζ v _).ne'
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact magneticScalarSlabMean_bias L hL hζ (abs_lt.mpr ht) v

lemma magneticScalarInverseCurvature_eq (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) :
    magneticScalarInverseCurvature L hL ζ v s =
      fieldCurvatureTransform ζ (Real.toNNReal v)
        (fieldScalarValue L (fun x => Real.log (Real.cosh x)))
        (magneticLogCoshMeanJet L hL).value (magneticLogCoshMeanJet L hL).first
        (magneticScalarSlabBias L ζ v s) := by
  exact magneticHeatCurvature_eq _ _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1 ζ _

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of the finite Gaussian slab and its physical inverse
coordinates, including zero Gaussian variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma continuous_magneticHeatMean (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Continuous F) (hG : HasLinearGrowth F) (ζ : ℝ) :
    Continuous (magneticHeatMean P F ζ) := by
  obtain ⟨C, L, hC, hL, hB⟩ := hG
  obtain ⟨M, hM, bM⟩ := P.bValue
  have hP : Continuous P.value := continuous_iff_continuousAt.mpr
    fun z => (P.dValue z).continuousAt
  exact continuous_field_gaussian_tilt_average
    (hF.comp continuous_snd) (hP.comp continuous_snd) continuous_fst continuous_snd
    hC hL hM (fun _ z => by simpa only [Real.norm_eq_abs] using hB z)
    (fun _ z => bM z) ζ

lemma continuous_magneticHeatCurvature (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Continuous F) (hG : HasLinearGrowth F) (ζ : ℝ) :
    Continuous (magneticHeatCurvature P F ζ) := by
  obtain ⟨C, L, hC, hL, hB⟩ := hG
  obtain ⟨M, hM, bM⟩ := P.bFirst
  have hP : Continuous P.first := continuous_iff_continuousAt.mpr
    fun z => (P.dFirst z).continuousAt
  have hfirst : Continuous (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F P.first q.2) :=
    continuous_field_gaussian_tilt_average
      (hF.comp continuous_snd) (hP.comp continuous_snd) continuous_fst continuous_snd
      hC hL hM (fun _ z => by simpa only [Real.norm_eq_abs] using hB z)
      (fun _ z => bM z) ζ
  exact hfirst.add (((continuous_magneticHeatMean P.square F hF
    ⟨C, L, hC, hL, hB⟩ ζ).sub
      ((continuous_magneticHeatMean P F hF ⟨C, L, hC, hL, hB⟩ ζ).pow 2)).const_mul ζ)

lemma continuous_magneticScalarSlabMean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) :
    Continuous (fun q : ℝ × ℝ => magneticScalarSlabMean L ζ q.1 q.2) := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hc : Continuous (fieldScalarValue L (fun z => Real.log (Real.cosh z))) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_fieldScalarLogCosh L hL z).continuousAt
  have he : (fun q : ℝ × ℝ => magneticScalarSlabMean L ζ q.1 q.2) =
      magneticHeatMean (magneticLogCoshMeanJet L hL)
        (fieldScalarValue L (fun z => Real.log (Real.cosh z))) ζ := by
    funext q
    exact magneticScalarSlabMean_eq L hL ζ q.1 q.2
  rw [he]
  exact continuous_magneticHeatMean _ _ hc hF.2 ζ

lemma continuousAt_parametric_strict_inverse (M b : ℝ → ℝ → ℝ)
    (hc : Continuous (fun q : ℝ × ℝ => M q.1 q.2))
    (hm : ∀ v, StrictMono (M v))
    (hroot : ∀ v s, |s| < 1 → M v (b v s) = s)
    {s v : ℝ} (hs : |s| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => b q.1 q.2) (v, s) := by
  have hn : ∀ᶠ q : ℝ × ℝ in 𝓝 (v, s), |q.2| < 1 :=
    (isOpen_lt continuous_snd.abs continuous_const).mem_nhds hs
  apply tendsto_order.2
  constructor
  · intro l hl
    have hlt : M v l < s := by
      rw [← hroot v s hs]
      exact hm v hl
    have hlc : Continuous (fun q : ℝ × ℝ => M q.1 l) :=
      hc.comp (continuous_fst.prodMk continuous_const)
    have hN : ∀ᶠ q : ℝ × ℝ in 𝓝 (v, s), M q.1 l < q.2 :=
      (isOpen_lt hlc continuous_snd).mem_nhds hlt
    filter_upwards [hn, hN] with q hq hq'
    apply (hm q.1).lt_iff_lt.mp
    rw [hroot q.1 q.2 hq]
    exact hq'
  · intro u hu
    have htu : s < M v u := by
      rw [← hroot v s hs]
      exact hm v hu
    have huc : Continuous (fun q : ℝ × ℝ => M q.1 u) :=
      hc.comp (continuous_fst.prodMk continuous_const)
    have hN : ∀ᶠ q : ℝ × ℝ in 𝓝 (v, s), q.2 < M q.1 u :=
      (isOpen_lt continuous_snd huc).mem_nhds htu
    filter_upwards [hn, hN] with q hq hq'
    apply (hm q.1).lt_iff_lt.mp
    rw [hroot q.1 q.2 hq]
    exact hq'


lemma magneticScalarSlabBias_continuousAt_joint (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => magneticScalarSlabBias L ζ q.1 q.2) (v, s) := by
  exact continuousAt_parametric_strict_inverse _ _
    (continuous_magneticScalarSlabMean L hL ζ)
    (magneticScalarSlabMean_strictMono L hL hζ)
    (fun v s hs => magneticScalarSlabMean_bias L hL hζ hs v) hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual slab inverse curvature extends continuously to both spin
endpoints. The uniform bound by 1-s² gives joint boundary continuity in
the variance parameter without an asymptotic expansion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarInverseCurvature_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v s : ℝ) :
    0 < magneticScalarInverseCurvature L hL ζ v s := by
  rw [magneticScalarInverseCurvature_eq]
  exact magneticScalarSlab_curvature_pos L hL hζ v _

lemma magneticScalarInverseCurvature_le_spin_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hs : |s| < 1) (v : ℝ) :
    magneticScalarInverseCurvature L hL ζ v s ≤ 1 - s ^ 2 := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  obtain ⟨K, _, bK⟩ := P.bValue
  obtain ⟨C, _, bC⟩ := P.bFirst
  have hbound (y : ℝ) : P.first y + (P.value y) ^ 2 ≤ 1 := by
    have hh := fieldScalarLogCoshSecond_le_spin_variance L hL hL1 y
    change P.first y ≤ 1 - (P.value y) ^ 2 at hh
    linarith
  have hh := fieldCurvatureTransform_le_spin_variance hζ1 (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mFirst bK bC hbound (magneticScalarSlabBias L ζ v s)
  change _ ≤ 1 - (magneticScalarSlabMean L ζ v (magneticScalarSlabBias L ζ v s)) ^ 2 at hh
  rw [magneticScalarSlabMean_bias L hL hζ hs v] at hh
  rwa [magneticScalarInverseCurvature_eq]

lemma magneticScalarInverseCurvature_continuousAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => magneticScalarInverseCurvature L hL ζ q.1 q.2) (v, s) := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hc : Continuous (fieldScalarValue L (fun z => Real.log (Real.cosh z))) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_fieldScalarLogCosh L hL z).continuousAt
  have hh := continuous_magneticHeatCurvature (magneticLogCoshMeanJet L hL) _ hc hF.2 ζ
  have hb := magneticScalarSlabBias_continuousAt_joint L hL hζ (v := v) hs
  exact hh.continuousAt.comp' (continuousAt_fst.prodMk hb)

lemma closedMagneticScalarCurvature_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (q : ℝ × ℝ) :
    0 ≤ closedMagneticScalarCurvature L hL ζ q := by
  unfold closedMagneticScalarCurvature
  split_ifs
  · exact (magneticScalarInverseCurvature_pos L hL hζ q.1 q.2).le
  · exact le_rfl

lemma closedMagneticScalarCurvature_le_spin_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (q : ℝ × ℝ) (hq : q.2 ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ q ≤ 1 - q.2 ^ 2 := by
  unfold closedMagneticScalarCurvature
  split_ifs with hs
  · exact magneticScalarInverseCurvature_le_spin_variance L hL hL1 hζ hζ1 hs q.1
  · have hh := mul_nonneg (by linarith [hq.1] : 0 ≤ q.2 + 1)
      (by linarith [hq.2] : 0 ≤ 1 - q.2)
    nlinarith

lemma continuousOn_closedMagneticScalarCurvature (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ContinuousOn (closedMagneticScalarCurvature L hL ζ)
      (univ ×ˢ Icc (-1 : ℝ) 1) := by
  intro p hp
  by_cases hs : |p.2| < 1
  · have he : closedMagneticScalarCurvature L hL ζ =ᶠ[𝓝 p]
        (fun q => magneticScalarInverseCurvature L hL ζ q.1 q.2) := by
      filter_upwards [(isOpen_lt continuous_snd.abs continuous_const).mem_nhds hs] with q hq
      exact ite_eq_left hq
    exact ((magneticScalarInverseCurvature_continuousAt L hL hζ hs).congr_of_eventuallyEq he).continuousWithinAt
  · have hps : |p.2| = 1 := le_antisymm (abs_le.mpr hp.2) (le_of_not_gt hs)
    have hps2 : p.2 ^ 2 = 1 := by nlinarith [sq_abs p.2]
    have he : closedMagneticScalarCurvature L hL ζ p = 0 := ite_eq_right hs
    change Tendsto (closedMagneticScalarCurvature L hL ζ)
      (𝓝[univ ×ˢ Icc (-1 : ℝ) 1] p) (𝓝 _)
    rw [he]
    have hg : Tendsto (fun q : ℝ × ℝ => 1 - q.2 ^ 2)
        (𝓝[univ ×ˢ Icc (-1 : ℝ) 1] p) (𝓝 0) := by
      have hc : ContinuousWithinAt (fun q : ℝ × ℝ => 1 - q.2 ^ 2)
          (univ ×ˢ Icc (-1 : ℝ) 1) p := by fun_prop
      change Tendsto _ _ (𝓝 (1 - p.2 ^ 2)) at hc
      simpa only [hps2, sub_self] using hc
    apply squeeze_zero' (Eventually.of_forall (closedMagneticScalarCurvature_nonneg L hL hζ)) ?_ hg
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact closedMagneticScalarCurvature_le_spin_variance L hL hL1 hζ hζ1 q hq.2

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal inverse-coordinate PDE of a finite Gaussian slab, with
spatial derivatives and inverse regularity discharged. Time here denotes
applied variance; reversing it gives the manuscript's backward equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarInverseCurvature_eq_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v s : ℝ) :
    magneticScalarInverseCurvature L hL ζ v s =
      (magneticScalarSlabJet L hL ζ v).first (magneticScalarSlabBias L ζ v s) := by
  rw [magneticScalarInverseCurvature_eq]
  simp only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two]

lemma magneticScalarSlabJet_curvature_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    0 < (magneticScalarSlabJet L hL ζ v).first z := by
  have hp := magneticScalarSlab_curvature_pos L hL hζ v z
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two] using hp

lemma magneticScalarSlabBias_hasDerivAt_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabBias L ζ v)
      (1 / (magneticScalarSlabJet L hL ζ v).first (magneticScalarSlabBias L ζ v s)) s := by
  have hd := magneticScalarSlabBias_hasDerivAt_spin L hL hζ hs v
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two, one_div] using hd

lemma magneticScalarInverseCurvature_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarInverseCurvature L hL ζ v)
      (magneticScalarInverseSlope L hL ζ v s) s := by
  have he : magneticScalarInverseCurvature L hL ζ v =
      fun t => (magneticScalarSlabJet L hL ζ v).first (magneticScalarSlabBias L ζ v t) :=
    funext (magneticScalarInverseCurvature_eq_jet L hL ζ v)
  rw [he]
  exact inverse_mean_pullback_derivative (magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v)
    ((magneticScalarSlabJet L hL ζ v).dFirst _)

lemma magneticScalarInverseSlope_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarInverseSlope L hL ζ v)
      (magneticScalarInverseSecond L hL ζ v s) s := by
  let J := magneticScalarSlabJet L hL ζ v
  let b := magneticScalarSlabBias L ζ v s
  have hd := inverse_mean_pullback_quotient
    (magneticScalarSlabJet_curvature_pos L hL hζ v b).ne'
    (magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v) rfl rfl
    (J.dSecond b) (J.dFirst b)
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp only [magneticScalarInverseSecond, J, b]
    ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounded potential for the actual finite-slab inverse-curvature
comparison. The cap depends on exponents, not on the variance parameter. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticScalarSlabJet_eq_cons (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 < ζ) (v : ℝ) :
    magneticScalarSlabJet L hL ζ v =
      magneticLogCoshMeanJet ((ζ, Real.toNNReal v) :: L)
        (by intro av hav; rcases List.mem_cons.mp hav with h | h
            · simpa only [h] using hζ
            · exact hL av h) := by
  apply MagneticContinuationJet.eq_of_value_eq
  rfl

lemma magneticScalarInverse_weighted_second_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (v s : ℝ) :
    |magneticScalarInverseCurvature L hL ζ v s * magneticScalarInverseSecond L hL ζ v s| ≤
      magneticSlabPotentialCap L ζ := by
  let K := (ζ, Real.toNNReal v) :: L
  have hK : ∀ av ∈ K, 0 < av.1 := by
    intro av hav
    rcases List.mem_cons.mp hav with h | h
    · simpa only [h] using hζ
    · exact hL av h
  have hK1 : ∀ av ∈ K, av.1 ≤ 1 := by
    intro av hav
    rcases List.mem_cons.mp hav with h | h
    · simpa only [h] using hζ1
    · exact hL1 av h
  let b := magneticScalarSlabBias L ζ v s
  let J := magneticScalarSlabJet L hL ζ v
  have hq : 0 < J.first b := magneticScalarSlabJet_curvature_pos L hL hζ.le v b
  have hr : |J.second b| ≤ magneticThirdRatioCap K * J.first b := by
    have hh := fieldScalarLogCoshThird_relative K hK b
    have he := magneticScalarSlabJet_eq_cons L hL hζ v
    change |J.second b| ≤ _
    dsimp only [J]
    rw [he]
    exact hh
  have hd : |J.third b| ≤ magneticFourthRatioCap K * J.first b := by
    have hh := fieldScalarLogCoshFourth_relative K hK hK1 b
    dsimp only [J]
    rw [magneticScalarSlabJet_eq_cons L hL hζ v]
    exact hh
  have hrq : |J.second b / J.first b| ≤ magneticThirdRatioCap K := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr hr
  have hdq : |J.third b / J.first b| ≤ magneticFourthRatioCap K := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr hd
  have he : magneticScalarInverseCurvature L hL ζ v s *
      magneticScalarInverseSecond L hL ζ v s =
      J.third b / J.first b - (J.second b / J.first b) ^ 2 := by
    rw [magneticScalarInverseCurvature_eq_jet]
    dsimp only [magneticScalarInverseSecond, J, b]
    field_simp [hq.ne']
  rw [he]
  have hr2 : |(J.second b / J.first b) ^ 2| ≤ (magneticThirdRatioCap K) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hrq 2
  have hh := (abs_sub _ _).trans (add_le_add hdq hr2)
  simpa only [magneticSlabPotentialCap, K, magneticFourthRatioCap, magneticThirdRatioCap] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabClosedDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed-spin-interval derivatives of the finite slab. The two endpoints
are constant zero in time, while all spatial derivatives are used only
in the open spin interval. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticScalarCurvature_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticScalarCurvature L hL ζ (v, u))
      (closedMagneticScalarSlope L hL ζ (v, s)) s := by
  have he : (fun u => closedMagneticScalarCurvature L hL ζ (v, u)) =ᶠ[𝓝 s]
      magneticScalarInverseCurvature L hL ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticScalarSlope, hs, ite_true, if_true] using
    (magneticScalarInverseCurvature_hasDerivAt_spin L hL hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticScalarSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticScalarSlope L hL ζ (v, u))
      (closedMagneticScalarSecond L hL ζ (v, s)) s := by
  have he : (fun u => closedMagneticScalarSlope L hL ζ (v, u)) =ᶠ[𝓝 s]
      magneticScalarInverseSlope L hL ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticScalarSecond, hs, ite_true, if_true] using
    (magneticScalarInverseSlope_hasDerivAt L hL hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticScalarCurvature_endpoints (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) :
    closedMagneticScalarCurvature L hL ζ (v, -1) = 0 ∧
      closedMagneticScalarCurvature L hL ζ (v, 1) = 0 := by
  simp only [closedMagneticScalarCurvature, abs_neg, abs_one, lt_self_iff_false, ite_false, if_false,
    and_self]

lemma closedMagneticScalarCurvature_le_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (q : ℝ × ℝ) (hq : q.2 ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ q ≤ 1 := by
  exact (closedMagneticScalarCurvature_le_spin_variance L hL hL1 hζ hζ1 q hq).trans
    (by linarith [sq_nonneg q.2])

lemma closedMagneticScalarCurvature_weighted_second_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (q : ℝ × ℝ) :
    |closedMagneticScalarCurvature L hL ζ q * closedMagneticScalarSecond L hL ζ q| ≤
      magneticSlabPotentialCap L ζ := by
  by_cases hs : |q.2| < 1
  · simpa only [closedMagneticScalarCurvature, closedMagneticScalarSecond, hs, ite_true, if_true] using
      magneticScalarInverse_weighted_second_bound L hL hL1 hζ hζ1 q.1 q.2
  · simp only [closedMagneticScalarCurvature, closedMagneticScalarSecond, hs, ite_false, if_false,
      mul_zero, abs_zero]
    exact add_nonneg (magneticFourthRatioCap_nonneg _) (sq_nonneg _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative derivative bounds for the ordinary Gaussian root step.
No positive cascade exponent is needed at this level. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticScalarSlabJet_zero_third_relative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v z : ℝ) :
    |(magneticScalarSlabJet L hL 0 v).second z| ≤
      magneticThirdRatioCap L * (magneticScalarSlabJet L hL 0 v).first z := by
  let P := magneticLogCoshMeanJet L hL
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have htan : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hM : ∀ z, |P.value z| ≤ 1 :=
    (fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
      htan field_abs_tanh_le_one).2
  obtain ⟨B, _, bQ⟩ := P.bFirst
  have hQ : ∀ z, 0 ≤ P.first z := fun z => (fieldScalarLogCoshSecond_pos L hL z).le
  have hR : ∀ z, |P.second z| ≤ magneticThirdRatioCap L * P.first z :=
    fieldScalarLogCoshThird_relative L hL
  have he := fieldThirdTransform_relative_bound (le_refl (0 : ℝ)) (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mFirst P.mSecond hM bQ hQ
    (magneticThirdRatioCap_nonneg L) hR z
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition, P,
    magneticContinuationSecond, fieldThirdTransform, fieldCurvatureTransform,
    fieldTiltSpatial, zero_mul, mul_zero, add_zero] using he

lemma magneticScalarSlabJet_zero_fourth_relative (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1) (v z : ℝ) :
    |(magneticScalarSlabJet L hL 0 v).third z| ≤
      magneticFourthRatioCap L * (magneticScalarSlabJet L hL 0 v).first z := by
  let P := magneticLogCoshMeanJet L hL
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have htan : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hM : ∀ z, |P.value z| ≤ 1 :=
    (fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
      htan field_abs_tanh_le_one).2
  have hQ : ∀ z, 0 ≤ P.first z := fun z => (fieldScalarLogCoshSecond_pos L hL z).le
  have hQ1 : ∀ z, P.first z ≤ 1 := by
    intro z
    have hh := fieldScalarLogCoshSecond_le_spin_variance L hL hL1 z
    change P.first z ≤ 1 - (P.value z) ^ 2 at hh
    linarith [sq_nonneg (P.value z)]
  have hR : ∀ z, |P.second z| ≤ magneticThirdRatioCap L * P.first z :=
    fieldScalarLogCoshThird_relative L hL
  have hS : ∀ z, |P.third z| ≤ magneticFourthRatioCap L * P.first z :=
    fieldScalarLogCoshFourth_relative L hL hL1
  have he := fieldFourthTransform_relative_bound (le_refl (0 : ℝ)) (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mFirst P.mSecond P.mThird hM hQ hQ1
    (magneticThirdRatioCap_nonneg L) (magneticFourthRatioCap_nonneg L) hR hS z
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition, P,
    magneticContinuationThird, magneticContinuationSecond, fieldFourthTransform,
    fieldThirdTransform, fieldCurvatureTransform, fieldTiltSpatial,
    zero_mul, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)] using he

lemma magneticScalarInverse_zero_weighted_second_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1) (v s : ℝ) :
    |magneticScalarInverseCurvature L hL 0 v s * magneticScalarInverseSecond L hL 0 v s| ≤
      magneticSlabPotentialCap L 0 := by
  let b := magneticScalarSlabBias L 0 v s
  let J := magneticScalarSlabJet L hL 0 v
  have hq : 0 < J.first b := magneticScalarSlabJet_curvature_pos L hL (le_refl _) v b
  have hrq : |J.second b / J.first b| ≤ magneticThirdRatioCap L := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (magneticScalarSlabJet_zero_third_relative L hL v b)
  have hdq : |J.third b / J.first b| ≤ magneticFourthRatioCap L := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (magneticScalarSlabJet_zero_fourth_relative L hL hL1 v b)
  have he : magneticScalarInverseCurvature L hL 0 v s * magneticScalarInverseSecond L hL 0 v s =
      J.third b / J.first b - (J.second b / J.first b) ^ 2 := by
    rw [magneticScalarInverseCurvature_eq_jet]
    dsimp only [magneticScalarInverseSecond, J, b]
    field_simp [hq.ne']
  rw [he]
  have hr2 : |(J.second b / J.first b) ^ 2| ≤ (magneticThirdRatioCap L) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hrq 2
  have hh := (abs_sub _ _).trans (add_le_add hdq hr2)
  simpa only [magneticSlabPotentialCap, magneticFourthRatioCap, magneticThirdRatioCap,
    abs_zero, mul_zero, zero_mul, add_zero, zero_pow (by norm_num : 2 ≠ 0)] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScaledBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient bounds for the actual radially scaled inverse
curvature, including its ordinary zero-exponent Gaussian step. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticScalarCurvature_weighted_second_bound_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (p : ℝ × ℝ) :
    |closedMagneticScalarCurvature L hL ζ p * closedMagneticScalarSecond L hL ζ p| ≤
      magneticSlabPotentialCap L ζ := by
  rcases eq_or_lt_of_le hζ with he | hp
  · subst ζ
    by_cases hs : |p.2| < 1
    · simpa only [closedMagneticScalarCurvature, closedMagneticScalarSecond, hs, ite_true, if_true] using
        magneticScalarInverse_zero_weighted_second_bound L hL hL1 p.1 p.2
    · simp only [closedMagneticScalarCurvature, closedMagneticScalarSecond, hs, ite_false, if_false,
        mul_zero, abs_zero]
      exact add_nonneg (magneticFourthRatioCap_nonneg _) (sq_nonneg _)
  · exact closedMagneticScalarCurvature_weighted_second_bound L hL hL1 hp hζ1 p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTailComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-tail comparison with initial inverse-curvature order. The
analytic comparison hypotheses are derived from the actual Gaussian
recursions, leaving only the initial orders for use in a finite induction. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticClosedCurvature_compare_initial_oai (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) (hM1 : ∀ av ∈ M, av.1 ≤ 1)
    {ζ η : ℝ} (hζ : 0 ≤ ζ) (hζη : ζ ≤ η) (hη1 : η ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticScalarCurvature L hL ζ (0, u) ≤
        closedMagneticScalarCurvature M hM η (0, u))
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ (v, s) ≤
      closedMagneticScalarCurvature M hM η (v, s) := by
  have hζ1 := hζη.trans hη1
  have hη := hζ.trans hζη
  have hall := inverse_curvature_parabolic_comparison_bound (A := 1) hv hη hζη
    (closedMagneticScalarCurvature L hL ζ) (closedMagneticScalarTime L hL ζ)
    (closedMagneticScalarSlope L hL ζ) (closedMagneticScalarSecond L hL ζ)
    (closedMagneticScalarCurvature M hM η) (closedMagneticScalarTime M hM η)
    (closedMagneticScalarSlope M hM η) (closedMagneticScalarSecond M hM η)
    ((continuousOn_closedMagneticScalarCurvature L hL hL1 hζ hζ1).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩))
    ((continuousOn_closedMagneticScalarCurvature M hM hM1 hη hη1).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩)) hinit
    (fun t ht u _ => (closedMagneticScalarCurvature_hasDerivAt_time L hL hζ ht.1 u).hasDerivWithinAt)
    (fun t ht u _ => (closedMagneticScalarCurvature_hasDerivAt_time M hM hη ht.1 u).hasDerivWithinAt)
    (fun t _ u hu => closedMagneticScalarCurvature_hasDerivAt_spin L hL hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarCurvature_hasDerivAt_spin M hM hη (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarSlope_hasDerivAt_spin L hL hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarSlope_hasDerivAt_spin M hM hη (abs_lt.mpr hu) t)
    (fun p _ => closedMagneticScalarCurvature_nonneg L hL hζ p)
    (fun p _ => closedMagneticScalarCurvature_nonneg M hM hη p)
    (fun p hp => closedMagneticScalarCurvature_le_one L hL hL1 hζ hζ1 p hp.2)
    (fun p _ => closedMagneticScalarCurvature_weighted_second_bound_nonneg L hL hL1 hζ hζ1 p)
    (fun t _ => by
      obtain ⟨ha, hb⟩ := closedMagneticScalarCurvature_endpoints L hL ζ t
      obtain ⟨hc, hd⟩ := closedMagneticScalarCurvature_endpoints M hM η t
      exact ⟨ha, hc, hb, hd⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact hall (v, s) ⟨⟨hv, le_rfl⟩, hs⟩

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.magneticClosedCurvature_compare_initial_oai := @OAI.InvariantIsing.magneticClosedCurvature_compare_initial_oai
