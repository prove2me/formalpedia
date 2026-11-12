-- Prove2me | solution 1 for OAI.InvariantIsing.closedMagneticSquareContinuationSecond_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:54:52.967339+00:00
-- url     : https://prove2.me/submissions/508834ae-aea5-43ec-a278-34a20b67ebec

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
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_closedMagneticSlabWeighted_hasDerivAt_time

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSpinTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar physical-spin transition and its bounded martingale
properties, including degenerate covariance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_zero_variance (ζ : ℝ) (F a : ℝ → ℝ) (z : ℝ) :
    fieldSpinTransition ζ 0 F a z = a z := by
  rw [fieldSpinTransition, integral_tilted_eq_div, gaussianReal_zero_var]
  simp only [integral_dirac]
  exact mul_div_cancel_left₀ (a z) (Real.exp_ne_zero _)

end InvariantIsing

end

end OAI
end

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticDerivativeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded second derivatives turn convergence of the scalar continuation
into vanishing first derivatives. Applied twice, this gives the endpoint
regularity of the weighted inverse-coordinate continuation curvature. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_derivative_increment_bound {F G D : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : ∀ x, HasDerivAt G (D x) x) (hD : ∀ x, |D x| ≤ L)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    |F (x + h) - F x - h * G x| ≤ L * h ^ 2 := by
  have hLip (y : ℝ) : |G y - G x| ≤ L * |y - x| := by
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (hG z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hD z)
      convex_univ (mem_univ x) (mem_univ y)
    simpa only [Real.norm_eq_abs] using he
  let R := fun z => F z - (z - x) * G x
  have hR (z : ℝ) : HasDerivAt R (G z - G x) z := by
    convert (hF z).sub (((hasDerivAt_id z).sub_const x).mul_const (G x)) using 1 <;>
      first | rfl | simp
  have hB (z : ℝ) (hz : z ∈ Icc x (x + h)) : |G z - G x| ≤ L * h := by
    have hb : |z - x| ≤ h := by rw [abs_of_nonneg (sub_nonneg.mpr hz.1)]; linarith [hz.2]
    exact (hLip z).trans (mul_le_mul_of_nonneg_left hb hL)
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Icc x (x + h)) => (hR z).hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hB z hz)
    (convex_Icc x (x + h)) (left_mem_Icc.mpr (by linarith : x ≤ x + h))
    (right_mem_Icc.mpr (by linarith : x ≤ x + h))
  have hdist : |x + h - x| = h := by rw [add_sub_cancel_left, abs_of_nonneg hh]
  have hRe : R (x + h) - R x = F (x + h) - F x - h * G x := by dsimp only [R] <;> ring
  simp only [Real.norm_eq_abs, hdist] at he
  rw [hRe] at he
  simpa only [pow_two, mul_assoc] using he

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFamilyDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-difference estimates for a varying Gaussian slab. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_family_derivative_tendsto_zero {ι : Type*} {l : Filter ι}
    {F G D : ι → ℝ → ℝ} {x : ι → ℝ} {c L : ℝ}
    (hL : 0 ≤ L) (hF : ∀ i z, HasDerivAt (F i) (G i z) z)
    (hG : ∀ i z, HasDerivAt (G i) (D i z) z) (hD : ∀ i z, |D i z| ≤ L)
    (hlimit : ∀ h : ℝ, Tendsto (fun i => F i (x i + h)) l (𝓝 c)) :
    Tendsto (fun i => G i (x i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let h := ε / (2 * (L + 1))
  have hden : 0 < 2 * (L + 1) := by positivity
  have hh : 0 < h := div_pos hε hden
  have hheq : 2 * (L + 1) * h = ε := by
    dsimp only [h]
    field_simp [hden.ne']
  have hLh : L * h ^ 2 < ε * h / 2 := by
    have hh2 : 0 < h ^ 2 := sq_pos_of_pos hh
    nlinarith
  have hinc : Tendsto (fun i => F i (x i + h) - F i (x i)) l (𝓝 0) := by
    simpa only [add_zero, sub_self] using (hlimit h).sub (hlimit 0)
  have hevent := (Metric.tendsto_nhds.mp hinc) (ε * h / 2) (by positivity)
  filter_upwards [hevent] with i hi
  rw [Real.dist_eq, sub_zero] at hi ⊢
  have hr := magnetic_derivative_increment_bound hL (hF i) (hG i) (hD i) (x i) hh.le
  have hg : |h * G i (x i)| ≤ |F i (x i + h) - F i (x i)| + L * h ^ 2 := by
    calc
      _ = |(F i (x i + h) - F i (x i)) -
          (F i (x i + h) - F i (x i) - h * G i (x i))| := by congr 1; ring
      _ ≤ |F i (x i + h) - F i (x i)| +
          |F i (x i + h) - F i (x i) - h * G i (x i)| := abs_sub _ _
      _ ≤ _ := add_le_add_right hr _
  rw [abs_mul, abs_of_pos hh] at hg
  nlinarith

lemma magnetic_family_second_tendsto_zero {ι : Type*} {l : Filter ι}
    {F G D E : ι → ℝ → ℝ} {x : ι → ℝ} {c L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hF : ∀ i z, HasDerivAt (F i) (G i z) z)
    (hG : ∀ i z, HasDerivAt (G i) (D i z) z)
    (hD : ∀ i z, HasDerivAt (D i) (E i z) z)
    (bD : ∀ i z, |D i z| ≤ L) (bE : ∀ i z, |E i z| ≤ K)
    (hlimit : ∀ h : ℝ, Tendsto (fun i => F i (x i + h)) l (𝓝 c)) :
    Tendsto (fun i => D i (x i)) l (𝓝 0) := by
  apply magnetic_family_derivative_tendsto_zero hK hG hD bE
  intro h
  apply magnetic_family_derivative_tendsto_zero hL hF hG bD
  intro k
  simpa only [add_assoc] using hlimit (h + k)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticMeanShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform mean-shift estimate from the Ising variance bound. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_mean_shift_deficit {M Q : ℝ → ℝ}
    (hd : ∀ z, HasDerivAt M (Q z) z)
    (hM : ∀ z, |M z| ≤ 1) (hQ : ∀ z, 0 ≤ Q z)
    (hb : ∀ z, Q z ≤ 1 - (M z) ^ 2) (x h : ℝ) :
    1 - M (x + h) ≤ Real.exp (2 * |h|) * (1 - M x) := by
  have hm : Monotone M := monotone_of_hasDerivAt_nonneg hd hQ
  have hp (z : ℝ) : 0 ≤ 1 - M z := by linarith [(abs_le.mp (hM z)).2]
  have hExp (z : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (2 * t))
      (2 * Real.exp (2 * z)) z := by
    simpa only [id_eq, one_mul, mul_one, mul_comm] using ((hasDerivAt_id z).const_mul 2).exp
  have he (z : ℝ) : HasDerivAt (fun t => Real.exp (2 * t) * (1 - M t))
      (Real.exp (2 * z) * (2 * (1 - M z) - Q z)) z := by
    convert (hExp z).mul ((hasDerivAt_const z 1).sub (hd z)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Pi.sub_apply]
    ring
  have hw : Monotone (fun t => Real.exp (2 * t) * (1 - M t)) := by
    apply monotone_of_hasDerivAt_nonneg he
    intro z
    apply mul_nonneg (Real.exp_pos _).le
    have hsq : 0 ≤ (1 - M z) ^ 2 := sq_nonneg _
    nlinarith [hb z]
  by_cases hh : 0 ≤ h
  · have hmono := hm (show x ≤ x + h by linarith)
    have hexp : 1 ≤ Real.exp (2 * |h|) := Real.one_le_exp (by positivity)
    exact (sub_le_sub_left hmono 1).trans (le_mul_of_one_le_left (hp x) hexp)
  · have hh' : h ≤ 0 := (lt_of_not_ge hh).le
    have ht := hw (show x + h ≤ x by linarith)
    change Real.exp (2 * (x + h)) * (1 - M (x + h)) ≤ Real.exp (2 * x) * (1 - M x) at ht
    have heq : Real.exp (2 * (x + h)) = Real.exp (2 * x) * Real.exp (2 * h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, mul_assoc] at ht
    have ht' := (mul_le_mul_iff_right₀ (Real.exp_pos (2 * x))).mp ht
    have hmul : Real.exp (2 * |h|) * Real.exp (2 * h) = 1 := by
      rw [abs_of_nonpos hh', ← Real.exp_add, show 2 * -h + 2 * h = 0 by ring, Real.exp_zero]
    have hh'' := mul_le_mul_of_nonneg_left ht' (Real.exp_pos (2 * |h|)).le
    simpa only [← mul_assoc, hmul, one_mul] using hh''

lemma magnetic_mean_shift_tendsto_one {ι : Type*} {l : Filter ι}
    {M Q : ι → ℝ → ℝ} {x : ι → ℝ}
    (hd : ∀ i z, HasDerivAt (M i) (Q i z) z)
    (hM : ∀ i z, |M i z| ≤ 1) (hQ : ∀ i z, 0 ≤ Q i z)
    (hb : ∀ i z, Q i z ≤ 1 - (M i z) ^ 2)
    (hx : Tendsto (fun i => M i (x i)) l (𝓝 1)) (h : ℝ) :
    Tendsto (fun i => M i (x i + h)) l (𝓝 1) := by
  have he : Tendsto (fun i => Real.exp (2 * |h|) * (1 - M i (x i))) l (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hx).const_mul (Real.exp (2 * |h|))
  have hzero : Tendsto (fun i => 1 - M i (x i + h)) l (𝓝 0) := by
    apply squeeze_zero (fun i => by linarith [(abs_le.mp (hM i (x i + h))).2])
      (fun i => magnetic_mean_shift_deficit (hd i) (hM i) (hQ i) (hb i) (x i) h)
    simpa only [sub_self, mul_zero] using he
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero

lemma magnetic_mean_shift_tendsto_neg_one {ι : Type*} {l : Filter ι}
    {M Q : ι → ℝ → ℝ} {x : ι → ℝ}
    (hd : ∀ i z, HasDerivAt (M i) (Q i z) z)
    (hM : ∀ i z, |M i z| ≤ 1) (hQ : ∀ i z, 0 ≤ Q i z)
    (hb : ∀ i z, Q i z ≤ 1 - (M i z) ^ 2)
    (hx : Tendsto (fun i => M i (x i)) l (𝓝 (-1))) (h : ℝ) :
    Tendsto (fun i => M i (x i + h)) l (𝓝 (-1)) := by
  have hd' (i : ι) (z : ℝ) : HasDerivAt (fun u => -M i (-u)) (Q i (-z)) z := by
    convert ((hd i (-z)).comp z (hasDerivAt_neg z)).neg using 1 <;>
      first | rfl | simp
  have hM' (i : ι) (z : ℝ) : |-M i (-z)| ≤ 1 := by simpa only [abs_neg] using hM i (-z)
  have hb' (i : ι) (z : ℝ) : Q i (-z) ≤ 1 - (-M i (-z)) ^ 2 := by
    simpa only [neg_sq] using hb i (-z)
  have hx' : Tendsto (fun i => -M i (- -x i)) l (𝓝 (1 : ℝ)) := by
    simpa only [neg_neg] using hx.neg
  have hh := magnetic_mean_shift_tendsto_one hd' hM' (fun i z => hQ i (-z)) hb' hx' (-h)
  simpa only [neg_add_rev, neg_neg, add_comm] using hh.neg


end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticUniformSlabBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial bounds for the actual Gaussian transition, uniform in its
variance. These are used to control both endpoints of inverse coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

namespace MagneticSlabBound

lemma const (c : ℝ) : MagneticSlabBound (fun _ _ => c) :=
  ⟨|c|, abs_nonneg _, fun _ _ => le_rfl⟩

lemma add {f g : ℝ≥0 → ℝ → ℝ} (hf : MagneticSlabBound f)
    (hg : MagneticSlabBound g) : MagneticSlabBound (fun v z => f v z + g v z) := by
  obtain ⟨C, hC, bC⟩ := hf
  obtain ⟨D, hD, bD⟩ := hg
  exact ⟨C + D, add_nonneg hC hD, fun v z =>
    (abs_add_le _ _).trans (add_le_add (bC v z) (bD v z))⟩

lemma sub {f g : ℝ≥0 → ℝ → ℝ} (hf : MagneticSlabBound f)
    (hg : MagneticSlabBound g) : MagneticSlabBound (fun v z => f v z - g v z) := by
  obtain ⟨C, hC, bC⟩ := hf
  obtain ⟨D, hD, bD⟩ := hg
  exact ⟨C + D, add_nonneg hC hD, fun v z =>
    (abs_sub _ _).trans (add_le_add (bC v z) (bD v z))⟩

lemma mul {f g : ℝ≥0 → ℝ → ℝ} (hf : MagneticSlabBound f)
    (hg : MagneticSlabBound g) : MagneticSlabBound (fun v z => f v z * g v z) := by
  obtain ⟨C, hC, bC⟩ := hf
  obtain ⟨D, hD, bD⟩ := hg
  refine ⟨C * D, mul_nonneg hC hD, fun v z => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (bC v z) (bD v z) (abs_nonneg _) hC

lemma transition (ζ : ℝ) {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : MagneticContinuationBound A) :
    MagneticSlabBound (fun v => fieldSpinTransition ζ v F A) := by
  obtain ⟨C, hC, bC⟩ := hA
  exact ⟨C, hC, fun v => fieldSpinTransition_bound ζ v hF hG bC⟩

lemma spatial (ζ : ℝ) {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hA : MagneticContinuationBound A)
    (hB : MagneticContinuationBound B) :
    MagneticSlabBound (fun v => fieldTiltSpatial ζ v F M A B) := by
  obtain ⟨C, hC, bC⟩ := hM
  obtain ⟨D, hD, bD⟩ := hA
  obtain ⟨E, _, bE⟩ := hB
  exact ⟨E + 2 * |ζ| * D * C, by positivity,
    fun v => fieldSpinTransition_derivative_bound ζ v hF hG hC hD bC bD bE⟩

end MagneticSlabBound

lemma magneticContinuationSecond_uniform (ζ : ℝ)
    {F M Q A B C : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hQ : MagneticContinuationBound Q)
    (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B)
    (hC : MagneticContinuationBound C) :
    MagneticSlabBound (fun v => magneticContinuationSecond ζ v F M Q A B C) := by
  have T {A : ℝ → ℝ} (hA : MagneticContinuationBound A) :=
    MagneticSlabBound.transition ζ hF hG hA
  have D {A B : ℝ → ℝ} (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B) :=
    MagneticSlabBound.spatial ζ hF hG hM hA hB
  exact (D hB hC).add ((MagneticSlabBound.const ζ).mul
    ((D (hA.mul hM) ((hB.mul hM).add (hA.mul hQ))).sub
      (((D hA hB).mul (T hM)).add ((T hA).mul (D hM hQ)))))

lemma magneticContinuationThird_uniform (ζ : ℝ)
    {F M Q R A B C D : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : MagneticContinuationBound M) (hQ : MagneticContinuationBound Q)
    (hR : MagneticContinuationBound R) (hA : MagneticContinuationBound A)
    (hB : MagneticContinuationBound B) (hC : MagneticContinuationBound C)
    (hD : MagneticContinuationBound D) :
    MagneticSlabBound (fun v => magneticContinuationThird ζ v F M Q R A B C D) := by
  have T {A : ℝ → ℝ} (hA : MagneticContinuationBound A) :=
    MagneticSlabBound.transition ζ hF hG hA
  have S {A B : ℝ → ℝ} (hA : MagneticContinuationBound A) (hB : MagneticContinuationBound B) :=
    MagneticSlabBound.spatial ζ hF hG hM hA hB
  have D2 {A B C : ℝ → ℝ} (hA : MagneticContinuationBound A)
      (hB : MagneticContinuationBound B) (hC : MagneticContinuationBound C) :=
    magneticContinuationSecond_uniform ζ hF hG hM hQ hA hB hC
  have hb2 := (hB.mul hM).add (hA.mul hQ)
  have hb3 := ((hC.mul hM).add
    (((MagneticContinuationBound.const 2).mul hB).mul hQ)).add (hA.mul hR)
  exact (D2 hB hC hD).add ((MagneticSlabBound.const ζ).mul
    ((D2 (hA.mul hM) hb2 hb3).sub
      ((((D2 hA hB hC).mul (T hM)).add
        ((((MagneticSlabBound.const 2).mul (S hA hB)).mul (S hM hQ)))).add
          ((T hA).mul (D2 hM hQ hR)))))

lemma MagneticContinuationJet.transition_second_uniform (A P : MagneticContinuationJet)
    (ζ : ℝ) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    MagneticSlabBound (fun v z => (A.transition P ζ v F hF hG dF).second z) :=
  magneticContinuationSecond_uniform ζ hF hG P.bValue P.bFirst A.bValue A.bFirst A.bSecond

lemma MagneticContinuationJet.transition_third_uniform (A P : MagneticContinuationJet)
    (ζ : ℝ) (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) :
    MagneticSlabBound (fun v z => (A.transition P ζ v F hF hG dF).third z) :=
  magneticContinuationThird_uniform ζ hF hG P.bValue P.bFirst P.bSecond
    A.bValue A.bFirst A.bSecond A.bThird

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint decay for bounded square continuations in a varying slab. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

lemma magnetic_family_continuation_endpoint {ι : Type*} {l : Filter ι}
    {M A B C D : ι → ℝ → ℝ} {x : ι → ℝ} {c L K : ℝ}
    (hc : c ^ 2 = 1) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hA : ∀ i z, (M i z) ^ 2 ≤ A i z ∧ A i z ≤ 1)
    (dA : ∀ i z, HasDerivAt (A i) (B i z) z)
    (dB : ∀ i z, HasDerivAt (B i) (C i z) z)
    (dC : ∀ i z, HasDerivAt (C i) (D i z) z)
    (bC : ∀ i z, |C i z| ≤ L) (bD : ∀ i z, |D i z| ≤ K)
    (hM : ∀ h : ℝ, Tendsto (fun i => M i (x i + h)) l (𝓝 c)) :
    Tendsto (fun i => B i (x i)) l (𝓝 0) ∧
      Tendsto (fun i => C i (x i)) l (𝓝 0) := by
  have hlim (h : ℝ) : Tendsto (fun i => A i (x i + h)) l (𝓝 (1 : ℝ)) := by
    have hs : Tendsto (fun i => (M i (x i + h)) ^ 2) l (𝓝 (1 : ℝ)) := by
      simpa only [hc] using (hM h).pow 2
    exact hs.squeeze tendsto_const_nhds (fun i => (hA i (x i + h)).1)
      (fun i => (hA i (x i + h)).2)
  exact ⟨magnetic_family_derivative_tendsto_zero hL dA dB bC hlim,
    magnetic_family_second_tendsto_zero hL hK dA dB dC bC bD hlim⟩

lemma magnetic_family_weighted_endpoint {ι : Type*} {l : Filter ι}
    {B C R : ι → ℝ} {K : ℝ}
    (hB : Tendsto B l (𝓝 0)) (hC : Tendsto C l (𝓝 0))
    (hR : ∀ i, |R i| ≤ K) :
    Tendsto (fun i => C i - B i * R i) l (𝓝 0) := by
  have hmul : Tendsto (fun i => B i * R i) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_)
      (show Tendsto (fun i => |B i| * K) l (𝓝 0) by
        simpa only [Real.norm_eq_abs, abs_zero, zero_mul] using hB.norm.mul_const K)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hR i) (abs_nonneg _)
  simpa only [sub_zero] using hC.sub hmul

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarSlabEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform endpoint decay of the actual finite-tail square continuation.
The variance may vary arbitrarily as the prescribed spin tends to ±1. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabJet_value_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v z : ℝ) :
    |(magneticScalarSlabJet L hL ζ v).value z| ≤ 1 := by
  have htan : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hP := fieldScalarMean_regular L hL measurable_logCosh logCosh_linearGrowth
    htan field_abs_tanh_le_one
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  exact fieldSpinTransition_bound ζ (Real.toNNReal v) hF.1 hF.2 hP.2 z

lemma magneticScalarSlabJet_curvature_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ1 : ζ ≤ 1) (v z : ℝ) :
    (magneticScalarSlabJet L hL ζ v).first z ≤
      1 - ((magneticScalarSlabJet L hL ζ v).value z) ^ 2 := by
  let P := magneticLogCoshMeanJet L hL
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  obtain ⟨K, _, bK⟩ := P.bValue
  obtain ⟨C, _, bC⟩ := P.bFirst
  have hb (y : ℝ) : P.first y + (P.value y) ^ 2 ≤ 1 := by
    have hh := fieldScalarLogCoshSecond_le_spin_variance L hL hL1 y
    change P.first y ≤ 1 - (P.value y) ^ 2 at hh
    linarith
  have hh := fieldCurvatureTransform_le_spin_variance hζ1 (Real.toNNReal v)
    hF.1 hF.2 P.mValue P.mFirst bK bC hb z
  simpa only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two] using hh

lemma magneticScalarSlabJet_third_ratio_bound_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 < ζ) (v z : ℝ) :
    |(magneticScalarSlabJet L hL ζ v).second z /
      (magneticScalarSlabJet L hL ζ v).first z| ≤
      magneticThirdRatioCap ((ζ, 0) :: L) := by
  let K := (ζ, Real.toNNReal v) :: L
  have hK : ∀ av ∈ K, 0 < av.1 := by
    intro av hav
    rcases List.mem_cons.mp hav with h | h
    · simpa only [h] using hζ
    · exact hL av h
  have hr := fieldScalarLogCoshThird_relative K hK z
  have he := magneticScalarSlabJet_eq_cons L hL hζ v
  have hp := magneticScalarSlabJet_curvature_pos L hL hζ.le v z
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  rw [he]
  simpa only [K, magneticThirdRatioCap, magneticLogCoshMeanJet] using hr

lemma magneticScalarSlabJet_third_ratio_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    |(magneticScalarSlabJet L hL ζ v).second z /
      (magneticScalarSlabJet L hL ζ v).first z| ≤
      magneticThirdRatioCap ((ζ, 0) :: L) := by
  rcases eq_or_lt_of_le hζ with he | hp
  · subst ζ
    have hq := magneticScalarSlabJet_curvature_pos L hL (le_refl (0 : ℝ)) v z
    rw [abs_div, abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    simpa only [magneticThirdRatioCap, abs_zero, mul_zero, add_zero] using
      magneticScalarSlabJet_zero_third_relative L hL v z
  · exact magneticScalarSlabJet_third_ratio_bound_pos L hL hp v z

lemma magneticScalarSlabContinuation_sandwich (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    (ζ v z : ℝ) :
    ((magneticScalarSlabJet L hL ζ v).value z) ^ 2 ≤
        (magneticScalarSlabContinuationJet L hL A ζ v).value z ∧
      (magneticScalarSlabContinuationJet L hL A ζ v).value z ≤ 1 := by
  let P := magneticLogCoshMeanJet L hL
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  obtain ⟨C, _, bC⟩ := P.bValue
  have bP2 (y : ℝ) : |(P.value y) ^ 2| ≤ C ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bC y) 2
  have bA (y : ℝ) : |A.value y| ≤ 1 := by
    rw [abs_of_nonneg ((sq_nonneg _).trans (hA y).1)]
    exact (hA y).2
  have hsq := fieldSpinTransition_square_le ζ (Real.toNNReal v) hF.1 hF.2 P.mValue bC z
  have hle := fieldSpinTransition_mono_test ζ (Real.toNNReal v) F
    (P.mValue.pow_const 2) A.mValue bP2 bA (fun y => (hA y).1) z
  exact ⟨hsq.trans hle, (le_abs_self _).trans
    (fieldSpinTransition_bound ζ (Real.toNNReal v) hF.1 hF.2 bA z)⟩

theorem magneticScalarSlabWeighted_tendsto_endpoint {ι : Type*} {l : Filter ι}
    (L : List (ℝ × ℝ≥0)) (hL : ∀ av ∈ L, 0 < av.1)
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ c : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hc : c = -1 ∨ c = 1)
    (v s : ι → ℝ) (hs : ∀ᶠ i in l, |s i| < 1) (hslim : Tendsto s l (𝓝 c)) :
    Tendsto (fun i => magneticScalarSlabWeighted L hL A ζ (v i) (s i)) l (𝓝 0) := by
  let P := magneticLogCoshMeanJet L hL
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let J := fun i => magneticScalarSlabJet L hL ζ (v i)
  let K := fun i => magneticScalarSlabContinuationJet L hL A ζ (v i)
  let x := fun i => magneticScalarSlabBias L ζ (v i) (s i)
  have hroot : Tendsto (fun i => (J i).value (x i)) l (𝓝 c) := by
    apply hslim.congr'
    filter_upwards [hs] with i hi
    exact (magneticScalarSlabMean_bias L hL hζ hi (v i)).symm
  have hshift (h : ℝ) : Tendsto (fun i => (J i).value (x i + h)) l (𝓝 c) := by
    rcases hc with rfl | rfl
    · exact magnetic_mean_shift_tendsto_neg_one (fun i => (J i).dValue)
        (fun i => magneticScalarSlabJet_value_bound L hL ζ (v i))
        (fun i z => (magneticScalarSlabJet_curvature_pos L hL hζ (v i) z).le)
        (fun i => magneticScalarSlabJet_curvature_bound L hL hL1 hζ1 (v i)) hroot h
    · exact magnetic_mean_shift_tendsto_one (fun i => (J i).dValue)
        (fun i => magneticScalarSlabJet_value_bound L hL ζ (v i))
        (fun i z => (magneticScalarSlabJet_curvature_pos L hL hζ (v i) z).le)
        (fun i => magneticScalarSlabJet_curvature_bound L hL hL1 hζ1 (v i)) hroot h
  obtain ⟨C, hC, bC⟩ := A.transition_second_uniform P ζ F hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL)
  obtain ⟨D, hD, bD⟩ := A.transition_third_uniform P ζ F hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL)
  have hc2 : c ^ 2 = 1 := by rcases hc with rfl | rfl <;> norm_num
  have hends := magnetic_family_continuation_endpoint hc2 hC hD
    (fun i => magneticScalarSlabContinuation_sandwich L hL A hA ζ (v i))
    (fun i => (K i).dValue) (fun i => (K i).dFirst) (fun i => (K i).dSecond)
    (fun i => bC (Real.toNNReal (v i))) (fun i => bD (Real.toNNReal (v i))) hshift
  exact magnetic_family_weighted_endpoint hends.1 hends.2
    (fun i => magneticScalarSlabJet_third_ratio_bound L hL hζ (v i) (x i))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSquareJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite-level square continuations satisfy every endpoint
hypothesis of the inverse-coordinate comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSquareFourJet_value (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) :
    (magneticScalarSquareFourJet L hL i).value =
      fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i :=
  (fieldScalarSquares_has_bounded_fourJet L hL i).choose_spec

lemma magneticScalarSquareFourJet_sandwich (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (i : Fin (L.length + 1)) (z : ℝ) :
    ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤
        (magneticScalarSquareFourJet L hL i).value z ∧
      (magneticScalarSquareFourJet L hL i).value z ≤ 1 := by
  rw [magneticScalarSquareFourJet_value]
  have htan : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hm := fieldScalarSquares_monotone L hL measurable_logCosh logCosh_linearGrowth
    htan field_abs_tanh_le_one z (show (0 : Fin (L.length + 1)) ≤ i by exact Fin.zero_le i)
  dsimp only at hm
  rw [fieldScalarSquares_zero] at hm
  exact ⟨hm, (fieldScalarSquares_regular L hL measurable_logCosh logCosh_linearGrowth
    htan field_abs_tanh_le_one i).2 z |>.2⟩

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

lemma closedMagneticScalarCurvature_endpoints (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) :
    closedMagneticScalarCurvature L hL ζ (v, -1) = 0 ∧
      closedMagneticScalarCurvature L hL ζ (v, 1) = 0 := by
  simp only [closedMagneticScalarCurvature, abs_neg, abs_one, lt_self_iff_false, ite_false, if_false,
    and_self]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed derivative of the first spatial derivative of a bounded
finite Gaussian continuation. The proof differentiates actual normalized
averages and identifies coefficients by ordinary derivative uniqueness. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticHeatSpatial_eq (P A : MagneticContinuationJet) (F : ℝ → ℝ)
    (hF : Measurable F) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatSpatial P A F ζ q =
      fieldTiltSpatial ζ (Real.toNNReal q.1) F P.value A.value A.first q.2 := by
  unfold magneticHeatSpatial fieldTiltSpatial
  rw [magneticHeatMean_eq _ _ hF, magneticHeatMean_eq _ _ hF, magneticHeatMean_eq _ _ hF]
  rw [field_gaussianTiltAverage_eq_transition q.1 ζ hF A.mFirst]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint variance/spatial differentiation of the second spatial
derivative. Fourth terminal derivatives suffice; no unproved interchange
of differentiation and Gaussian integration is used. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticHeatSecond_eq (P : MagneticContinuationJet) (A : MagneticContinuationFourJet)
    (F : ℝ → ℝ) (hF : Measurable F) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatSecond P A F ζ q = magneticContinuationSecond ζ (Real.toNNReal q.1)
      F P.value P.first A.value A.first A.second q.2 := by
  unfold magneticHeatSecond
  simp only [magneticHeatSpatial_eq _ _ F hF, magneticHeatMean_eq _ F hF]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatJetContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity of the actual first and second spatial derivatives
of the finite Gaussian continuation, including zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma continuous_magneticGaussianTest {F B : ℝ → ℝ}
    (hF : Continuous F) (hG : HasLinearGrowth F) (hB : Continuous B)
    (bB : MagneticContinuationBound B) (ζ : ℝ) :
    Continuous (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F B q.2) := by
  obtain ⟨C, L, hC, hL, bF⟩ := hG
  obtain ⟨M, hM, bM⟩ := bB
  exact continuous_field_gaussian_tilt_average
    (hF.comp continuous_snd) (hB.comp continuous_snd) continuous_fst continuous_snd
    hC hL hM (fun _ z => by simpa only [Real.norm_eq_abs] using bF z) (fun _ z => bM z) ζ

lemma continuous_magneticHeatSpatial (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Continuous F) (hG : HasLinearGrowth F) (ζ : ℝ) :
    Continuous (magneticHeatSpatial P A F ζ) := by
  have hA1 : Continuous A.first := continuous_iff_continuousAt.mpr
    fun z => (A.dFirst z).continuousAt
  exact (continuous_magneticGaussianTest hF hG hA1 A.bFirst ζ).add
    (((continuous_magneticHeatMean (A.mul P) F hF hG ζ).sub
      ((continuous_magneticHeatMean A F hF hG ζ).mul
        (continuous_magneticHeatMean P F hF hG ζ))).const_mul ζ)

lemma continuous_magneticHeatSecond (P : MagneticContinuationJet) (A : MagneticContinuationFourJet)
    (F : ℝ → ℝ) (hF : Continuous F) (hG : HasLinearGrowth F) (ζ : ℝ) :
    Continuous (magneticHeatSecond P A F ζ) := by
  exact (continuous_magneticHeatSpatial P A.slope F hF hG ζ).add
    (((continuous_magneticHeatSpatial P (A.toMagneticContinuationJet.mul P) F hF hG ζ).sub
      (((continuous_magneticHeatSpatial P A.toMagneticContinuationJet F hF hG ζ).mul
        (continuous_magneticHeatMean P F hF hG ζ)).add
          ((continuous_magneticHeatMean A.toMagneticContinuationJet F hF hG ζ).mul
            (continuous_magneticHeatSpatial P P F hF hG ζ)))).const_mul ζ)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial derivatives of q²Hᵤᵤ. Multiplying by q² removes the first-order
term from the differentiated inverse-coordinate continuation equation. -/

noncomputable section

namespace InvariantIsing

lemma magneticWeightedJetValue_hasDerivAt (P A : MagneticContinuationFourJet)
    {z : ℝ} (hq : P.first z ≠ 0) :
    HasDerivAt (magneticWeightedJetValue P A) (magneticWeightedJetFirst P A z) z := by
  have hd := (A.dSecond z).sub (((A.dFirst z).mul (P.dSecond z)).div (P.dFirst z) hq)
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp only [magneticWeightedJetFirst]
    simp only [Pi.mul_apply]
    field_simp [hq]
    ring

lemma magneticWeightedJetFirst_hasDerivAt (P A : MagneticContinuationFourJet)
    {z : ℝ} (hq : P.first z ≠ 0) :
    HasDerivAt (magneticWeightedJetFirst P A) (magneticWeightedJetSecond P A z) z := by
  have hnum := ((A.dSecond z).mul (P.dSecond z)).add ((A.dFirst z).mul (P.dThird z))
  have hlast := ((A.dFirst z).mul ((P.dSecond z).pow 2)).div ((P.dFirst z).pow 2)
    (pow_ne_zero 2 hq)
  have hd := ((A.dThird z).sub (hnum.div (P.dFirst z) hq)).add hlast
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp only [magneticWeightedJetSecond]
    simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hq]
    ring

lemma magneticWeightedInverseFirst_hasDerivAt (P A : MagneticContinuationFourJet)
    {b : ℝ → ℝ} {s : ℝ} (hq : P.first (b s) ≠ 0)
    (hb : HasDerivAt b (1 / P.first (b s)) s) :
    HasDerivAt (fun u => magneticWeightedJetFirst P A (b u) / P.first (b u))
      (magneticWeightedInverseSecond P A (b s)) s := by
  exact inverse_mean_pullback_quotient hq hb rfl rfl
    (magneticWeightedJetFirst_hasDerivAt P A hq) (P.dFirst (b s))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual drift-free equation for q²Hᵤᵤ along the inverse mean.
All time derivatives come from normalized Gaussian averages. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticHeatWeighted_eq (P A : MagneticContinuationFourJet) (F : ℝ → ℝ)
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) (q : ℝ × ℝ) :
    magneticHeatWeighted P A F ζ q =
      magneticWeightedJetValue
        (P.transition P.toMagneticContinuationJet ζ (Real.toNNReal q.1) F hF hG dF)
        (A.transition P.toMagneticContinuationJet ζ (Real.toNNReal q.1) F hF hG dF) q.2 := by
  unfold magneticHeatWeighted magneticWeightedJetValue
  rw [magneticHeatSecond_eq _ _ F hF, magneticHeatSecond_eq _ _ F hF,
    magneticHeatSpatial_eq _ _ F hF, magneticHeatCurvature_eq _ F hF]
  simp only [MagneticContinuationFourJet.transition, MagneticContinuationJet.transition,
    fieldCurvatureTransform, fieldTiltSpatial, pow_two]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScalarWeightedPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted continuation equation specialized to the actual finite
Ising tail. Its inverse coordinate is the proved minimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabFourJet_toJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) :
    (magneticScalarSlabFourJet L hL ζ v).toMagneticContinuationJet =
      magneticScalarSlabJet L hL ζ v := by
  simp only [magneticScalarSlabFourJet, MagneticContinuationFourJet.transition,
    magneticLogCoshMeanFourJet_eq, magneticScalarSlabJet]

lemma magneticScalarSlabContinuationFourJet_toJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v : ℝ) :
    (magneticScalarSlabContinuationFourJet L hL A ζ v).toMagneticContinuationJet =
      magneticScalarSlabContinuationJet L hL A.toMagneticContinuationJet ζ v := by
  simp only [magneticScalarSlabContinuationFourJet, MagneticContinuationFourJet.transition,
    magneticLogCoshMeanFourJet_eq, magneticScalarSlabContinuationJet]

lemma magneticScalarSlabWeighted_eq_heat (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v s : ℝ) :
    magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v s =
      magneticHeatWeighted (magneticLogCoshMeanFourJet L hL) A
        (fieldScalarValue L (fun y => Real.log (Real.cosh y))) ζ
          (v, magneticScalarSlabBias L ζ v s) := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  rw [magneticHeatWeighted_eq _ _ _ hF.1 hF.2 (magneticLogCoshMeanFourJet_derivative L hL)]
  simp only [magneticWeightedJetValue, MagneticContinuationFourJet.transition,
    magneticLogCoshMeanFourJet_eq, magneticScalarSlabWeighted,
    magneticScalarSlabJet, magneticScalarSlabContinuationJet]
  ring

lemma magneticScalarSlabWeighted_eq_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ v s : ℝ) :
    magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v s =
      magneticWeightedJetValue (magneticScalarSlabFourJet L hL ζ v)
        (magneticScalarSlabContinuationFourJet L hL A ζ v) (magneticScalarSlabBias L ζ v s) := by
  unfold magneticWeightedJetValue magneticScalarSlabWeighted
  rw [← magneticScalarSlabFourJet_toJet L hL ζ v,
    ← magneticScalarSlabContinuationFourJet_toJet L hL A ζ v]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous extension of the actual weighted continuation to the
closed spin interval, uniformly with respect to the slab variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma continuousOn_zero_spin_extension (f : ℝ × ℝ → ℝ)
    (hc : ∀ p : ℝ × ℝ, |p.2| < 1 → ContinuousAt f p)
    (hb : ∀ p : ℝ × ℝ, |p.2| = 1 →
      Tendsto f (𝓝[{q : ℝ × ℝ | |q.2| < 1}] p) (𝓝 0)) :
    ContinuousOn (fun p : ℝ × ℝ => if |p.2| < 1 then f p else 0)
      (univ ×ˢ Icc (-1 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := {q | |q.2| < 1}
  let g := fun p : ℝ × ℝ => if |p.2| < 1 then f p else 0
  intro p hp
  change ContinuousWithinAt g _ p
  by_cases hi : |p.2| < 1
  · have he : g =ᶠ[𝓝 p] f := by
      filter_upwards [(isOpen_lt continuous_snd.abs continuous_const).mem_nhds hi] with q hq
      exact ite_eq_left hq
    exact ((hc p hi).congr_of_eventuallyEq he).continuousWithinAt
  · have he : |p.2| = 1 := le_antisymm (abs_le.mpr hp.2) (le_of_not_gt hi)
    have hg : g p = 0 := ite_eq_right hi
    have hin : Tendsto g (𝓝[S] p) (𝓝 (0 : ℝ)) := by
      apply (hb p he).congr'
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (ite_eq_left hq).symm
    have hout : Tendsto g (𝓝[Sᶜ] p) (𝓝 (0 : ℝ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (ite_eq_right hq).symm
    have hall : Tendsto g (𝓝[S ∪ Sᶜ] p) (𝓝 (0 : ℝ)) := by
      rw [nhdsWithin_union, tendsto_sup]
      exact ⟨hin, hout⟩
    have hall' : Tendsto g (𝓝 p) (𝓝 (0 : ℝ)) := by simpa only [union_compl_self, nhdsWithin_univ] using hall
    rw [← hg] at hall'
    exact hall'.mono_left nhdsWithin_le_nhds

lemma magneticScalarSlabWeighted_continuousAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ : ℝ} (hζ : 0 ≤ ζ) {p : ℝ × ℝ} (hp : |p.2| < 1) :
    ContinuousAt (fun q : ℝ × ℝ =>
      magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ q.1 q.2) p := by
  let P := magneticLogCoshMeanFourJet L hL
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun z =>
    (hasDerivAt_fieldScalarLogCosh L hL z).continuousAt
  let q := (p.1, magneticScalarSlabBias L ζ p.1 p.2)
  have hq : magneticHeatCurvature P.toMagneticContinuationJet F ζ q ≠ 0 := by
    have hh := (magneticScalarSlab_curvature_pos L hL hζ p.1 q.2).ne'
    simpa only [magneticHeatCurvature_eq _ F hF.1, P, magneticLogCoshMeanFourJet_eq, q, F] using hh
  have hcont : ContinuousAt (magneticHeatWeighted P A F ζ) q := by
    exact (continuous_magneticHeatSecond P.toMagneticContinuationJet A F hcF hF.2 ζ).continuousAt.sub
      (((continuous_magneticHeatSpatial P.toMagneticContinuationJet A.toMagneticContinuationJet
        F hcF hF.2 ζ).continuousAt.mul
          (continuous_magneticHeatSecond P.toMagneticContinuationJet P F hcF hF.2 ζ).continuousAt).div
            (continuous_magneticHeatCurvature P.toMagneticContinuationJet F hcF hF.2 ζ).continuousAt hq)
  have hb := magneticScalarSlabBias_continuousAt_joint L hL (v := p.1) hζ hp
  have hh := hcont.comp' (f := fun r : ℝ × ℝ =>
    (r.1, magneticScalarSlabBias L ζ r.1 r.2)) (x := p) (continuousAt_fst.prodMk hb)
  simpa only [← magneticScalarSlabWeighted_eq_heat, P, F, q] using hh

theorem continuousOn_closedMagneticSlabWeighted (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (A : MagneticContinuationFourJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ContinuousOn (closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ)
      (univ ×ˢ Icc (-1 : ℝ) 1) := by
  apply continuousOn_zero_spin_extension
  · exact fun p hp => magneticScalarSlabWeighted_continuousAt L hL A hζ hp
  · intro p hp
    have he : p.2 = -1 ∨ p.2 = 1 := by
      rcases le_total 0 p.2 with h | h
      · exact Or.inr (by rwa [abs_of_nonneg h] at hp)
      · exact Or.inl (by rw [abs_of_nonpos h] at hp; linarith)
    apply magneticScalarSlabWeighted_tendsto_endpoint L hL hL1 A.toMagneticContinuationJet hA hζ hζ1 he
    · exact self_mem_nhdsWithin
    · exact continuous_snd.continuousAt.mono_left nhdsWithin_le_nhds

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual spatial derivatives and the uniformly bounded potential of the
weighted inverse-coordinate continuation equation. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabFourJet_pos (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    0 < (magneticScalarSlabFourJet L hL ζ v).first z := by
  have he := congrArg MagneticContinuationJet.first (magneticScalarSlabFourJet_toJet L hL ζ v)
  rw [he]
  exact magneticScalarSlabJet_curvature_pos L hL hζ v z

lemma magneticScalarSlabBias_hasDerivAt_fourJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabBias L ζ v)
      (1 / (magneticScalarSlabFourJet L hL ζ v).first (magneticScalarSlabBias L ζ v s)) s := by
  have he := congrArg MagneticContinuationJet.first (magneticScalarSlabFourJet_toJet L hL ζ v)
  rw [he]
  exact magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v

lemma magneticScalarSlabWeighted_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v)
      (magneticScalarWeightedSlope L hL A ζ v s) s := by
  have he : magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v =
      fun u => magneticWeightedJetValue (magneticScalarSlabFourJet L hL ζ v)
        (magneticScalarSlabContinuationFourJet L hL A ζ v) (magneticScalarSlabBias L ζ v u) :=
    funext (magneticScalarSlabWeighted_eq_jet L hL A ζ v)
  rw [he]
  exact inverse_mean_pullback_derivative (magneticScalarSlabBias_hasDerivAt_fourJet L hL hζ hs v)
    (magneticWeightedJetValue_hasDerivAt _ _ (magneticScalarSlabFourJet_pos L hL hζ v _).ne')

lemma magneticScalarWeightedSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarWeightedSlope L hL A ζ v)
      (magneticScalarWeightedSecond L hL A ζ v s) s := by
  exact magneticWeightedInverseFirst_hasDerivAt _ _
    (magneticScalarSlabFourJet_pos L hL hζ v _).ne'
    (magneticScalarSlabBias_hasDerivAt_fourJet L hL hζ hs v)

lemma magneticScalarWeightedPotential_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hs : |s| < 1) (v : ℝ) :
    |magneticScalarWeightedPotential L hL ζ v s| ≤ magneticSlabPotentialCap L ζ + 2 := by
  have ha := magneticScalarInverseCurvature_pos L hL hζ v s
  have ha1 : magneticScalarInverseCurvature L hL ζ v s ≤ 1 :=
    (magneticScalarInverseCurvature_le_spin_variance L hL hL1 hζ hζ1 hs v).trans
      (by linarith [sq_nonneg s])
  have hb : |magneticScalarInverseCurvature L hL ζ v s *
      magneticScalarInverseSecond L hL ζ v s| ≤ magneticSlabPotentialCap L ζ := by
    rcases eq_or_lt_of_le hζ with he | hp
    · subst ζ
      exact magneticScalarInverse_zero_weighted_second_bound L hL hL1 v s
    · exact magneticScalarInverse_weighted_second_bound L hL hL1 hp hζ1 v s
  have hc : |2 * ζ * magneticScalarInverseCurvature L hL ζ v s| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hζ1) ha.le]
  exact (abs_add_le _ _).trans (add_le_add hb hc)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed-strip derivative data for the weighted continuation. At either
spin endpoint the continued function is identically zero in time. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticSlabWeighted_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ (v, u))
      (closedMagneticWeightedSlope L hL A ζ (v, s)) s := by
  have he : (fun u => closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ (v, u))
      =ᶠ[𝓝 s] magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticWeightedSlope, hs, ite_true, if_true] using
    (magneticScalarSlabWeighted_hasDerivAt_spin L hL A hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticWeightedSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticWeightedSlope L hL A ζ (v, u))
      (closedMagneticWeightedSecond L hL A ζ (v, s)) s := by
  have he : (fun u => closedMagneticWeightedSlope L hL A ζ (v, u))
      =ᶠ[𝓝 s] magneticScalarWeightedSlope L hL A ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticWeightedSecond, hs, ite_true, if_true] using
    (magneticScalarWeightedSlope_hasDerivAt_spin L hL A hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticWeightedPotential_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (p : ℝ × ℝ) :
    closedMagneticWeightedPotential L hL ζ p ≤ magneticSlabPotentialCap L ζ + 2 := by
  by_cases hs : |p.2| < 1
  · exact (le_abs_self _).trans (by simpa only [closedMagneticWeightedPotential, hs,
      ite_true, if_true] using magneticScalarWeightedPotential_bound L hL hL1 hζ hζ1 hs p.1)
  · simp only [closedMagneticWeightedPotential, hs, ite_false, if_false]
    exact add_nonneg (add_nonneg (magneticFourthRatioCap_nonneg _) (sq_nonneg _)) (by norm_num)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial data of the weighted square-continuation equation. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticScalarSlabJet_zero (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) :
    magneticScalarSlabJet L hL ζ 0 = magneticLogCoshMeanJet L hL := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  simp only [magneticScalarSlabJet, MagneticContinuationJet.transition,
    Real.toNNReal_zero, fieldSpinTransition_zero_variance]

lemma magneticScalarSlabContinuationJet_zero (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ) :
    magneticScalarSlabContinuationJet L hL A ζ 0 = A := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
    Real.toNNReal_zero, fieldSpinTransition_zero_variance]

lemma magneticScalarSlabWeighted_zero (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ s : ℝ) :
    let P := magneticLogCoshMeanJet L hL
    let z := magneticScalarSlabBias L ζ 0 s
    magneticScalarSlabWeighted L hL A ζ 0 s =
      A.second z - A.first z * (P.second z / P.first z) := by
  simp only [magneticScalarSlabWeighted, magneticScalarSlabJet_zero,
    magneticScalarSlabContinuationJet_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedNonnegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual weighted inverse-coordinate continuation preserves
nonnegativity. The maximum principle uses its proved zero endpoint limits. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticScalarSlabWeighted_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (A : MagneticContinuationFourJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hi : ∀ s, |s| < 1 →
      0 ≤ magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ 0 s)
    {v s : ℝ} (hv : 0 ≤ v) (hs : |s| < 1) :
    0 ≤ magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v s := by
  let W := closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ
  let Wt := closedMagneticWeightedTime L hL A ζ
  let Wx := closedMagneticWeightedSlope L hL A ζ
  let Wxx := closedMagneticWeightedSecond L hL A ζ
  let a := fun p => (closedMagneticScalarCurvature L hL ζ p) ^ 2 / 2
  let c := closedMagneticWeightedPotential L hL ζ
  have hw : ContinuousOn W (Icc (0 : ℝ) v ×ˢ Icc (-1 : ℝ) 1) :=
    (continuousOn_closedMagneticSlabWeighted L hL hL1 A hA hζ hζ1).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩)
  have hinit : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ W (0, x) := by
    intro x hx
    by_cases h : |x| < 1
    · simpa only [W, closedMagneticSlabWeighted, h, ite_true, if_true] using hi x h
    · simp only [W, closedMagneticSlabWeighted, h, ite_false, if_false, le_refl]
  have hdt : ∀ t ∈ Ioc (0 : ℝ) v, ∀ x ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun q => W (q, x)) (Wt (t, x)) (Iic t) t := by
    intro t ht x hx
    exact (closedMagneticSlabWeighted_hasDerivAt_time L hL A hζ ht.1 x).hasDerivWithinAt
  have hdx : ∀ t ∈ Icc (0 : ℝ) v, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => W (t, y)) (Wx (t, x)) x := by
    intro t ht x hx
    exact closedMagneticSlabWeighted_hasDerivAt_spin L hL A hζ (abs_lt.mpr hx) t
  have hdxx : ∀ t ∈ Icc (0 : ℝ) v, ∀ x ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun y => Wx (t, y)) (Wxx (t, x)) x := by
    intro t ht x hx
    exact closedMagneticWeightedSlope_hasDerivAt_spin L hL A hζ (abs_lt.mpr hx) t
  have hb : ∀ t ∈ Icc (0 : ℝ) v,
      a (t, -1) = 0 ∧ (0 : ℝ) = 0 ∧ a (t, 1) = 0 ∧ (0 : ℝ) = 0 := by
    intro t ht
    obtain ⟨hminus, hplus⟩ := closedMagneticScalarCurvature_endpoints L hL ζ t
    simp only [a, hminus, hplus, zero_pow (by norm_num : 2 ≠ 0), zero_div, and_self]
  have hpde : ∀ p ∈ Ioc (0 : ℝ) v ×ˢ Icc (-1 : ℝ) 1,
      a p * Wxx p + (0 : ℝ) * Wx p + c p * W p ≤ Wt p := by
    intro p hp
    simp only [a, Wxx, c, W, Wt, closedMagneticWeightedTime, zero_mul, add_zero, le_refl]
  have hn := parabolic_minimum_nonneg_bounded hv W Wt Wx Wxx a (fun _ => 0) c hw hinit
    hdt hdx hdxx (fun p hp => div_nonneg (sq_nonneg _) (by norm_num))
    (fun p hp => closedMagneticWeightedPotential_bound L hL hL1 hζ hζ1 p) hb hpde
  simpa only [W, closedMagneticSlabWeighted, hs, ite_true, if_true] using
    hn (v, s) ⟨⟨hv, le_rfl⟩, abs_le.mp hs.le⟩

lemma magneticScalarSlabWeighted_eq_curvature_square (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (v s : ℝ) :
    magneticScalarSlabWeighted L hL A ζ v s =
      (magneticScalarInverseCurvature L hL ζ v s) ^ 2 *
        magneticScalarSlabContinuationSecond L hL A ζ v s := by
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  have hq : J.first b ≠ 0 := (magneticScalarSlabJet_curvature_pos L hL hζ v b).ne'
  rw [magneticScalarInverseCurvature_eq_jet]
  change K.second b - K.first b * (J.second b / J.first b) =
    (J.first b) ^ 2 * (K.second b / (J.first b) ^ 2 - K.first b * J.second b / (J.first b) ^ 3)
  field_simp [hq]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticWeightedPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport of the weighted continuation inequality back from the inverse
spin coordinate to every finite physical field position. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabMean_abs_lt_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    |magneticScalarSlabMean L ζ v z| < 1 := by
  have hm := magneticScalarSlabMean_strictMono L hL hζ v
  have hb (x : ℝ) : |magneticScalarSlabMean L ζ v x| ≤ 1 :=
    magneticScalarSlabJet_value_bound L hL ζ v x
  have hlo := hm (show z - 1 < z by linarith)
  have hhi := hm (show z < z + 1 by linarith)
  have hminus := (abs_le.mp (hb (z - 1))).1
  have hplus := (abs_le.mp (hb (z + 1))).2
  exact abs_lt.mpr ⟨lt_of_le_of_lt hminus hlo, lt_of_lt_of_le hhi hplus⟩

lemma magneticScalarSlabBias_mean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (v z : ℝ) :
    magneticScalarSlabBias L ζ v (magneticScalarSlabMean L ζ v z) = z := by
  apply (magneticScalarSlabMean_strictMono L hL hζ v).injective
  exact magneticScalarSlabMean_bias L hL hζ
    (magneticScalarSlabMean_abs_lt_one L hL hζ v z) v

lemma magneticScalarSlabWeighted_nonneg_at_position (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (A : MagneticContinuationFourJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hi : ∀ z, 0 ≤ A.second z - A.first z *
      ((magneticLogCoshMeanJet L hL).second z / (magneticLogCoshMeanJet L hL).first z))
    {v : ℝ} (hv : 0 ≤ v) (z : ℝ) :
    let J := magneticScalarSlabJet L hL ζ v
    let K := magneticScalarSlabContinuationJet L hL A.toMagneticContinuationJet ζ v
    0 ≤ K.second z - K.first z * (J.second z / J.first z) := by
  have hinit : ∀ s, |s| < 1 →
      0 ≤ magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ 0 s := by
    intro s hs
    rw [magneticScalarSlabWeighted_zero]
    exact hi _
  have hn := magneticScalarSlabWeighted_nonneg L hL hL1 A hA hζ hζ1 hinit hv
    (magneticScalarSlabMean_abs_lt_one L hL hζ v z)
  simpa only [magneticScalarSlabWeighted, magneticScalarSlabBias_mean L hL hζ v z] using hn

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSquareInverseConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every finite conditional square mean is convex in the inverse mean
coordinate. This is derived by induction through the actual Gaussian steps. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSquareFourJet_zero_toJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    (magneticScalarSquareFourJet L hL 0).toMagneticContinuationJet =
      (magneticLogCoshMeanJet L hL).square := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  rw [magneticScalarSquareFourJet_value]
  exact fieldScalarSquares_zero L _ _ z

lemma magneticScalarSquareFourJet_succ_toJet (av : ℝ × ℝ≥0) (L : List (ℝ × ℝ≥0))
    (hL : ∀ bv ∈ av :: L, 0 < bv.1) (i : Fin (L.length + 1)) :
    (magneticScalarSquareFourJet (av :: L) hL i.succ).toMagneticContinuationJet =
      magneticScalarSlabContinuationJet L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        (magneticScalarSquareFourJet L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
          i).toMagneticContinuationJet av.1 (av.2 : ℝ) := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  rw [magneticScalarSquareFourJet_value]
  simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
    Real.toNNReal_coe, magneticScalarSquareFourJet_value]
  rfl

lemma magneticSquareJet_weighted_nonneg (P : MagneticContinuationJet) (z : ℝ)
    (hq : P.first z ≠ 0) :
    0 ≤ P.square.second z - P.square.first z * (P.second z / P.first z) := by
  have he : P.square.second z - P.square.first z * (P.second z / P.first z) =
      2 * (P.first z) ^ 2 := by
    simp only [MagneticContinuationJet.square]
    field_simp [hq]
    ring
  rw [he]
  positivity

theorem magneticScalarSquare_inverse_convex (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (i : Fin (L.length + 1)) (z : ℝ) :
    let P := magneticLogCoshMeanJet L hL
    let A := magneticScalarSquareFourJet L hL i
    0 ≤ A.second z - A.first z * (P.second z / P.first z) := by
  induction L generalizing z with
  | nil =>
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      have hh : i.val < 1 := by simpa only [List.length_nil, zero_add] using i.isLt
      omega
    subst i
    dsimp only
    rw [show (magneticScalarSquareFourJet [] hL 0).second =
      (magneticLogCoshMeanJet [] hL).square.second from
        congrArg MagneticContinuationJet.second (magneticScalarSquareFourJet_zero_toJet [] hL)]
    rw [show (magneticScalarSquareFourJet [] hL 0).first =
      (magneticLogCoshMeanJet [] hL).square.first from
        congrArg MagneticContinuationJet.first (magneticScalarSquareFourJet_zero_toJet [] hL)]
    exact magneticSquareJet_weighted_nonneg _ z (fieldScalarLogCoshSecond_pos [] hL z).ne'
  | cons av L ih =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let ht1 := fun bv hb => hL1 bv (List.mem_cons_of_mem av hb)
    refine Fin.cases ?_ (fun j => ?_) i
    · have he := magneticScalarSquareFourJet_zero_toJet (av :: L) hL
      dsimp only
      rw [congrArg MagneticContinuationJet.second he, congrArg MagneticContinuationJet.first he]
      exact magneticSquareJet_weighted_nonneg _ z (fieldScalarLogCoshSecond_pos _ hL z).ne'
    · have hn := magneticScalarSlabWeighted_nonneg_at_position L ht ht1
        (magneticScalarSquareFourJet L ht j) (magneticScalarSquareFourJet_sandwich L ht j)
        (hL av List.mem_cons_self).le (hL1 av List.mem_cons_self)
        (fun x => ih ht ht1 j x) (show 0 ≤ (av.2 : ℝ) from av.2.property) z
      have hJ := magneticScalarSlabJet_eq_cons L ht (hL av List.mem_cons_self) (av.2 : ℝ)
      have hA := magneticScalarSquareFourJet_succ_toJet av L hL j
      dsimp only at hn ⊢
      rw [← hA, hJ] at hn
      simpa only [Real.toNNReal_coe] using hn

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSquareSlabConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative inverse-spin second derivatives of the actual finite-level
conditional square means, after an additional Gaussian root step. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticScalarSlabSquare_second_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (i : Fin (L.length + 1)) {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    {v s : ℝ} (hv : 0 ≤ v) (hs : |s| < 1) :
    0 ≤ magneticScalarSlabContinuationSecond L hL
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ v s := by
  have hinit : ∀ u, |u| < 1 → 0 ≤ magneticScalarSlabWeighted L hL
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ 0 u := by
    intro u hu
    rw [magneticScalarSlabWeighted_zero]
    exact magneticScalarSquare_inverse_convex L hL hL1 i _
  have hn := magneticScalarSlabWeighted_nonneg L hL hL1 _
    (magneticScalarSquareFourJet_sandwich L hL i) hζ hζ1 hinit hv hs
  rw [magneticScalarSlabWeighted_eq_curvature_square L hL _ hζ] at hn
  exact nonneg_of_mul_nonneg_right hn (sq_pos_of_pos
    (magneticScalarInverseCurvature_pos L hL hζ v s))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationClosedPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed-interval derivative data for finite inverse-coordinate square
continuations, with a zero second derivative chosen at the endpoints. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticSquareContinuationSecond_nonneg_oai (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (i : Fin (L.length + 1)) {ζ v : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (s : ℝ) :
    0 ≤ closedMagneticContinuationSecond L hL
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ (v, s) := by
  by_cases hs : |s| < 1
  · simpa only [closedMagneticContinuationSecond, hs, ite_true, if_true] using
      magneticScalarSlabSquare_second_nonneg L hL hL1 i hζ hζ1 hv hs
  · simp only [closedMagneticContinuationSecond, hs, ite_false, if_false, le_refl]

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.closedMagneticSquareContinuationSecond_nonneg_oai := @OAI.InvariantIsing.closedMagneticSquareContinuationSecond_nonneg_oai
