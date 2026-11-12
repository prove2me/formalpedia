-- Prove2me | solution 1 for OAI.InvariantIsing.finiteMagneticFunctional_transport_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:17:13.509993+00:00
-- url     : https://prove2.me/submissions/1f9f5319-9436-49dc-bb34-141fb57bcd24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_real_profile
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finiteVariational_ne_top_bot

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightChart
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldLowerBound
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldParameter
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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

lemma concaveOn_constrainedFieldValue_magnetization (h : FieldStep) :
    ConcaveOn ℝ (Icc (-1 : ℝ) 1) (constrainedFieldValue h) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro s hs t ht a b ha hb hab
  have hs' : |s| ≤ 1 := abs_le.mpr hs
  have ht' : |t| ≤ 1 := abs_le.mpr ht
  apply le_csInf (range_nonempty _)
  rintro _ ⟨c, rfl⟩
  have hsc := mul_le_mul_of_nonneg_left (constrainedFieldValue_le_trial h hs' c) ha
  have htc := mul_le_mul_of_nonneg_left (constrainedFieldValue_le_trial h ht' c) hb
  simp only [smul_eq_mul, magneticBiasObjective]
  calc
    a * constrainedFieldValue h s + b * constrainedFieldValue h t ≤
        a * (fieldValue h c - c * s) + b * (fieldValue h c - c * t) := add_le_add hsc htc
    _ = (a + b) * fieldValue h c - c * (a * s + b * t) := by ring
    _ = fieldValue h c - c * (a * s + b * t) := by rw [hab, one_mul]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPopulationCoupling
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transporting a magnetization profile through a finite coupling of
field populations increases its grouped constrained entropy. -/
noncomputable section
open Set
open scoped BigOperators
namespace InvariantIsing

lemma transportedMagnetization_radius {A B : Type*} [Fintype A]
    (w : A → B → ℝ) (δ : B → ℝ) (mag : A → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hδ : ∀ b, 0 < δ b) (hcol : ∀ b, ∑ a, w a b=δ b)
    {s : ℝ} (hm : ∀ a, |mag a| ≤ s) (b : B) :
    |transportedMagnetization w δ mag b| ≤ s := by
  rw [transportedMagnetization,abs_div,abs_of_pos (hδ b)]
  apply (div_le_iff₀ (hδ b)).mpr
  calc
    |∑ a, w a b*mag a| ≤ ∑ a, |w a b*mag a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w a b*|mag a| := by simp_rw [abs_mul,abs_of_nonneg (hw _ _)]
    _ ≤ ∑ a, w a b*s := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hm a) (hw a b))
    _ = s*δ b := by rw [← Finset.sum_mul,hcol,mul_comm]

lemma transportedMagnetization_groupValue {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℝ) (γ : A → ℝ) (δ : B → ℝ) (mag : A → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hδ : ∀ b, 0 < δ b)
    (hrow : ∀ a, ∑ b, w a b=γ a) (hcol : ∀ b, ∑ a, w a b=δ b)
    (hm : ∀ a, |mag a| ≤ 1) (h : FieldStep) :
    magneticGroupValue γ mag h ≤
      magneticGroupValue δ (transportedMagnetization w δ mag) h := by
  have hJ b : (∑ a, w a b*constrainedFieldValue h (mag a)) ≤
      δ b*constrainedFieldValue h (transportedMagnetization w δ mag b) := by
    have hj := (concaveOn_constrainedFieldValue_magnetization h).le_map_sum
      (t := Finset.univ) (w := fun a => w a b/δ b) (p := mag)
      (fun a _ => div_nonneg (hw a b) (hδ b).le)
      (by rw [← Finset.sum_div,hcol,div_self (hδ b).ne'])
      (fun a _ => abs_le.mp (hm a))
    simp only [smul_eq_mul] at hj
    have he : (∑ a, w a b/δ b*mag a)=transportedMagnetization w δ mag b := by
      simp only [transportedMagnetization,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [he] at hj
    have hl : (∑ a, w a b/δ b*constrainedFieldValue h (mag a))=
        (∑ a, w a b*constrainedFieldValue h (mag a))/δ b := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hl] at hj
    simpa only [mul_comm] using (div_le_iff₀ (hδ b)).mp hj
  calc
    magneticGroupValue γ mag h = ∑ a, ∑ b, w a b*constrainedFieldValue h (mag a) := by
      simp_rw [magneticGroupValue,← Finset.sum_mul,hrow]
    _ = ∑ b, ∑ a, w a b*constrainedFieldValue h (mag a) := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun b _ => hJ b)

lemma transportedMagnetization_variational {A B : Type*} [Fintype A] [Fintype B]
    (R : ℝ → ℝ) (w : A → B → ℝ) (γ : A → ℝ) (δ : B → ℝ) (mag : A → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hδ : ∀ b, 0 < δ b)
    (hrow : ∀ a, ∑ b, w a b=γ a) (hcol : ∀ b, ∑ a, w a b=δ b)
    (hm : ∀ a, |mag a| ≤ 1) :
    magneticVariationalFunctional R γ mag ≤
      magneticVariationalFunctional R δ (transportedMagnetization w δ mag) := by
  apply iInf_mono
  intro p
  apply add_le_add _ le_rfl
  apply iSup_mono
  intro h
  apply EReal.coe_le_coe
  exact add_le_add (transportedMagnetization_groupValue w γ δ mag hw hδ hrow hcol hm h) le_rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticCouplingField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The field contribution changes by at most the transportation cost
when an interior profile is averaged across field populations. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma transportedMagnetization_field_term {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℝ) (δ c : B → ℝ) (mag : A → ℝ) (hδ : ∀ b, 0 < δ b) :
    (∑ b, δ b*c b*transportedMagnetization w δ mag b)=
      ∑ a, ∑ b, w a b*c b*mag a := by
  calc
    _ = ∑ b, c b*(∑ a, w a b*mag a) := by
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [transportedMagnetization]
      field_simp [(hδ b).ne']
    _ = ∑ b, ∑ a, w a b*c b*mag a := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := Finset.sum_comm

lemma transportedMagnetization_field_cost {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℝ) (γ b : A → ℝ) (δ c : B → ℝ) (mag : A → ℝ)
    (hw : ∀ a j, 0 ≤ w a j) (hδ : ∀ j, 0 < δ j)
    (hrow : ∀ a, ∑ j, w a j=γ a) (hm : ∀ a, |mag a| ≤ 1) :
    (∑ a, γ a*b a*mag a)-(∑ j, δ j*c j*transportedMagnetization w δ mag j) ≤
      ∑ a, ∑ j, w a j* |b a-c j| := by
  have hsource : (∑ a, γ a*b a*mag a)=∑ a, ∑ j, w a j*b a*mag a := by
    simp_rw [← Finset.sum_mul,hrow]
  rw [hsource,transportedMagnetization_field_term w δ c mag hδ,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ = w a j*(b a-c j)*mag a := by ring
    _ ≤ |w a j*(b a-c j)*mag a| := le_abs_self _
    _ = w a j* |b a-c j| * |mag a| := by rw [abs_mul,abs_mul,abs_of_nonneg (hw a j)]
    _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (hw a j) (abs_nonneg _)) (hm a)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGroupInterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An interior limit gives a common strict magnetization bound for all
sufficiently large members of a finite family. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma exists_uniform_magnetization_radius {A : Type*} [Fintype A]
    (s : ℕ → A → ℝ) (t : A → ℝ) (hs : Tendsto s atTop (𝓝 t))
    (ht : ∀ a, |t a|<1) :
    ∃ r : ℝ, r<1 ∧ (∀ a, |t a| ≤ r) ∧ ∀ᶠ k in atTop, ∀ a, |s k a| ≤ r := by
  classical
  by_cases hA : Nonempty A
  · have : Nonempty A := hA
    have hne : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
    let M := Finset.univ.sup' hne (fun a => |t a|)
    have hM : M<1 := (Finset.sup'_lt_iff hne).mpr (fun a _ => ht a)
    obtain ⟨r, hMr, hr⟩ := exists_between hM
    have htr a : |t a| < r := (Finset.le_sup' (fun a => |t a|) (Finset.mem_univ a)).trans_lt hMr
    refine ⟨r, hr, fun a => (htr a).le, ?_⟩
    rw [Filter.eventually_all]
    intro a
    exact ((((tendsto_pi_nhds.mp hs) a).abs).eventually (Iio_mem_nhds (htr a))).mono
      (fun _ h => h.le)
  · have : IsEmpty A := not_nonempty_iff.mp hA
    exact ⟨0, by norm_num, fun a => isEmptyElim a, Filter.Eventually.of_forall (fun _ a => isEmptyElim a)⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticVariationalTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transportation stability of the finite magnetic variational formula.
The bound is independent of the covariance path and optimizing bias. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

theorem finiteMagneticFunctional_transport_le_oai {A B ι : Type*}
    [Fintype A] [Fintype B] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (w : A → B → ℝ) (γ b : A → ℝ) (δ c : B → ℝ)
    (hw : ∀ a j, 0 ≤ w a j) (hγ : ∀ a, 0 ≤ γ a) (hδ : ∀ j, 0 < δ j)
    (hγsum : ∑ a, γ a=1) (hδsum : ∑ j, δ j=1)
    (hrow : ∀ a, ∑ j, w a j=γ a) (hcol : ∀ j, ∑ a, w a j=δ j) :
    (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) δ c).toReal+
        ∑ a, ∑ j, w a j* |b a-c j| := by
  classical
  let R := finiteR ρ eig hρ hsum
  let T := (finiteMagneticFunctional R δ c).toReal
  let cost := ∑ a, ∑ j, w a j* |b a-c j|
  have hR := finiteVariational_ne_top_bot ρ eig hρ hsum
  have hF := finiteMagneticFunctional_ne_top_bot R γ b hγ hγsum hR.1 hR.2
  have hbound : finiteMagneticFunctional R γ b ≤ ((T+cost : ℝ) : EReal) := by
    apply iSup_le
    intro mag
    let u := transportedMagnetization w δ (fun a => (mag.val a : ℝ))
    obtain ⟨s,hs,hms,_⟩ := exists_uniform_magnetization_radius
      (fun _ : ℕ => fun a => (mag.val a : ℝ)) (fun a => (mag.val a : ℝ))
      tendsto_const_nhds mag.property
    have hu j : |u j|<1 :=
      (transportedMagnetization_radius w δ _ hw hδ hcol hms j).trans_lt hs
    have hv := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ
      (fun a => (mag.val a : ℝ)) hγ hγsum (fun a => (mag.property a).le)
    have hvu := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum δ u
      (fun j => (hδ j).le) hδsum (fun j => (hu j).le)
    have he := transportedMagnetization_variational R w γ δ
      (fun a => (mag.val a : ℝ)) hw hδ hrow hcol (fun a => (mag.property a).le)
    rw [← EReal.coe_toReal hv.1 hv.2,← EReal.coe_toReal hvu.1 hvu.2] at he
    have he' := EReal.coe_le_coe_iff.mp he
    have htrial := finiteMagneticFunctional_real_profile ρ eig hρ hsum δ c u
      (fun j => (hδ j).le) hδsum hu
    have hcost := transportedMagnetization_field_cost w γ b δ c
      (fun a => (mag.val a : ℝ)) hw hδ hrow (fun a => (mag.property a).le)
    rw [← EReal.coe_toReal hv.1 hv.2,← EReal.coe_add]
    apply EReal.coe_le_coe
    change _ ≤ cost at hcost
    change _ ≤ T at htrial
    change _ ≤ (magneticVariationalFunctional R δ u).toReal at he'
    linarith
  rw [← EReal.coe_toReal hF.1 hF.2] at hbound
  exact EReal.coe_le_coe_iff.mp hbound

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.InvariantIsing.finiteMagneticFunctional_transport_le_oai.{u_1, u_2, u_3} := @OAI.InvariantIsing.finiteMagneticFunctional_transport_le_oai.{u_1, u_2, u_3}
