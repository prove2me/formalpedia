-- Prove2me | solution 1 for OAI.InvariantIsing.finiteMagneticVariational_ne_top_bot
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:26:26.024181+00:00
-- url     : https://prove2.me/submissions/463042da-e08c-4a49-b367-9c404cd3ba45

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
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
import Theorems.Thm_OAI_InvariantIsing_entropyFunctional_zero
import Theorems.Thm_OAI_InvariantIsing_magneticEntropyFunctional_lower

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

lemma entropyFunctional_nonneg (p : OverlapPath) : 0 ≤ entropyFunctional p := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simpa only [entropyFunctional, fieldValue_zero, Real.cosh_zero, Real.log_one, fieldPairing_zero,
    zero_div, add_zero, EReal.coe_zero] using h

lemma spectralFunctional_constant (a : ℝ) (p : OverlapPath) :
    spectralFunctional (fun _ => a) p = a / 2 := by
  simp [spectralFunctional]
  ring

lemma integrable_spectral_composition (R : ℝ → ℝ) (hR : Continuous R)
    (p : OverlapPath) : Integrable (fun r => R (deficit p r)) pathMeasure := by
  change IntegrableOn (fun r => R (deficit p r)) (Set.Ioo (0 : ℝ) 1)
  exact ((hR.comp (continuous_deficit p)).continuousOn.integrableOn_Icc).mono_set
    Set.Ioo_subset_Icc_self

/-- Section 6's uniform comparison of spectral functionals. -/
lemma abs_spectralFunctional_sub_le (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |R x - Q x| ≤ δ) (p : OverlapPath) :
    |spectralFunctional R p - spectralFunctional Q p| ≤ δ / 2 := by
  have hr : ∀ᵐ r ∂pathMeasure, r ∈ Set.Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have hi := norm_integral_le_of_norm_le_const (μ := pathMeasure)
    (f := fun r => R (deficit p r) - Q (deficit p r)) (C := δ) (by
      filter_upwards [hr] with r hr
      simpa only [Real.norm_eq_abs] using hδ _ (deficit_mem_unit p ⟨hr.1.le, hr.2.le⟩))
  have hib : |∫ r, R (deficit p r) - Q (deficit p r) ∂pathMeasure| ≤ δ := by
    simpa only [Real.norm_eq_abs, measureReal_def, pathMeasure_univ,
      ENNReal.toReal_one, mul_one] using hi
  rw [spectralFunctional, spectralFunctional, ← mul_sub,
    ← integral_sub (integrable_spectral_composition R hR p)
      (integrable_spectral_composition Q hQ p), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * δ := mul_le_mul_of_nonneg_left hib (by norm_num)
    _ = δ / 2 := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteVariationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finiteness and finite-entropy approximate minimizers of the finite-spectrum
variational problem. These justify taking the infimum in the pressure bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

theorem finiteSpectralFunctional_abs_le {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (K : ℝ) (heig : ∀ a, |eig a| ≤ K) (p : OverlapPath) :
    |spectralFunctional (finiteR ρ eig hρ hρsum) p| ≤ K / 2 := by
  have hb x : |finiteR ρ eig hρ hρsum x - 0| ≤ K := by
    simpa only [sub_zero] using abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  simpa only [spectralFunctional_constant, zero_div, sub_zero] using
    abs_spectralFunctional_sub_le (finiteR ρ eig hρ hρsum) (fun _ => 0)
      (continuous_finiteR ρ eig hρ hρsum) continuous_const K (fun x _ => hb x) p

theorem finiteVariational_mem_interval {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (K : ℝ) (heig : ∀ a, |eig a| ≤ K) :
    (-(K / 2) : ℝ) ≤ variationalFunctional (finiteR ρ eig hρ hρsum) ∧
      variationalFunctional (finiteR ρ eig hρ hρsum) ≤ (K / 2 : ℝ) := by
  constructor
  · apply le_iInf
    intro p
    have hs := (abs_le.mp (finiteSpectralFunctional_abs_le ρ eig hρ hρsum K heig p)).1
    have he : ((-(K / 2) : ℝ) : EReal) ≤
        (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal) := by exact_mod_cast hs
    have hadd := add_le_add (entropyFunctional_nonneg p)
      (le_rfl : (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal) ≤ _)
    exact he.trans (by simpa only [zero_add] using hadd)
  · let p := constantPath 0 (by constructor <;> norm_num)
    have hi := iInf_le (fun p : OverlapPath => entropyFunctional p +
      (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal)) p
    have hs := (abs_le.mp (finiteSpectralFunctional_abs_le ρ eig hρ hρsum K heig p)).2
    simp only [p, entropyFunctional_zero, zero_add] at hi
    exact hi.trans (by exact_mod_cast hs)

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticVariational
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure
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

lemma magneticVariationalFunctional_le {A : Type*} [Fintype A]
    (R : ℝ → ℝ) (γ m : A → ℝ) (hγ : ∀ a, 0 ≤ γ a)
    (hγsum : ∑ a, γ a = 1) (hm : ∀ a, |m a| ≤ 1) :
    magneticVariationalFunctional R γ m ≤ variationalFunctional R := by
  apply iInf_mono
  intro p
  exact add_le_add (magneticEntropyFunctional_le γ m hγ hγsum hm p) le_rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticVariationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finiteness of the magnetic variational value, with the original
cube-mass entropy lower bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace InvariantIsing

theorem finiteMagneticVariational_mem_interval {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (K : ℝ) (heig : ∀ a, |eig a| ≤ K) :
    ((-Real.log 2-K/2 : ℝ) : EReal) ≤ magneticVariationalFunctional (finiteR ρ eig hρ hρsum) γ mag ∧
      magneticVariationalFunctional (finiteR ρ eig hρ hρsum) γ mag ≤ ((K/2 : ℝ) : EReal) := by
  constructor
  · apply le_iInf
    intro p
    have hs := (abs_le.mp (finiteSpectralFunctional_abs_le ρ eig hρ hρsum K heig p)).1
    have hh := add_le_add (magneticEntropyFunctional_lower γ mag hγ hγsum hmag p)
      (EReal.coe_le_coe hs)
    simpa only [← EReal.coe_add, sub_eq_add_neg, neg_div] using hh
  · exact (magneticVariationalFunctional_le (finiteR ρ eig hρ hρsum) γ mag hγ hγsum hmag).trans
      (finiteVariational_mem_interval ρ eig hρ hρsum K heig).2

theorem finiteMagneticVariational_ne_top_bot_oai {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) :
    magneticVariationalFunctional (finiteR ρ eig hρ hρsum) γ mag ≠ ⊤ ∧
      magneticVariationalFunctional (finiteR ρ eig hρ hρsum) γ mag ≠ ⊥ := by
  let K := ∑ a, |eig a|
  have heig a : |eig a| ≤ K := Finset.single_le_sum
    (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hb := finiteMagneticVariational_mem_interval ρ eig hρ hρsum γ mag hγ hγsum hmag K heig
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hb.2,
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb.1⟩

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.InvariantIsing.finiteMagneticVariational_ne_top_bot_oai.{u_1, u_2} := @OAI.InvariantIsing.finiteMagneticVariational_ne_top_bot_oai.{u_1, u_2}
