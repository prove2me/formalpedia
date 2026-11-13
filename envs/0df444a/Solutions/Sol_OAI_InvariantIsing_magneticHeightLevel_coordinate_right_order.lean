-- Prove2me | solution 1 for OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:00:15.517199+00:00
-- url     : https://prove2.me/submissions/19d90c7f-6e1e-48f2-a5f0-b6291900bd80

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_IsingFiniteness
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_closedMagneticSquareContinuationSecond_nonneg
import Theorems.Thm_OAI_InvariantIsing_magneticClosedCurvature_compare_initial

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VariationalDefs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variational Defs. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma gaussian_linearGrowth_integrable {F : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (m : ℝ) (v : ℝ≥0) : Integrable F (gaussianReal m v) := by
  obtain ⟨C,L,hC,hL,h⟩ := hG
  have hi : Integrable (fun x : ℝ => C+L*‖x‖) (gaussianReal m v) :=
    (integrable_const _).add (((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable le_rfl).norm.const_mul L)
  exact hi.mono' hF.aestronglyMeasurable (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using h x))

lemma gaussianTransform_const_add {U : ℝ → ℝ} (hU : Measurable U) (hG : HasLinearGrowth U)
    (s d c : ℝ) :
    gaussianTransform s d (fun x => c+U x) = fun x => c+gaussianTransform s d U x := by
  ext x
  by_cases hd : d=0
  · simp only [gaussianTransform,hd,ite_true, if_true]
    have hi : Integrable (fun z : ℝ => U (x+Real.sqrt s*z)) (gaussianReal 0 1) :=
      gaussian_linearGrowth_integrable
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) _ _
    rw [integral_add (integrable_const c) hi]
    simp only [integral_const,probReal_univ,one_smul]
  · simp only [gaussianTransform,hd,ite_false, if_false]
    exact logMean_const_add (gaussianReal 0 1) hd
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
        (hU.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) d) c

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldMajorantFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The one-step majorant iterated through the actual finite field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma gaussianOperator_const_add {F : ℝ → ℝ} (hF : Measurable F)
    (hFG : IsingPerceptron.HasLinearGrowth F) (c a v z : ℝ) :
    gaussianOperator a v (fun x => c + F x) z = c + gaussianOperator a v F z := by
  simp only [gaussianOperator_eq_transform]
  exact congrFun (IsingPerceptron.gaussianTransform_const_add hF hFG v a c) z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTiltedFamilyDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating a normalized scalar Gaussian average with a varying
observable. The local envelopes allow the affine-noise quadratic terms
needed in the second derivative of the finite Ising recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_tiltedFamily_hasFDerivAt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A : (ℝ × ℝ) → ℝ → ℝ)
    (DU DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    {p : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 p) (ζ : ℝ)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) μ) (hDA : AEStronglyMeasurable (DA p) μ)
    (hE : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u) μ)
    (MD MN : ℝ → ℝ) (hMD : Integrable MD μ) (hMN : Integrable MN μ)
    (hDen : ∀ q ∈ S, ∀ u, ‖fieldWeightDifferential U DU ζ q u‖ ≤ MD u)
    (hNum : ∀ q ∈ S, ∀ u, ‖fieldObservableDifferential U A DU DA ζ q u‖ ≤ MN u)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    let Z := ∫ u, Real.exp (ζ * U p u) ∂μ
    let N := ∫ u, Real.exp (ζ * U p u) * A p u ∂μ
    HasFDerivAt (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u))
      (Z⁻¹ • (∫ u, fieldObservableDifferential U A DU DA ζ p u ∂μ) -
        (N * (Z ^ 2)⁻¹) • (∫ u, fieldWeightDifferential U DU ζ p u ∂μ)) p := by
  let Z := ∫ u, Real.exp (ζ * U p u) ∂μ
  let N := ∫ u, Real.exp (ζ * U p u) * A p u ∂μ
  let DZ := ∫ u, fieldWeightDifferential U DU ζ p u ∂μ
  let DN := ∫ u, fieldObservableDifferential U A DU DA ζ p u ∂μ
  have hZD : HasFDerivAt (fun q => ∫ u, Real.exp (ζ * U q u) ∂μ) DZ p := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => ((hU q).const_mul ζ).exp.aestronglyMeasurable)
      hE (((hU p).const_mul ζ).exp.aestronglyMeasurable.smul (hDU.const_smul ζ))
      (ae_of_all _ fun u q hq => hDen q hq u) hMD
    exact ae_of_all _ fun u q hq => ((dU q hq u).const_mul ζ).exp
  have hND : HasFDerivAt (fun q => ∫ u, Real.exp (ζ * U q u) * A q u ∂μ) DN p := by
    have hDM : AEStronglyMeasurable (fieldObservableDifferential U A DU DA ζ p) μ :=
      ((hU p).const_mul ζ).exp.aestronglyMeasurable.smul
        (hDA.add (((hA p).const_mul ζ).aestronglyMeasurable.smul hDU))
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le hS
      (Eventually.of_forall fun q => (((hU q).const_mul ζ).exp.mul (hA q)).aestronglyMeasurable)
      hEA hDM (ae_of_all _ fun u q hq => hNum q hq u) hMN
    refine ae_of_all _ fun u q hq => ?_
    convert (((dU q hq u).const_mul ζ).exp).mul (dA q hq u) using 1
    all_goals try with_reducible_and_instances rfl
    apply ContinuousLinearMap.ext
    intro v
    simp only [fieldObservableDifferential, smul_apply,
      add_apply, smul_eq_mul]
    ring
  have hZ : Z ≠ 0 := (integral_exp_pos μ (U p) hE).ne'
  have hInv : HasFDerivAt (fun q => (∫ u, Real.exp (ζ * U q u) ∂μ)⁻¹)
      (-(Z ^ 2)⁻¹ • DZ) p := by
    refine ((hasDerivAt_inv hZ).hasFDerivAt.comp p hZD).congr_fderiv (Eq.symm ?_)
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        smul_eq_mul]
      change -(Z ^ 2)⁻¹ * DZ v = DZ v * -(Z ^ 2)⁻¹
      ring
  have hquot := hND.mul hInv
  have he : (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u)) =
      fun q => (∫ u, Real.exp (ζ * U q u) * A q u ∂μ) *
        (∫ u, Real.exp (ζ * U q u) ∂μ)⁻¹ := by
    funext q
    rw [integral_tilted_eq_div, div_eq_mul_inv]
  rw [he]
  convert hquot using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, smul_apply,
    add_apply, smul_eq_mul]
  change Z⁻¹ * DN v - N * (Z ^ 2)⁻¹ * DZ v =
    N * (-(Z ^ 2)⁻¹ * DZ v) + Z⁻¹ * DN v
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTiltedPairDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariance form of the derivative of an actual normalized average.
This is the two-coordinate formula used by the finite scalar recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_tiltedFamily_covariance_hasFDerivAt
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (U A : (ℝ × ℝ) → ℝ → ℝ)
    (DU DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    {p : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 p) (ζ : ℝ)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) μ) (hDA : AEStronglyMeasurable (DA p) μ)
    (hE : Integrable (fun u => Real.exp (ζ * U p u)) μ)
    (hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u) μ)
    (MD MN : ℝ → ℝ) (hMD : Integrable MD μ) (hMN : Integrable MN μ)
    (hDen : ∀ q ∈ S, ∀ u, ‖fieldWeightDifferential U DU ζ q u‖ ≤ MD u)
    (hNum : ∀ q ∈ S, ∀ u, ‖fieldObservableDifferential U A DU DA ζ q u‖ ≤ MN u)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    HasFDerivAt (fun q => ∫ u, A q u ∂μ.tilted (fun u => ζ * U q u))
      ((∫ u, DA p u + (ζ * A p u) • DU p u
          ∂μ.tilted (fun u => ζ * U p u)) -
        (∫ u, A p u ∂μ.tilted (fun u => ζ * U p u)) •
          (∫ u, ζ • DU p u ∂μ.tilted (fun u => ζ * U p u))) p := by
  have h := field_tiltedFamily_hasFDerivAt μ U A DU DA hS ζ hU hA hDU hDA
    hE hEA MD MN hMD hMN hDen hNum dU dA
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [field_tilted_integral_normalize, field_tilted_integral_normalize,
    field_tilted_integral_normalize]
  simp only [smul_eq_mul, fieldObservableDifferential, fieldWeightDifferential,
    pow_two, smul_smul]
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [smul_apply, smul_eq_mul]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianPairDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial envelopes for differentiating the finite scalar Gaussian
recursion twice. The envelope has degree two in the single Gaussian mark. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_gaussianPair_hasFDerivAt
    (U A : (ℝ × ℝ) → ℝ → ℝ)
    (DU DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    {p : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 p) (hpS : p ∈ S)
    (ζ C L CA CD CE : ℝ) (hCA : 0 ≤ CA) (hCD : 0 ≤ CD) (_hCE : 0 ≤ CE)
    (hU : ∀ q, Measurable (U q)) (hA : ∀ q, Measurable (A q))
    (hDU : AEStronglyMeasurable (DU p) (gaussianReal 0 1))
    (hDA : AEStronglyMeasurable (DA p) (gaussianReal 0 1))
    (hExp : ∀ q ∈ S, ∀ u, Real.exp (ζ * U q u) ≤ Real.exp (C + L * |u|))
    (hAb : ∀ q ∈ S, ∀ u, |A q u| ≤ CA * (1 + |u|))
    (hDb : ∀ q ∈ S, ∀ u, ‖DU q u‖ ≤ CD * (1 + |u|))
    (hEb : ∀ q ∈ S, ∀ u, ‖DA q u‖ ≤ CE * (1 + |u|) ^ 2)
    (dU : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => U r u) (DU q u) q)
    (dA : ∀ q ∈ S, ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q) :
    HasFDerivAt (fun q => ∫ u, A q u
      ∂(gaussianReal 0 1).tilted (fun u => ζ * U q u))
      ((∫ u, DA p u + (ζ * A p u) • DU p u
          ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u)) -
        (∫ u, A p u ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u)) •
          (∫ u, ζ • DU p u ∂(gaussianReal 0 1).tilted (fun u => ζ * U p u))) p := by
  let E : ℝ → ℝ := fun u => Real.exp (C + L * |u|) * (1 + |u|) ^ 2
  have hEi : Integrable E (gaussianReal 0 1) :=
    field_gaussian_quadratic_envelope_integrable C L
  have hE : Integrable (fun u => Real.exp (ζ * U p u)) (gaussianReal 0 1) := by
    apply hEi.mono' ((hU p).const_mul ζ).exp.aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (hExp p hpS u).trans (le_mul_of_one_le_right (Real.exp_pos _).le (by
      nlinarith [abs_nonneg u]))
  have hEA : Integrable (fun u => Real.exp (ζ * U p u) * A p u)
      (gaussianReal 0 1) := by
    apply (hEi.const_mul CA).mono' (((hU p).const_mul ζ).exp.mul (hA p)).aestronglyMeasurable
    refine ae_of_all _ fun u => ?_
    change ‖Real.exp (ζ * U p u) * A p u‖ ≤ CA * E u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (C + L * |u|) * (CA * (1 + |u|)) :=
        mul_le_mul (hExp p hpS u) (hAb p hpS u) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (C + L * |u|) * (CA * (1 + |u|) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hCA) (Real.exp_pos _).le
      _ = CA * E u := by dsimp only [E] <;> ring
  apply field_tiltedFamily_covariance_hasFDerivAt (gaussianReal 0 1) U A DU DA
    hS ζ hU hA hDU hDA hE hEA
    (fun u => (|ζ| * CD) * E u) (fun u => (CE + |ζ| * CA * CD) * E u)
    (hEi.const_mul _) (hEi.const_mul _)
  · intro q hq u
    rw [fieldWeightDifferential, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (C + L * |u|) * (|ζ| * (CD * (1 + |u|))) :=
        mul_le_mul (hExp q hq u)
          (mul_le_mul_of_nonneg_left (hDb q hq u) (abs_nonneg _))
          (by positivity) (Real.exp_pos _).le
      _ ≤ Real.exp (C + L * |u|) * (|ζ| * (CD * (1 + |u|) ^ 2)) := by
        gcongr
        exact field_mark_one_add_le_sq u
      _ = _ := by dsimp only [E] <;> ring
  · intro q hq u
    rw [fieldObservableDifferential, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hinner : ‖DA q u + (ζ * A q u) • DU q u‖ ≤
        (CE + |ζ| * CA * CD) * (1 + |u|) ^ 2 := by
      calc
        _ ≤ ‖DA q u‖ + ‖(ζ * A q u) • DU q u‖ := norm_add_le _ _
        _ = ‖DA q u‖ + |ζ| * |A q u| * ‖DU q u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul]
        _ ≤ CE * (1 + |u|) ^ 2 + |ζ| * (CA * (1 + |u|)) * (CD * (1 + |u|)) := by
          gcongr
          · exact hEb q hq u
          · exact hAb q hq u
          · exact hDb q hq u
        _ = _ := by ring
    calc
      _ ≤ Real.exp (C + L * |u|) * ((CE + |ζ| * CA * CD) * (1 + |u|) ^ 2) :=
        mul_le_mul (hExp q hq u) hinner (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by dsimp only [E] <;> ring
  · exact dU
  · exact dA

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldAffineAverageDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the quadratic-envelope differentiation theorem to the
actual affine Gaussian shift of a finite scalar-field family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing
namespace FieldSmoothFamily

variable {I : Set ℝ} (F : FieldSmoothFamily I)

lemma affine_average_hasFDerivAt (hI : IsOpen I)
    (A : (ℝ × ℝ) → ℝ → ℝ)
    (DA : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ)
    (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V)
    {CA CE : ℝ} (hCA : 0 ≤ CA) (hCE : 0 ≤ CE)
    (hA : ∀ q, Measurable (A q))
    (hDA : ∀ q, AEStronglyMeasurable (DA q) (gaussianReal 0 1))
    (hAb : ∀ q, q.1 ∈ I → ∀ u, |A q u| ≤ CA * (1 + |u|))
    (hEb : ∀ q, q.1 ∈ I → ∀ u, ‖DA q u‖ ≤ CE * (1 + |u|) ^ 2)
    (dA : ∀ q, q.1 ∈ I → ∀ u, HasFDerivAt (fun r => A r u) (DA q u) q)
    {p : ℝ × ℝ} (hp : p.1 ∈ I) :
    HasFDerivAt (fun q => ∫ u, A q u
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v q u))
      ((∫ u, DA p u + (ζ * A p u) • F.affineDifferential a v p u
          ∂(gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u)) -
        (∫ u, A p u
          ∂(gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u)) •
          (∫ u, ζ • F.affineDifferential a v p u
            ∂(gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u))) p := by
  let R := |v| / (2 * Real.sqrt m)
  let CD := F.KT + F.KX * R + F.KX
  let K := |F.U (p.1, 0)| + 1
  let C := |ζ| * (K + F.KX * (|p.2| + 1))
  let L := |ζ| * F.KX * Real.sqrt V
  have hR : 0 ≤ R := by dsimp only [R] <;> positivity
  have hX := F.kx_nonneg
  have hT : 0 ≤ F.KT := (abs_nonneg _).trans (F.bT (p.1, 0) hp)
  have hCD : 0 ≤ CD := by dsimp only [CD] <;> positivity
  have hpair : ContinuousAt (fun t : ℝ => (t, (0 : ℝ))) p.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hc : ContinuousAt (fun t => F.U (t, 0)) p.1 :=
    ContinuousAt.comp (f := fun t : ℝ => (t, (0 : ℝ))) (x := p.1)
      (F.derivative (p.1, 0) hp).continuousAt hpair
  have hg := field_parameter_growth_eventually hX F.bX F.spatial hc
  have hset : {t : ℝ | t ∈ I ∧ ∀ y,
      |F.U (t, y)| ≤ K + F.KX * |y|} ∈ 𝓝 p.1 := by
    filter_upwards [hI.mem_nhds hp, hg] with t ht hgt
    exact ⟨ht, hgt⟩
  obtain ⟨J, hJsub, hJopen, hpJ⟩ := mem_nhds_iff.mp hset
  let S : Set (ℝ × ℝ) := (Prod.fst ⁻¹' J) ∩
    (Prod.snd ⁻¹' Ioo (p.2 - 1) (p.2 + 1))
  have hS : S ∈ 𝓝 p :=
    Filter.inter_mem ((hJopen.preimage continuous_fst).mem_nhds hpJ)
      ((isOpen_Ioo.preimage continuous_snd).mem_nhds ⟨by linarith, by linarith⟩)
  have hpS : p ∈ S := ⟨hpJ, by constructor <;> linarith⟩
  apply field_gaussianPair_hasFDerivAt (F.affineShift a v) A
    (F.affineDifferential a v) DA hS hpS ζ C L CA CD CE hCA hCD hCE
    (fun q => F.mU.comp (by fun_prop)) hA
    ((measurable_pairLinear
      ((F.mT.comp (by fun_prop)).add ((F.mX.comp (by fun_prop)).mul (by
        dsimp only [fieldAmplitudeSlope]
        fun_prop))) (F.mX.comp (by fun_prop))).aestronglyMeasurable)
    (hDA p)
  · intro q hq u
    have hqI := (hJsub hq.1).1
    have hq2 : |q.2| ≤ |p.2| + 1 := by
      have hh : |q.2 - p.2| ≤ 1 := abs_le.mpr ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
      calc
        |q.2| = |q.2 - p.2 + p.2| := by congr 1; ring
        _ ≤ |q.2 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hshift : |q.2 + Real.sqrt (a + v * q.1) * u| ≤
        |p.2| + 1 + Real.sqrt V * |u| := by
      calc
        _ ≤ |q.2| + |Real.sqrt (a + v * q.1) * u| := abs_add_le _ _
        _ = |q.2| + Real.sqrt (a + v * q.1) * |u| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ _ := add_le_add hq2
          (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hhi q.1 hqI)) (abs_nonneg _))
    apply Real.exp_le_exp.mpr
    calc
      ζ * F.affineShift a v q u ≤ |ζ| * |F.affineShift a v q u| := by
        simpa only [abs_mul] using le_abs_self (ζ * F.affineShift a v q u)
      _ ≤ |ζ| * (K + F.KX * |q.2 + Real.sqrt (a + v * q.1) * u|) :=
        mul_le_mul_of_nonneg_left ((hJsub hq.1).2 _) (abs_nonneg _)
      _ ≤ |ζ| * (K + F.KX * (|p.2| + 1 + Real.sqrt V * |u|)) := by gcongr
      _ = C + L * |u| := by dsimp only [C, L]; ring
  · intro q hq u
    exact hAb q (hJsub hq.1).1 u
  · intro q hq u
    have hqI := (hJsub hq.1).1
    have hc : |fieldAmplitudeSlope a v q.1| ≤ R := abs_div_two_sqrt_le hm (hlo q.1 hqI) v
    unfold affineDifferential
    refine (norm_pairLinear_le _ _).trans ?_
    calc
      _ ≤ F.KT + F.KX * (R * |u|) + F.KX := by
        refine add_le_add ((abs_add_le _ _).trans (add_le_add (F.bT _ hqI) ?_)) (F.bX _)
        rw [abs_mul, abs_mul]
        gcongr
        exact F.bX _
      _ ≤ CD * (1 + |u|) := by
        dsimp only [CD]
        nlinarith [mul_nonneg hT (abs_nonneg u), mul_nonneg hX (abs_nonneg u)]
  · intro q hq u
    exact hEb q (hJsub hq.1).1 u
  · intro q hq u
    exact affine_gaussian_shift_hasFDerivAt F.derivative a v u (hJsub hq.1).1
      (hm.trans_le (hlo q.1 (hJsub hq.1).1))
  · intro q hq u
    exact dA q (hJsub hq.1).1 u

end FieldSmoothFamily
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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Combining successive Gaussian increments with the same exponent.
Both the log partition and the normalized transition retain their actual
Gaussian laws, including zero variances and the ordinary exponent zero. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal

namespace InvariantIsing

lemma fieldGaussian_integral_comp (v w : ℝ≥0) (z : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hi : Integrable f (gaussianReal z (v + w))) :
    (∫ x, (∫ y, f y ∂gaussianReal x w) ∂gaussianReal z v) =
      ∫ y, f y ∂gaussianReal z (v + w) := by
  have hc : (gaussianReal z v) ∗ (gaussianReal 0 w) = gaussianReal z (v + w) := by
    simpa only [add_zero] using gaussianReal_conv_gaussianReal (m₁ := z) (m₂ := 0)
      (v₁ := v) (v₂ := w)
  have hi' : Integrable f ((gaussianReal z v) ∗ (gaussianReal 0 w)) := by rwa [hc]
  simp_rw [field_gaussian_integral_shift w _ hf]
  simpa only [hc] using (integral_conv hi').symm

lemma exp_mul_gaussianOperator (ζ : ℝ) (w : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (z : ℝ) :
    Real.exp (ζ * gaussianOperator ζ w F z) =
      ∫ y, Real.exp (ζ * F y) ∂gaussianReal z w := by
  by_cases hζ : ζ = 0
  · subst ζ
    simp only [zero_mul, Real.exp_zero, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul]
  · have hp : 0 < ∫ y, Real.exp (ζ * F y) ∂gaussianReal z w :=
      MeasureTheory.integral_exp_pos (integrable_exp_of_linearGrowth _
        (gaussianReal_exponentialNormMoments z w) hF hG ζ)
    rw [gaussianOperator_eq_gaussian_exp_integral hζ w hF z]
    rw [← mul_assoc, mul_inv_cancel₀ hζ, one_mul, Real.exp_log hp]

theorem gaussianOperator_same_exponent (ζ : ℝ) (v w : ℝ≥0) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (z : ℝ) :
    gaussianOperator ζ v (gaussianOperator ζ w F) z =
      gaussianOperator ζ (v + w : ℝ≥0) F z := by
  have hm : Measurable (gaussianOperator ζ w F) := by
    rw [gaussianOperator_eq_transform]
    exact measurable_gaussianTransform hF w ζ
  by_cases hζ : ζ = 0
  · subst ζ
    rw [gaussianOperator_eq_gaussian_integral v hm z,
      gaussianOperator_eq_gaussian_integral (v + w) hF z]
    simp_rw [gaussianOperator_eq_gaussian_integral w hF]
    exact fieldGaussian_integral_comp v w z hF (field_gaussian_linear_integrable (v + w) z hF hG)
  · rw [gaussianOperator_eq_gaussian_exp_integral hζ v hm z,
      gaussianOperator_eq_gaussian_exp_integral hζ (v + w) hF z]
    apply congrArg (fun r : ℝ => ζ⁻¹ * Real.log r)
    simp_rw [exp_mul_gaussianOperator ζ w hF hG]
    exact fieldGaussian_integral_comp v w z (hF.const_mul ζ).exp
      (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z (v + w)) hF hG ζ)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldSecondCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two-coordinate covariance algebra for second derivatives of
the scalar Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma field_pair_covariance (ν : Measure ℝ) (ζ : ℝ)
    (α A B L M : ℝ → ℝ)
    (hA : Integrable A ν) (hB : Integrable B ν)
    (hL : Integrable L ν) (hM : Integrable M ν)
    (hαL : Integrable (fun u => α u * L u) ν)
    (hαM : Integrable (fun u => α u * M u) ν) :
    (∫ u, pairLinear (A u) (B u) + (ζ * α u) • pairLinear (L u) (M u) ∂ν) -
        (∫ u, α u ∂ν) • (∫ u, ζ • pairLinear (L u) (M u) ∂ν) =
      pairLinear
        ((∫ u, A u ∂ν) + ζ * ((∫ u, α u * L u ∂ν) - (∫ u, α u ∂ν) * (∫ u, L u ∂ν)))
        ((∫ u, B u ∂ν) + ζ * ((∫ u, α u * M u ∂ν) - (∫ u, α u ∂ν) * (∫ u, M u ∂ν))) := by
  have he : (fun u => pairLinear (A u) (B u) + (ζ * α u) • pairLinear (L u) (M u)) =
      fun u => pairLinear (A u + ζ * (α u * L u)) (B u + ζ * (α u * M u)) := by
    funext u
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, smul_apply, pairLinear_apply, smul_eq_mul]
    ring
  have hiA : Integrable (fun u => A u + ζ * (α u * L u)) ν := hA.add (hαL.const_mul ζ)
  have hiB : Integrable (fun u => B u + ζ * (α u * M u)) ν := hB.add (hαM.const_mul ζ)
  have heA : (∫ u, A u + ζ * (α u * L u) ∂ν) =
      (∫ u, A u ∂ν) + ζ * ∫ u, α u * L u ∂ν := by
    rw [integral_add hA (hαL.const_mul ζ), integral_const_mul]
  have heB : (∫ u, B u + ζ * (α u * M u) ∂ν) =
      (∫ u, B u ∂ν) + ζ * ∫ u, α u * M u ∂ν := by
    rw [integral_add hB (hαM.const_mul ζ), integral_const_mul]
  rw [he, integral_pairLinear ν hiA hiB, heA, heB, integral_smul,
    integral_pairLinear ν hL hM]
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, smul_apply, pairLinear_apply, smul_eq_mul]
  ring

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticImplicitBias
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parametric inversion of a strictly increasing physical mean spin.
This supplies the finite-dimensional inverse-coordinate and envelope steps
without assuming differentiability of the minimizing bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma parametric_bias_continuousAt {A : ℝ × ℝ → ℝ} {b : ℝ → ℝ} {t s : ℝ}
    (hc : ∀ z, ContinuousAt (fun q => A (q, z)) t)
    (hm : ∀ᶠ q in 𝓝 t, StrictMono (fun z => A (q, z)))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s) : ContinuousAt b t := by
  have het := he.self_of_nhds
  have hmt := hm.self_of_nhds
  apply tendsto_order.2
  constructor
  · intro l hl
    have hlt : A (t, l) < s := by rw [← het]; exact hmt hl
    have hn : ∀ᶠ q in 𝓝 t, A (q, l) < s :=
      (hc l).tendsto.eventually (Iio_mem_nhds hlt)
    filter_upwards [hm, he, hn] with q hmq heq hq
    apply hmq.lt_iff_lt.mp
    rwa [heq]
  · intro u hu
    have htu : s < A (t, u) := by rw [← het]; exact hmt hu
    have hn : ∀ᶠ q in 𝓝 t, s < A (q, u) :=
      (hc u).tendsto.eventually (Ioi_mem_nhds htu)
    filter_upwards [hm, he, hn] with q hmq heq hq
    apply hmq.lt_iff_lt.mp
    rwa [heq]

/-- The implicit bias derivative follows from the derivative of the actual
mean-spin map and the local root equation. -/
lemma parametric_bias_hasDerivAt {A : ℝ × ℝ → ℝ} {b : ℝ → ℝ} {t s a c : ℝ}
    (hb : ContinuousAt b t) (hc : c ≠ 0)
    (hA : HasFDerivAt A (pairLinear a c) (t, b t))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s) :
    HasDerivAt b (-a / c) t := by
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (pairLinear a c)
  let M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (pairLinear (-a / c) (1 / c))
  have hleft : Function.LeftInverse M L := by
    rintro ⟨x, y⟩
    apply Prod.ext
    · rfl
    · change -a / c * x + (1 / c) * (a * x + c * y) = y
      field_simp [hc]
      ring
  have hf : HasFDerivAt (fun p : ℝ × ℝ => (p.1, A p)) L (t, b t) :=
    hasFDerivAt_fst.prodMk hA
  have hg : ContinuousAt (fun q => (q, b q)) t := continuousAt_id.prodMk hb
  have hh : HasFDerivAt (fun q : ℝ => (q, s))
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)) t :=
    (hasFDerivAt_id t).prodMk (hasFDerivAt_const s t)
  have hcomp : (fun p : ℝ × ℝ => (p.1, A p)) ∘ (fun q => (q, b q)) =ᶠ[𝓝 t]
      (fun q => (q, s)) := by
    filter_upwards [he] with q hq
    exact congrArg (Prod.mk q) hq
  have hd := HasFDerivAt.of_comp_of_leftInverse hg hf hh hcomp hleft
  have hsnd := hd.snd.hasDerivAt
  convert hsnd using 1
  all_goals try with_reducible_and_instances rfl
  simp [M, pairLinear]

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

lemma inverse_mean_curvature_variation {A C : ℝ × ℝ → ℝ}
    {b : ℝ → ℝ} {t s a c v d : ℝ}
    (hb : ContinuousAt b t) (hc : c ≠ 0)
    (hA : HasFDerivAt A (pairLinear a c) (t, b t))
    (he : ∀ᶠ q in 𝓝 t, A (q, b q) = s)
    (hC : HasFDerivAt C (pairLinear v d) (t, b t)) :
    HasDerivAt (fun q => C (q, b q)) (v - d * a / c) t := by
  have hdb := parametric_bias_hasDerivAt hb hc hA he
  have hd := hC.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hdb)
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | (simp only [pairLinear_apply]; ring)

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian integration by parts for the bounded continuation test,
with the actual linearly growing scalar field as tilted potential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magnetic_gaussian_tilted_test_ibp {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hA : Measurable A) (hB : Measurable B)
    {K C D : ℝ} (bM : ∀ x, |M x| ≤ K) (bA : ∀ x, |A x| ≤ C)
    (bB : ∀ x, |B x| ≤ D) (dF : ∀ x, HasDerivAt F (M x) x)
    (dA : ∀ x, HasDerivAt A (B x) x) (r ζ z : ℝ) :
    (∫ u, u * A (z + r * u)
      ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) =
      r * (∫ u, B (z + r * u) + ζ * A (z + r * u) * M (z + r * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (bA 0)
  let U := fun u => F (z + r * u)
  let V := fun u => Real.exp (ζ * U u) * A (z + r * u)
  let DV := fun u => r * (Real.exp (ζ * U u) *
    (B (z + r * u) + ζ * A (z + r * u) * M (z + r * u)))
  have hUm : Measurable U := hF.comp (by fun_prop)
  have hUg : HasLinearGrowth U := (hG.add_left z).scale_argument r
  have hw := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hUm hUg ζ
  have bgen (x : ℝ) : |B x + ζ * A x * M x| ≤ D + |ζ| * C * K := by
    refine (abs_add_le _ _).trans (add_le_add (bB x) ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bA x) (abs_nonneg ζ))
      (bM x) (abs_nonneg _) (mul_nonneg (abs_nonneg ζ) hC)
  have hV : Integrable V (gaussianReal 0 1) :=
    hw.mul_bdd (hA.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        simpa only [Real.norm_eq_abs] using bA (z + r * u))
  have hDV : Integrable DV (gaussianReal 0 1) := by
    apply Integrable.const_mul
    exact hw.mul_bdd
      ((hB.comp (by fun_prop)).add
        (((hA.comp (by fun_prop)).const_mul ζ).mul (hM.comp (by fun_prop)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        simpa only [Real.norm_eq_abs] using bgen (z + r * u))
  have hderiv (u : ℝ) : HasDerivAt V (DV u) u := by
    have hs : HasDerivAt (fun x : ℝ => z + r * x) r u := by
      convert ((hasDerivAt_id u).const_mul r).const_add z using 1 <;> first | rfl | simp
    have hf : HasDerivAt (fun x => F (z + r * x)) (M (z + r * u) * r) u :=
      (dF (z + r * u)).comp u hs
    have ha : HasDerivAt (fun x => A (z + r * x)) (B (z + r * u) * r) u :=
      (dA (z + r * u)).comp u hs
    convert ((hf.const_mul ζ).exp).mul ha using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [V, DV, U]
    ring
  have hlinear : HasLinearGrowth (fun u => u * A (z + r * u)) := by
    refine ⟨0, C, le_rfl, hC, fun u => ?_⟩
    rw [abs_mul, Real.norm_eq_abs, zero_add]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (bA (z + r * u)) (abs_nonneg u)
  have hUV : Integrable (fun u => u * V u) (gaussianReal 0 1) := by
    convert field_exp_mul_linear_integrable 1 0 ζ hUm hUg
      (measurable_id.mul (hA.comp (by fun_prop))) hlinear using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    dsimp only [V, Pi.mul_apply, Function.comp_apply, id_eq]
    ring
  have hibp := gaussian_integration_by_parts hderiv hV hDV hUV
  simp only [integral_tilted_eq_div]
  have hn : (∫ u, Real.exp (ζ * F (z + r * u)) * (u * A (z + r * u))
      ∂gaussianReal 0 1) =
      r * ∫ u, Real.exp (ζ * F (z + r * u)) *
        (B (z + r * u) + ζ * A (z + r * u) * M (z + r * u)) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]
    convert hibp using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext u
    dsimp only [V, DV, U]
    ring
  rw [hn]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint variance/spatial differentiation of the actual scalar
continuation. The covariance differential is left as integrals here;
Gaussian integration by parts then identifies its time generator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticGaussianAverageTwo_hasFDerivAt (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (dF : ∀ z, HasDerivAt F (P.value z) z)
    (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F A.value q.2)
      (magneticGaussianAverageDifferential ζ v F P.value A.value A.first z) (v, z) := by
  obtain ⟨K, hK, bK⟩ := P.bValue
  obtain ⟨L, _, bL⟩ := P.bFirst
  obtain ⟨CA, hCA, bCA⟩ := A.bValue
  obtain ⟨CB, hCB, bCB⟩ := A.bFirst
  let I := Ioo (v / 2) (v + 1)
  let S := (magneticStationaryFamily I F P hF K L bK bL dF).toFieldSmoothFamily
  let α : (ℝ × ℝ) → ℝ → ℝ := fun q u => A.value (q.2 + Real.sqrt q.1 * u)
  let Dα : (ℝ × ℝ) → ℝ → (ℝ × ℝ) →L[ℝ] ℝ := fun q u => pairLinear
    (A.first (q.2 + Real.sqrt q.1 * u) * ((1 / (2 * Real.sqrt q.1)) * u))
    (A.first (q.2 + Real.sqrt q.1 * u))
  let R := 1 / (2 * Real.sqrt (v / 2))
  have hR : 0 ≤ R := by dsimp only [R] <;> positivity
  have hm : 0 < v / 2 := by linarith
  have hbound (q : ℝ × ℝ) (hq : q.1 ∈ I) :
      |1 / (2 * Real.sqrt q.1)| ≤ R := by
    simpa only [abs_one] using abs_div_two_sqrt_le hm hq.1.le 1
  have hdα (q : ℝ × ℝ) (hq : q.1 ∈ I) (u : ℝ) :
      HasFDerivAt (fun r => α r u) (Dα q u) q := by
    have hb (p : ℝ × ℝ) (_ : p.1 ∈ I) :
        HasFDerivAt (fun r : ℝ × ℝ => A.value r.2) (pairLinear 0 (A.first p.2)) p := by
      refine ((A.dValue p.2).hasFDerivAt.comp p hasFDerivAt_snd).congr_fderiv (Eq.symm ?_)
      · apply ContinuousLinearMap.ext
        intro w
        simp [pairLinear, mul_comm]
    simpa only [zero_add, one_mul] using
      affine_gaussian_shift_hasFDerivAt hb 0 1 u hq (by
        dsimp only [I] at hq
        linarith [hq.1])
  have hbα (q : ℝ × ℝ) (_ : q.1 ∈ I) (u : ℝ) : |α q u| ≤ CA * (1 + |u|) := by
    exact (bCA _).trans (le_mul_of_one_le_right hCA (by linarith [abs_nonneg u]))
  have hbDα (q : ℝ × ℝ) (hq : q.1 ∈ I) (u : ℝ) :
      ‖Dα q u‖ ≤ (CB * (R + 1)) * (1 + |u|) ^ 2 := by
    refine (norm_pairLinear_le _ _).trans ?_
    have hf : |A.first (q.2 + Real.sqrt q.1 * u) * ((1 / (2 * Real.sqrt q.1)) * u)| ≤
        CB * R * |u| := by
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (bCB _) (mul_le_mul_of_nonneg_right (hbound q hq) (abs_nonneg u))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hCB).trans_eq (by ring)
    have hg := bCB (q.2 + Real.sqrt q.1 * u)
    have h1 : 1 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
    have h2 : |u| ≤ (1 + |u|) ^ 2 := by nlinarith [sq_nonneg |u|, abs_nonneg u]
    nlinarith [mul_le_mul_of_nonneg_left h1 hCB,
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hCB hR)]
  have hp : (v, z) ∈ I ×ˢ univ := ⟨by dsimp only [I]; constructor <;> linarith, mem_univ z⟩
  have hh := S.affine_average_hasFDerivAt isOpen_Ioo α Dα 0 1 ζ hm
    (fun t ht => by simpa only [zero_add, one_mul] using ht.1.le)
    (fun t ht => by simpa only [zero_add, one_mul] using ht.2.le)
    hCA (mul_nonneg hCB (by linarith : 0 ≤ R + 1))
    (fun q => A.mValue.comp (by fun_prop))
    (fun q => (measurable_pairLinear
      (A.mFirst.comp (by fun_prop) |>.mul (by fun_prop))
      (A.mFirst.comp (by fun_prop))).aestronglyMeasurable)
    hbα hbDα hdα hp.1
  simpa only [α, Dα, S, magneticStationaryFamily, FieldSmoothFamily.affineShift,
    FieldSmoothFamily.affineDifferential, fieldAmplitudeSlope, zero_add, one_mul,
    gaussianTiltAverage, magneticGaussianAverageDifferential] using hh

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGaussianMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrable moments and the scaled Gaussian integration-by-parts identity
used to turn the variance differential of a bounded continuation into its
parabolic generator. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magnetic_tilted_shift_integrable {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {C : ℝ} (bA : ∀ x, |A x| ≤ C) (r ζ z : ℝ) :
    Integrable (fun u => A (z + r * u))
      ((gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  have he := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) (hF.comp (by fun_prop))
    ((hG.add_left z).scale_argument r) ζ
  have : IsProbabilityMeasure ((gaussianReal 0 1).tilted
      (fun u => ζ * F (z + r * u))) := MeasureTheory.isProbabilityMeasure_tilted he
  exact Integrable.of_bound (hA.comp (by fun_prop)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs] using bA (z + r * u))

lemma magnetic_tilted_linear_integrable {F A : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hA : Measurable A)
    {C : ℝ} (bA : ∀ x, |A x| ≤ C) (r ζ z : ℝ) :
    Integrable (fun u => u * A (z + r * u))
      ((gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  have hshift := hF.comp (show Measurable (fun u : ℝ => z + r * u) by fun_prop)
  have hg := (hG.add_left z).scale_argument r
  have he := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hshift hg ζ
  apply (integrable_tilted_iff he _).mpr
  apply field_exp_mul_linear_integrable 1 0 ζ hshift hg
    (measurable_id.mul (hA.comp (by fun_prop)))
  refine ⟨0, C, le_rfl, (abs_nonneg _).trans (bA 0), fun u => ?_⟩
  change |u * A (z + r * u)| ≤ 0 + C * ‖u‖
  rw [abs_mul, Real.norm_eq_abs, zero_add]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (bA (z + r * u)) (abs_nonneg u)

lemma magnetic_tilted_scaled_test_ibp {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hA : Measurable A) (hB : Measurable B)
    {K C D : ℝ} (bM : ∀ x, |M x| ≤ K) (bA : ∀ x, |A x| ≤ C)
    (bB : ∀ x, |B x| ≤ D) (dF : ∀ x, HasDerivAt F (M x) x)
    (dA : ∀ x, HasDerivAt A (B x) x) {r : ℝ} (hr : r ≠ 0) (ζ z : ℝ) :
    (∫ u, A (z + r * u) * ((1 / (2 * r)) * u)
      ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) =
      (1 / 2 : ℝ) * (∫ u, B (z + r * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) +
      ζ / 2 * (∫ u, A (z + r * u) * M (z + r * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))
  have hiB : Integrable (fun u => B (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG hB bB r ζ z
  have hiAM : Integrable (fun u => A (z + r * u) * M (z + r * u)) ν := by
    apply magnetic_tilted_shift_integrable hF hG (hA.mul hM)
      (C := C * K) (r := r) (ζ := ζ) (z := z)
    intro x
    change |A x * M x| ≤ C * K
    rw [abs_mul]
    exact mul_le_mul (bA x) (bM x) (abs_nonneg _) ((abs_nonneg _).trans (bA 0))
  have he : (fun u => A (z + r * u) * ((1 / (2 * r)) * u)) =
      fun u => (1 / (2 * r)) * (u * A (z + r * u)) := by
    funext u
    ring
  rw [he, integral_const_mul]
  rw [magnetic_gaussian_tilted_test_ibp hF hG hM hA hB bM bA bB dF dA r ζ z]
  have he' : (fun u => B (z + r * u) + ζ * A (z + r * u) * M (z + r * u)) =
      fun u => B (z + r * u) + ζ * (A (z + r * u) * M (z + r * u)) := by
    funext u
    ring
  rw [he', integral_add hiB (hiAM.const_mul ζ), integral_const_mul]
  field_simp [hr]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticGaussianCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar-coordinate form of the actual joint Gaussian continuation
differential. All integrability is supplied by bounded finite-spin jets. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticGaussianAverageDifferentialTwo_eq_pair (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (ζ v z : ℝ) :
    magneticGaussianAverageDifferential ζ v F P.value A.value A.first z =
      pairLinear (magneticGaussianTime ζ v F P.value A.value A.first z)
        (magneticGaussianSpace ζ v F P.value A.value A.first z) := by
  let r := Real.sqrt v
  let c := 1 / (2 * r)
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))
  obtain ⟨KM, _, bM⟩ := P.bValue
  obtain ⟨KA, hKA, bA⟩ := A.bValue
  obtain ⟨KB, _, bB⟩ := A.bFirst
  have bAM (y : ℝ) : |A.value y * P.value y| ≤ KA * KM := by
    rw [abs_mul]
    exact mul_le_mul (bA y) (bM y) (abs_nonneg _) hKA
  have iB : Integrable (fun u => A.first (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG A.mFirst bB r ζ z
  have iM : Integrable (fun u => P.value (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG P.mValue bM r ζ z
  have iAM : Integrable (fun u => A.value (z + r * u) * P.value (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG (A.mValue.mul P.mValue) bAM r ζ z
  have linear {a : ℝ → ℝ} (ha : Measurable a) {K : ℝ} (ba : ∀ y, |a y| ≤ K) :
      Integrable (fun u => a (z + r * u) * (c * u)) ν := by
    have hi := (magnetic_tilted_linear_integrable hF hG ha ba r ζ z).const_mul c
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    ring
  have iBt := linear A.mFirst bB
  have iMt := linear P.mValue bM
  have iAMt : Integrable (fun u => A.value (z + r * u) *
      (P.value (z + r * u) * (c * u))) ν := by
    convert linear (A.mValue.mul P.mValue) bAM using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    dsimp only [Pi.mul_apply]
    ring
  exact field_pair_covariance ν ζ (fun u => A.value (z + r * u))
    (fun u => A.first (z + r * u) * (c * u)) (fun u => A.first (z + r * u))
    (fun u => P.value (z + r * u) * (c * u)) (fun u => P.value (z + r * u))
    iBt iB iMt iM iAMt iAM

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact heat generator of the scalar continuation. Integration by
parts removes the apparent inverse square-root singularity from the
positive-variance differential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticGaussianTimeTwo_eq_generator (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    magneticGaussianTime ζ v F P.value A.value A.first z =
      magneticGaussianGenerator ζ v F P.value P.first A.value A.first A.second z := by
  let r := Real.sqrt v
  let ν := (gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))
  obtain ⟨KM, _, bM⟩ := P.bValue
  obtain ⟨KQ, _, bQ⟩ := P.bFirst
  obtain ⟨KA, hKA, bA⟩ := A.bValue
  obtain ⟨KB, hKB, bB⟩ := A.bFirst
  obtain ⟨KC, _, bC⟩ := A.bSecond
  have hr : r ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have bAM (y : ℝ) : |A.value y * P.value y| ≤ KA * KM := by
    rw [abs_mul]
    exact mul_le_mul (bA y) (bM y) (abs_nonneg _) hKA
  have bBM (y : ℝ) : |A.first y * P.value y| ≤ KB * KM := by
    rw [abs_mul]
    exact mul_le_mul (bB y) (bM y) (abs_nonneg _) hKB
  have bAQ (y : ℝ) : |A.value y * P.first y| ≤ KA * KQ := by
    rw [abs_mul]
    exact mul_le_mul (bA y) (bQ y) (abs_nonneg _) hKA
  have bdAM (y : ℝ) : |A.first y * P.value y + A.value y * P.first y| ≤
      KB * KM + KA * KQ := (abs_add_le _ _).trans (add_le_add (bBM y) (bAQ y))
  have iBM : Integrable (fun u => A.first (z + r * u) * P.value (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG (A.mFirst.mul P.mValue) bBM r ζ z
  have iAQ : Integrable (fun u => A.value (z + r * u) * P.first (z + r * u)) ν :=
    magnetic_tilted_shift_integrable hF hG (A.mValue.mul P.mFirst) bAQ r ζ z
  have hB := magnetic_tilted_scaled_test_ibp hF hG P.mValue A.mFirst A.mSecond
    bM bB bC dF A.dFirst hr ζ z
  have hM := magnetic_tilted_scaled_test_ibp hF hG P.mValue P.mValue P.mFirst
    bM bM bQ dF P.dValue hr ζ z
  have hAM := magnetic_tilted_scaled_test_ibp hF hG P.mValue
    (A.mValue.mul P.mValue) ((A.mFirst.mul P.mValue).add (A.mValue.mul P.mFirst))
    bM bAM bdAM dF (fun y => (A.dValue y).mul (P.dValue y)) hr ζ z
  dsimp only [Pi.mul_apply, Pi.add_apply] at hAM
  have hAMleft : (∫ u, A.value (z + r * u) *
      (P.value (z + r * u) * ((1 / (2 * r)) * u)) ∂ν) =
      (∫ u, (A.value (z + r * u) * P.value (z + r * u)) *
        ((1 / (2 * r)) * u) ∂ν) := by
    congr 1
    funext u
    ring
  have hAMright : (∫ u, (A.value (z + r * u) * P.value (z + r * u)) *
      P.value (z + r * u) ∂ν) =
      ∫ u, A.value (z + r * u) * (P.value (z + r * u)) ^ 2 ∂ν := by
    congr 1
    funext u
    ring
  have hMright : (∫ u, P.value (z + r * u) * P.value (z + r * u) ∂ν) =
      ∫ u, (P.value (z + r * u)) ^ 2 ∂ν := by
    congr 1
    funext u
    ring
  change magneticGaussianTime ζ v F P.value A.value A.first z = _
  dsimp only [magneticGaussianTime]
  rw [hB, hAMleft, hAM, hM, hAMright, hMright, integral_add iBM iAQ]
  dsimp only [magneticGaussianGenerator, gaussianTiltAverage]
  ring

lemma magneticContinuation_secondTwo_generator (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    magneticContinuationSecond ζ v F P.value P.first A.value A.first A.second z / 2 +
        ζ * fieldSpinTransition ζ v F P.value z *
          fieldTiltSpatial ζ v F P.value A.value A.first z =
      (let T := fun f => fieldSpinTransition ζ v F f z
       T A.second / 2 + ζ * T (fun y => A.first y * P.value y) +
         ζ / 2 * (T (fun y => A.value y * P.first y) - T A.value * T P.first) +
         ζ ^ 2 / 2 * (T (fun y => A.value y * (P.value y) ^ 2) -
           T A.value * T (fun y => (P.value y) ^ 2))) := by
  obtain ⟨KM, _, bM⟩ := P.bValue
  obtain ⟨KQ, _, bQ⟩ := P.bFirst
  obtain ⟨KA, hKA, bA⟩ := A.bValue
  obtain ⟨KB, hKB, bB⟩ := A.bFirst
  have bBM (y : ℝ) : |A.first y * P.value y| ≤ KB * KM := by
    rw [abs_mul]
    exact mul_le_mul (bB y) (bM y) (abs_nonneg _) hKB
  have bAQ (y : ℝ) : |A.value y * P.first y| ≤ KA * KQ := by
    rw [abs_mul]
    exact mul_le_mul (bA y) (bQ y) (abs_nonneg _) hKA
  have hadd := fieldSpinTransition_add ζ v hF hG (A.mFirst.mul P.mValue)
    (A.mValue.mul P.mFirst) bBM bAQ z
  change fieldSpinTransition ζ v F (fun y => A.first y * P.value y + A.value y * P.first y) z =
    fieldSpinTransition ζ v F (fun y => A.first y * P.value y) z +
      fieldSpinTransition ζ v F (fun y => A.value y * P.first y) z at hadd
  have hassoc : (fun y => (A.value y * P.value y) * P.value y) =
      (fun y => A.value y * (P.value y) ^ 2) := by
    funext y
    ring
  have hsquare : (fun y => P.value y * P.value y) = (fun y => (P.value y) ^ 2) := by
    funext y
    ring
  dsimp only [magneticContinuationSecond, fieldTiltSpatial]
  rw [hadd, hassoc, hsquare]
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationPDE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual bounded continuation solves the scalar heat equation with
the nonlinear backward-field drift. The first coordinate is the amount
of Gaussian variance already applied; reversing it gives the backward
time convention in the manuscript. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticGaussianSpaceTwo_eq (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (ζ v z : ℝ) :
    magneticGaussianSpace ζ v F P.value A.value A.first z =
      fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z := by
  unfold magneticGaussianSpace fieldTiltSpatial
  rw [field_gaussianTiltAverage_eq_transition v ζ hF A.mFirst,
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => A.value y * P.value y)
      hF (A.mValue.mul P.mValue),
    field_gaussianTiltAverage_eq_transition v ζ hF A.mValue,
    field_gaussianTiltAverage_eq_transition v ζ hF P.mValue]

lemma magneticGaussianGeneratorTwo_eq (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (ζ v z : ℝ) :
    magneticGaussianGenerator ζ v F P.value P.first A.value A.first A.second z =
      magneticContinuationSecond ζ (Real.toNNReal v) F P.value P.first
          A.value A.first A.second z / 2 +
        ζ * fieldSpinTransition ζ (Real.toNNReal v) F P.value z *
          fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z := by
  rw [magneticContinuation_secondTwo_generator P A F hF hG]
  dsimp only [magneticGaussianGenerator]
  rw [field_gaussianTiltAverage_eq_transition v ζ hF A.mSecond,
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => A.first y * P.value y)
      hF (A.mFirst.mul P.mValue),
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => A.value y * P.first y)
      hF (A.mValue.mul P.mFirst),
    field_gaussianTiltAverage_eq_transition v ζ hF A.mValue,
    field_gaussianTiltAverage_eq_transition v ζ hF P.mFirst,
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => A.value y * (P.value y) ^ 2)
      hF (A.mValue.mul (P.mValue.pow_const 2)),
    field_gaussianTiltAverage_eq_transition v ζ (a := fun y => (P.value y) ^ 2)
      hF (P.mValue.pow_const 2)]

theorem magneticGaussianAverageTwo_hasFDerivAt_generator (P : MagneticContinuationJet) (A : MagneticContinuationTwoJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F A.value q.2)
      (pairLinear
        (magneticContinuationSecond ζ (Real.toNNReal v) F P.value P.first
            A.value A.first A.second z / 2 +
          ζ * fieldSpinTransition ζ (Real.toNNReal v) F P.value z *
            fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z)
        (fieldTiltSpatial ζ (Real.toNNReal v) F P.value A.value A.first z)) (v, z) := by
  have hd := magneticGaussianAverageTwo_hasFDerivAt P A F hF dF ζ hv z
  rw [magneticGaussianAverageDifferentialTwo_eq_pair P A F hF hG,
    magneticGaussianTimeTwo_eq_generator P A F hF hG dF ζ hv,
    magneticGaussianGeneratorTwo_eq P A F hF hG,
    magneticGaussianSpaceTwo_eq P A F hF] at hd
  exact hd

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

theorem magneticHeatMean_hasFDerivAt (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    HasFDerivAt (magneticHeatMean P F ζ)
      (pairLinear (J.second z / 2 + ζ * J.value z * J.first z)
        (J.first z)) (v, z) := by
  exact magneticGaussianAverageTwo_hasFDerivAt_generator P P.toTwoJet F hF hG dF ζ hv z

theorem magneticHeatContinuation_hasFDerivAt (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    let K := A.transition P ζ (Real.toNNReal v) F hF hG dF
    HasFDerivAt (magneticHeatMean A F ζ)
      (pairLinear (K.second z / 2 + ζ * J.value z * K.first z)
        (K.first z)) (v, z) := by
  exact magneticGaussianAverageTwo_hasFDerivAt_generator P A.toTwoJet F hF hG dF ζ hv z

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

lemma magneticScalarSlabBias_continuousAt_variance (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ}
    (hζ : 0 ≤ ζ) (hs : |s| < 1) (hv : 0 < v) :
    ContinuousAt (fun t => magneticScalarSlabBias L ζ t s) v := by
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  let P := magneticLogCoshMeanJet L hL
  have heq : (fun q : ℝ × ℝ => magneticScalarSlabMean L ζ q.1 q.2) =
      magneticHeatMean P (fieldScalarValue L (fun x => Real.log (Real.cosh x))) ζ := by
    funext q
    exact magneticScalarSlabMean_eq L hL ζ q.1 q.2
  apply parametric_bias_continuousAt (A := fun q => magneticScalarSlabMean L ζ q.1 q.2)
  · intro z
    have hc := (magneticHeatMean_hasFDerivAt P _ hF.1 hF.2
      (hasDerivAt_fieldScalarLogCosh L hL) ζ hv z).continuousAt
    rw [← heq] at hc
    have hp : ContinuousAt (fun t : ℝ => (t, z)) v :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp' (f := fun t : ℝ => (t, z)) (x := v) hc hp
  · exact Eventually.of_forall fun t => magneticScalarSlabMean_strictMono L hL hζ t
  · exact Eventually.of_forall fun t => magneticScalarSlabMean_bias L hL hζ hs t

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldGaussianTerminal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At exponent one the Gaussian log-cosh operator adds only a constant.
This is the terminal endpoint of the adjacent-variance comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldGaussian_integral_cosh (v : ℝ≥0) (z : ℝ) :
    (∫ y, Real.cosh y ∂gaussianReal z v) = Real.exp (v / 2) * Real.cosh z := by
  have hp : (∫ y, Real.exp y ∂gaussianReal z v) = Real.exp (z + v / 2) := by
    simpa only [mgf, one_mul, mul_one, one_pow] using
      congrFun (mgf_fun_id_gaussianReal (μ := z) (v := v)) 1
  have hn : (∫ y, Real.exp (-y) ∂gaussianReal z v) = Real.exp (-z + v / 2) := by
    simpa only [mgf, neg_one_mul, mul_neg_one, neg_one_sq, mul_one] using
      congrFun (mgf_fun_id_gaussianReal (μ := z) (v := v)) (-1)
  have hip : Integrable (fun y => Real.exp y) (gaussianReal z v) := by
    simpa only [one_mul] using integrable_exp_mul_gaussianReal (μ := z) (v := v) 1
  have hin : Integrable (fun y => Real.exp (-y)) (gaussianReal z v) := by
    simpa only [neg_one_mul] using integrable_exp_mul_gaussianReal (μ := z) (v := v) (-1)
  simp only [Real.cosh_eq, integral_div, integral_add hip hin, hp, hn, Real.exp_add]
  ring

lemma gaussianOperator_one_logCosh (v : ℝ≥0) (z : ℝ) :
    gaussianOperator 1 v (fun y => Real.log (Real.cosh y)) z =
      v / 2 + Real.log (Real.cosh z) := by
  rw [gaussianOperator_eq_gaussian_exp_integral (by norm_num) v measurable_logCosh z]
  simp only [one_mul, inv_one]
  have he : (fun y : ℝ => Real.exp (Real.log (Real.cosh y))) = Real.cosh := by
    funext y
    exact Real.exp_log (Real.cosh_pos y)
  rw [he, fieldGaussian_integral_cosh, Real.log_mul (Real.exp_ne_zero _)
    (Real.cosh_pos z).ne', Real.log_exp]

lemma fieldSpinTransition_one_tanh (v : ℝ≥0) (z : ℝ) :
    fieldSpinTransition 1 v (fun y => Real.log (Real.cosh y)) Real.tanh z =
      Real.tanh z := by
  have hnil : ∀ av ∈ ([] : List (ℝ × ℝ≥0)), 0 < av.1 := by simp
  have hd := magneticScalarSlab_value_hasDerivAt [] hnil 1 (v : ℝ) z
  have he : gaussianOperator 1 v (fun y => Real.log (Real.cosh y)) =
      (fun y => v / 2 + Real.log (Real.cosh y)) :=
    funext (gaussianOperator_one_logCosh v)
  have ht : HasDerivAt (fun y => v / 2 + Real.log (Real.cosh y)) (Real.tanh z) z := by
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      ((Real.hasDerivAt_cosh z).log (Real.cosh_pos z).ne').const_add ((v : ℝ) / 2)
  change HasDerivAt (gaussianOperator 1 (Real.toNNReal (v : ℝ))
    (fun y => Real.log (Real.cosh y)))
    (fieldSpinTransition 1 (Real.toNNReal (v : ℝ))
      (fun y => Real.log (Real.cosh y)) Real.tanh z) z at hd
  rw [Real.toNNReal_coe, he] at hd
  exact hd.unique ht

lemma fieldSpinTransition_const_add (ζ : ℝ) (v : ℝ≥0) (F a : ℝ → ℝ)
    (c z : ℝ) :
    fieldSpinTransition ζ v (fun y => c + F y) a z = fieldSpinTransition ζ v F a z := by
  unfold fieldSpinTransition
  simp only [integral_tilted_eq_div, mul_add, Real.exp_add, mul_assoc,
    integral_const_mul]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightUpdate
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the finite covariance charts with literal updates
of a field height. The formula is defined without choosing proofs of the
order constraints; whenever the updated heights are admissible it is the
original `fieldValue` of that field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

private lemma list_set_two {α : Type*} (L : List α) (i : ℕ)
    (A B : α) (hi : i + 1 < L.length) :
    (L.set i A).set (i + 1) B = L.take i ++ A :: B :: L.drop (i + 2) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    cases i with
    | zero =>
      cases L with
      | nil => simp at hi
      | cons y L => rfl
    | succ i =>
      have hh : i + 1 < L.length := by simp only [List.length_cons] at hi; omega
      simpa only [List.set_cons_succ, List.take_succ_cons, List.drop_succ_cons,
        List.cons_append, Nat.succ_eq_add_one, Nat.add_assoc] using
        congrArg (List.cons x) (ih i hh)

lemma updated_increments_interior (h : FieldStep) (i : Fin h.depth) (t : ℝ) :
    (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height i.castSucc (h.height i.castSucc + t)) j))) =
    fieldAdjacentIncrements ((fieldAllIncrements h).take i.val)
      ((fieldAllIncrements h).drop (i.val + 2))
      (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
      (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 t := by
  classical
  let L := fieldAllIncrements h
  let A : ℝ × ℝ≥0 := ((fieldIncrement h i.castSucc).1,
    Real.toNNReal ((fieldIncrement h i.castSucc).2 + t))
  let B : ℝ × ℝ≥0 := ((fieldIncrement h i.succ).1,
    Real.toNNReal ((fieldIncrement h i.succ).2 - t))
  have he : (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height i.castSucc (h.height i.castSucc + t)) j))) =
      (L.set i.val A).set (i.val + 1) B := by
    apply List.ext_getElem
    · simp [L]
    · intro j hj hj'
      have hjn : j < h.depth + 1 := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_set, fieldHeightIncrement_update,
        Fin.ext_iff, Fin.val_castSucc, fieldHeightIncrement_eq]
      by_cases he : j = i.val
      · subst j
        simp [A, fieldIncrement]
        constructor <;> rfl
      · by_cases hs : j = i.val + 1
        · subst j
          simp [B, fieldIncrement, sub_eq_add_neg]
          constructor <;> rfl
        · have he' : i.val ≠ j := Ne.symm he
          have hs' : i.val + 1 ≠ j := Ne.symm hs
          simp only [he, hs, he', hs', ite_false, if_false, add_zero]
          change (h.cut (⟨j, hjn⟩ : Fin (h.depth + 1)).castSucc,
            Real.toNNReal (fieldHeightIncrement h.height ⟨j, hjn⟩)) = L[j]'(by simpa [L] using hjn)
          rw [show L[j]'(by simpa [L] using hjn) = ((fieldIncrement h ⟨j, hjn⟩).1,
            NNReal.mk (fieldIncrement h ⟨j, hjn⟩).2 (fieldIncrement_nonneg h ⟨j, hjn⟩)) from
              List.getElem_ofFn _]
          apply Prod.ext
          · rfl
          · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg h ⟨j, hjn⟩)
  rw [he, list_set_two L i.val A B (by simp only [L, fieldAllIncrements_length]; omega)]
  rfl

lemma updated_increments_final (h : FieldStep) (t : ℝ) :
    (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) j))) =
    fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
      (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 t := by
  classical
  let L := fieldAllIncrements h
  let A : ℝ × ℝ≥0 := ((fieldIncrement h (Fin.last h.depth)).1,
    Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))
  have he : (List.ofFn fun j : Fin (h.depth + 1) => (h.cut j.castSucc,
      Real.toNNReal (fieldHeightIncrement
        (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) j))) =
      L.set h.depth A := by
    apply List.ext_getElem
    · simp [L]
    · intro j hj hj'
      have hjn : j < h.depth + 1 := by simpa using hj
      have hn : j ≠ h.depth + 1 := by omega
      simp only [List.getElem_ofFn, List.getElem_set, fieldHeightIncrement_update,
        Fin.ext_iff, Fin.val_last, hn, ite_false, if_false, fieldHeightIncrement_eq]
      by_cases he : j = h.depth
      · subst j
        simp [A, fieldIncrement]
        constructor <;> rfl
      · have he' : h.depth ≠ j := Ne.symm he
        simp only [he, he', ite_false, if_false, add_zero]
        change (h.cut (⟨j, hjn⟩ : Fin (h.depth + 1)).castSucc,
          Real.toNNReal (fieldHeightIncrement h.height ⟨j, hjn⟩)) = L[j]'(by simpa [L] using hjn)
        rw [show L[j]'(by simpa [L] using hjn) = ((fieldIncrement h ⟨j, hjn⟩).1,
          NNReal.mk (fieldIncrement h ⟨j, hjn⟩).2 (fieldIncrement_nonneg h ⟨j, hjn⟩)) from
            List.getElem_ofFn _]
        apply Prod.ext
        · rfl
        · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg h ⟨j, hjn⟩)
  rw [he, List.set_eq_take_append_cons_drop]
  simp only [L, fieldAllIncrements_length, Nat.lt_succ_self, ite_true, if_true]
  rw [List.drop_eq_nil_of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict finite field-height cone and its original FieldStep
representatives. Positive increments give every height and order constraint. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma continuous_fieldHeightIncrement {n : ℕ} (j : Fin (n + 1)) :
    Continuous (fun r : Fin (n + 1) → ℝ => fieldHeightIncrement r j) := by
  unfold fieldHeightIncrement
  split_ifs <;> fun_prop

lemma isOpen_fieldStrictHeightCone (n : ℕ) : IsOpen (fieldStrictHeightCone n) := by
  simpa only [fieldStrictHeightCone, ofPred_forall] using
    isOpen_iInter_of_finite (fun j : Fin (n + 1) =>
      isOpen_lt continuous_const (continuous_fieldHeightIncrement j))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldHeightLists
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact transition-list laws for a literal height update. -/

noncomputable section
open IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldAllIncrements_withHeights (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldAllIncrements (fieldWithHeights h r hr0 hrmono) =
      List.ofFn (fun j : Fin (h.depth + 1) =>
        (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j))) := by
  unfold fieldAllIncrements
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · rfl
  · exact (Real.toNNReal_of_nonneg (fieldIncrement_nonneg (fieldWithHeights h r hr0 hrmono) j)).symm

lemma fieldAllIncrements_update_interior (h : FieldStep) (j : Fin h.depth) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) =
      fieldAdjacentIncrements ((fieldAllIncrements h).take j.val)
        ((fieldAllIncrements h).drop (j.val + 2))
        (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
        (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 t := by
  rw [fieldStepOfStrictHeights, fieldAllIncrements_withHeights]
  exact updated_increments_interior h j t

lemma fieldAllIncrements_update_final (h : FieldStep) (t : ℝ)
    (ht : Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) ∈
      fieldStrictHeightCone h.depth) :
    fieldAllIncrements (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) ht) =
      fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
        (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 t := by
  rw [fieldStepOfStrictHeights, fieldAllIncrements_withHeights]
  exact updated_increments_final h t

lemma fieldAdjacentIncrements_root (P S : List (ℝ × ℝ≥0))
    (root : ℝ≥0) (a b ζ η t : ℝ) :
    fieldAdjacentIncrements ((0, root) :: P) S a b ζ η t =
      (0, root) :: (P ++ (ζ, Real.toNNReal (a + t)) :: (η, Real.toNNReal (b - t)) :: S) := rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldTerminalOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Appending an exponent-one terminal increment changes the scalar
value by its Gaussian constant and preserves every earlier spin moment. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

private lemma squares_cons_succ (av : ℝ × ℝ≥0) (L : List (ℝ × ℝ≥0))
    (F a : ℝ → ℝ) (i : Fin (L.length + 1)) :
    fieldScalarSquares (av :: L) F a i.succ =
      fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSquares L F a i) := rfl

lemma fieldScalarValue_const_add (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (c : ℝ) :
    fieldScalarValue L (fun z => c + F z) = fun z => c + fieldScalarValue L F z := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hv := fieldScalarValue_regular L ht hF hG
    change gaussianOperator av.1 av.2 (fieldScalarValue L (fun z => c + F z)) = _
    rw [ih ht]
    funext z
    exact gaussianOperator_const_add hv.1 hv.2 c av.1 av.2 z

lemma fieldScalarValue_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0) :
    fieldScalarValue (L ++ [(1, v)]) (fun z => Real.log (Real.cosh z)) =
      fun z => v / 2 + fieldScalarValue L (fun z => Real.log (Real.cosh z)) z := by
  have he : fieldScalarValue (L ++ [(1, v)]) (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue L (fun z => v / 2 + Real.log (Real.cosh z)) := by
    simp only [fieldScalarValue, List.foldr_append, List.foldr_cons, List.foldr_nil]
    congr 1
    funext z
    exact gaussianOperator_one_logCosh v z
  rw [he]
  exact fieldScalarValue_const_add L hL measurable_logCosh logCosh_linearGrowth _

lemma fieldScalarMean_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0) :
    fieldScalarMean (L ++ [(1, v)]) (fun z => Real.log (Real.cosh z)) Real.tanh =
      fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh := by
  induction L with
  | nil =>
    funext z
    exact fieldSpinTransition_one_tanh v z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    simp only [List.cons_append, fieldScalarMean]
    rw [fieldScalarValue_terminal_one L ht v, ih ht]
    funext z
    exact fieldSpinTransition_const_add av.1 av.2 _ _ (v / 2) z

lemma fieldScalarSquares_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0) (i : ℕ) (hi : i ≤ L.length) :
    fieldScalarSquares (L ++ [(1, v)]) (fun z => Real.log (Real.cosh z)) Real.tanh
      ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩ =
    fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh
      ⟨i, by omega⟩ := by
  induction L generalizing i with
  | nil =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    funext z
    change (fieldSpinTransition 1 v (fun z => Real.log (Real.cosh z)) Real.tanh z) ^ 2 =
      (Real.tanh z) ^ 2
    rw [fieldSpinTransition_one_tanh]
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    cases i with
    | zero =>
      funext z
      change (fieldScalarMean ((av :: L) ++ [(1, v)]) (fun z => Real.log (Real.cosh z))
        Real.tanh z) ^ 2 = (fieldScalarMean (av :: L) (fun z => Real.log (Real.cosh z))
        Real.tanh z) ^ 2
      rw [fieldScalarMean_terminal_one (av :: L) hL v]
    | succ i =>
      have hiL : i ≤ L.length := Nat.le_of_succ_le_succ hi
      simp only [List.cons_append]
      have hleft : (⟨i + 1, by simp only [List.length_cons, List.length_append]; omega⟩ :
          Fin ((av :: (L ++ [(1, v)])).length + 1)) =
          (⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩ :
            Fin ((L ++ [(1, v)]).length + 1)).succ := rfl
      have hright : (⟨i + 1, by simp only [List.length_cons]; omega⟩ : Fin ((av :: L).length + 1)) =
          (⟨i, by omega⟩ : Fin (L.length + 1)).succ := rfl
      rw [hleft, hright, squares_cons_succ, squares_cons_succ]
      rw [fieldScalarValue_terminal_one L ht v, ih ht i hiL]
      funext z
      exact fieldSpinTransition_const_add av.1 av.2 _ _ (v / 2) z

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeatInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Gaussian continuations in the inverse mean coordinate. The
root equation, rather than a derivative of the inverse, is the premise;
the inverse derivative and drift cancellation are proved here. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticHeatInverse_continuation_hasDerivAt (P A : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v s : ℝ} (hv : 0 < v)
    {b : ℝ → ℝ} (hb : ContinuousAt b v)
    (he : ∀ᶠ t in 𝓝 v, magneticHeatMean P F ζ (t, b t) = s)
    (hq : (P.transition P ζ (Real.toNNReal v) F hF hG dF).first (b v) ≠ 0) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    let K := A.transition P ζ (Real.toNNReal v) F hF hG dF
    HasDerivAt (fun t => magneticHeatMean A F ζ (t, b t))
      ((J.first (b v)) ^ 2 / 2 *
        (K.second (b v) / (J.first (b v)) ^ 2 -
          K.first (b v) * J.second (b v) / (J.first (b v)) ^ 3)) v := by
  have hd := inverse_mean_curvature_variation hb hq
    (magneticHeatMean_hasFDerivAt P F hF hG dF ζ hv (b v)) he
    (magneticHeatContinuation_hasFDerivAt P A F hF hG dF ζ hv (b v))
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hq]
  ring

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

lemma closedMagneticScalarCurvature_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 ≤ ζ) (q : ℝ × ℝ) :
    0 ≤ closedMagneticScalarCurvature L hL ζ q := by
  unfold closedMagneticScalarCurvature
  split_ifs
  · exact (magneticScalarInverseCurvature_pos L hL hζ q.1 q.2).le
  · exact le_rfl

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual bounded observables continued in the inverse mean coordinate.
Both spatial derivatives and the drift cancellation follow from the finite
Gaussian field, with no inverse-regularity assumptions left over. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabContinuation_eq_jet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ v s : ℝ) :
    magneticScalarSlabContinuation L A ζ v s =
      (magneticScalarSlabContinuationJet L hL A ζ v).value (magneticScalarSlabBias L ζ v s) := by
  exact magneticHeatMean_eq A _
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1 ζ _

lemma magneticScalarSlabContinuation_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabContinuation L A ζ v)
      (magneticScalarSlabContinuationSlope L hL A ζ v s) s := by
  have he : magneticScalarSlabContinuation L A ζ v = fun u =>
      (magneticScalarSlabContinuationJet L hL A ζ v).value
        (magneticScalarSlabBias L ζ v u) :=
    funext (magneticScalarSlabContinuation_eq_jet L hL A ζ v)
  rw [he]
  exact inverse_mean_pullback_derivative (magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v)
    ((magneticScalarSlabContinuationJet L hL A ζ v).dValue _)

lemma magneticScalarSlabContinuationSlope_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (magneticScalarSlabContinuationSlope L hL A ζ v)
      (magneticScalarSlabContinuationSecond L hL A ζ v s) s := by
  let J := magneticScalarSlabJet L hL ζ v
  let K := magneticScalarSlabContinuationJet L hL A ζ v
  let b := magneticScalarSlabBias L ζ v s
  have hd := inverse_mean_pullback_quotient
    (magneticScalarSlabJet_curvature_pos L hL hζ v b).ne'
    (magneticScalarSlabBias_hasDerivAt_jet L hL hζ hs v) rfl rfl
    (K.dFirst b) (J.dFirst b)
  exact hd

lemma magneticScalarSlabContinuation_second_deriv (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    deriv (deriv (magneticScalarSlabContinuation L A ζ v)) s =
      magneticScalarSlabContinuationSecond L hL A ζ v s := by
  apply HasDerivAt.deriv
  apply (magneticScalarSlabContinuationSlope_hasDerivAt L hL A hζ hs v).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact (magneticScalarSlabContinuation_hasDerivAt_spin L hL A hζ (abs_lt.mpr ht) v).deriv

theorem magneticScalarSlabContinuation_PDE (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s v : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (hv : 0 < v) :
    HasDerivAt (fun t => magneticScalarSlabContinuation L A ζ t s)
      ((magneticScalarInverseCurvature L hL ζ v s) ^ 2 / 2 *
        deriv (deriv (magneticScalarSlabContinuation L A ζ v)) s) v := by
  rw [magneticScalarSlabContinuation_second_deriv L hL A hζ hs v,
    magneticScalarInverseCurvature_eq_jet]
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  apply magneticHeatInverse_continuation_hasDerivAt (s := s)
    (magneticLogCoshMeanJet L hL) A _ hF.1 hF.2
    (hasDerivAt_fieldScalarLogCosh L hL) ζ hv
    (magneticScalarSlabBias_continuousAt_variance L hL hζ hs hv)
  · exact Eventually.of_forall fun t => by
      rw [← magneticScalarSlabMean_eq L hL]
      exact magneticScalarSlabMean_bias L hL hζ hs t
  · exact (magneticScalarSlabJet_curvature_pos L hL hζ v _).ne'

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSlabInitial
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero-variance data for the inverse-coordinate slab equations.
The continued square starts at s², and the final tanh curvature at 1-s². -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticScalarSlabMean_zero (L : List (ℝ × ℝ≥0)) (ζ z : ℝ) :
    magneticScalarSlabMean L ζ 0 z =
      fieldScalarMean L (fun x => Real.log (Real.cosh x)) Real.tanh z := by
  simp only [magneticScalarSlabMean, Real.toNNReal_zero, fieldSpinTransition_zero_variance]

lemma magneticScalarSlabBias_zero (L : List (ℝ × ℝ≥0)) (ζ η s : ℝ) :
    magneticScalarSlabBias L ζ 0 s = magneticScalarSlabBias L η 0 s := by
  unfold magneticScalarSlabBias
  apply congrArg (fun f : ℝ → ℝ => Function.invFun f s)
  funext z
  rw [magneticScalarSlabMean_zero, magneticScalarSlabMean_zero]

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

lemma closedMagneticScalarCurvature_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ η s : ℝ) :
    closedMagneticScalarCurvature L hL ζ (0, s) =
      closedMagneticScalarCurvature L hL η (0, s) := by
  by_cases hs : |s| < 1
  · simp only [closedMagneticScalarCurvature, hs, ite_true, if_true, magneticScalarInverseCurvature_eq,
      Real.toNNReal_zero, fieldCurvatureTransform, fieldSpinTransition_zero_variance,
      sub_self, mul_zero, add_zero]
    rw [magneticScalarSlabBias_zero L ζ η s]
  · simp only [closedMagneticScalarCurvature, hs, ite_false, if_false]

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

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite square continuation on the closed spin interval. Its two
endpoint values are one, and its time derivatives there vanish. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabContinuation_bounds (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    magneticScalarSlabContinuation L A ζ v s ∈ Icc (s ^ 2) 1 := by
  have hb := magneticScalarSlabContinuation_sandwich L hL A hA ζ v (magneticScalarSlabBias L ζ v s)
  have hr := magneticScalarSlabMean_bias L hL hζ hs v
  change (magneticScalarSlabJet L hL ζ v).value (magneticScalarSlabBias L ζ v s) = s at hr
  rw [hr] at hb
  rwa [magneticScalarSlabContinuation_eq_jet L hL A ζ v s]

lemma magneticScalarSlabContinuation_continuousAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ : ℝ} (hζ : 0 ≤ ζ) {p : ℝ × ℝ} (hp : |p.2| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => magneticScalarSlabContinuation L A ζ q.1 q.2) p := by
  let F := fieldScalarValue L (fun y => Real.log (Real.cosh y))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hcF : Continuous F := continuous_iff_continuousAt.mpr fun z =>
    (hasDerivAt_fieldScalarLogCosh L hL z).continuousAt
  have hc := (continuous_magneticHeatMean A F hcF hF.2 ζ).continuousAt
    (x := (p.1, magneticScalarSlabBias L ζ p.1 p.2))
  have hb := magneticScalarSlabBias_continuousAt_joint L hL (v := p.1) hζ hp
  exact hc.comp' (f := fun q : ℝ × ℝ => (q.1, magneticScalarSlabBias L ζ q.1 q.2))
    (x := p) (continuousAt_fst.prodMk hb)

lemma closedMagneticContinuation_bounds (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (p : ℝ × ℝ) (hp : p.2 ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation L A ζ p ∈ Icc (p.2 ^ 2) 1 := by
  by_cases hs : |p.2| < 1
  · simpa only [closedMagneticContinuation, hs, ite_true, if_true] using
      magneticScalarSlabContinuation_bounds L hL A hA hζ hs p.1
  · have hsq : p.2 ^ 2 ≤ 1 := by nlinarith [hp.1, hp.2]
    simpa only [closedMagneticContinuation, hs, ite_false, if_false, Set.mem_Icc, le_refl, and_true] using hsq

lemma continuousOn_closedMagneticContinuation (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    (hA : ∀ z, ((magneticLogCoshMeanJet L hL).value z) ^ 2 ≤ A.value z ∧ A.value z ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) :
    ContinuousOn (closedMagneticContinuation L A ζ) (univ ×ˢ Icc (-1 : ℝ) 1) := by
  intro p hp
  by_cases hs : |p.2| < 1
  · have he : closedMagneticContinuation L A ζ =ᶠ[𝓝 p]
        (fun q : ℝ × ℝ => magneticScalarSlabContinuation L A ζ q.1 q.2) := by
      filter_upwards [(isOpen_lt continuous_snd.abs continuous_const).mem_nhds hs] with q hq
      exact ite_eq_left hq
    exact ((magneticScalarSlabContinuation_continuousAt L hL A hζ hs).congr_of_eventuallyEq he).continuousWithinAt
  · have hps : |p.2| = 1 := le_antisymm (abs_le.mpr hp.2) (le_of_not_gt hs)
    have hps2 : p.2 ^ 2 = 1 := by nlinarith [sq_abs p.2]
    change Tendsto (closedMagneticContinuation L A ζ) (𝓝[univ ×ˢ Icc (-1 : ℝ) 1] p) (𝓝 _)
    rw [show closedMagneticContinuation L A ζ p = 1 from ite_eq_right hs]
    have hlo : Tendsto (fun q : ℝ × ℝ => q.2 ^ 2)
        (𝓝[univ ×ˢ Icc (-1 : ℝ) 1] p) (𝓝 (1 : ℝ)) := by
      have hc : ContinuousWithinAt (fun q : ℝ × ℝ => q.2 ^ 2)
          (univ ×ˢ Icc (-1 : ℝ) 1) p := by fun_prop
      simpa only [ContinuousWithinAt, hps2] using hc
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (closedMagneticContinuation_bounds L hL A hA hζ q hq.2).1
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (closedMagneticContinuation_bounds L hL A hA hζ q hq.2).2

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

lemma closedMagneticContinuation_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticContinuation L A ζ (v, u))
      (closedMagneticContinuationSlope L hL A ζ (v, s)) s := by
  have he : (fun u => closedMagneticContinuation L A ζ (v, u)) =ᶠ[𝓝 s]
      magneticScalarSlabContinuation L A ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticContinuationSlope, hs, ite_true, if_true] using
    (magneticScalarSlabContinuation_hasDerivAt_spin L hL A hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticContinuationSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticContinuationSlope L hL A ζ (v, u))
      (closedMagneticContinuationSecond L hL A ζ (v, s)) s := by
  have he : (fun u => closedMagneticContinuationSlope L hL A ζ (v, u)) =ᶠ[𝓝 s]
      magneticScalarSlabContinuationSlope L hL A ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticContinuationSecond, hs, ite_true, if_true] using
    (magneticScalarSlabContinuationSlope_hasDerivAt L hL A hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticContinuation_hasDerivAt_time (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ v : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (s : ℝ) :
    HasDerivAt (fun t => closedMagneticContinuation L A ζ (t, s))
      (closedMagneticContinuationTime L hL A ζ (v, s)) v := by
  by_cases hs : |s| < 1
  · have hd := magneticScalarSlabContinuation_PDE L hL A hζ hs hv
    rw [magneticScalarSlabContinuation_second_deriv L hL A hζ hs v] at hd
    simpa only [closedMagneticContinuation, closedMagneticContinuationTime,
      closedMagneticScalarCurvature, closedMagneticContinuationSecond, hs, ite_true, if_true] using hd
  · simpa only [closedMagneticContinuation, closedMagneticContinuationTime,
      closedMagneticScalarCurvature, closedMagneticContinuationSecond, hs, ite_false, if_false,
      zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_mul] using (hasDerivAt_const v (1 : ℝ))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticContinuationComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing the inverse-curvature coefficient increases a convex
continued observable. This is the comparison used for conditional square means. -/

noncomputable section
open Filter Set
open scoped Topology

namespace InvariantIsing

theorem magnetic_continuation_coefficient_comparison {T : ℝ} (hT : 0 ≤ T)
    (U Ut Ux Uxx V Vt Vx Vxx a b : ℝ × ℝ → ℝ)
    (hU : ContinuousOn U (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hV : ContinuousOn V (Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1))
    (hinit : ∀ s ∈ Icc (-1 : ℝ) 1, U (0, s) ≤ V (0, s))
    (hUt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun r => U (r, s)) (Ut (t, s)) (Iic t) t)
    (hVt : ∀ t ∈ Ioc (0 : ℝ) T, ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun r => V (r, s)) (Vt (t, s)) (Iic t) t)
    (hUx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => U (t, r)) (Ux (t, s)) s)
    (hVx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => V (t, r)) (Vx (t, s)) s)
    (hUxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => Ux (t, r)) (Uxx (t, s)) s)
    (hVxx : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioo (-1 : ℝ) 1,
      HasDerivAt (fun r => Vx (t, r)) (Vxx (t, s)) s)
    (ha : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ a p)
    (hab : ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, a p ≤ b p)
    (hconvex : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, 0 ≤ Uxx p)
    (hbdy : ∀ t ∈ Icc (0 : ℝ) T, b (t, -1) = 0 ∧ b (t, 1) = 0)
    (hPU : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, Ut p = a p ^ 2 / 2 * Uxx p)
    (hPV : ∀ p ∈ Ioc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, Vt p = b p ^ 2 / 2 * Vxx p) :
    ∀ p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1, U p ≤ V p := by
  have hn := parabolic_minimum_nonneg_bounded (M := 0) hT
    (fun p => V p - U p) (fun p => Vt p - Ut p)
    (fun p => Vx p - Ux p) (fun p => Vxx p - Uxx p)
    (fun p => b p ^ 2 / 2) (fun _ => 0) (fun _ => 0)
    (hV.sub hU) (fun s hs => sub_nonneg.mpr (hinit s hs))
    (fun t ht s hs => (hVt t ht s hs).sub (hUt t ht s hs))
    (fun t ht s hs => (hVx t ht s hs).sub (hUx t ht s hs))
    (fun t ht s hs => (hVxx t ht s hs).sub (hUxx t ht s hs))
    (fun p hp => div_nonneg (sq_nonneg _) (by norm_num))
    (fun p hp => le_refl 0)
    (fun t ht => by
      rcases hbdy t ht with ⟨hl, hr⟩
      simp only [hl, hr, zero_pow (by norm_num : 2 ≠ 0), zero_div, and_self]) ?_
  · intro p hp
    exact sub_nonneg.mp (hn p hp)
  · intro p hp
    have hp' : p ∈ Icc (0 : ℝ) T ×ˢ Icc (-1 : ℝ) 1 := ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
    have hs : 0 ≤ (b p) ^ 2 - (a p) ^ 2 := by
      have ha0 := ha p hp'
      have hab' := hab p hp'
      nlinarith
    have hmul := mul_nonneg hs (hconvex p hp)
    rw [hPV p hp, hPU p hp]
    simp only [zero_mul, add_zero]
    nlinarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScaledInitial
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact initial-data identification for induction over physical Gaussian
increments in the radial inverse-curvature comparison. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScalarSlabBias_cons_initial (av : ℝ × ℝ≥0) (L : List (ℝ × ℝ≥0))
    (ζ s : ℝ) :
    magneticScalarSlabBias (av :: L) ζ 0 s = magneticScalarSlabBias L av.1 (av.2 : ℝ) s := by
  unfold magneticScalarSlabBias
  apply congrArg (fun f : ℝ → ℝ => Function.invFun f s)
  funext z
  rw [magneticScalarSlabMean_zero]
  simp only [fieldScalarMean, magneticScalarSlabMean, Real.toNNReal_coe]

lemma magneticScalarInverseCurvature_cons_initial (av : ℝ × ℝ≥0) (L : List (ℝ × ℝ≥0))
    (hL : ∀ bv ∈ av :: L, 0 < bv.1) (ζ s : ℝ) :
    magneticScalarInverseCurvature (av :: L) hL ζ 0 s =
      magneticScalarInverseCurvature L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        av.1 (av.2 : ℝ) s := by
  have hp : 0 < av.1 := hL av List.mem_cons_self
  rw [magneticScalarInverseCurvature_eq_jet, magneticScalarSlabJet_zero,
    magneticScalarSlabBias_cons_initial, magneticScalarInverseCurvature_eq_jet,
    magneticScalarSlabJet_eq_cons L _ hp]
  simp only [Real.toNNReal_coe]

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

theorem magneticClosedSquare_compare_initial (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) (hM1 : ∀ av ∈ M, av.1 ≤ 1)
    (i : Fin (L.length + 1)) (j : Fin (M.length + 1))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hcurv : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticScalarCurvature L hL ζ (0, u) ≤
        closedMagneticScalarCurvature M hM ζ (0, u))
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticContinuation L (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ (0, u) ≤
        closedMagneticContinuation M (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ (0, u))
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation L (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ (v, s) ≤
      closedMagneticContinuation M (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ (v, s) := by
  let A := (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet
  let B := (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet
  have hall := magnetic_continuation_coefficient_comparison hv
    (closedMagneticContinuation L A ζ) (closedMagneticContinuationTime L hL A ζ)
    (closedMagneticContinuationSlope L hL A ζ) (closedMagneticContinuationSecond L hL A ζ)
    (closedMagneticContinuation M B ζ) (closedMagneticContinuationTime M hM B ζ)
    (closedMagneticContinuationSlope M hM B ζ) (closedMagneticContinuationSecond M hM B ζ)
    (closedMagneticScalarCurvature L hL ζ) (closedMagneticScalarCurvature M hM ζ)
    ((continuousOn_closedMagneticContinuation L hL A
      (magneticScalarSquareFourJet_sandwich L hL i) hζ).mono (fun p hp => ⟨mem_univ _, hp.2⟩))
    ((continuousOn_closedMagneticContinuation M hM B
      (magneticScalarSquareFourJet_sandwich M hM j) hζ).mono (fun p hp => ⟨mem_univ _, hp.2⟩)) hinit
    (fun t ht u _ => (closedMagneticContinuation_hasDerivAt_time L hL A hζ ht.1 u).hasDerivWithinAt)
    (fun t ht u _ => (closedMagneticContinuation_hasDerivAt_time M hM B hζ ht.1 u).hasDerivWithinAt)
    (fun t _ u hu => closedMagneticContinuation_hasDerivAt_spin L hL A hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticContinuation_hasDerivAt_spin M hM B hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticContinuationSlope_hasDerivAt_spin L hL A hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticContinuationSlope_hasDerivAt_spin M hM B hζ (abs_lt.mpr hu) t)
    (fun p _ => closedMagneticScalarCurvature_nonneg L hL hζ p)
    (fun p hp => magneticClosedCurvature_compare_initial L M hL hM hL1 hM1 hζ
      (le_refl ζ) hζ1 hcurv hp.1.1 hp.2)
    (fun p hp => closedMagneticSquareContinuationSecond_nonneg L hL hL1 i hζ hζ1 hp.1.1.le p.2)
    (fun t _ => closedMagneticScalarCurvature_endpoints M hM ζ t)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact hall (v, s) ⟨⟨hv, le_rfl⟩, hs⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTailCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equality of backward field values gives equality of their actual
inverse curvatures. In particular, an equal-exponent Gaussian step may be
split without changing the inverse-coordinate model. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticScalarCurvature_cons_initial (av : ℝ × ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ bv ∈ av :: L, 0 < bv.1) (ζ s : ℝ) :
    closedMagneticScalarCurvature (av :: L) hL ζ (0, s) =
      closedMagneticScalarCurvature L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        av.1 ((av.2 : ℝ), s) := by
  by_cases hs : |s| < 1
  · simp only [closedMagneticScalarCurvature, hs, ite_true, if_true]
    exact magneticScalarInverseCurvature_cons_initial av L hL ζ s
  · simp only [closedMagneticScalarCurvature, hs, ite_false, if_false]

lemma magneticClosedCurvature_exponent_mono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ η : ℝ} (hζ : 0 ≤ ζ) (hζη : ζ ≤ η) (hη1 : η ≤ 1)
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ (v, s) ≤
      closedMagneticScalarCurvature L hL η (v, s) := by
  apply magneticClosedCurvature_compare_initial L L hL hL hL1 hL1 hζ hζη hη1 ?_ hv hs
  intro u _
  exact (closedMagneticScalarCurvature_initial L hL ζ η u).le

lemma magneticLogCoshMeanJet_eq_of_value_eq (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue M (fun z => Real.log (Real.cosh z))) :
    magneticLogCoshMeanJet L hL = magneticLogCoshMeanJet M hM := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  have hl := hasDerivAt_fieldScalarLogCosh L hL z
  rw [he] at hl
  exact hl.unique (hasDerivAt_fieldScalarLogCosh M hM z)

lemma magneticScalarSlabBias_eq_of_value_eq (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue M (fun z => Real.log (Real.cosh z))) (ζ v : ℝ) :
    magneticScalarSlabBias L ζ v = magneticScalarSlabBias M ζ v := by
  have hJ := magneticLogCoshMeanJet_eq_of_value_eq L M hL hM he
  have hm : magneticScalarSlabMean L ζ v = magneticScalarSlabMean M ζ v := by
    funext z
    rw [magneticScalarSlabMean_eq L hL, magneticScalarSlabMean_eq M hM, hJ, he]
  unfold magneticScalarSlabBias
  rw [hm]

lemma closedMagneticScalarCurvature_eq_of_value_eq (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue M (fun z => Real.log (Real.cosh z))) (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticScalarCurvature L hL ζ p = closedMagneticScalarCurvature M hM ζ p := by
  have hJ := magneticLogCoshMeanJet_eq_of_value_eq L M hL hM he
  have hb := magneticScalarSlabBias_eq_of_value_eq L M hL hM he ζ p.1
  unfold closedMagneticScalarCurvature
  split_ifs
  · unfold magneticScalarInverseCurvature
    rw [hJ, he, hb]
  · rfl

lemma fieldScalarValue_same_exponent (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (v w : ℝ≥0) :
    fieldScalarValue ((ζ, v) :: (ζ, w) :: L) (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue ((ζ, v + w) :: L) (fun z => Real.log (Real.cosh z)) := by
  funext z
  exact gaussianOperator_same_exponent ζ v w
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).1
    (fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth).2 z

lemma closedMagneticScalarCurvature_same_exponent (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ : ℝ} (hζ : 0 < ζ)
    (v w : ℝ≥0) (η : ℝ) (p : ℝ × ℝ) :
    closedMagneticScalarCurvature ((ζ, v) :: (ζ, w) :: L)
      (by intro av hav; simp only [List.mem_cons] at hav; rcases hav with rfl | rfl | hav
          · exact hζ
          · exact hζ
          · exact hL av hav) η p =
    closedMagneticScalarCurvature ((ζ, v + w) :: L)
      (by intro av hav; rcases List.mem_cons.mp hav with rfl | hav
          · exact hζ
          · exact hL av hav) η p :=
  closedMagneticScalarCurvature_eq_of_value_eq _ _ _ _
    (fieldScalarValue_same_exponent L hL ζ v w) η p

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticAdjacentCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving a nonnegative variance increment from a larger exponent to the
preceding smaller exponent decreases the actual inverse curvature. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

private lemma upper_cons {a : ℝ} (ha : a ≤ 1) (v : ℝ≥0)
    {L : List (ℝ × ℝ≥0)} (hL : ∀ av ∈ L, av.1 ≤ 1) :
    ∀ av ∈ (a, v) :: L, av.1 ≤ 1 := by
  intro av hav
  rcases List.mem_cons.mp hav with rfl | hav
  · exact ha
  · exact hL av hav

theorem magneticClosedCurvature_adjacent_transfer
    (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (x δ y : ℝ≥0) {η v s : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature ((a, x + δ) :: (b, y) :: L)
      (positive_cons ha _ (positive_cons (ha.trans_le hab) _ hL)) η (v, s) ≤
    closedMagneticScalarCurvature ((a, x) :: (b, δ + y) :: L)
      (positive_cons ha _ (positive_cons (ha.trans_le hab) _ hL)) η (v, s) := by
  have hb : 0 < b := ha.trans_le hab
  have ha1 : a ≤ 1 := hab.trans hb1
  let T := (b, y) :: L
  have hT : ∀ av ∈ T, 0 < av.1 := positive_cons hb y hL
  have hT1 : ∀ av ∈ T, av.1 ≤ 1 := upper_cons hb1 y hL1
  let A := (a, δ) :: T
  let B := (b, δ) :: T
  have hA : ∀ av ∈ A, 0 < av.1 := positive_cons ha δ hT
  have hB : ∀ av ∈ B, 0 < av.1 := positive_cons hb δ hT
  have hA1 : ∀ av ∈ A, av.1 ≤ 1 := upper_cons ha1 δ hT1
  have hB1 : ∀ av ∈ B, av.1 ≤ 1 := upper_cons hb1 δ hT1
  have hmid (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      closedMagneticScalarCurvature A hA a (0, u) ≤
        closedMagneticScalarCurvature B hB a (0, u) := by
    rw [closedMagneticScalarCurvature_cons_initial,
      closedMagneticScalarCurvature_cons_initial]
    exact magneticClosedCurvature_exponent_mono T hT hT1 ha.le hab hb1 δ.property hu
  have houter (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      closedMagneticScalarCurvature A hA a (x, u) ≤
        closedMagneticScalarCurvature B hB a (x, u) :=
    magneticClosedCurvature_compare_initial A B hA hB hA1 hB1 ha.le le_rfl ha1
      hmid x.property hu
  let N := (a, x + δ) :: T
  let O := (a, x) :: (b, δ + y) :: L
  have hN : ∀ av ∈ N, 0 < av.1 := positive_cons ha _ hT
  have hO : ∀ av ∈ O, 0 < av.1 := positive_cons ha _ (positive_cons hb _ hL)
  have hN1 : ∀ av ∈ N, av.1 ≤ 1 := upper_cons ha1 _ hT1
  have hO1 : ∀ av ∈ O, av.1 ≤ 1 := upper_cons ha1 _ (upper_cons hb1 _ hL1)
  have hsplit : fieldScalarValue ((a, x) :: B) (fun z => Real.log (Real.cosh z)) =
      fieldScalarValue O (fun z => Real.log (Real.cosh z)) := by
    change gaussianOperator a x (fieldScalarValue ((b, δ) :: (b, y) :: L)
        (fun z => Real.log (Real.cosh z))) =
      gaussianOperator a x (fieldScalarValue ((b, δ + y) :: L)
        (fun z => Real.log (Real.cosh z)))
    rw [fieldScalarValue_same_exponent L hL b δ y]
  have hinit (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      closedMagneticScalarCurvature N hN η (0, u) ≤
        closedMagneticScalarCurvature O hO η (0, u) := by
    have hn := closedMagneticScalarCurvature_same_exponent T hT ha x δ η (0, u)
    have ho := closedMagneticScalarCurvature_eq_of_value_eq ((a, x) :: B) O
      (positive_cons ha x hB) hO hsplit η (0, u)
    rw [← hn, ← ho]
    rw [closedMagneticScalarCurvature_cons_initial,
      closedMagneticScalarCurvature_cons_initial]
    exact houter u hu
  exact magneticClosedCurvature_compare_initial N O hN hO hN1 hO1 hη le_rfl hη1
    hinit hv hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticSquareInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact initial square data for the induction over Gaussian levels. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma closedMagneticSquareContinuation_zero_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ)
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation L
      (magneticScalarSquareFourJet L hL 0).toMagneticContinuationJet ζ (0, s) = s ^ 2 := by
  by_cases hsi : |s| < 1
  · simp only [closedMagneticContinuation, hsi, ite_true, if_true]
    rw [magneticScalarSlabContinuation_eq_jet L hL,
      magneticScalarSlabContinuationJet_zero, magneticScalarSquareFourJet_value,
      fieldScalarSquares_zero]
    have hm := magneticScalarSlabMean_bias L hL hζ hsi (0 : ℝ)
    rw [magneticScalarSlabMean_zero] at hm
    rw [hm]
  · have he : |s| = 1 := le_antisymm (abs_le.mpr hs) (le_of_not_gt hsi)
    have hsq : s ^ 2 = 1 := by rw [← sq_abs, he]; norm_num
    simp only [closedMagneticContinuation, hsi, ite_false, if_false, hsq]

lemma closedMagneticSquareContinuation_cons_initial (av : ℝ × ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ bv ∈ av :: L, 0 < bv.1)
    (i : Fin (L.length + 1)) (ζ s : ℝ) :
    closedMagneticContinuation (av :: L)
      (magneticScalarSquareFourJet (av :: L) hL i.succ).toMagneticContinuationJet ζ (0, s) =
    closedMagneticContinuation L
      (magneticScalarSquareFourJet L
        (fun bv hb => hL bv (List.mem_cons_of_mem av hb)) i).toMagneticContinuationJet
      av.1 ((av.2 : ℝ), s) := by
  by_cases hs : |s| < 1
  · simp only [closedMagneticContinuation, hs, ite_true, if_true]
    rw [magneticScalarSlabContinuation_eq_jet (av :: L) hL,
      magneticScalarSlabContinuationJet_zero, magneticScalarSlabBias_cons_initial,
      magneticScalarSlabContinuation_eq_jet L
        (fun bv hb => hL bv (List.mem_cons_of_mem av hb))]
    simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
      magneticScalarSquareFourJet_value, Real.toNNReal_coe]
    rfl
  · simp only [closedMagneticContinuation, hs, ite_false, if_false]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticPrefixComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common finite prefix preserves inverse-curvature order and the
associated conditional-square order up to the end of that prefix. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma upper_append (P L : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, av.1 ≤ 1) (hL : ∀ av ∈ L, av.1 ≤ 1) :
    ∀ av ∈ P ++ L, av.1 ≤ 1 := by
  intro av hav
  rcases List.mem_append.mp hav with hp | hl
  · exact hP av hp
  · exact hL av hl

theorem magneticClosedCurvature_append_mono (P L M : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hP1 : ∀ av ∈ P, av.1 ≤ 1)
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (hM : ∀ av ∈ M, 0 < av.1) (hM1 : ∀ av ∈ M, av.1 ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticScalarCurvature L hL 0 (0, u) ≤
        closedMagneticScalarCurvature M hM 0 (0, u))
    {ζ v s : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature (P ++ L) (positive_append P L hP hL) ζ (v, s) ≤
      closedMagneticScalarCurvature (P ++ M) (positive_append P M hP hM) ζ (v, s) := by
  induction P generalizing ζ v s with
  | nil =>
    apply magneticClosedCurvature_compare_initial L M hL hM hL1 hM1 hζ le_rfl hζ1 ?_ hv hs
    intro u hu
    rw [closedMagneticScalarCurvature_initial L hL ζ 0 u,
      closedMagneticScalarCurvature_initial M hM ζ 0 u]
    exact hinit u hu
  | cons av P ih =>
    apply magneticClosedCurvature_compare_initial (av :: P ++ L) (av :: P ++ M)
      (positive_append _ _ hP hL) (positive_append _ _ hP hM)
      (upper_append _ _ hP1 hL1) (upper_append _ _ hP1 hM1) hζ le_rfl hζ1 ?_ hv hs
    intro u hu
    simp only [List.cons_append]
    rw [closedMagneticScalarCurvature_cons_initial,
      closedMagneticScalarCurvature_cons_initial]
    exact ih (fun bv hb => hP bv (List.mem_cons_of_mem av hb))
      (fun bv hb => hP1 bv (List.mem_cons_of_mem av hb))
      (hP av List.mem_cons_self).le (hP1 av List.mem_cons_self) av.2.property hu

theorem magneticClosedSquare_append_mono (P L M : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hP1 : ∀ av ∈ P, av.1 ≤ 1)
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (hM : ∀ av ∈ M, 0 < av.1) (hM1 : ∀ av ∈ M, av.1 ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticScalarCurvature L hL 0 (0, u) ≤
        closedMagneticScalarCurvature M hM 0 (0, u))
    (i : ℕ) (hi : i ≤ P.length) {ζ v s : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation (P ++ L)
      (magneticScalarSquareFourJet (P ++ L) (positive_append P L hP hL)
        ⟨i, by simp only [List.length_append]; omega⟩).toMagneticContinuationJet ζ (v, s) ≤
    closedMagneticContinuation (P ++ M)
      (magneticScalarSquareFourJet (P ++ M) (positive_append P M hP hM)
        ⟨i, by simp only [List.length_append]; omega⟩).toMagneticContinuationJet ζ (v, s) := by
  induction P generalizing i ζ v s with
  | nil =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    apply magneticClosedSquare_compare_initial L M hL hM hL1 hM1 0 0 hζ hζ1 ?_ ?_ hv hs
    · intro u hu
      rw [closedMagneticScalarCurvature_initial L hL ζ 0 u,
        closedMagneticScalarCurvature_initial M hM ζ 0 u]
      exact hinit u hu
    · intro u hu
      rw [closedMagneticSquareContinuation_zero_initial L hL hζ hu,
        closedMagneticSquareContinuation_zero_initial M hM hζ hu]
  | cons av P ih =>
    apply magneticClosedSquare_compare_initial (av :: P ++ L) (av :: P ++ M)
      (positive_append _ _ hP hL) (positive_append _ _ hP hM)
      (upper_append _ _ hP1 hL1) (upper_append _ _ hP1 hM1) _ _ hζ hζ1 ?_ ?_ hv hs
    · intro u hu
      exact magneticClosedCurvature_append_mono (av :: P) L M hP hP1 hL hL1 hM hM1
        hinit hζ hζ1 (le_refl 0) hu
    · intro u hu
      simp only [List.cons_append]
      cases i with
      | zero =>
        exact (closedMagneticSquareContinuation_zero_initial (av :: P ++ L)
          (positive_append _ _ hP hL) hζ hu).le.trans
          (closedMagneticSquareContinuation_zero_initial (av :: P ++ M)
            (positive_append _ _ hP hM) hζ hu).ge
      | succ i =>
        have hiP : i ≤ P.length := by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hi
        have heL : (⟨i + 1, by simp only [List.length_cons, List.length_append]; omega⟩ :
            Fin ((av :: P ++ L).length + 1)) =
            (⟨i, by simp only [List.length_append]; omega⟩ : Fin ((P ++ L).length + 1)).succ := rfl
        have heM : (⟨i + 1, by simp only [List.length_cons, List.length_append]; omega⟩ :
            Fin ((av :: P ++ M).length + 1)) =
            (⟨i, by simp only [List.length_append]; omega⟩ : Fin ((P ++ M).length + 1)).succ := rfl
        rw [heL, heM, closedMagneticSquareContinuation_cons_initial,
          closedMagneticSquareContinuation_cons_initial]
        exact ih (fun bv hb => hP bv (List.mem_cons_of_mem av hb))
          (fun bv hb => hP1 bv (List.mem_cons_of_mem av hb)) i hiP
          (hP av List.mem_cons_self).le (hP1 av List.mem_cons_self) av.2.property hu

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticAdjacentSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The conditional square means preceding a transferred variance
increment decrease at fixed total mean spin. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticClosedSquare_adjacent_transfer (P L : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hP1 : ∀ av ∈ P, av.1 ≤ 1)
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (x δ y : ℝ≥0)
    (hN : ∀ av ∈ P ++ (a, x + δ) :: (b, y) :: L, 0 < av.1)
    (hO : ∀ av ∈ P ++ (a, x) :: (b, δ + y) :: L, 0 < av.1)
    (i : ℕ) (hi : i ≤ P.length) {ζ v s : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation (P ++ (a, x + δ) :: (b, y) :: L)
      (magneticScalarSquareFourJet _ hN
        ⟨i, by simp only [List.length_append, List.length_cons]; omega⟩).toMagneticContinuationJet
        ζ (v, s) ≤
    closedMagneticContinuation (P ++ (a, x) :: (b, δ + y) :: L)
      (magneticScalarSquareFourJet _ hO
        ⟨i, by simp only [List.length_append, List.length_cons]; omega⟩).toMagneticContinuationJet
        ζ (v, s) := by
  let N := (a, x + δ) :: (b, y) :: L
  let O := (a, x) :: (b, δ + y) :: L
  have hNT : ∀ av ∈ N, 0 < av.1 := fun av hav => hN av (List.mem_append_right P hav)
  have hOT : ∀ av ∈ O, 0 < av.1 := fun av hav => hO av (List.mem_append_right P hav)
  have hNT1 : ∀ av ∈ N, av.1 ≤ 1 := by
    intro av hav
    rcases List.mem_cons.mp hav with rfl | hav
    · exact hab.trans hb1
    · rcases List.mem_cons.mp hav with rfl | hav
      · exact hb1
      · exact hL1 av hav
  have hOT1 : ∀ av ∈ O, av.1 ≤ 1 := by
    intro av hav
    rcases List.mem_cons.mp hav with rfl | hav
    · exact hab.trans hb1
    · rcases List.mem_cons.mp hav with rfl | hav
      · exact hb1
      · exact hL1 av hav
  have hinit (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
      closedMagneticScalarCurvature N hNT 0 (0, u) ≤
        closedMagneticScalarCurvature O hOT 0 (0, u) :=
    magneticClosedCurvature_adjacent_transfer L hL hL1 ha hab hb1 x δ y
      (le_refl 0) (by norm_num) (le_refl 0) hu
  exact magneticClosedSquare_append_mono P N O hP hP1 hNT hNT1 hOT hOT1 hinit i hi
    hζ hζ1 hv hs

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldInverseConvex
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite conditional overlap is convex in prescribed mean spin.
The ordinary root Gaussian is included in this identification. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma scalarFieldIncrements_exponent_le_one (h : FieldStep) :
    ∀ av ∈ scalarFieldIncrements h, av.1 ≤ 1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  change h.cut i.succ.castSucc ≤ 1
  rw [← h.last]
  exact h.ordered_cut.monotone (Fin.le_last _)

lemma magneticScalarSlabBias_root (h : FieldStep) :
    magneticScalarSlabBias (scalarFieldIncrements h) 0 (h.height 0) = magneticBias h := by
  have he : Real.toNNReal (h.height 0) = NNReal.mk (h.height 0) (h.nonneg 0) := Real.toNNReal_of_nonneg (h.nonneg 0)
  have hm : magneticScalarSlabMean (scalarFieldIncrements h) 0 (h.height 0) = fieldBiasMean h := by
    funext z
    simp only [magneticScalarSlabMean, fieldBiasMean, he]
  funext s
  change Function.invFun (magneticScalarSlabMean (scalarFieldIncrements h) 0 (h.height 0)) s =
    Function.invFun (fieldBiasMean h) s
  rw [hm]

lemma magneticFieldLevel_eq_slab (h : FieldStep) (i : Fin (h.depth + 1)) :
    (fun s => magneticFieldLevel h s i) =
      magneticScalarSlabContinuation (scalarFieldIncrements h)
        (magneticScalarSquareFourJet (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
          (Fin.cast (by rw [scalarFieldIncrements_length]) i)).toMagneticContinuationJet
        0 (h.height 0) := by
  funext s
  rw [magneticScalarSlabContinuation_eq_jet _ (scalarFieldIncrements_positive h)]
  have he : Real.toNNReal (h.height 0) = NNReal.mk (h.height 0) (h.nonneg 0) := Real.toNNReal_of_nonneg (h.nonneg 0)
  simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
    magneticScalarSquareFourJet_value, magneticScalarSlabBias_root, he,
    magneticFieldLevel, magneticLevelAtBias]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeightLists
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal two-increment decomposition of a positive-index height
update after removing the ordinary Gaussian root. -/

noncomputable section
open Set
open scoped NNReal

namespace InvariantIsing

private lemma allIncrements_toNNReal (h : FieldStep) :
    fieldAllIncrements h = List.ofFn (fun j : Fin (h.depth + 1) =>
      (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement h.height j))) := by
  unfold fieldAllIncrements
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · rfl
  · exact (Real.toNNReal_of_nonneg (fieldIncrement_nonneg h j)).symm

private lemma allIncrements_take_positive (h : FieldStep) (k : ℕ) (hk : 0 < k) :
    (fieldAllIncrements h).take k =
      (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
        (scalarFieldIncrements h).take (k - 1) := by
  cases k with
  | zero => omega
  | succ k => simp only [fieldAllIncrements_root, List.take_succ_cons, Nat.add_sub_cancel]

private lemma scalarIncrements_of_adjacent (h k : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) (t : ℝ) (hroot : k.height 0 = h.height 0)
    (hall : fieldAllIncrements k =
      fieldAdjacentIncrements ((fieldAllIncrements h).take j.val)
        ((fieldAllIncrements h).drop (j.val + 2))
        (fieldIncrement h j.castSucc).2 (fieldIncrement h j.succ).2
        (fieldIncrement h j.castSucc).1 (fieldIncrement h j.succ).1 t) :
    scalarFieldIncrements k = (scalarFieldIncrements h).take (j.val - 1) ++
      ((fieldIncrement h j.castSucc).1, Real.toNNReal ((fieldIncrement h j.castSucc).2 + t)) ::
      ((fieldIncrement h j.succ).1, Real.toNNReal ((fieldIncrement h j.succ).2 - t)) ::
      (scalarFieldIncrements h).drop (j.val + 1) := by
  have ht := allIncrements_take_positive h j.val hj
  have hd : (fieldAllIncrements h).drop (j.val + 2) =
      (scalarFieldIncrements h).drop (j.val + 1) := by
    rw [fieldAllIncrements_root]
    exact List.drop_succ_cons
  rw [fieldAllIncrements_root k, ht, hd, fieldAdjacentIncrements_root] at hall
  have hr : (NNReal.mk (k.height 0) (k.nonneg 0)) =
      (NNReal.mk (h.height 0) (h.nonneg 0)) := Subtype.ext hroot
  rw [hr] at hall
  exact (List.cons.inj hall).2

lemma scalarFieldIncrements_interior_layout (h : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) :
    scalarFieldIncrements h = (scalarFieldIncrements h).take (j.val - 1) ++
      ((fieldIncrement h j.castSucc).1, Real.toNNReal (fieldIncrement h j.castSucc).2) ::
      ((fieldIncrement h j.succ).1, Real.toNNReal (fieldIncrement h j.succ).2) ::
      (scalarFieldIncrements h).drop (j.val + 1) := by
  have he := updated_increments_interior h j 0
  simp only [add_zero, Function.update_eq_self] at he
  rw [← allIncrements_toNNReal h] at he
  simpa only [add_zero, sub_zero] using scalarIncrements_of_adjacent h h j hj 0 rfl he

lemma scalarFieldIncrements_update_interior (h : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) (t : ℝ)
    (ht : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) :
    scalarFieldIncrements (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) ht) =
      (scalarFieldIncrements h).take (j.val - 1) ++
      ((fieldIncrement h j.castSucc).1, Real.toNNReal ((fieldIncrement h j.castSucc).2 + t)) ::
      ((fieldIncrement h j.succ).1, Real.toNNReal ((fieldIncrement h j.succ).2 - t)) ::
      (scalarFieldIncrements h).drop (j.val + 1) := by
  apply scalarIncrements_of_adjacent h _ j hj t ?_
    (fieldAllIncrements_update_interior h j t ht)
  change Function.update h.height j.castSucc (h.height j.castSucc + t) 0 = h.height 0
  apply Function.update_of_ne
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_zero, Fin.val_castSucc] at hv
  omega

private lemma scalarIncrements_of_terminal (h k : FieldStep) (hn : 0 < h.depth)
    (t : ℝ) (hroot : k.height 0 = h.height 0)
    (hall : fieldAllIncrements k =
      fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
        (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 t) :
    scalarFieldIncrements k = (scalarFieldIncrements h).take (h.depth - 1) ++
      [((fieldIncrement h (Fin.last h.depth)).1,
        Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))] := by
  rw [fieldAllIncrements_root k, allIncrements_take_positive h h.depth hn] at hall
  simp only [fieldTerminalIncrements, List.cons_append] at hall
  have hr : (NNReal.mk (k.height 0) (k.nonneg 0)) =
      (NNReal.mk (h.height 0) (h.nonneg 0)) := Subtype.ext hroot
  rw [hr] at hall
  exact (List.cons.inj hall).2

lemma scalarFieldIncrements_terminal_layout (h : FieldStep) (hn : 0 < h.depth) :
    scalarFieldIncrements h = (scalarFieldIncrements h).take (h.depth - 1) ++
      [((fieldIncrement h (Fin.last h.depth)).1,
        Real.toNNReal (fieldIncrement h (Fin.last h.depth)).2)] := by
  have he := updated_increments_final h 0
  simp only [add_zero, Function.update_eq_self] at he
  rw [← allIncrements_toNNReal h] at he
  simpa only [add_zero] using scalarIncrements_of_terminal h h hn 0 rfl he

lemma scalarFieldIncrements_update_terminal (h : FieldStep) (hn : 0 < h.depth)
    (t : ℝ) (ht : Function.update h.height (Fin.last h.depth)
      (h.height (Fin.last h.depth) + t) ∈ fieldStrictHeightCone h.depth) :
    scalarFieldIncrements (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) ht) =
      (scalarFieldIncrements h).take (h.depth - 1) ++
      [((fieldIncrement h (Fin.last h.depth)).1,
        Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t))] := by
  apply scalarIncrements_of_terminal h _ hn t ?_
    (fieldAllIncrements_update_final h t ht)
  change Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) 0 = h.height 0
  apply Function.update_of_ne
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_zero, Fin.val_last] at hv
  omega

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTerminalCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constant terminal shifts leave the optimizing bias, inverse
curvature, and all preceding conditional square means unchanged. -/

noncomputable section
open Filter Set IsingPerceptron
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticLogCoshMeanJet_eq_of_value_const_add (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1) (c : ℝ)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fun z => c + fieldScalarValue M (fun z => Real.log (Real.cosh z)) z) :
    magneticLogCoshMeanJet L hL = magneticLogCoshMeanJet M hM := by
  apply MagneticContinuationJet.eq_of_value_eq
  funext z
  have hl := hasDerivAt_fieldScalarLogCosh L hL z
  rw [he] at hl
  exact hl.unique ((hasDerivAt_fieldScalarLogCosh M hM z).const_add c)

lemma magneticScalarSlabMean_eq_of_value_const_add (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1) (c : ℝ)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fun z => c + fieldScalarValue M (fun z => Real.log (Real.cosh z)) z)
    (ζ v : ℝ) : magneticScalarSlabMean L ζ v = magneticScalarSlabMean M ζ v := by
  have hj := magneticLogCoshMeanJet_eq_of_value_const_add L M hL hM c he
  have hm := congrArg MagneticContinuationJet.value hj
  change fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh =
    fieldScalarMean M (fun z => Real.log (Real.cosh z)) Real.tanh at hm
  unfold magneticScalarSlabMean
  rw [he, hm]
  funext z
  exact fieldSpinTransition_const_add ζ (Real.toNNReal v) _ _ c z

lemma magneticScalarSlabBias_eq_of_value_const_add (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1) (c : ℝ)
    (he : fieldScalarValue L (fun z => Real.log (Real.cosh z)) =
      fun z => c + fieldScalarValue M (fun z => Real.log (Real.cosh z)) z)
    (ζ v : ℝ) : magneticScalarSlabBias L ζ v = magneticScalarSlabBias M ζ v := by
  unfold magneticScalarSlabBias
  rw [magneticScalarSlabMean_eq_of_value_const_add L M hL hM c he]

lemma closedMagneticSquare_terminal_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (v : ℝ≥0)
    (hT : ∀ av ∈ L ++ [(1, v)], 0 < av.1)
    (i : ℕ) (hi : i ≤ L.length) (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticContinuation (L ++ [(1, v)])
      (magneticScalarSquareFourJet _ hT
        ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩).toMagneticContinuationJet ζ p =
    closedMagneticContinuation L
      (magneticScalarSquareFourJet L hL ⟨i, by omega⟩).toMagneticContinuationJet ζ p := by
  have hb := magneticScalarSlabBias_eq_of_value_const_add _ _ hT hL (v / 2)
    (fieldScalarValue_terminal_one L hL v) ζ p.1
  unfold closedMagneticContinuation
  split_ifs
  · rw [magneticScalarSlabContinuation_eq_jet _ hT,
      magneticScalarSlabContinuation_eq_jet _ hL]
    simp only [magneticScalarSlabContinuationJet, MagneticContinuationJet.transition,
      magneticScalarSquareFourJet_value]
    rw [fieldScalarSquares_terminal_one L hL v i hi, fieldScalarValue_terminal_one L hL v,
      fieldSpinTransition_const_add, hb]
  · rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTerminalOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing the final covariance height decreases each preceding
conditional square at fixed total magnetization. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma square_congr_list {L M : List (ℝ × ℝ≥0)} (he : L = M)
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (i : Fin (L.length + 1)) (j : Fin (M.length + 1)) (hij : i.val = j.val)
    (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticContinuation L
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ p =
    closedMagneticContinuation M
      (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ p := by
  subst M
  have hj : i = j := Fin.ext hij
  subst j
  rfl

theorem magneticClosedSquare_terminal_variance_mono (P : List (ℝ × ℝ≥0))
    (hP : ∀ av ∈ P, 0 < av.1) (hP1 : ∀ av ∈ P, av.1 ≤ 1)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (x δ : ℝ≥0)
    (hN : ∀ av ∈ P ++ [(a, x + δ)], 0 < av.1)
    (hO : ∀ av ∈ P ++ [(a, x)], 0 < av.1)
    (i : ℕ) (hi : i ≤ P.length) {ζ v s : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation (P ++ [(a, x + δ)])
      (magneticScalarSquareFourJet _ hN
        ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩).toMagneticContinuationJet
        ζ (v, s) ≤
    closedMagneticContinuation (P ++ [(a, x)])
      (magneticScalarSquareFourJet _ hO
        ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩).toMagneticContinuationJet
        ζ (v, s) := by
  have hn : ∀ av ∈ P ++ (a, x + δ) :: (1, (0 : ℝ≥0)) :: [], 0 < av.1 := by
    intro av hav
    rcases List.mem_append.mp hav with hp | ht
    · exact hP av hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ha
      · norm_num
  have ho : ∀ av ∈ P ++ (a, x) :: (1, δ + 0) :: [], 0 < av.1 := by
    intro av hav
    rcases List.mem_append.mp hav with hp | ht
    · exact hP av hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact ha
      · norm_num
  have h := magneticClosedSquare_adjacent_transfer P [] hP hP1 (by simp) (by simp)
    ha ha1 (le_refl 1) x δ 0 hn ho i hi hζ hζ1 hv hs
  have hn' : ∀ av ∈ (P ++ [(a, x + δ)]) ++ [(1, (0 : ℝ≥0))], 0 < av.1 := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hn
  have ho' : ∀ av ∈ (P ++ [(a, x)]) ++ [(1, δ)], 0 < av.1 := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append, add_zero] using ho
  have hni : i ≤ (P ++ [(a, x + δ)]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hoi : i ≤ (P ++ [(a, x)]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have en := closedMagneticSquare_terminal_one (P ++ [(a, x + δ)]) hN 0 hn' i hni ζ (v, s)
  have eo := closedMagneticSquare_terminal_one (P ++ [(a, x)]) hO δ ho' i hoi ζ (v, s)
  have enC := square_congr_list
    (show (P ++ [(a, x + δ)]) ++ [(1, (0 : ℝ≥0))] =
      P ++ (a, x + δ) :: (1, (0 : ℝ≥0)) :: [] by simp only [List.append_assoc,
        List.cons_append, List.nil_append]) hn' hn
    ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩
    ⟨i, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
    rfl ζ (v, s)
  have eoC := square_congr_list
    (show (P ++ [(a, x)]) ++ [(1, δ)] = P ++ (a, x) :: (1, δ + 0) :: [] by
      simp only [List.append_assoc, List.cons_append, List.nil_append, add_zero]) ho' ho
    ⟨i, by simp only [List.length_append, List.length_singleton]; omega⟩
    ⟨i, by simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
    rfl ζ (v, s)
  exact (enC.symm.trans en).ge.trans (h.trans (eoC.symm.trans eo).le)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticHeightOrder
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal increase of an interior height decreases each earlier
conditional square mean at fixed prescribed magnetization. -/

noncomputable section
open Set
open scoped NNReal

namespace InvariantIsing

private lemma nonneg_toNNReal_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.toNNReal (a + b) = Real.toNNReal a + Real.toNNReal b := by
  rw [Real.toNNReal_of_nonneg (add_nonneg ha hb), Real.toNNReal_of_nonneg ha,
    Real.toNNReal_of_nonneg hb]
  rfl

private lemma closedSquare_congr {L M : List (ℝ × ℝ≥0)} (he : L = M)
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (i : Fin (L.length + 1)) (j : Fin (M.length + 1)) (hij : i.val = j.val)
    (ζ : ℝ) (p : ℝ × ℝ) :
    closedMagneticContinuation L (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ p =
    closedMagneticContinuation M (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ p := by
  subst M
  have hi : i = j := Fin.ext hij
  subst j
  rfl

lemma magneticFieldLevel_eq_closed (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : |s| < 1) :
    magneticFieldLevel h s i = closedMagneticContinuation (scalarFieldIncrements h)
      (magneticScalarSquareFourJet _ (scalarFieldIncrements_positive h)
        (Fin.cast (by rw [scalarFieldIncrements_length]) i)).toMagneticContinuationJet
      0 (h.height 0, s) := by
  rw [congrFun (magneticFieldLevel_eq_slab h i) s, closedMagneticContinuation, ite_eq_left hs]

theorem magneticFieldLevel_interior_update_le (h : FieldStep) (j : Fin h.depth)
    (hj : 0 < j.val) {t s : ℝ} (ht : 0 ≤ t)
    (htb : t ≤ (fieldIncrement h j.succ).2)
    (hk : Function.update h.height j.castSucc (h.height j.castSucc + t) ∈
      fieldStrictHeightCone h.depth) (hs : |s| < 1)
    (i : Fin (h.depth + 1)) (hij : i.val < j.val) :
    magneticFieldLevel (fieldStepOfStrictHeights h
      (Function.update h.height j.castSucc (h.height j.castSucc + t)) hk) s i ≤
      magneticFieldLevel h s i := by
  let k := fieldStepOfStrictHeights h
    (Function.update h.height j.castSucc (h.height j.castSucc + t)) hk
  let P := (scalarFieldIncrements h).take (j.val - 1)
  let S := (scalarFieldIncrements h).drop (j.val + 1)
  let a := (fieldIncrement h j.castSucc).1
  let b := (fieldIncrement h j.succ).1
  let x := Real.toNNReal (fieldIncrement h j.castSucc).2
  let δ := Real.toNNReal t
  let y := Real.toNNReal ((fieldIncrement h j.succ).2 - t)
  let N := P ++ (a, x + δ) :: (b, y) :: S
  let O := P ++ (a, x) :: (b, δ + y) :: S
  have hx : Real.toNNReal ((fieldIncrement h j.castSucc).2 + t) = x + δ :=
    nonneg_toNNReal_add _ _ (fieldIncrement_nonneg h _) ht
  have hy : δ + y = Real.toNNReal (fieldIncrement h j.succ).2 := by
    dsimp only [δ, y]
    rw [← nonneg_toNNReal_add _ _ ht (sub_nonneg.mpr htb)]
    congr 1
    ring
  have hn : scalarFieldIncrements k = N := by
    rw [scalarFieldIncrements_update_interior h j hj t hk, hx]
  have ho : scalarFieldIncrements h = O := by
    rw [scalarFieldIncrements_interior_layout h j hj]
    dsimp only [O, P, S, a, b, x]
    rw [hy]
  have hN : ∀ av ∈ N, 0 < av.1 := by
    intro av hav
    apply scalarFieldIncrements_positive k av
    rwa [hn]
  have hO : ∀ av ∈ O, 0 < av.1 := by
    intro av hav
    apply scalarFieldIncrements_positive h av
    rwa [ho]
  have hP : ∀ av ∈ P, 0 < av.1 := fun av hav =>
    scalarFieldIncrements_positive h av (List.mem_of_mem_take hav)
  have hP1 : ∀ av ∈ P, av.1 ≤ 1 := fun av hav =>
    scalarFieldIncrements_exponent_le_one h av (List.mem_of_mem_take hav)
  have hS : ∀ av ∈ S, 0 < av.1 := fun av hav =>
    scalarFieldIncrements_positive h av (List.mem_of_mem_drop hav)
  have hS1 : ∀ av ∈ S, av.1 ≤ 1 := fun av hav =>
    scalarFieldIncrements_exponent_le_one h av (List.mem_of_mem_drop hav)
  have ha : 0 < a := by
    change 0 < h.cut j.castSucc.castSucc
    rw [← h.first]
    exact h.ordered_cut (Fin.lt_def.mpr hj)
  have hab : a ≤ b := by
    change h.cut j.castSucc.castSucc ≤ h.cut j.succ.castSucc
    exact h.ordered_cut.monotone (Fin.le_iff_val_le_val.mpr (Nat.le_succ _))
  have hb : b ≤ 1 := by
    change h.cut j.succ.castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hip : i.val ≤ P.length := by
    dsimp only [P]
    rw [List.length_take, scalarFieldIncrements_length, Nat.min_eq_left (by omega)]
    omega
  have hcmp := magneticClosedSquare_adjacent_transfer P S hP hP1 hS hS1 ha hab hb
    x δ y hN hO i.val hip (le_refl 0) (by norm_num) (h.nonneg 0)
    ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩
  have hroot : k.height 0 = h.height 0 := by
    change Function.update h.height j.castSucc (h.height j.castSucc + t) 0 = h.height 0
    apply Function.update_of_ne
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero, Fin.val_castSucc] at hv
    omega
  rw [magneticFieldLevel_eq_closed k i hs, magneticFieldLevel_eq_closed h i hs, hroot]
  have en := closedSquare_congr hn (scalarFieldIncrements_positive k) hN
    (Fin.cast (by rw [scalarFieldIncrements_length]; rfl) i)
    ⟨i.val, by dsimp only [N]; simp only [List.length_append, List.length_cons]; omega⟩
    rfl 0 (h.height 0, s)
  have eo := closedSquare_congr ho (scalarFieldIncrements_positive h) hO
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
    ⟨i.val, by dsimp only [O]; simp only [List.length_append, List.length_cons]; omega⟩
    rfl 0 (h.height 0, s)
  exact en.le.trans (hcmp.trans eo.ge)

theorem magneticFieldLevel_terminal_update_le (h : FieldStep) {t s : ℝ} (ht : 0 ≤ t)
    (hk : Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) ∈
      fieldStrictHeightCone h.depth) (hs : |s| < 1)
    (i : Fin (h.depth + 1)) (hi : i.val < h.depth) :
    magneticFieldLevel (fieldStepOfStrictHeights h
      (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) hk) s i ≤
      magneticFieldLevel h s i := by
  have hn : 0 < h.depth := by omega
  let k := fieldStepOfStrictHeights h
    (Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t)) hk
  let P := (scalarFieldIncrements h).take (h.depth - 1)
  let a := (fieldIncrement h (Fin.last h.depth)).1
  let x := Real.toNNReal (fieldIncrement h (Fin.last h.depth)).2
  let δ := Real.toNNReal t
  let N := P ++ [(a, x + δ)]
  let O := P ++ [(a, x)]
  have hx : Real.toNNReal ((fieldIncrement h (Fin.last h.depth)).2 + t) = x + δ :=
    nonneg_toNNReal_add _ _ (fieldIncrement_nonneg h _) ht
  have hnew : scalarFieldIncrements k = N := by
    rw [scalarFieldIncrements_update_terminal h hn t hk, hx]
  have hold : scalarFieldIncrements h = O := scalarFieldIncrements_terminal_layout h hn
  have hN : ∀ av ∈ N, 0 < av.1 := by
    intro av hav
    apply scalarFieldIncrements_positive k av
    rwa [hnew]
  have hO : ∀ av ∈ O, 0 < av.1 := by
    intro av hav
    apply scalarFieldIncrements_positive h av
    rwa [hold]
  have hP : ∀ av ∈ P, 0 < av.1 := fun av hav =>
    scalarFieldIncrements_positive h av (List.mem_of_mem_take hav)
  have hP1 : ∀ av ∈ P, av.1 ≤ 1 := fun av hav =>
    scalarFieldIncrements_exponent_le_one h av (List.mem_of_mem_take hav)
  have ha : 0 < a := by
    change 0 < h.cut (Fin.last h.depth).castSucc
    rw [← h.first]
    exact h.ordered_cut (Fin.lt_def.mpr hn)
  have ha1 : a ≤ 1 := by
    change h.cut (Fin.last h.depth).castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hip : i.val ≤ P.length := by
    dsimp only [P]
    rw [List.length_take, scalarFieldIncrements_length, Nat.min_eq_left (by omega)]
    omega
  have hcmp := magneticClosedSquare_terminal_variance_mono P hP hP1 ha ha1 x δ hN hO
    i.val hip (le_refl 0) (by norm_num) (h.nonneg 0)
    ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩
  have hroot : k.height 0 = h.height 0 := by
    change Function.update h.height (Fin.last h.depth) (h.height (Fin.last h.depth) + t) 0 = h.height 0
    apply Function.update_of_ne
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  rw [magneticFieldLevel_eq_closed k i hs, magneticFieldLevel_eq_closed h i hs, hroot]
  have en := closedSquare_congr hnew (scalarFieldIncrements_positive k) hN
    (Fin.cast (by rw [scalarFieldIncrements_length]; rfl) i)
    ⟨i.val, by dsimp only [N]; simp only [List.length_append, List.length_singleton]; omega⟩
    rfl 0 (h.height 0, s)
  have eo := closedSquare_congr hold (scalarFieldIncrements_positive h) hO
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
    ⟨i.val, by dsimp only [O]; simp only [List.length_append, List.length_singleton]; omega⟩
    rfl 0 (h.height 0, s)
  exact en.le.trans (hcmp.trans eo.ge)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticOffDiagonalHessian
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed sign of the constrained height Hessian follows from the
actual positive coordinate variation. Together with radial monotonicity,
it gives the negative quadratic-form sign. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

private lemma update_eq_coordinate_line {n : ℕ} (r : Fin n → ℝ)
    (j : Fin n) (t : ℝ) :
    Function.update r j (r j + t) = r + t • Pi.single j (1 : ℝ) := by
  classical
  funext k
  by_cases hkj : k = j
  · subst k
    simp
  · simp [Function.update_of_ne hkj, Pi.single_eq_of_ne hkj]

private lemma heightLevel_update (h : FieldStep) {s : ℝ}
    (r : Fin (h.depth + 1) → ℝ) (hrs : r ∈ fieldStrictHeightCone h.depth)
    (j : Fin (h.depth + 1)) (t : ℝ)
    (ht : Function.update r j (r j + t) ∈ fieldStrictHeightCone h.depth)
    (i : Fin (h.depth + 1)) :
    magneticHeightLevel h s (r + t • Pi.single j (1 : ℝ)) i =
      magneticFieldLevel (fieldStepOfStrictHeights (fieldStepOfStrictHeights h r hrs)
        (Function.update r j (r j + t)) ht) s i := by
  rw [← update_eq_coordinate_line, magneticHeightLevel, dite_eq_left ht]
  rfl

lemma magneticHeightLevel_coordinate_right_order_oai (h : FieldStep) {s : ℝ}
    (hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ)
    (hrs : r ∈ fieldStrictHeightCone h.depth)
    (i j : Fin (h.depth + 1)) (hij : i < j) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      magneticHeightLevel h s (r + t • Pi.single j (1 : ℝ)) i ≤
        magneticHeightLevel h s r i := by
  let k := fieldStepOfStrictHeights h r hrs
  have hbase : magneticHeightLevel h s r i = magneticFieldLevel k s i := by
    rw [magneticHeightLevel, dite_eq_left hrs]
  have hq : ContinuousAt (fun t : ℝ => Function.update r j (r j + t)) 0 := by
    apply continuousAt_pi.2
    intro l
    by_cases hlj : l = j
    · subst l
      simp only [Function.update_self]
      fun_prop
    · simpa only [Function.update_of_ne hlj] using continuousAt_const
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ),
      Function.update r j (r j + t) ∈ fieldStrictHeightCone h.depth :=
    hq.eventually ((isOpen_fieldStrictHeightCone _).mem_nhds (by simpa using hrs))
  revert hij hn
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij hn
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hpos
    rw [heightLevel_update h r hrs _ t ht i, hbase]
    exact magneticFieldLevel_terminal_update_le k hpos.le ht hs i hij
  · intro hij hn
    have hj : 0 < j.val := by change i.val < j.val at hij; omega
    have hgap : 0 < (fieldIncrement k j.succ).2 := hrs j.succ
    have hb : ∀ᶠ t in 𝓝 (0 : ℝ), t < (fieldIncrement k j.succ).2 :=
      Iio_mem_nhds hgap
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds,
      hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hbound hpos
    rw [heightLevel_update h r hrs _ t ht i, hbase]
    exact magneticFieldLevel_interior_update_le k j hj hpos.le hbound.le ht hs i hij

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order_oai := @OAI.InvariantIsing.magneticHeightLevel_coordinate_right_order_oai
