-- Prove2me | solution 1 for OAI.InvariantIsing.magneticFieldLevel_radial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:00:14.175641+00:00
-- url     : https://prove2.me/submissions/ebe809ba-7ff7-47e5-92bd-3090df231e11

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
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
import Theorems.Thm_OAI_InvariantIsing_closedMagneticSquareContinuationSecond_nonneg
import Theorems.Thm_OAI_InvariantIsing_magneticScaledClosedCurvature_mono

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
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_FieldRadialCovariance
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial monotonicity of the actual finite-field overlap levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma scalarFieldIncrements_scale (h : FieldStep) (c : ℝ≥0) :
    scalarFieldIncrements (fieldScaleCovariance h c) =
      fieldScaleIncrements c (scalarFieldIncrements h) := by
  unfold scalarFieldIncrements fieldScaleIncrements
  rw [List.map_ofFn]
  congr 1
  funext i
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (fieldIncrement (fieldScaleCovariance h c) i.succ).2 =
      (c : ℝ) ^ 2 * (fieldIncrement h i.succ).2
    simp only [fieldIncrement, fieldScaleCovariance]
    split_ifs <;> ring

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

lemma closedMagneticScalarCurvature_le_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (q : ℝ × ℝ) (hq : q.2 ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ q ≤ 1 := by
  exact (closedMagneticScalarCurvature_le_spin_variance L hL hL1 hζ hζ1 q hq).trans
    (by linarith [sq_nonneg q.2])

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScaledSlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal scaled inverse curvature used in the radial comparison.
Time is physical variance; its scaling yields the coefficient αζ. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldScaleIncrements_exponent_le_one (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) :
    ∀ av ∈ fieldScaleIncrements c L, av.1 ≤ 1 := by
  intro av hav
  obtain ⟨bv, hb, rfl⟩ := List.mem_map.mp hav
  exact hL1 bv hb

lemma magneticScaledClosedCurvature_mem_interval (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1) (α : ℝ≥0)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (p : ℝ × ℝ)
    (hp : p.2 ∈ Icc (-1 : ℝ) 1) :
    magneticScaledClosedCurvature L hL α ζ p ∈ Icc 0 (α : ℝ) := by
  have h0 := closedMagneticScalarCurvature_nonneg (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) hζ ((α : ℝ) ^ 2 * p.1, p.2)
  have h1 := closedMagneticScalarCurvature_le_one (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (fieldScaleIncrements_exponent_le_one α L hL1)
    hζ hζ1 ((α : ℝ) ^ 2 * p.1, p.2) hp
  exact ⟨mul_nonneg α.coe_nonneg h0, (mul_le_mul_of_nonneg_left h1 α.coe_nonneg).trans_eq (mul_one _)⟩

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

lemma magneticScaledClosedCurvature_endpoints (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ v : ℝ) :
    magneticScaledClosedCurvature L hL α ζ (v, -1) = 0 ∧
      magneticScaledClosedCurvature L hL α ζ (v, 1) = 0 := by
  obtain ⟨hl, hr⟩ := closedMagneticScalarCurvature_endpoints (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * v)
  simp only [magneticScaledClosedCurvature, hl, hr, mul_zero, and_self]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScaledContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual square continuation in the rescaled physical variance.
Its diffusion coefficient is the rescaled inverse curvature. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma magneticScaledSquareContinuation_continuousOn (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    {ζ : ℝ} (hζ : 0 ≤ ζ) :
    ContinuousOn (magneticScaledSquareContinuation L hL α i ζ)
      (univ ×ˢ Icc (-1 : ℝ) 1) := by
  have hc := continuousOn_closedMagneticContinuation (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    (magneticScalarSquareFourJet_sandwich _ _ _) hζ
  have hm : Continuous (fun p : ℝ × ℝ => ((α : ℝ) ^ 2 * p.1, p.2)) := by fun_prop
  exact hc.comp hm.continuousOn (fun p hp => ⟨mem_univ _, hp.2⟩)

lemma magneticScaledSquareContinuation_hasDerivAt_time (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {α : ℝ≥0} (hα : 0 < α)
    (i : Fin (L.length + 1)) {ζ v : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (s : ℝ) :
    HasDerivAt (fun t => magneticScaledSquareContinuation L hL α i ζ (t, s))
      (magneticScaledSquareTime L hL α i ζ (v, s)) v := by
  have hαr : 0 < (α : ℝ) := hα
  have hd := closedMagneticContinuation_hasDerivAt_time (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    hζ (mul_pos (sq_pos_of_pos hαr) hv) s
  have ht := hd.comp v ((hasDerivAt_id v).const_mul ((α : ℝ) ^ 2))
  refine ht.congr_deriv (Eq.symm ?_)
  · simp only [magneticScaledSquareTime, magneticScaledClosedCurvature,
      magneticScaledSquareSecond, closedMagneticContinuationTime]
    ring

lemma magneticScaledSquareContinuation_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => magneticScaledSquareContinuation L hL α i ζ (v, u))
      (magneticScaledSquareSlope L hL α i ζ (v, s)) s :=
  closedMagneticContinuation_hasDerivAt_spin (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    hζ hs ((α : ℝ) ^ 2 * v)

lemma magneticScaledSquareSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => magneticScaledSquareSlope L hL α i ζ (v, u))
      (magneticScaledSquareSecond L hL α i ζ (v, s)) s :=
  closedMagneticContinuationSlope_hasDerivAt_spin (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    hζ hs ((α : ℝ) ^ 2 * v)

lemma magneticScaledSquareSecond_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (α : ℝ≥0) (i : Fin (L.length + 1)) {ζ v : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (s : ℝ) :
    0 ≤ magneticScaledSquareSecond L hL α i ζ (v, s) :=
  closedMagneticSquareContinuationSecond_nonneg (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (fieldScaleIncrements_exponent_le_one α L hL1)
    _ hζ hζ1 (mul_nonneg (sq_nonneg _) hv) s

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

lemma magneticScaledSquareContinuation_zero_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) {ζ s : ℝ} (hζ : 0 ≤ ζ)
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledSquareContinuation L hL α 0 ζ (0, s) = s ^ 2 := by
  simpa only [magneticScaledSquareContinuation, magneticScaledSquareJet, mul_zero,
    Fin.cast_zero] using
    closedMagneticSquareContinuation_zero_initial (fieldScaleIncrements α L)
      (fieldScaleIncrements_positive α L hL) hζ hs

lemma magneticScaledSquareContinuation_cons_initial (av : ℝ × ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (hL : ∀ bv ∈ av :: L, 0 < bv.1)
    (α : ℝ≥0) (i : Fin (L.length + 1)) (ζ s : ℝ) :
    magneticScaledSquareContinuation (av :: L) hL α i.succ ζ (0, s) =
      magneticScaledSquareContinuation L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        α i av.1 ((av.2 : ℝ), s) := by
  have hi : (Fin.cast (by simp only [fieldScaleIncrements_length, List.length_cons]) i.succ :
      Fin ((fieldScaleIncrements α (av :: L)).length + 1)) =
      (Fin.cast (by rw [fieldScaleIncrements_length]) i :
        Fin ((fieldScaleIncrements α L).length + 1)).succ := by
    apply Fin.ext
    rfl
  unfold magneticScaledSquareContinuation magneticScaledSquareJet
  rw [hi]
  convert closedMagneticSquareContinuation_cons_initial (av.1, α ^ 2 * av.2)
      (fieldScaleIncrements α L) (fieldScaleIncrements_positive α (av :: L) hL)
      (Fin.cast (by rw [fieldScaleIncrements_length]) i) ζ s using 1 <;>
    simp only [fieldScaleIncrements, List.map_cons, mul_zero, NNReal.coe_mul, NNReal.coe_pow]
  all_goals rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticScaledSquareOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial order for the actual conditional square means in inverse
magnetization coordinates, including a final ordinary Gaussian level. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma magneticScaledSquareContinuation_mono_of_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) (i : Fin (L.length + 1))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      magneticScaledSquareContinuation L hL α i ζ (0, u) ≤
        magneticScaledSquareContinuation L hL β i ζ (0, u))
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledSquareContinuation L hL α i ζ (v, s) ≤
      magneticScaledSquareContinuation L hL β i ζ (v, s) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hall := magnetic_continuation_coefficient_comparison hv
    (magneticScaledSquareContinuation L hL α i ζ) (magneticScaledSquareTime L hL α i ζ)
    (magneticScaledSquareSlope L hL α i ζ) (magneticScaledSquareSecond L hL α i ζ)
    (magneticScaledSquareContinuation L hL β i ζ) (magneticScaledSquareTime L hL β i ζ)
    (magneticScaledSquareSlope L hL β i ζ) (magneticScaledSquareSecond L hL β i ζ)
    (magneticScaledClosedCurvature L hL α ζ) (magneticScaledClosedCurvature L hL β ζ)
    ((magneticScaledSquareContinuation_continuousOn L hL α i hζ).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩))
    ((magneticScaledSquareContinuation_continuousOn L hL β i hζ).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩)) hinit
    (fun t ht u _ => (magneticScaledSquareContinuation_hasDerivAt_time L hL hα i hζ ht.1 u).hasDerivWithinAt)
    (fun t ht u _ => (magneticScaledSquareContinuation_hasDerivAt_time L hL hβ i hζ ht.1 u).hasDerivWithinAt)
    (fun t _ u hu => magneticScaledSquareContinuation_hasDerivAt_spin L hL α i hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledSquareContinuation_hasDerivAt_spin L hL β i hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledSquareSlope_hasDerivAt_spin L hL α i hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledSquareSlope_hasDerivAt_spin L hL β i hζ (abs_lt.mpr hu) t)
    (fun p hp => (magneticScaledClosedCurvature_mem_interval L hL hL1 α hζ hζ1 p hp.2).1)
    (fun p hp => magneticScaledClosedCurvature_mono L hL hL1 hα hαβ hζ hζ1 hp.1.1 hp.2)
    (fun p hp => magneticScaledSquareSecond_nonneg L hL hL1 α i hζ hζ1 hp.1.1.le p.2)
    (fun t _ => magneticScaledClosedCurvature_endpoints L hL β ζ t)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact hall (v, s) ⟨⟨hv, le_rfl⟩, hs⟩

theorem magneticScaledSquareContinuation_mono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) (i : Fin (L.length + 1))
    {ζ v s : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledSquareContinuation L hL α i ζ (v, s) ≤
      magneticScaledSquareContinuation L hL β i ζ (v, s) := by
  induction L generalizing ζ v s with
  | nil =>
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      have h := i.isLt
      change i.val < 1 at h
      omega
    subst i
    apply magneticScaledSquareContinuation_mono_of_initial [] hL hL1 hα hαβ 0 hζ hζ1 ?_ hv hs
    intro u hu
    rw [magneticScaledSquareContinuation_zero_initial [] hL α hζ hu,
      magneticScaledSquareContinuation_zero_initial [] hL β hζ hu]
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply magneticScaledSquareContinuation_mono_of_initial (av :: L) hL hL1 hα hαβ 0 hζ hζ1 ?_ hv hs
      intro u hu
      rw [magneticScaledSquareContinuation_zero_initial (av :: L) hL α hζ hu,
        magneticScaledSquareContinuation_zero_initial (av :: L) hL β hζ hu]
    · apply magneticScaledSquareContinuation_mono_of_initial (av :: L) hL hL1 hα hαβ j.succ hζ hζ1 ?_ hv hs
      intro u hu
      rw [magneticScaledSquareContinuation_cons_initial,
        magneticScaledSquareContinuation_cons_initial]
      exact ih (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        (fun bv hb => hL1 bv (List.mem_cons_of_mem av hb)) j
        (hL av List.mem_cons_self).le (hL1 av List.mem_cons_self) av.2.property hu

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticFieldRadial
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalSpinLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability
attribute [-simp] _root_.OAI.InvariantIsing.mem_fieldCutSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Radial monotonicity of the finite prescribed-magnetization overlap.
The root bias is chosen at the fixed prescribed magnetization at every scale. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma squareContinuation_congr_list {L M : List (ℝ × ℝ≥0)} (he : L = M)
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (i : Fin (L.length + 1)) (j : Fin (M.length + 1)) (hij : i.val = j.val)
    (ζ v s : ℝ) :
    magneticScalarSlabContinuation L (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ v s =
      magneticScalarSlabContinuation M (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ v s := by
  subst M
  have hi : i = j := Fin.ext hij
  subst j
  rfl

lemma magneticFieldLevel_eq_scaled (h : FieldStep) (c : ℝ≥0)
    (i : Fin (h.depth + 1)) {s : ℝ} (hs : |s| < 1) :
    magneticFieldLevel (fieldScaleCovariance h c) s i =
      magneticScaledSquareContinuation (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
        c (Fin.cast (by rw [scalarFieldIncrements_length]) i) 0 (h.height 0, s) := by
  rw [congrFun (magneticFieldLevel_eq_slab (fieldScaleCovariance h c) i) s]
  unfold magneticScaledSquareContinuation magneticScaledSquareJet
  rw [closedMagneticContinuation, ite_eq_left hs]
  exact squareContinuation_congr_list (scalarFieldIncrements_scale h c)
    (scalarFieldIncrements_positive (fieldScaleCovariance h c))
    (fieldScaleIncrements_positive c (scalarFieldIncrements h) (scalarFieldIncrements_positive h))
    _ _ rfl 0 ((c : ℝ) ^ 2 * h.height 0) s

theorem magneticFieldLevel_radial_oai (h : FieldStep) {α β : ℝ≥0}
    (hα : 0 < α) (hαβ : α ≤ β) (i : Fin (h.depth + 1)) {s : ℝ} (hs : |s| < 1) :
    magneticFieldLevel (fieldScaleCovariance h α) s i ≤
      magneticFieldLevel (fieldScaleCovariance h β) s i := by
  rw [magneticFieldLevel_eq_scaled h α i hs, magneticFieldLevel_eq_scaled h β i hs]
  exact magneticScaledSquareContinuation_mono (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h) (scalarFieldIncrements_exponent_le_one h)
    hα hαβ _ (by norm_num) (by norm_num) (h.nonneg 0)
    ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.magneticFieldLevel_radial_oai := @OAI.InvariantIsing.magneticFieldLevel_radial_oai
