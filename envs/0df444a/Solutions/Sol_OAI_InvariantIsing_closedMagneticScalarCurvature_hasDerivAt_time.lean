-- Prove2me | solution 1 for OAI.InvariantIsing.closedMagneticScalarCurvature_hasDerivAt_time
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:25:10.438601+00:00
-- url     : https://prove2.me/submissions/b3644477-2308-43e9-b817-395a65d263df

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
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticTwoJetSpatial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial derivatives for the minimal bounded test data used by the
variance generator, including the ordinary scalar curvature test. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magneticTwoJet_average_hasDerivAt (P : MagneticContinuationJet)
    (A : MagneticContinuationTwoJet) (F : ℝ → ℝ)
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    HasDerivAt (fieldSpinTransition ζ v F A.value)
      (fieldTiltSpatial ζ v F P.value A.value A.first z) z := by
  obtain ⟨K, hK, bK⟩ := P.bValue
  obtain ⟨C, hC, bC⟩ := A.bValue
  obtain ⟨D, _, bD⟩ := A.bFirst
  exact hasDerivAt_fieldSpinTransition ζ v hF hG P.mValue A.mValue A.mFirst
    hK hC bK bC bD dF A.dValue z

lemma magneticTwoJet_spatial_hasDerivAt (P : MagneticContinuationJet)
    (A : MagneticContinuationTwoJet) (F : ℝ → ℝ)
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) (v : ℝ≥0) (z : ℝ) :
    HasDerivAt (fieldTiltSpatial ζ v F P.value A.value A.first)
      (magneticContinuationSecond ζ v F P.value P.first A.value A.first A.second z) z := by
  obtain ⟨K, hK, bK⟩ := P.bValue
  obtain ⟨L, hL, bL⟩ := P.bFirst
  obtain ⟨a, ha, ba⟩ := A.bValue
  obtain ⟨b, hb, bb⟩ := A.bFirst
  obtain ⟨c, _, bc⟩ := A.bSecond
  exact hasDerivAt_magneticContinuationSecond ζ v hF hG P.mValue P.mFirst
    A.mValue A.mFirst A.mSecond hK hL ha hb bK bL ba bb bc dF P.dValue
    A.dValue A.dFirst z

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

theorem magneticHeatCurvature_hasFDerivAt (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v : ℝ} (hv : 0 < v) (z : ℝ) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    HasFDerivAt (magneticHeatCurvature P F ζ)
      (pairLinear (J.third z / 2 + ζ * ((J.first z) ^ 2 + J.value z * J.second z))
        (J.second z)) (v, z) := by
  let w := Real.toNNReal v
  let J := P.transition P ζ w F hF hG dF
  let U := fieldSpinTransition ζ w F P.first
  let V := fieldSpinTransition ζ w F P.square.value
  let U1 := fieldTiltSpatial ζ w F P.value P.first P.second
  let V1 := fieldTiltSpatial ζ w F P.value P.square.value P.square.first
  let U2 := magneticContinuationSecond ζ w F P.value P.first P.first P.second P.third
  let V2 := magneticContinuationSecond ζ w F P.value P.first
    P.square.value P.square.first P.square.second
  have hU (x : ℝ) : HasDerivAt U (U1 x) x :=
    magneticTwoJet_average_hasDerivAt P P.slopeTwoJet F hF hG dF ζ w x
  have hV (x : ℝ) : HasDerivAt V (V1 x) x :=
    magneticTwoJet_average_hasDerivAt P P.square.toTwoJet F hF hG dF ζ w x
  have hU1 (x : ℝ) : HasDerivAt U1 (U2 x) x :=
    magneticTwoJet_spatial_hasDerivAt P P.slopeTwoJet F hF hG dF ζ w x
  have hV1 (x : ℝ) : HasDerivAt V1 (V2 x) x :=
    magneticTwoJet_spatial_hasDerivAt P P.square.toTwoJet F hF hG dF ζ w x
  have hJ : J.first = fun x => U x + ζ * (V x - (J.value x) ^ 2) := by
    funext x
    dsimp only [J, MagneticContinuationJet.transition, fieldTiltSpatial, U, V,
      MagneticContinuationJet.square]
    simp only [pow_two]
  have hr (x : ℝ) : U1 x + ζ * (V1 x - 2 * J.value x * J.first x) = J.second x := by
    have hd := (hU x).add (((hV x).sub ((J.dValue x).pow 2)).const_mul ζ)
    change HasDerivAt (fun y => U y + ζ * (V y - (J.value y) ^ 2))
      (U1 x + ζ * (V1 x - (2 : ℝ) * J.value x ^ (2 - 1) * J.first x)) x at hd
    rw [← hJ] at hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd.unique (J.dFirst x)
  have hR : (fun x => U1 x + ζ * (V1 x - 2 * J.value x * J.first x)) = J.second :=
    funext hr
  have hs : U2 z + ζ * (V2 z - 2 * (J.first z) ^ 2 -
      2 * J.value z * J.second z) = J.third z := by
    have hd := (hU1 z).add (((hV1 z).sub
      (((J.dValue z).mul (J.dFirst z)).const_mul 2)).const_mul ζ)
    have hd' : HasDerivAt
        (fun x => U1 x + ζ * (V1 x - 2 * J.value x * J.first x))
        (U2 z + ζ * (V2 z - 2 * (J.first z) ^ 2 -
          2 * J.value z * J.second z)) z := by
      refine (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)).congr_deriv (Eq.symm ?_)
      · beta_reduce
        dsimp
        ring
      · ring
    rw [hR] at hd'
    exact hd'.unique (J.dSecond z)
  have hM := magneticGaussianAverageTwo_hasFDerivAt_generator P P.toTwoJet F hF hG dF ζ hv z
  have hQ := magneticGaussianAverageTwo_hasFDerivAt_generator P P.slopeTwoJet F hF hG dF ζ hv z
  have hS := magneticGaussianAverageTwo_hasFDerivAt_generator P P.square.toTwoJet F hF hG dF ζ hv z
  change HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F P.value q.2)
    (pairLinear (J.second z / 2 + ζ * J.value z * J.first z) (J.first z)) (v, z) at hM
  change HasFDerivAt (fun q : ℝ × ℝ => gaussianTiltAverage q.1 ζ F P.first q.2)
    (pairLinear (U2 z / 2 + ζ * J.value z * U1 z) (U1 z)) (v, z) at hQ
  change HasFDerivAt (fun q : ℝ × ℝ =>
      gaussianTiltAverage q.1 ζ F (fun y => (P.value y) ^ 2) q.2)
    (pairLinear (V2 z / 2 + ζ * J.value z * V1 z) (V1 z)) (v, z) at hS
  have hm : gaussianTiltAverage v ζ F P.value z = J.value z :=
    congrFun (field_gaussianTiltAverage_eq_transition v ζ hF P.mValue) z
  have hd := hQ.add ((hS.sub (hM.pow 2)).const_mul ζ)
  change HasFDerivAt (magneticHeatCurvature P F ζ)
    (pairLinear (J.third z / 2 + ζ * ((J.first z) ^ 2 + J.value z * J.second z))
      (J.second z)) (v, z)
  refine hd.congr_fderiv (Eq.symm ?_)
  · apply ContinuousLinearMap.ext
    intro p
    simp only [add_apply, sub_apply, smul_apply, pairLinear_apply, smul_eq_mul]
    simp only [hm]
    have hrz := hr z
    linear_combination -(p.1 / 2) * hs - ζ * J.value z * p.1 * hrz - p.2 * hrz

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

theorem magneticHeatInverse_curvature_hasDerivAt (P : MagneticContinuationJet)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (dF : ∀ z, HasDerivAt F (P.value z) z) (ζ : ℝ) {v s : ℝ} (hv : 0 < v)
    {b : ℝ → ℝ} (hb : ContinuousAt b v)
    (he : ∀ᶠ t in 𝓝 v, magneticHeatMean P F ζ (t, b t) = s)
    (hq : (P.transition P ζ (Real.toNNReal v) F hF hG dF).first (b v) ≠ 0) :
    let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
    HasDerivAt (fun t => magneticHeatCurvature P F ζ (t, b t))
      ((J.first (b v)) ^ 2 / 2 *
        (J.third (b v) / (J.first (b v)) ^ 2 -
          (J.second (b v)) ^ 2 / (J.first (b v)) ^ 3) +
        ζ * (J.first (b v)) ^ 2) v := by
  let J := P.transition P ζ (Real.toNNReal v) F hF hG dF
  have hd := inverse_mean_curvature_variation hb hq
    (magneticHeatMean_hasFDerivAt P F hF hG dF ζ hv (b v)) he
    (magneticHeatCurvature_hasFDerivAt P F hF hG dF ζ hv (b v))
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

lemma magneticScalarInverseCurvature_variance_hasDerivAt (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ}
    (hζ : 0 ≤ ζ) (hs : |s| < 1) (hv : 0 < v) :
    let P := magneticLogCoshMeanJet L hL
    let F := fieldScalarValue L (fun x => Real.log (Real.cosh x))
    let hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
    let J := P.transition P ζ (Real.toNNReal v) F hF.1 hF.2
      (hasDerivAt_fieldScalarLogCosh L hL)
    let z := magneticScalarSlabBias L ζ v s
    HasDerivAt (fun t => magneticScalarInverseCurvature L hL ζ t s)
      ((J.first z) ^ 2 / 2 * (J.third z / (J.first z) ^ 2 -
        (J.second z) ^ 2 / (J.first z) ^ 3) + ζ * (J.first z) ^ 2) v := by
  let P := magneticLogCoshMeanJet L hL
  let F := fieldScalarValue L (fun x => Real.log (Real.cosh x))
  have hF := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hd : ∀ z, HasDerivAt F (P.value z) z := hasDerivAt_fieldScalarLogCosh L hL
  have hq : (P.transition P ζ (Real.toNNReal v) F hF.1 hF.2 hd).first
      (magneticScalarSlabBias L ζ v s) ≠ 0 := by
    have hp := (magneticScalarSlab_curvature_pos L hL hζ v
      (magneticScalarSlabBias L ζ v s)).ne'
    simpa only [P, MagneticContinuationJet.transition, fieldTiltSpatial,
      fieldCurvatureTransform, pow_two] using hp
  apply magneticHeatInverse_curvature_hasDerivAt P F hF.1 hF.2 hd ζ (s := s) hv
    (magneticScalarSlabBias_continuousAt_variance L hL hζ hs hv) ?_ hq
  exact Eventually.of_forall fun t => by
    rw [← magneticScalarSlabMean_eq L hL ζ t]
    exact magneticScalarSlabMean_bias L hL hζ hs t

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

lemma magneticScalarInverse_second_deriv (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    deriv (deriv (magneticScalarInverseCurvature L hL ζ v)) s =
      magneticScalarInverseSecond L hL ζ v s := by
  apply HasDerivAt.deriv
  apply (magneticScalarInverseSlope_hasDerivAt L hL hζ hs v).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2] with t ht
  exact (magneticScalarInverseCurvature_hasDerivAt_spin L hL hζ (abs_lt.mpr ht) v).deriv

/-- The actual inverse curvature solves the forward-variance version of
`mag:inverse-PDE` on every positive-variance slab. -/
theorem magneticScalarInverseCurvature_PDE (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s v : ℝ}
    (hζ : 0 ≤ ζ) (hs : |s| < 1) (hv : 0 < v) :
    HasDerivAt (fun t => magneticScalarInverseCurvature L hL ζ t s)
      ((magneticScalarInverseCurvature L hL ζ v s) ^ 2 / 2 *
        deriv (deriv (magneticScalarInverseCurvature L hL ζ v)) s +
        ζ * (magneticScalarInverseCurvature L hL ζ v s) ^ 2) v := by
  rw [magneticScalarInverse_second_deriv L hL hζ hs v,
    magneticScalarInverseCurvature_eq_jet]
  exact magneticScalarInverseCurvature_variance_hasDerivAt L hL hζ hs hv

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

lemma closedMagneticScalarCurvature_hasDerivAt_time_oai (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ v : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (s : ℝ) :
    HasDerivAt (fun t => closedMagneticScalarCurvature L hL ζ (t, s))
      (closedMagneticScalarTime L hL ζ (v, s)) v := by
  by_cases hs : |s| < 1
  · have hd := magneticScalarInverseCurvature_PDE L hL hζ hs hv
    rw [magneticScalarInverse_second_deriv L hL hζ hs v] at hd
    simpa only [closedMagneticScalarCurvature, closedMagneticScalarSecond,
      closedMagneticScalarTime, hs, ite_true, if_true] using hd
  · simpa only [closedMagneticScalarCurvature, closedMagneticScalarSecond,
      closedMagneticScalarTime, hs, ite_false, if_false, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, zero_mul, mul_zero, add_zero] using (hasDerivAt_const v (0 : ℝ))

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.closedMagneticScalarCurvature_hasDerivAt_time_oai := @OAI.InvariantIsing.closedMagneticScalarCurvature_hasDerivAt_time_oai
