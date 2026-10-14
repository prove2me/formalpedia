-- Prove2me | solution 1 for IntroMatrixConc.GaussianSeries.jensen_lower
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T03:32:48.200635+00:00
-- url     : https://prove2.me/submissions/0ee5edd5-3699-464a-b809-fa0ea11f7623

import Mathlib
import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator ENNReal
namespace TroppGaussianLower
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {d₁ d₂ : ℕ}

lemma scalar_memLp (g : Ω → ℝ) (hm : Measurable g) (hl : standardGaussianLaw μ g) :
    MemLp g 2 μ := by
  have h : MemLp id 2 (Measure.map g μ) := by
    rw [hl]
    exact memLp_id_gaussianReal' 2 (by norm_num)
  simpa only [Function.comp_def, id_eq] using h.comp_of_map hm.aemeasurable

lemma series_memLp {N : ℕ} (B : Fin N → Matrix (Fin d₁) (Fin d₂) ℂ)
    (g : Fin N → Ω → ℝ) (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, standardGaussianLaw μ (g k)) :
    MemLp (fun ω => ∑ k, g k ω • B k) 2 μ := by
  apply memLp_finsetSum Finset.univ
  intro k hk
  have hc : MemLp (fun _ : Ω => B k) ∞ μ := memLp_const _
  exact hc.smul (scalar_memLp μ (g k) (hm k) (hl k))

lemma right_gram_bound (A : Matrix (Fin d₁) (Fin d₂) ℂ) :
    ‖A * A.conjTranspose‖ ≤ ‖A‖ ^ 2 := by
  simpa only [Matrix.l2_opNorm_conjTranspose, pow_two] using Matrix.l2_opNorm_mul A A.conjTranspose

lemma left_gram_bound (A : Matrix (Fin d₁) (Fin d₂) ℂ) :
    ‖A.conjTranspose * A‖ ≤ ‖A‖ ^ 2 := by
  simpa only [Matrix.l2_opNorm_conjTranspose, pow_two] using Matrix.l2_opNorm_mul A.conjTranspose A

lemma variance_le (Z : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (hm : Measurable Z) (hZ : MemLp Z 2 μ) :
    rectSecondMoment μ Z ≤ ∫ ω, spectralNorm (Z ω) ^ 2 ∂μ := by
  have hi : Integrable (fun ω => ‖Z ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).mp hZ
  have hR : AEStronglyMeasurable (fun ω => Z ω * (Z ω).conjTranspose) μ := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hL : AEStronglyMeasurable (fun ω => (Z ω).conjTranspose * Z ω) μ := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hiR := hi.mono' hR (Filter.Eventually.of_forall (fun ω => right_gram_bound (Z ω)))
  have hiL := hi.mono' hL (Filter.Eventually.of_forall (fun ω => left_gram_bound (Z ω)))
  unfold rectSecondMoment TroppMatrixConcentration.spectralNorm
  apply max_le
  · exact (norm_integral_le_integral_norm _).trans
      (integral_mono hiR.norm hi (fun ω => right_gram_bound (Z ω)))
  · exact (norm_integral_le_integral_norm _).trans
      (integral_mono hiL.norm hi (fun ω => left_gram_bound (Z ω)))

end TroppGaussianLower

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ N : ℕ} [NeZero d₁] [NeZero d₂]
    (B : Fin N → Matrix (Fin d₁) (Fin d₂) ℂ)
    (g : Fin N → Ω → ℝ)
    (hMeas : ∀ k, Measurable (g k))
    (hIndep : iIndepFun g μ)
    (hLaw : ∀ k, standardGaussianLaw μ (g k)) :
    let Z := fun ω => ∑ k, g k ω • B k
    rectSecondMoment μ Z ≤ ∫ ω, spectralNorm (Z ω) ^ 2 ∂μ := by
  dsimp only
  apply TroppGaussianLower.variance_le μ _ (by fun_prop)
  exact TroppGaussianLower.series_memLp μ B g hMeas hLaw

#print axioms solution
