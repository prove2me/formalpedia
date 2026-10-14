-- Prove2me | solution 1 for IntroMatrixConc.Sampling.summand_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T05:59:22.079232+00:00
-- url     : https://prove2.me/submissions/64f5969a-502b-49ca-b655-be4ed49cad27

import Definitions.Def_IntroMatrixConc_Sampling_Defs
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator
noncomputable section
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ n : ℕ} [NeZero d₁] [NeZero d₂]
    (R₀ : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (R : Fin n → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (B : Matrix (Fin d₁) (Fin d₂) ℂ) (L : ℝ)
    (hn : 0 < n)
    (hMeas₀ : Measurable R₀) (hMeas : ∀ k, Measurable (R k))
    (hIndep : iIndepFun R μ)
    (hCopies : ∀ k, IdentDistrib (R k) R₀ μ μ)
    (hMean : (∫ ω, R₀ ω ∂μ) = B)
    (hBound : ∀ᵐ ω ∂μ, spectralNorm (R₀ ω) ≤ L) :
    let S := fun (k : Fin n) (ω : Ω) => ((n : ℝ)⁻¹) • (R k ω - B)
    iIndepFun S μ ∧ (∀ k j, IdentDistrib (S k) (S j) μ μ) ∧
    (∀ k, (∫ ω, S k ω ∂μ) = 0) ∧
    ∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω) ≤ 2 * L / n := by
  classical

  let c : ℝ := (n : ℝ)⁻¹
  let f : Matrix (Fin d₁) (Fin d₂) ℂ → Matrix (Fin d₁) (Fin d₂) ℂ := fun A => c • (A - B)
  have hf : Measurable f := by unfold f; fun_prop
  have hRi : ∀ k, Integrable (R k) μ := by
    intro k
    apply (integrable_const L).mono' (hMeas k).aestronglyMeasurable
    exact (hCopies k).symm.ae_snd (p := fun A : Matrix (Fin d₁) (Fin d₂) ℂ => ‖A‖ ≤ L) (isClosed_le continuous_norm continuous_const).measurableSet hBound
  have hBi : ‖B‖ ≤ L := by
    rw [← hMean]
    have h := norm_integral_le_of_norm_le_const hBound
    simpa [Measure.real] using h
  have hcopybound : ∀ k, ∀ᵐ ω ∂μ, ‖R k ω‖ ≤ L := by
    intro k
    exact (hCopies k).symm.ae_snd (p := fun A : Matrix (Fin d₁) (Fin d₂) ℂ => ‖A‖ ≤ L) (isClosed_le continuous_norm continuous_const).measurableSet hBound
  refine ⟨hIndep.comp (fun _ => f) (fun _ => hf), ?_, ?_, ?_⟩
  · intro k j
    exact ((hCopies k).trans (hCopies j).symm).comp hf
  · intro k
    rw [integral_smul, integral_sub (hRi k) (integrable_const B), (hCopies k).integral_eq, hMean]
    simp
  · intro k
    filter_upwards [hcopybound k] with ω hw
    change ‖c • (R k ω - B)‖ ≤ 2 * L / n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    have hsub : ‖R k ω - B‖ ≤ 2 * L := (norm_sub_le _ _).trans (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr (Nat.cast_nonneg n))
    simpa [c, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

#print axioms solution
