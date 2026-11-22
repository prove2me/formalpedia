-- Prove2me | solution 1 for InfoLossLAR.WorstCase.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:19:00.129418+00:00
-- url     : https://prove2.me/submissions/1593561b-2563-4ada-b520-a2b33b8de15f

import Mathlib

set_option autoImplicit false

open MeasureTheory
namespace MilestoneCalibration
variable {Coefficients : Type*} [NormedAddCommGroup Coefficients] [NormedSpace ℝ Coefficients]
theorem coefficient_norm_le (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) (coefficient : Coefficients) :
    ‖coefficient‖ ≤ ‖operator coefficient‖ / (1 - theta) := by
  have hpoint : ‖(operator - ContinuousLinearMap.id ℝ Coefficients) coefficient‖ ≤
      theta * ‖coefficient‖ :=
    ((operator - ContinuousLinearMap.id ℝ Coefficients).le_opNorm coefficient).trans
      (mul_le_mul_of_nonneg_right hdefect (norm_nonneg coefficient))
  have htriangle : ‖coefficient‖ ≤ ‖operator coefficient‖ +
      ‖(operator - ContinuousLinearMap.id ℝ Coefficients) coefficient‖ := by
    calc
      ‖coefficient‖ =
          ‖operator coefficient -
            (operator - ContinuousLinearMap.id ℝ Coefficients) coefficient‖ := by simp
      _ ≤ _ := norm_sub_le _ _
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  nlinarith

theorem stable_operator_injective (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) : Function.Injective operator := by
  intro first second hequal
  have hnorm := coefficient_norm_le operator theta hdefect hgap (first - second)
  have hzero : operator (first - second) = 0 := by simp [map_sub, hequal]
  rw [hzero, norm_zero, zero_div] at hnorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

/-- Finite dimensionality turns the proved injectivity into
surjectivity; invertibility is not an input assumption. -/
theorem stable_operator_bijective [FiniteDimensional ℝ Coefficients]
    (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) : Function.Bijective operator := by
  have hinjective := stable_operator_injective operator theta hdefect hgap
  exact ⟨hinjective, LinearMap.surjective_of_injective (f := operator.toLinearMap) hinjective⟩

theorem coefficient_equation_existsUnique [FiniteDimensional ℝ Coefficients]
    (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) (target : Coefficients) :
    ∃! coefficient, operator coefficient = target := by
  have hbijective := stable_operator_bijective operator theta hdefect hgap
  obtain ⟨coefficient, hcoefficient⟩ := hbijective.2 target
  exact ⟨coefficient, hcoefficient,
    fun other hother => hbijective.1 (hother.trans hcoefficient.symm)⟩

/-- Stability is measured by the actual residual of any reference
coefficient, without requiring the target itself to be small. -/
theorem reference_correction_bound (operator : Coefficients →L[ℝ] Coefficients)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) (coefficient target : Coefficients)
    (hcoefficient : operator coefficient = target) (reference : Coefficients) :
    ‖coefficient - reference‖ ≤ ‖target - operator reference‖ / (1 - theta) := by
  simpa only [map_sub, hcoefficient] using
    coefficient_norm_le operator theta hdefect hgap (coefficient - reference)

variable {Weights Outputs : Type*} [AddCommGroup Weights] [Module ℝ Weights]
  [AddCommGroup Outputs] [Module ℝ Outputs]

/-- The current manuscript's stable calibration theorem. The
factorization is a relation among actual linear maps, and the reference
evaluation is not assumed to have an inverse. -/
theorem stable_finite_dimensional_calibration
    [FiniteDimensional ℝ Coefficients]
    (operator : Coefficients →L[ℝ] Coefficients)
    (synthesis : Coefficients →ₗ[ℝ] Weights) (response : Weights →ₗ[ℝ] Outputs)
    (evaluation : Coefficients →ₗ[ℝ] Outputs)
    (hresponse : response.comp synthesis = evaluation.comp operator.toLinearMap)
    (theta : ℝ) (hdefect : ‖operator - ContinuousLinearMap.id ℝ Coefficients‖ ≤ theta)
    (hgap : theta < 1) (target : Coefficients) :
    ∃ coefficient,
      operator coefficient = target ∧
      (∀ other, operator other = target → other = coefficient) ∧
      response (synthesis coefficient) = evaluation target ∧
      ∀ reference, ‖coefficient - reference‖ ≤
        ‖target - operator reference‖ / (1 - theta) := by
  obtain ⟨coefficient, hcoefficient, hunique⟩ :=
    coefficient_equation_existsUnique operator theta hdefect hgap target
  refine ⟨coefficient, hcoefficient, hunique, ?_, ?_⟩
  · have hfactor := LinearMap.congr_fun hresponse coefficient
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hcoefficient] using hfactor
  · exact reference_correction_bound operator theta hdefect hgap coefficient target hcoefficient


end MilestoneCalibration

open MilestoneCalibration

theorem solution {V Y Ω : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ψ : V →ₗ[ℝ] Lp ℝ 1 μ) (M : Lp ℝ 1 μ →ₗ[ℝ] Y) (E : V →ₗ[ℝ] Y) (A : V →L[ℝ] V) (κ : ℝ)
    (hfac : M ∘ₗ Ψ = E ∘ₗ (A : V →ₗ[ℝ] V)) (hA : ‖A - ContinuousLinearMap.id ℝ V‖ ≤ κ)
    (hκ : κ < 1) (τ : V) :
    ∃ z : V, (A z = τ ∧ ∀ z' : V, A z' = τ → z' = z) ∧
      M (Ψ z) = E τ ∧
      (∀ z₀ : V, ‖z - z₀‖ ≤ ‖τ - A z₀‖ / (1 - κ)) ∧
      (∀ m : Y →ₗ[ℝ] ℝ, (∀ w' : Lp ℝ 1 μ, m (M w') = ∫ ω, w' ω ∂μ) → m (E τ) = 1 →
        ∫ ω, (Ψ z) ω ∂μ = 1) := by
  obtain ⟨z, hz, huniq, hw, herr⟩ := stable_finite_dimensional_calibration A Ψ M E
    hfac κ hA hκ τ
  refine ⟨z, ⟨hz, huniq⟩, hw, herr, ?_⟩
  intro m hmass htarget
  calc
    ∫ ω, (Ψ z) ω ∂μ = m (M (Ψ z)) := (hmass (Ψ z)).symm
    _ = m (E τ) := congrArg m hw
    _ = 1 := htarget
