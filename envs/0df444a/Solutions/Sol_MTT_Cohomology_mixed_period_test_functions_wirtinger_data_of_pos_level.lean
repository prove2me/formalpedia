-- Prove2me | solution 1 for MTT.Cohomology.mixed_period_test_functions_wirtinger_data_of_pos_level
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-08T08:05:50.790012+00:00
-- url     : https://prove2.me/submissions/e0c42735-ff3f-4268-8af1-6d8d282f3c9e

import Theorems.Thm_MTT_Cohomology_mixed_period_test_functions_local_equivariant
import Theorems.Thm_MTT_Cohomology_mixed_period_test_functions_cusp_decay_of_pos_level
import Theorems.Thm_MTT_Cohomology_mixed_period_test_functions_tile_integrable_of_pos_level

set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ∃ A₁ A₂ : ℂ → ℂ,
      ContDiffOn ℝ 1 A₁ upperHalfPlaneSet ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
        A₁ ((γ • τ : ℍ) : ℂ) =
          (starRingEnd ℂ (denom γ τ)) ^ 2 * A₁ τ) ∧
      (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
        fun τ : ℍ ↦ A₁ ((σ • τ : ℍ) : ℂ) *
          ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
      (∀ σ ∈ R, IntegrableOn
        (fun z ↦ (1 / 2 : ℂ) *
          (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I))
        ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) ∧
      (∀ z : ℍ,
        (1 / 2 : ℂ) *
            (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I) =
          periodContraction (k - 2)
            (g z • periodPower (k - 2) (z : ℂ))
            (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) ∧
      ContDiffOn ℝ 1 A₂ upperHalfPlaneSet ∧
      (∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ,
        A₂ ((γ • τ : ℍ) : ℂ) =
          (starRingEnd ℂ (denom γ τ)) ^ 2 * A₂ τ) ∧
      (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
        fun τ : ℍ ↦ A₂ ((σ • τ : ℍ) : ℂ) *
          ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
      (∀ σ ∈ R, IntegrableOn
        (fun z ↦ (1 / 2 : ℂ) *
          (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I))
        ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume) ∧
      (∀ z : ℍ,
        (1 / 2 : ℂ) *
            (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I) =
          -conj (periodContraction (k - 2)
            (q z • periodPower (k - 2) (z : ℂ))
            (conj (v z) • periodPower (k - 2) (conj (z : ℂ))))) := by
  let A₁ : ℂ → ℂ := fun z =>
    periodContraction (k - 2) (U z)
      (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
  let A₂ : ℂ → ℂ := fun z => conj <|
    periodContraction (k - 2)
      (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
  have hlocal :=
    MTT.Cohomology.mixed_period_test_functions_local_equivariant hk g v q U hU
  have hdecay :=
    MTT.Cohomology.mixed_period_test_functions_cusp_decay_of_pos_level hN hk g v q U hU
  have hint :=
    MTT.Cohomology.mixed_period_test_functions_tile_integrable_of_pos_level
      hN hk g v q U hU R
  dsimp only at hlocal hdecay hint
  rcases hlocal with ⟨hC₁, hE₁, hD₁, hC₂, hE₂, hD₂⟩
  rcases hdecay with ⟨hZ₁, hZ₂⟩
  rcases hint with ⟨hI₁, hI₂⟩
  exact ⟨A₁, A₂, hC₁, hE₁, hZ₁, hI₁, hD₁,
    hC₂, hE₂, hZ₂, hI₂, hD₂⟩
