-- Prove2me | solution 1 for MTT.Cohomology.period_pairings_eq_wirtinger_sums_of_weight_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-08T07:25:14.953449+00:00
-- url     : https://prove2.me/submissions/7aac4487-175e-4753-ac28-efd3cd33877d

import Theorems.Thm_MTT_Cohomology_periodPairing_eq_transversal_integral_of_weight_ge_two

set_option autoImplicit false
noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hR : Subgroup.IsComplement
      (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))
    {A₁ A₂ : ℂ → ℂ}
    (hint₁ : ∀ σ ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) *
        (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I))
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume)
    (hint₂ : ∀ σ ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) *
        (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I))
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume)
    (hderiv₁ : ∀ z : ℍ,
      (1 / 2 : ℂ) *
          (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I) =
        periodContraction (k - 2)
          (g z • periodPower (k - 2) (z : ℂ))
          (conj (q z) • periodPower (k - 2) (conj (z : ℂ))))
    (hderiv₂ : ∀ z : ℍ,
      (1 / 2 : ℂ) *
          (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I) =
        -conj (periodContraction (k - 2)
          (q z • periodPower (k - 2) (z : ℂ))
          (conj (v z) • periodPower (k - 2) (conj (z : ℂ))))) :
    periodPairing N (k - 2) g q =
        ∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟,
          (1 / 2 : ℂ) *
            (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I) ∧
    periodPairing N (k - 2) q v =
        -conj (∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟,
          (1 / 2 : ℂ) *
            (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I)) := by
  let D₁ : ℂ → ℂ := fun z => (1 / 2 : ℂ) *
    (fderiv ℝ A₁ z 1 - Complex.I * fderiv ℝ A₁ z Complex.I)
  let D₂ : ℂ → ℂ := fun z => (1 / 2 : ℂ) *
    (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I)
  constructor
  · exact periodPairing_eq_transversal_integral_of_weight_ge_two
      hk g q R hR D₁ hint₁ hderiv₁
  · have hintD : ∀ σ ∈ R, IntegrableOn (fun z => -conj (D₂ z))
        ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume := by
      intro σ hσ
      change IntegrableOn (fun z => -conj ((1 / 2 : ℂ) *
        (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I))) _ volume
      exact (Complex.conjCLE.toContinuousLinearMap.integrableOn_comp (hint₂ σ hσ)).neg
    have hD : ∀ z : ℍ, -conj (D₂ z) =
        periodContraction (k - 2)
          (q z • periodPower (k - 2) (z : ℂ))
          (conj (v z) • periodPower (k - 2) (conj (z : ℂ))) := by
      intro z
      change -conj ((1 / 2 : ℂ) *
        (fderiv ℝ A₂ z 1 - Complex.I * fderiv ℝ A₂ z Complex.I)) = _
      rw [hderiv₂ z]
      simp
    calc
      periodPairing N (k - 2) q v =
          ∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟,
            -conj (D₂ z) :=
        periodPairing_eq_transversal_integral_of_weight_ge_two hk q v R hR _ hintD hD
      _ = -conj (∑ σ ∈ R, ∫ z in
          (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟, D₂ z) := by
        simp_rw [integral_neg, integral_conj]
        simp
