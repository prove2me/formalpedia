-- Prove2me | solution 1 for MasulloRH.trace_formula_inversion_odd
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:49:07.679391+00:00
-- url     : https://prove2.me/submissions/b37aa33e-0619-48fe-93c7-666558d34809

import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_RiemannZetaOrders_zeta_analyticOrderAt_one_sub

set_option autoImplicit false
open MasulloRH MeasureTheory Set Filter

private theorem odd_mellin {φ : ℝ → ℂ} (hodd : ∀ t : ℝ, 0 < t → φ t⁻¹ = -φ t) (s : ℂ) :
    mellin φ (-s) = -mellin φ s := by
  rw [← mellin_comp_inv]
  unfold mellin
  rw [← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp [hodd t ht]

private def reflectZero {α : ℝ} (ρ : ZetaZerosInTraceStrip α) : ZetaZerosInTraceStrip α := ⟨1 - (ρ : ℂ), by
  obtain ⟨hz, hp, hq, hw⟩ := ρ.property
  have hr : (ρ : ℂ) ≠ 1 := fun he => by simp [he] at hq
  have href := RiemannZetaOrders.zeta_analyticOrderAt_one_sub hp hq
  have hord := analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta _ hr, hz⟩
  refine ⟨(analyticOrderAt_ne_zero.mp (href ▸ hord)).2, ?_, ?_, ?_⟩
  · simp only [Complex.sub_re, Complex.one_re]; linarith
  · simp only [Complex.sub_re, Complex.one_re]; linarith
  · rw [Complex.sub_re, Complex.one_re, show 1 - (ρ : ℂ).re - 1/2 = -((ρ : ℂ).re - 1/2) by ring, abs_neg]
    exact hw⟩

private theorem odd_strip_sum (α : ℝ) (φ : ℝ → ℂ) (hodd : ∀ t : ℝ, 0 < t → φ t⁻¹ = -φ t) :
    (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) = 0 := by
  have hsq (ρ : ZetaZerosInTraceStrip α) : reflectZero (reflectZero ρ) = ρ := by
    apply Subtype.ext
    change 1 - (1 - (ρ : ℂ)) = _
    ring
  let e : ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip α := ⟨reflectZero, reflectZero, hsq, hsq⟩
  have hflip (ρ : ZetaZerosInTraceStrip α) : zetaTraceTerm φ α (e ρ) = -zetaTraceTerm φ α ρ := by
    unfold zetaTraceTerm analyticOrderNatAt
    change ((analyticOrderAt riemannZeta (1 - (ρ : ℂ))).toNat : ℂ) *
      mellin φ (1 - (ρ : ℂ) - 1/2) = _
    rw [RiemannZetaOrders.zeta_analyticOrderAt_one_sub ρ.property.2.1 ρ.property.2.2.1,
      show 1 - (ρ : ℂ) - 1/2 = -((ρ : ℂ)-1/2) by ring, odd_mellin hodd]
    ring
  have h := e.tsum_eq (zetaTraceTerm φ α)
  simp only [hflip, tsum_neg] at h
  linear_combination -h / 2

/-- For an inversion-odd test, each side of the strip trace identity vanishes. -/
theorem solution (α : ℝ) (_hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (hodd : ∀ t : ℝ, 0 < t → φ t⁻¹ = -φ t) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  obtain ⟨hi, hp, hz, _⟩ := trace_window_comparison α φ hφ
  refine ⟨hi, hp, hz, ?_⟩
  have ha : (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    simp [realTraceIntegrand, hodd t (zero_lt_one.trans ht)]
  have hpr (i : Nat.Primes × ℕ) : primePowerTraceTerm φ i = 0 := by
    have hpos : 0 < ((i.1 : ℕ) : ℝ) ^ (i.2+1) :=
      pow_pos (by exact_mod_cast i.1.property.pos) _
    simp [primePowerTraceTerm, hodd _ hpos]
  rw [ha, odd_strip_sum α φ hodd, show (-1/2 : ℂ) = -(1/2) by ring, odd_mellin hodd]
  simp [hpr]
