-- Prove2me | solution 1 for Kyprianou.Ch04.physicalCompensatedL1DifferenceBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:44:47.35384+00:00
-- url     : https://prove2.me/submissions/c1fa3399-7aed-44f3-9af2-215aec14ea8c

import Mathlib
open MeasureTheory
set_option autoImplicit false
universe u v

/-- Absolute variation bounds differences of physical compensated integrals. -/
theorem solution
    {A : Type u} {Ω : Type v} [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure A) (μ : Measure A)
    (f g : Ω → A → ℝ)
    (hfM : ∀ᵐ ω ∂P, Integrable (f ω) (M ω))
    (hgM : ∀ᵐ ω ∂P, Integrable (g ω) (M ω))
    (hfμ : ∀ᵐ ω ∂P, Integrable (f ω) μ)
    (hgμ : ∀ᵐ ω ∂P, Integrable (g ω) μ)
    (R C I : Ω → ℝ)
    (hR : R =ᵐ[P] fun ω => ∫ x, |f ω x - g ω x| ∂M ω)
    (hC : C =ᵐ[P] fun ω => ∫ x, |f ω x - g ω x| ∂μ)
    (hI : I =ᵐ[P] fun ω =>
      ((∫ x, f ω x ∂M ω) - ∫ x, f ω x ∂μ) -
      ((∫ x, g ω x ∂M ω) - ∫ x, g ω x ∂μ))
    (hIm : AEStronglyMeasurable I P)
    (hRi : Integrable R P) (hCi : Integrable C P)
    (hBalance : (∫ ω, R ω ∂P) = ∫ ω, C ω ∂P) :
    Integrable I P ∧ (∫ ω, |I ω| ∂P) ≤ 2 * ∫ ω, C ω ∂P := by
  have hbound : ∀ᵐ ω ∂P, ‖I ω‖ ≤ R ω + C ω := by
    filter_upwards [hfM, hgM, hfμ, hgμ, hR, hC, hI] with ω hfm hgm hf hgg hr hc hi
    rw [Real.norm_eq_abs, hi, hr, hc]
    have he : ((∫ x, f ω x ∂M ω) - ∫ x, f ω x ∂μ) -
        ((∫ x, g ω x ∂M ω) - ∫ x, g ω x ∂μ) =
        (∫ x, f ω x - g ω x ∂M ω) - ∫ x, f ω x - g ω x ∂μ := by
      rw [integral_sub hfm hgm, integral_sub hf hgg]
      ring
    rw [he]
    calc
      _ ≤ |∫ x, f ω x - g ω x ∂M ω| +
          |∫ x, f ω x - g ω x ∂μ| := by simpa only [Real.norm_eq_abs] using norm_sub_le (∫ x, f ω x - g ω x ∂M ω) (∫ x, f ω x - g ω x ∂μ)
      _ ≤ _ := add_le_add
        (by simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => f ω x - g ω x))
        (by simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ) (fun x => f ω x - g ω x))
  have hInt := (hRi.add hCi).mono' hIm hbound
  refine ⟨hInt, ?_⟩
  have hb : (∫ ω, ‖I ω‖ ∂P) ≤ ∫ ω, R ω + C ω ∂P :=
    integral_mono_ae hInt.norm (hRi.add hCi) hbound
  rw [integral_add hRi hCi, hBalance, ← two_mul] at hb
  simpa only [Real.norm_eq_abs] using hb
