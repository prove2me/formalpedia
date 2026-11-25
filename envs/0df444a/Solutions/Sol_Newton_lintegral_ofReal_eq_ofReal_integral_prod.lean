-- Prove2me | solution 1 for Newton.lintegral_ofReal_eq_ofReal_integral_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:19:34.340465+00:00
-- url     : https://prove2.me/submissions/63caa185-7604-4949-8f6e-3943e9cbb7a3

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open Newton
variable {G : Type*} [MeasurableSpace G]
variable {μ : Measure G}
namespace Newton
theorem _root_.solution
    {G : Type*} [MeasurableSpace G] (μ : Measure G) [SFinite μ]
    {H : G × G → ℝ}
    (hH_nonneg : ∀ p, 0 ≤ H p)
    (hH_int : Integrable H (μ.prod μ)) :
    ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) =
      ENNReal.ofReal (∫ x, ∫ y, H (x, y) ∂μ ∂μ) := by
  -- Convert lintegral of ofReal to integral for nonneg integrable functions
  have h_lintegral_eq_integral :
      ∫⁻ p, ENNReal.ofReal (H p) ∂(μ.prod μ) = ENNReal.ofReal (∫ p, H p ∂(μ.prod μ)) := by
    -- For nonneg integrable functions, lintegral ∘ ofReal = ofReal ∘ integral
    -- Use the ofReal_integral_eq_lintegral_ofReal for nonneg functions
    have h_ofReal_eq :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := μ.prod μ)
        hH_int
        (Filter.Eventually.of_forall hH_nonneg)
    exact h_ofReal_eq.symm
  -- Apply Fubini's theorem to convert ∫ H ∂(μ.prod μ) to ∫∫ H dμ dμ
  have h_fubini :
      ∫ p, H p ∂(μ.prod μ) = ∫ x, ∫ y, H (x, y) ∂μ ∂μ := by
    have := MeasureTheory.integral_prod (μ := μ) (ν := μ) (f := H) hH_int
    simpa [Function.uncurry] using this
  rw [h_lintegral_eq_integral, h_fubini]
end Newton
