-- Prove2me | solution 1 for Kyprianou.Ch04.ennrealBudgetToRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:27:43.663506+00:00
-- url     : https://prove2.me/submissions/5686b367-7c38-44b6-8a6a-a40e1c4d83ed

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite extended moment gives an integrable real representative and its bound. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (K : ℝ) (hK : 0 ≤ K)
    (hbudget : (∫⁻ ω, F ω ∂P) ≤ ENNReal.ofReal K) :
    Integrable (fun ω => (F ω).toReal) P ∧
      (∫ ω, (F ω).toReal ∂P) ≤ K ∧
      (∀ᵐ ω ∂P, F ω < ⊤) := by
  have hfinite : (∫⁻ ω, F ω ∂P) < ⊤ :=
    hbudget.trans_lt ENNReal.ofReal_lt_top
  have hFae : ∀ᵐ ω ∂P, F ω < ⊤ := ae_lt_top hF hfinite.ne
  have hint : Integrable (fun ω => (F ω).toReal) P := by
    refine ⟨(ENNReal.measurable_toReal.comp hF).aestronglyMeasurable, ?_⟩
    change (∫⁻ ω, ‖(F ω).toReal‖ₑ ∂P) < ⊤
    apply lt_of_le_of_lt _ hfinite
    apply lintegral_mono
    intro ω
    change ‖(F ω).toReal‖ₑ ≤ F ω
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  refine ⟨hint, ?_, hFae⟩
  have hle : ENNReal.ofReal (∫ ω, (F ω).toReal ∂P) ≤ ENNReal.ofReal K := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    exact (lintegral_mono fun _ => ENNReal.ofReal_toReal_le).trans hbudget
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp hle
