-- Prove2me | solution 1 for Kyprianou.Ch04.martingaleTerminalL1LimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:17:13.392415+00:00
-- url     : https://prove2.me/submissions/ab1ae1ec-c74c-4f18-b06d-84d4a413d56c

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Adapted terminal L1 limits of martingales are martingales. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal inferInstance)
    (M : ℕ → NNReal → Ω → ℝ) (L : NNReal → Ω → ℝ)
    (hM : ∀ n, Martingale (M n) F P)
    (hA : StronglyAdapted F L) (hI : ∀ t, Integrable (L t) P)
    (hConv : ∀ t, Tendsto
      (fun n => ∫ w, |M n t w - L t w| ∂P) atTop (𝓝 0)) :
    Martingale L F P := by
  have hSet (t : NNReal) (A : Set Ω) :
      Tendsto (fun n => ∫ w in A, M n t w ∂P) atTop
        (𝓝 (∫ w in A, L t w ∂P)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ (hConv t)
    intro n
    have hm := (hM n).integrable t
    have hl := hI t
    rw [← integral_sub hm.integrableOn hl.integrableOn]
    calc
      _ ≤ ∫ w in A, ‖M n t w - L t w‖ ∂P :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ w, |M n t w - L t w| ∂P := by
        simp only [Real.norm_eq_abs]
        exact setIntegral_le_integral (hm.sub hl).abs
          (Eventually.of_forall fun w => abs_nonneg _)
  refine ⟨hA, fun s t hst => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hI t)
    (fun A _ _ => (hI s).integrableOn) _ (hA s).aestronglyMeasurable
  intro A hAset _
  apply tendsto_nhds_unique (hSet s A)
  simpa only [(hM _).setIntegral_eq hst hAset] using hSet t A
