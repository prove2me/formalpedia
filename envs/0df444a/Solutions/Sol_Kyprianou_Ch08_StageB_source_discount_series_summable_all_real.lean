-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_discount_series_summable_all_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:34:48.113153+00:00
-- url     : https://prove2.me/submissions/69f302af-ca24-465a-bbb0-455bfa956791

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_series_summable
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_all_power_local_integrability
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ∀ x : ℝ, Summable (fun n : ℕ =>
      q ^ n * scaleConvolutionPower (W 0) n x) := by
  intro x
  by_cases hx : 0 ≤ x
  · exact source_scale_discount_series_summable ψ W hW
      (source_scale_all_power_local_integrability ψ W hW) x q hx hq
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hzero : ∀ n : ℕ, scaleConvolutionPower (W 0) n x = 0 := by
      intro n
      cases n with
      | zero =>
          exact (hW 0 (le_refl (0 : ℝ))).2.1 x hxneg
      | succ n =>
          change (∫ s in Set.Ioc (0 : ℝ) x,
            W 0 s * scaleConvolutionPower (W 0) n (x - s) ∂volume) = 0
          have hempty : Set.Ioc (0 : ℝ) x = ∅ :=
            Set.Ioc_eq_empty_of_le hxneg.le
          simp [hempty]
    have hf : (fun n : ℕ => q ^ n * scaleConvolutionPower (W 0) n x) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      simp [hzero n]
    rw [hf]
    exact summable_zero
