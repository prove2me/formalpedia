-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_discount_series_laplace_zero_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:30:21.398349+00:00
-- url     : https://prove2.me/submissions/be75fa47-cdba-4524-8ae9-73149ef62437

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (β : ℝ) (hβ : 0 ≤ β) (hroot0 : Phi ψ 0 < β) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
      (∑' n : ℕ, (0 : ℝ) ^ n * scaleConvolutionPower (W 0) n x) ∂volume) =
      (ψ β)⁻¹ := by
  have hzero : ∀ x : ℝ,
      (∑' n : ℕ, (0 : ℝ) ^ n * scaleConvolutionPower (W 0) n x) =
      W 0 x := by
    intro x
    rw [tsum_eq_single 0]
    · simp [scaleConvolutionPower]
    · intro n hn
      cases n with
      | zero => exact (hn rfl).elim
      | succ n => simp
  have hmass := ((hW 0 (le_refl (0 : ℝ))).2.2.2.2.2 β hβ hroot0).2
  simpa only [hzero, neg_mul, sub_zero] using hmass
