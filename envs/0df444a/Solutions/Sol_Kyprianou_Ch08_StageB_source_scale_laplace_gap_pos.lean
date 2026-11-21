-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_laplace_gap_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:35:23.253602+00:00
-- url     : https://prove2.me/submissions/96fc588a-a83f-43f5-8ef5-06fbc38f9597

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 ≤ β)
    (hroot : Phi ψ q < β) :
    q < ψ β := by
  have hscale := hW q hq
  have hnonzero : ψ β - q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hr : β ∈ RightRootSet ψ q := ⟨hβ, heq⟩
    have hbound := hscale.1.2.2 β hr
    linarith
  have hmass := (hscale.2.2.2.2.2 β hβ hroot).2
  have hnonneg : 0 ≤ (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-β * x) * W q x ∂volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [] with x
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hscale.2.2.1 x)
  have hge : 0 ≤ (ψ β - q)⁻¹ := by
    rw [← hmass]
    exact hnonneg
  have hpos : 0 < (ψ β - q)⁻¹ :=
    lt_of_le_of_ne hge (Ne.symm (inv_ne_zero hnonzero))
  exact sub_pos.mp (inv_pos.mp hpos)
