-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_resolvent_kernel_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:05:53.858557+00:00
-- url     : https://prove2.me/submissions/0894b177-bcea-41f2-9aba-9fdecabf8759

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_of_weighted_integrable
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    ContinuousOn (fun x : ℝ => W 0 x + q *
      (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume))
      (Set.Ioi (0 : ℝ)) ∧
    (∀ x : ℝ, 0 < x → 0 ≤ (fun y : ℝ => W 0 y + q *
      (∫ s in Set.Ioc (0 : ℝ) y, W 0 s * W q (y - s) ∂volume)) x) := by
  have hcont0 := (source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))).2.2
  have hpos0 := (source_family_positive_monotone ψ W hW 0
    (le_refl (0 : ℝ))).1
  have hposq := (source_family_positive_monotone ψ W hW q hq).1
  let β : ℝ := max 0 (Phi ψ q) + 1
  have hβ : 0 ≤ β := by
    dsimp [β]
    linarith [le_max_left (0 : ℝ) (Phi ψ q)]
  have hroot : Phi ψ q < β := by
    dsimp [β]
    linarith [le_max_right (0 : ℝ) (Phi ψ q)]
  have hi := ((hW q hq).2.2.2.2.2 β hβ hroot).1
  have hc := AvramDividend.Classical.positive_causal_convolution_continuous_of_weighted_integrable
    (W 0) (W q) β hcont0 (by simpa only [neg_mul] using hi)
  have hcont0' : ContinuousOn (W 0) (Set.Ioi (0 : ℝ)) :=
    hcont0.mono (by intro t ht; change 0 < t at ht; exact ht.le)
  constructor
  · exact hcont0'.add (continuousOn_const.mul hc)
  · intro x _
    have hknonneg : 0 ≤
        (∫ s in Set.Ioc (0 : ℝ) x, W 0 s * W q (x - s) ∂volume) := by
      apply integral_nonneg_of_ae
      filter_upwards [] with s
      exact mul_nonneg (hpos0 s) (hposq (x - s))
    exact add_nonneg (hpos0 x) (mul_nonneg hq hknonneg)
