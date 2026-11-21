-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_resolvent_positive_x
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:51:34.943403+00:00
-- url     : https://prove2.me/submissions/8fcdf8ab-1c09-467f-a443-ccf5e250624b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_resolvent_kernel_regular
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_resolvent_laplace_uniqueness_premises
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 < x) :
    W q x = W 0 x +
      q * (∫ s in Set.Ioc (0 : ℝ) x,
        W 0 s * W q (x - s) ∂volume) := by
  obtain ⟨hcontg,hposg⟩ := source_scale_resolvent_kernel_regular ψ W hW q hq
  obtain ⟨b,hlap⟩ := source_scale_resolvent_laplace_uniqueness_premises ψ W hW q hq
  obtain ⟨hposq,_,hcontq⟩ := source_family_positive_monotone ψ W hW q hq
  exact AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq
    (W q) (fun y => W 0 y + q * (∫ s in Set.Ioc (0 : ℝ) y,
      W 0 s * W q (y - s) ∂volume)) b
    (hcontq.mono (by intro y hy; change 0 < y at hy; exact hy.le)) hcontg
    (fun y _ => hposq y) hposg hlap x hx
