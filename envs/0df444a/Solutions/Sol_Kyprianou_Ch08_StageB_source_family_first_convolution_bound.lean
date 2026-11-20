-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_family_first_convolution_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:06:03.127206+00:00
-- url     : https://prove2.me/submissions/ede06ead-10a5-4beb-b937-bb0a9bc64a2d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_source_family_positive_monotone
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_causal_convolution_integrable
import Theorems.Thm_Kyprianou_Ch08_StageB_scale_first_causal_convolution_bound
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x : ℝ) (hq : 0 ≤ q) (hx : 0 ≤ x) :
    (∫ s in Set.Ioc (0 : ℝ) x, W q s * W q (x - s) ∂volume) ≤
      x * (W q x) ^ 2 := by
  rcases source_family_positive_monotone ψ W hW q hq with ⟨hpos, hmono, _⟩
  exact scale_first_causal_convolution_bound (W q) hmono (fun t _ => hpos t) x hx
    (source_scale_causal_convolution_integrable ψ W hW q x hq hx)
