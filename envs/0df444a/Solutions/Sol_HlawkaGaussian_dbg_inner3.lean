-- Prove2me | solution 1 for HlawkaGaussian.dbg_inner3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:31:16.762412+00:00
-- url     : https://prove2.me/submissions/29bfdce1-f1ba-491a-b315-3861a000765c

import Mathlib
set_option autoImplicit false

theorem solution : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v w : E),
    inner (𝕜 := ℝ) v w = inner (𝕜 := ℝ) w v := by
  intro E _ _ v w
  exact real_inner_comm w v
