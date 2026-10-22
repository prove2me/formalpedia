-- Prove2me | solution 1 for NonconvexAG.Composite.eq_2_42
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:46:34.204337+00:00
-- url     : https://prove2.me/submissions/4f345703-fb8a-488d-be9b-d142141c8fc7

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

set_option autoImplicit false

open ConvexOptAlg.SmoothGD
open NonconvexAG.Composite

theorem solution {n : ℕ} (gΨ : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n) (P : NonconvexAG.Smooth.E n → NonconvexAG.Smooth.E n → ℝ → NonconvexAG.Smooth.E n) (α β lam : ℕ → ℝ) (x0 : NonconvexAG.Smooth.E n) :
    ∀ k, 1 ≤ k →
      gradMap P (xmdSeq gΨ P α β lam x0 k) (gΨ (xmdSeq gΨ P α β lam x0 k)) (β k) =
        (1 / β k) • (xmdSeq gΨ P α β lam x0 k - xagSeq gΨ P α β lam x0 k) := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e2 : xagSeq gΨ P α β lam x0 (j + 1) =
      P (xmdSeq gΨ P α β lam x0 (j + 1)) (gΨ (xmdSeq gΨ P α β lam x0 (j + 1))) (β (j + 1)) := rfl
  rw [e2]
  simp only [gradMap]
