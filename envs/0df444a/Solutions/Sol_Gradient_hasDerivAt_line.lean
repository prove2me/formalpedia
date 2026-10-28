-- Prove2me | solution 1 for Gradient.hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T00:31:16.441646+00:00
-- url     : https://prove2.me/submissions/920f04e4-9e2a-40e4-a455-6f30203e9fa1

import Mathlib

set_option autoImplicit false
open scoped InnerProductSpace

-- carved verbatim out of submission 23766413-5769-4c79-8267-9febba86ff5e, lines 120-130


open scoped RealInnerProductSpace in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1
