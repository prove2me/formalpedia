-- Prove2me | solution 1 for JaggiFW.PrimalDual.gap_eq_of_linear_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:05:55.824738+00:00
-- url     : https://prove2.me/submissions/80283fbf-2eaf-4309-9eb9-30243fea0898

import Mathlib
import Definitions.Def_JaggiFW_PrimalDual_Setting

set_option autoImplicit false

open JaggiFW.PrimalDual in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (hDc : IsCompact D) (f : E → ℝ)
    (x s : E) (hx : x ∈ D) (hs : s ∈ D)
    (hsmin : ∀ ŝ ∈ D, fderiv ℝ f x s ≤ fderiv ℝ f x ŝ) :
    dualityGap f D x = fderiv ℝ f x (x - s) := by
  unfold dualityGap
  apply IsGreatest.csSup_eq
  refine ⟨⟨s, hs, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have h := hsmin t ht
  show fderiv ℝ f x (x - t) ≤ fderiv ℝ f x (x - s)
  rw [map_sub, map_sub]
  linarith
