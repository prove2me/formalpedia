-- Prove2me | solution 1 for MCAEndToEndMission.concentration_summation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:45:05.938215+00:00
-- url     : https://prove2.me/submissions/96022655-34f0-4c2f-8345-297eb0aa442c

import Mathlib
import Definitions.Def_MCAEndToEnd_formalization
open scoped BigOperators
open Matrix

theorem solution
    {n m : ℕ}
    (s : (Fin n → ℝ) → (Fin m → ℝ))
    (p : Fin n → ℝ)
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hscale : ∀ c : ℝ, 0 < c → s (c • p) = s p)
    (hs0 : ∀ i, s p i ≠ 0) :
    ∀ i, ∑ l, MCAEndToEnd.concentrationControl s p i l = 0 :=
  MCAEndToEnd.concentration_summation (s := s) (p := p) hs hscale hs0
