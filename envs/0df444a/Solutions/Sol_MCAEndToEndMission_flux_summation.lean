-- Prove2me | solution 1 for MCAEndToEndMission.flux_summation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:03:34.896953+00:00
-- url     : https://prove2.me/submissions/7e7a6de5-ef68-4ad6-a6b4-f57028ecebee

import Mathlib
import Definitions.Def_MCAEndToEnd_formalization
open scoped BigOperators
open Matrix

theorem solution
    {n m q : ℕ}
    (R : Matrix (Fin q) (Fin n) ℝ)
    (f : Fin n → (Fin m → ℝ) → ℝ)
    (s : (Fin n → ℝ) → (Fin m → ℝ))
    (p : Fin n → ℝ)
    (hf : ∀ k, HasFDerivAt (f k) (fderiv ℝ (f k) (s p)) (s p))
    (hs : HasFDerivAt s (fderiv ℝ s p) p)
    (hscale : ∀ c : ℝ, 0 < c → s (c • p) = s p)
    (hJ0 : ∀ r, MCAEndToEnd.flux R f s p r ≠ 0) :
    ∀ r, ∑ l, MCAEndToEnd.fluxControl R f s p r l = 1 :=
  MCAEndToEnd.flux_summation (f := f) (s := s) (R := R) (p := p) hf hs hscale hJ0
