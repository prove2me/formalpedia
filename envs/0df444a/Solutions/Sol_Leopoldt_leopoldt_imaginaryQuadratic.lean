-- Prove2me | solution 1 for Leopoldt.leopoldt_imaginaryQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-09T14:45:39.738619+00:00
-- url     : https://prove2.me/submissions/9b31fed2-8ae9-48fc-a6a7-a95c9de09be9

import Definitions.Def_LeopoldtDefect

open NumberField

/-- An imaginary quadratic field has a single infinite place, hence unit rank `0`, hence
Leopoldt defect `0`. -/
theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) :
    Leopoldt.LeopoldtConjecture p K := by
  -- `finrank ℚ K = 2 * r₂` and `r₁ = 0`, so `K` has exactly one infinite place.
  have h1 := IsTotallyComplex.finrank K
  have h2 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have hr : Units.rank K = 0 := by unfold NumberField.Units.rank; omega
  show Leopoldt.defect p K = 0
  simp [Leopoldt.defect, hr]
