-- Prove2me | solution 1 for Leopoldt.defect_eq_zero_of_units_rank_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-09T14:45:38.545561+00:00
-- url     : https://prove2.me/submissions/3bce580c-0fb7-4601-8107-acd042b278ca

import Definitions.Def_LeopoldtDefect

open NumberField

/-- The Leopoldt defect is a truncated difference `ℤ-rk(E) - ℤ_p-rk(Ē)` of natural numbers, so it
vanishes as soon as Dirichlet's unit rank does, whatever the `ℤ_p`-rank of the closure is. -/
theorem solution (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [NumberField K] (h : Units.rank K = 0) :
    Leopoldt.defect p K = 0 := by
  simp [Leopoldt.defect, h]
