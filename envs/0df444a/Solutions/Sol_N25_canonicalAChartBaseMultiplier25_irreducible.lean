-- Prove2me | solution 1 for N25.canonicalAChartBaseMultiplier25_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:55.687736+00:00
-- url     : https://prove2.me/submissions/ac5305f2-7027-4658-a6c2-fad004847c81

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_s50a102 :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- The two coefficients of the multiplier are relatively prime. -/
theorem _root_.solution :
    Irreducible (canonicalAChartBaseMultiplier25 K) := by
  have hn : (X+1 : Polynomial K) ≠ 0 := (monic_X_add_C 1).ne_zero
  have hr : IsRelPrime (X+1 : Polynomial K) X := by
    intro d hd1 hdx
    apply isUnit_of_dvd_one
    have hh := dvd_sub hd1 hdx
    simpa using hh
  convert irreducible_C_mul_X_add_C hn hr using 1
  unfold canonicalAChartBaseMultiplier25 canonicalAChartBaseX25 canonicalAChartBaseZ25
  simp only [map_add, map_one]
  ring

end N25
