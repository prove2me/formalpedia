-- Prove2me | solution 1 for N25.canonicalAChartLinearRemainder25_mk
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:58.491847+00:00
-- url     : https://prove2.me/submissions/e0479808-444f-4583-a13e-a5c0afa890ef

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

/-! Coordinate regularity in the monic presentation of the canonical A-chart. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

/-- The cubic remainder evaluates to its two displayed terms after any base specialization. -/
theorem _root_.solution
    {S : Type*} [CommRing S] (π : CanonicalAChartBase25 K →+* S) :
    let q := (canonicalAChartQuadratic25 K).map π
    let ι := AdjoinRoot.of q
    let x := ι (π (canonicalAChartBaseX25 K))
    let z := ι (π (canonicalAChartBaseZ25 K))
    let y := AdjoinRoot.root q
    AdjoinRoot.mk q ((canonicalAChartLinearRemainder25 K).map π) =
      (x*z+x+z)*y+z*(z-1-x^2) := by
  dsimp only
  simp only [canonicalAChartLinearRemainder25, canonicalAChartBaseMultiplier25,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one,
    _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_one,
    AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.root]

local instance xSpecialization_semiring_s7fb1c1 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

local instance zSpecialization_semiring_s7fb1c1 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

end N25
