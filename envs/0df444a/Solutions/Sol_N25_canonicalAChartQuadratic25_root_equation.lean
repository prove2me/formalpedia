-- Prove2me | solution 1 for N25.canonicalAChartQuadratic25_root_equation
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:59.987458+00:00
-- url     : https://prove2.me/submissions/ece08c59-8ddd-41ca-a222-42a92c043137

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

/-! Coordinate regularity in the monic presentation of the canonical A-chart. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

/-- The monic root satisfies the specialized literal quadric. -/
theorem _root_.solution
    {S : Type*} [CommRing S] (π : CanonicalAChartBase25 K →+* S) :
    let q := (canonicalAChartQuadratic25 K).map π
    let ι := AdjoinRoot.of q
    let x := ι (π (canonicalAChartBaseX25 K))
    let z := ι (π (canonicalAChartBaseZ25 K))
    let y := AdjoinRoot.root q
    y^2+(2*z-x)*y+z^2-2*x*z+x-z = 0 := by
  dsimp only
  let q := (canonicalAChartQuadratic25 K).map π
  let m : Polynomial S →+* AdjoinRoot q := AdjoinRoot.mk q
  change (m X)^2+(2*m (C (π (canonicalAChartBaseZ25 K)))-
    m (C (π (canonicalAChartBaseX25 K))))*m X+
    (m (C (π (canonicalAChartBaseZ25 K))))^2-
    2*m (C (π (canonicalAChartBaseX25 K)))*m (C (π (canonicalAChartBaseZ25 K)))+
    m (C (π (canonicalAChartBaseX25 K)))-m (C (π (canonicalAChartBaseZ25 K))) = 0
  have h : m q = 0 := AdjoinRoot.mk_self
  have he : q = X^2+C (2*π (canonicalAChartBaseZ25 K)-π (canonicalAChartBaseX25 K))*X+
      C ((π (canonicalAChartBaseZ25 K))^2-
        2*π (canonicalAChartBaseX25 K)*π (canonicalAChartBaseZ25 K)+
        π (canonicalAChartBaseX25 K)-π (canonicalAChartBaseZ25 K)) := by
    simp [q, canonicalAChartQuadratic25, _root_.map_ofNat]
  have hh := (congrArg m he).symm.trans h
  simp only [_root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow,
    _root_.map_ofNat] at hh
  linear_combination hh

local instance xSpecialization_semiring_s0c5ac3 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

local instance zSpecialization_semiring_s0c5ac3 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

end N25
