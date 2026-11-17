-- Prove2me | solution 1 for N25.canonicalAChartBase_constant_not_mem_x
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:57.956462+00:00
-- url     : https://prove2.me/submissions/9a9e8ea8-d28c-4268-92dc-58870854898f

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

/-! Coordinate regularity in the monic presentation of the canonical A-chart. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

/-- A nonzero constant in the outer variable survives setting x to zero. -/
theorem _root_.solution (p : Polynomial K) (hp : p ≠ 0) :
    C p ∉ Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K)) := by
  intro h
  have hdvd := Ideal.mem_span_singleton.mp h
  have hn := natDegree_le_of_dvd hdvd (C_ne_zero.mpr hp)
  norm_num [canonicalAChartBaseX25] at hn

local instance xSpecialization_semiring_sf1148d : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

local instance zSpecialization_semiring_sf1148d : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

end N25
