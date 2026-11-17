-- Prove2me | solution 1 for N25.canonicalAChartBaseZ25_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:57.379261+00:00
-- url     : https://prove2.me/submissions/36232c20-528d-43de-b0d5-60608f7dc03a

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_se7056b :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- z also survives the multiplier quotient. -/
theorem _root_.solution : canonicalAChartBaseZ25 K ∉
    Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K)) := by
  intro h
  have hdvd := Ideal.mem_span_singleton.mp h
  have hz : canonicalAChartBaseZ25 K ≠ 0 := C_ne_zero.mpr X_ne_zero
  have hn := natDegree_le_of_dvd hdvd hz
  have hdeg : (canonicalAChartBaseMultiplier25 K).natDegree = 1 := by
    have he : canonicalAChartBaseMultiplier25 K = C (X+1)*X+C X := by
      unfold canonicalAChartBaseMultiplier25 canonicalAChartBaseX25 canonicalAChartBaseZ25
      simp only [map_add, map_one]
      ring
    rw [he]
    exact natDegree_linear (monic_X_add_C 1).ne_zero
  rw [hdeg] at hn
  norm_num [canonicalAChartBaseZ25] at hn

end N25
