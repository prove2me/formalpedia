-- Prove2me | solution 1 for N25.canonicalAChartLinearRemainder25_mod_multiplier_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:58.164257+00:00
-- url     : https://prove2.me/submissions/36c56e6e-d10b-4867-a121-115b43fe7d79

import Mathlib
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_isRegular_algebraMap_adjoinRoot_of_monic
import Theorems.Thm_N25_canonicalAChartBaseZ25_not_mem
import Theorems.Thm_N25_canonicalAChartQuadratic25_monic
import Theorems.Thm_N25_canonicalAChartBaseNumerator25_not_mem
import Theorems.Thm_N25_canonicalAChartBaseMultiplierQuotient25_isDomain

/-! Regularity of the canonical multiplier in the monic A-chart presentation. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance multiplierQuotient_semiring_s9fbfae :
    Semiring (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- The cubic becomes a nonzero regular scalar modulo the multiplier and quadric. -/
theorem _root_.solution :
    let π : CanonicalAChartBase25 K →+*
        (CanonicalAChartBase25 K ⧸ Ideal.span ({canonicalAChartBaseMultiplier25 K} :
          Set (CanonicalAChartBase25 K))) := Ideal.Quotient.mk _
    IsRegular (AdjoinRoot.mk ((canonicalAChartQuadratic25 K).map π)
      ((canonicalAChartLinearRemainder25 K).map π)) := by
  dsimp only
  let I := Ideal.span ({canonicalAChartBaseMultiplier25 K} : Set (CanonicalAChartBase25 K))
  let π : CanonicalAChartBase25 K →+* (CanonicalAChartBase25 K ⧸ I) := Ideal.Quotient.mk I
  letI := canonicalAChartBaseMultiplierQuotient25_isDomain K
  have hB : π (canonicalAChartBaseMultiplier25 K) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hz : π (canonicalAChartBaseZ25 K) ≠ 0 :=
    fun h => canonicalAChartBaseZ25_not_mem K (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hn : π ((canonicalAChartBaseX25 K)^2-canonicalAChartBaseZ25 K+1) ≠ 0 :=
    fun h => canonicalAChartBaseNumerator25_not_mem K (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hN : π (canonicalAChartBaseZ25 K *
      (canonicalAChartBaseZ25 K-1-(canonicalAChartBaseX25 K)^2)) ≠ 0 := by
    have he : canonicalAChartBaseZ25 K-1-(canonicalAChartBaseX25 K)^2 =
        -((canonicalAChartBaseX25 K)^2-canonicalAChartBaseZ25 K+1) := by ring
    rw [he, map_mul, map_neg]
    exact mul_ne_zero hz (neg_ne_zero.mpr hn)
  have hs := isRegular_algebraMap_adjoinRoot_of_monic
    ((canonicalAChartQuadratic25 K).map π) ((canonicalAChartQuadratic25_monic K).map π) hN
  have he : AdjoinRoot.mk ((canonicalAChartQuadratic25 K).map π)
      ((canonicalAChartLinearRemainder25 K).map π) =
      AdjoinRoot.of ((canonicalAChartQuadratic25 K).map π)
        (π (canonicalAChartBaseZ25 K *
          (canonicalAChartBaseZ25 K-1-(canonicalAChartBaseX25 K)^2))) := by
    simp only [canonicalAChartLinearRemainder25, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, hB, C_0, zero_mul, zero_add]
    rfl
  rw [he]
  exact hs

end N25
