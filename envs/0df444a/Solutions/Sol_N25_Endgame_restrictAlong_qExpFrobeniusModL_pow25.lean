-- Prove2me | solution 1 for N25.Endgame.restrictAlong_qExpFrobeniusModL_pow25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:03.009219+00:00
-- url     : https://prove2.me/submissions/cbbc764b-7292-4f67-93e7-7d8379c4592c

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_N25_Endgame_qExpFrobeniusModL_pow_isIntegral25
import Theorems.Thm_N25_Endgame_mem_qExpFrobeniusPlaceModL_iterate25

/-! Iterates of the prime q-expansion Frobenius on functions and places. -/
noncomputable section

namespace N25.Endgame

/-- Restriction along the iterated function map is the iterate of prime place Frobenius. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] (n : ℕ) :
    AlgebraicCurve.Place.restrictAlong (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n)
      (qExpFrobeniusModL_pow_isIntegral25 p K n) =
        (ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n] := by
  funext P
  apply AlgebraicCurve.Place.ext
  ext x
  change (ModularCurve.qExpFrobeniusModL K Γ25 p ^ n) x ∈ P.toValuationSubring ↔ _
  exact (mem_qExpFrobeniusPlaceModL_iterate25 p K n P x).symm

end N25.Endgame
