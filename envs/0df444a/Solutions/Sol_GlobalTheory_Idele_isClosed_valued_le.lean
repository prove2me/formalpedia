-- Prove2me | solution 1 for GlobalTheory.Idele.isClosed_valued_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:15.082003+00:00
-- url     : https://prove2.me/submissions/19e715f0-0185-4b38-81e1-137fdb6da95e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory.Idele
theorem _root_.solution (v : HeightOneSpectrum R) (n : ℤ) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ exp n} := by
  obtain ⟨c, hc, h⟩ := setOf_valued_le_eq (K := K) v n
  rw [h]; exact Valued.isClosed_closedBall _ _
end GlobalTheory.Idele
