-- Prove2me | solution 1 for GlobalTheory.Idele.mem_localIdeal_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:16.98697+00:00
-- url     : https://prove2.me/submissions/21153961-0e6f-40fd-bc01-4437e29bd865

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
theorem _root_.solution (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    x ∈ localIdeal v (1 : FractionalIdeal R⁰ K) ↔ x ∈ v.adicCompletionIntegers K := by
  rw [mem_localIdeal_iff (one_ne_zero (α := FractionalIdeal R⁰ K)), FractionalIdeal.count_one, mem_adicCompletionIntegers]
  simp
end GlobalTheory.Idele
