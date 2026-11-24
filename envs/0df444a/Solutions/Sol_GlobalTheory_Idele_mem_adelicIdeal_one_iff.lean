-- Prove2me | solution 1 for GlobalTheory.Idele.mem_adelicIdeal_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:10:45.569803+00:00
-- url     : https://prove2.me/submissions/b6360ee6-d8cf-42bb-b64f-50ce7346e9f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Theorems.Thm_GlobalTheory_Idele_mem_localIdeal_one_iff

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
theorem _root_.solution {a : 𝔸ᶠ[R, K]} :
    a ∈ adelicIdeal (1 : FractionalIdeal R⁰ K) ↔ ∀ v, Valued.v (a v) ≤ 1 := by
  simp_rw [mem_adelicIdeal, mem_localIdeal_one_iff, mem_adicCompletionIntegers]
end GlobalTheory.Idele
