-- Prove2me | solution 1 for GlobalTheory.AdicValuationCountFactors.valuation_algebraMap_eq_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:55:26.026138+00:00
-- url     : https://prove2.me/submissions/3bb152d8-c68d-4237-852b-3a191acb19e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.AdicValuationCountFactors
variable {R : Type*} {K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
namespace GlobalTheory.AdicValuationCountFactors
theorem _root_.solution {r : R} (hr : r ≠ 0) :
    v.valuation K (algebraMap R K r) =
      WithZero.exp (-FractionalIdeal.count K v (spanSingleton R⁰ (algebraMap R K r))) := by
  have hJ : Ideal.span {r} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hr
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v hr,
    ← coeIdeal_span_singleton, count_coe K v hJ]
end GlobalTheory.AdicValuationCountFactors
