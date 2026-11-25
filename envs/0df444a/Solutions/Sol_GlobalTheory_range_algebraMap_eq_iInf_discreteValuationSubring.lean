-- Prove2me | solution 1 for GlobalTheory.range_algebraMap_eq_iInf_discreteValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:21.334131+00:00
-- url     : https://prove2.me/submissions/27e7a30a-db84-4ef2-9025-57bf0b09b4de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_integralClosure_eq_iInf_discreteValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution [IsIntegrallyClosed R] :
    (algebraMap R K).range =
      ⨅ V : {V : ValuationSubring K // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring}, V.1.toSubring := by
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  rw [← integralClosure_eq_iInf_discreteValuationSubring]
  ext x
  exact (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).symm
end GlobalTheory
