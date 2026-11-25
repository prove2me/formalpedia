-- Prove2me | solution 1 for GlobalTheory.exists_algebraMap_eq_of_forall_discreteValuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:59.569731+00:00
-- url     : https://prove2.me/submissions/b9eeb7a1-8c19-40c0-a1e5-8939bff0c830

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_localSubring_range_le_valuationSubring_iff
import Theorems.Thm_GlobalTheory_range_algebraMap_eq_iInf_discreteValuationSubring

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
variable {R K}
namespace GlobalTheory
theorem _root_.solution [IsIntegrallyClosed R] {x : K}
    (hx : ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ r, algebraMap R K r ∈ V) →
      (∀ r ∈ maximalIdeal R, algebraMap R K r ∈ V.nonunits) → x ∈ V) :
    ∃ r : R, algebraMap R K r = x := by
  change x ∈ (algebraMap R K).range
  rw [range_algebraMap_eq_iInf_discreteValuationSubring, Subring.mem_iInf]
  rintro ⟨V, h1, h2⟩
  rw [localSubring_range_le_valuationSubring_iff] at h2
  exact hx V h1 h2.1 h2.2
end GlobalTheory
