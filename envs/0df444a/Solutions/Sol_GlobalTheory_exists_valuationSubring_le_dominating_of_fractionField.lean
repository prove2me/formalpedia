-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_le_dominating_of_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:41.953997+00:00
-- url     : https://prove2.me/submissions/5b7a2670-0c5b-46c3-b932-9598b03606cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
import Theorems.Thm_GlobalTheory_exists_valuationSubring_le_dominating

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
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
      [Algebra O F] [IsFractionRing O F] [Field L] (ι : F →+* L) (W : ValuationSubring L),
      (∀ x, ι x ∈ W) → ∃ W' : ValuationSubring L, W' ≤ W ∧
        (∀ x : O, ι (algebraMap O F x) ∈ W') ∧
        ∀ x ∈ IsLocalRing.maximalIdeal O, ι (algebraMap O F x) ∈ W'.nonunits := by
  intro O F L _ _ _ _ _ _ _ ι W hW
  exact exists_valuationSubring_le_dominating (ι.comp (algebraMap O F)) W fun x => hW _
end GlobalTheory
