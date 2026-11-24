-- Prove2me | solution 1 for GlobalTheory.exists_valuationSubring_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:11.591327+00:00
-- url     : https://prove2.me/submissions/45324804-28a4-435a-ab99-9fe9f31242f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Theorems.Thm_GlobalTheory_exists_valuationSubring_dominating

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {V K K' : Type*} [CommRing V] [Field K] [Field K']
namespace GlobalTheory
theorem _root_.solution (T : ValuationSubring K) (χ : K →+* K') :
    ∃ V' : ValuationSubring K', V'.comap χ = T := by
  obtain ⟨V', -, -, -, h⟩ := exists_valuationSubring_dominating (V := T) χ
  refine ⟨V', ValuationSubring.ext _ _ fun x ↦ (h x).trans ⟨?_, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩⟩
  rintro ⟨a, rfl⟩
  exact a.2
end GlobalTheory
