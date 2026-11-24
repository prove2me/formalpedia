-- Prove2me | solution 1 for GlobalTheory.T.exists_dominating_dvr_containing_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:06:49.160122+00:00
-- url     : https://prove2.me/submissions/95c3fdab-9d65-4dcf-bc81-a19892305d84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingDvrContainingFinset
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingDvrContainingFinsetStatement
import Theorems.Thm_GlobalTheory_DomDVR_exists_dominating_dvr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by
  first | exact @GlobalTheory.DomDVR.exists_dominating_dvr | exact GlobalTheory.DomDVR.exists_dominating_dvr | (intros; apply GlobalTheory.DomDVR.exists_dominating_dvr <;> assumption)
end _root_.GlobalTheory.T
