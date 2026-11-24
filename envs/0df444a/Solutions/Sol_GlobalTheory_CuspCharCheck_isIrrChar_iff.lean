-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.isIrrChar_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:23:22.868319+00:00
-- url     : https://prove2.me/submissions/5b31fb9f-608b-455b-8c04-1f11097ad436

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
import Theorems.Thm_GlobalTheory_CuspCharCheck_isChar_iff
import Theorems.Thm_GlobalTheory_CuspCharCheck_norm_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {G : Type} [Group G]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution [Fintype G] (χ : G → ℂ) : IsIrrChar χ ↔ ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ := by
  unfold IsIrrChar
  rw [isChar_iff]
  constructor
  · rintro ⟨⟨V, rfl⟩, h⟩
    exact ⟨V, (norm_iff V).1 h, rfl⟩
  · rintro ⟨V, h, rfl⟩
    exact ⟨⟨V, rfl⟩, (norm_iff V).2 h⟩
end GlobalTheory.CuspCharCheck
