-- Prove2me | solution 1 for GlobalTheory.PrimaryCharacter.exists_factor_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:19.362193+00:00
-- url     : https://prove2.me/submissions/50e32a71-cc71-49b1-b3b9-b797b5bbf57d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsExtensionCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGeneratingCharacters
import Theorems.Thm_GlobalTheory_PrimaryCharacter_exists_extend_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimaryCharacter
namespace GlobalTheory.PrimaryCharacter
theorem _root_.solution {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (χ : H →* Fˣ) (h : Φ.ker ≤ χ.ker) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  obtain ⟨κ, hκ⟩ := exists_extend_of_injective (QuotientGroup.kerLift Φ)
    (QuotientGroup.kerLift_injective Φ) (QuotientGroup.lift Φ.ker χ h)
  exact ⟨κ, fun x => hκ (QuotientGroup.mk x)⟩
end GlobalTheory.PrimaryCharacter
