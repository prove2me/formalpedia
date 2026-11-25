-- Prove2me | solution 1 for GlobalTheory.PrimaryCharacter.exists_extend_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:00:55.602979+00:00
-- url     : https://prove2.me/submissions/cb662fe4-b496-4bc8-ae8a-a1459192ae04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsExtensionCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGeneratingCharacters
import Theorems.Thm_GlobalTheory_ExtensionCharacter_exists_extension_character


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
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  first
  | exact @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | (apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character ..)
end GlobalTheory.PrimaryCharacter
