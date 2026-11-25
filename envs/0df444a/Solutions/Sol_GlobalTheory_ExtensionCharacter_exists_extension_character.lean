-- Prove2me | solution 1 for GlobalTheory.ExtensionCharacter.exists_extension_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:49:08.648502+00:00
-- url     : https://prove2.me/submissions/93d91afa-282d-4584-adf0-10287d0a5d03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsExtensionCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExtensionCharacter
namespace GlobalTheory.ExtensionCharacter
theorem _root_.solution : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M]
    [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) →
    ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x := by
  intro H M F _ _ _ _ Φ hΦ χ
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this
end GlobalTheory.ExtensionCharacter
