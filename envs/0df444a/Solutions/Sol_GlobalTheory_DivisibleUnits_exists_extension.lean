-- Prove2me | solution 1 for GlobalTheory.DivisibleUnits.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:24:59.013919+00:00
-- url     : https://prove2.me/submissions/55a2be35-9e80-4d64-b55e-daa3646eadbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DivisibleUnits
namespace GlobalTheory.DivisibleUnits
theorem _root_.solution {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) :
    ∃ κ : M →* Fˣ, ∀ x : H, κ (Φ x) = χ x := by
  letI := divisibleUnits F
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this
end GlobalTheory.DivisibleUnits
