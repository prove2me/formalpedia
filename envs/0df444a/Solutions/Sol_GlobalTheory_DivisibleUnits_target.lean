-- Prove2me | solution 1 for GlobalTheory.DivisibleUnits.target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:42:41.74618+00:00
-- url     : https://prove2.me/submissions/18d33d3b-24e1-43cb-806e-a5986ee480f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitsZpowSurjective
import Theorems.Thm_GlobalTheory_DivisibleUnits_exists_extension

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
theorem _root_.solution : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M] [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) → ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x :=
  fun Φ hΦ χ => exists_extension Φ hΦ χ
end GlobalTheory.DivisibleUnits
