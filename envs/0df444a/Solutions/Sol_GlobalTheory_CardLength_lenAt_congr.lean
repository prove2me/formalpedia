-- Prove2me | solution 1 for GlobalTheory.CardLength.lenAt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:08:22.232096+00:00
-- url     : https://prove2.me/submissions/39a4e0a5-cfb9-4159-8b4b-01a620f4ae23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardLength
variable {R : Type} [CommRing R]
namespace GlobalTheory.CardLength
theorem _root_.solution (w : Ideal R) [w.IsPrime] {M N : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] N) : lenAt w M = lenAt w N :=
  le_antisymm
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.toLinearMap)
      (LocalizedModule.map_injective _ _ e.injective))
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.symm.toLinearMap)
      (LocalizedModule.map_injective _ _ e.symm.injective))
end GlobalTheory.CardLength
