-- Prove2me | solution 1 for GlobalTheory.TorsionFourier.charOfValues_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:41.443151+00:00
-- url     : https://prove2.me/submissions/8cda3004-a1d1-4162-8742-f68144bf81f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open GlobalTheory.TorsionFourier
variable {K X : Type} [Field K] [AddCommGroup X]
namespace GlobalTheory.TorsionFourier
theorem _root_.solution {ι : Type} [Fintype ι] (b : Basis ι ℤ X) (u : ι → Kˣ) (x : X) :
    charOfValues b u (Multiplicative.ofAdd x) = ∏ i, u i ^ (b.repr x i) := rfl
end GlobalTheory.TorsionFourier
