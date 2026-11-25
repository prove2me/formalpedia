-- Prove2me | solution 1 for GlobalTheory.SwapSlice.barL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:13:33.142173+00:00
-- url     : https://prove2.me/submissions/7b19071f-9d84-4242-bef3-fca7978956cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SwapNegApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SwapSlice
open GlobalTheory.WeilM
variable {k κ Y : Type}
namespace GlobalTheory.SwapSlice
theorem _root_.solution (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ → k) → ℂ) (y : Y) :
    barL ι Φ y = starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y) := rfl
end GlobalTheory.SwapSlice
