-- Prove2me | solution 1 for GlobalTheory.SwapSlice.sliceT_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:55.283147+00:00
-- url     : https://prove2.me/submissions/aa634a8d-8b37-40cc-8b4a-8c1596458f59

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
theorem _root_.solution (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ ⊕ κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι Φ Z = barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2 := rfl
end GlobalTheory.SwapSlice
