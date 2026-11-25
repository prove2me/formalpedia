-- Prove2me | solution 1 for GlobalTheory.SwapSlice.swapNeg_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:11:23.7774+00:00
-- url     : https://prove2.me/submissions/91111474-8ffd-427e-9460-fa48bc560645

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
theorem _root_.solution [Neg Y] (Z : Y × Y) : swapNeg Z = (-Z.2, -Z.1) := rfl
end GlobalTheory.SwapSlice
