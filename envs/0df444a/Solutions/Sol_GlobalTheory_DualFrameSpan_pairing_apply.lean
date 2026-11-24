-- Prove2me | solution 1 for GlobalTheory.DualFrameSpan.pairing_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:55.860504+00:00
-- url     : https://prove2.me/submissions/e821d125-e8f0-4cb2-b654-6709486c99ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.DualFrameSpan
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace GlobalTheory.DualFrameSpan
theorem _root_.solution (W : Submodule ℂ (H →ₗ[ℂ] H)) (X Y : W) :
    pairing W X Y = LinearMap.trace ℂ H ((X : H →ₗ[ℂ] H) ∘ₗ (Y : H →ₗ[ℂ] H)) := rfl
end GlobalTheory.DualFrameSpan
