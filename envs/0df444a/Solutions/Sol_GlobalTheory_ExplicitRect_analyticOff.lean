-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.analyticOff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:39.032868+00:00
-- url     : https://prove2.me/submissions/499bf9a2-264b-4ffb-b668-c4118c72fa78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := DifferentiableOn.analyticOnNhd
    (fun s hs => (DirichletCharacter.differentiableAt_LFunction χ s (.inl hs)).differentiableWithinAt)
    isOpen_compl_singleton
end GlobalTheory.ExplicitRect
