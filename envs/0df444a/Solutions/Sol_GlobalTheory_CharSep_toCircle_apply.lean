-- Prove2me | solution 1 for GlobalTheory.CharSep.toCircle_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:44.863908+00:00
-- url     : https://prove2.me/submissions/f051b7b6-bc08-44da-bf34-12b48a728c91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryAndSeparates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CharSep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CharSep
theorem _root_.solution (ψ0 : AddChar k ℂ) (h : ∀ x, ‖ψ0 x‖ = 1) (x : k) :
    ((toCircle ψ0 h x : Circle) : ℂ) = ψ0 x := rfl
end GlobalTheory.CharSep
