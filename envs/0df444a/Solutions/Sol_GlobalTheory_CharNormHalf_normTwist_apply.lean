-- Prove2me | solution 1 for GlobalTheory.CharNormHalf.normTwist_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:42.997436+00:00
-- url     : https://prove2.me/submissions/e2faa4bb-a384-4516-a5c0-14c2b9a145f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormMulNormalisedAbsPowHalfEqOne

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
open GlobalTheory GlobalTheory.CharNormHalf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CharNormHalf
theorem _root_.solution (d : ℕ) (χ : kˣ →* ℂˣ) (x : kˣ) :
    (normTwist d χ x : ℂ) = ((‖(χ x : ℂ)‖ : ℝ) : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2)) := rfl
end GlobalTheory.CharNormHalf
