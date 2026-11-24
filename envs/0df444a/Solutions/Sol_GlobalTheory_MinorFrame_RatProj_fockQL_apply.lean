-- Prove2me | solution 1 for GlobalTheory.MinorFrame.RatProj.fockQL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:25.6289+00:00
-- url     : https://prove2.me/submissions/60c4a79b-53ff-4d8a-bce3-6cb566c659f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsRationalFockProjectionMaximalMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RatProj
variable {σ : Type}
namespace GlobalTheory.MinorFrame.RatProj
theorem _root_.solution (f g : MvPolynomial σ ℚ) : fockQL f g = fockQ f g := rfl
end GlobalTheory.MinorFrame.RatProj
