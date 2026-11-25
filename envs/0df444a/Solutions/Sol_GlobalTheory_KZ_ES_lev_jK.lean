-- Prove2me | solution 1 for GlobalTheory.KZ.ES.lev_jK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:58:50.398638+00:00
-- url     : https://prove2.me/submissions/d55c33b8-a957-491e-afa0-d8db995a50ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EigenOfTwoStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DiagMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open Matrix
open GlobalTheory GlobalTheory.KZ GlobalTheory.KZ.ES
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
namespace GlobalTheory.KZ.ES
theorem _root_.solution (X : Tower Ω ε) (M : ℕ) : Lev X M X.jK := fun γ _ => X.j_inv γ
end GlobalTheory.KZ.ES
