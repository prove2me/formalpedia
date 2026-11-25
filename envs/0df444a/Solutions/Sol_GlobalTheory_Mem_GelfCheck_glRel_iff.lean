-- Prove2me | solution 1 for GlobalTheory.Mem.GelfCheck.glRel_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:13:54.753599+00:00
-- url     : https://prove2.me/submissions/3b50f942-9294-4079-b7e8-33118c169f72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_GelfA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TracePowApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.GelfCheck
open MvPolynomial GlobalTheory.Mem.Gelf
namespace GlobalTheory.Mem.GelfCheck
theorem _root_.solution {A : Type} [Ring A] {N : ℕ} (E : Matrix (Fin N) (Fin N) A) :
    GlRel E ↔ Formalism.REAL.GlRel (fun a b => E a b) := Iff.rfl
end GlobalTheory.Mem.GelfCheck
