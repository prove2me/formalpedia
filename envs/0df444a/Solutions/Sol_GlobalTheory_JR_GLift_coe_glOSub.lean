-- Prove2me | solution 1 for GlobalTheory.JR.GLift.coe_glOSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:59:10.426795+00:00
-- url     : https://prove2.me/submissions/f30bc335-3c18-41f7-8aa1-8ce88309752a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.GLift
namespace GlobalTheory.JR.GLift
theorem _root_.solution (n : ℕ) (F : Type) [NormedField F] [IsUltrametricDist F] :
    (glOSub n F : Set (GL (Fin n) F)) = glO n F := rfl
end GlobalTheory.JR.GLift
