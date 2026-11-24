-- Prove2me | solution 1 for GlobalTheory.WeylDuality.fockB_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:49.966656+00:00
-- url     : https://prove2.me/submissions/ce876c3b-bb41-481e-a790-27893f7f4f6c

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution {σ : Type} (f g : MvPolynomial σ ℚ) : fockB σ f g = fockQ f g := rfl
end GlobalTheory.WeylDuality
