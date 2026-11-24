-- Prove2me | solution 1 for GlobalTheory.WeylDuality.weyl_dualities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:57.02365+00:00
-- url     : https://prove2.me/submissions/e16d3f8e-950d-4b21-b82d-0913ec5aaba5

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_GlobalTheory_WeylDuality_nablaEqDualWeylOf
import Theorems.Thm_GlobalTheory_WeylDuality_weylEqDualNablaOf

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
theorem _root_.solution : NablaEqDualWeylOf ∧ WeylEqDualNablaOf := by
  exact ⟨nablaEqDualWeylOf, weylEqDualNablaOf⟩
end GlobalTheory.WeylDuality
