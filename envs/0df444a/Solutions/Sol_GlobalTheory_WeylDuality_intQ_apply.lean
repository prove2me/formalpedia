-- Prove2me | solution 1 for GlobalTheory.WeylDuality.intQ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:21.073173+00:00
-- url     : https://prove2.me/submissions/f8fa4c8c-451c-4622-a046-b10cd0171084

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
theorem _root_.solution {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n F = map (Int.castRingHom ℚ) F := rfl
end GlobalTheory.WeylDuality
