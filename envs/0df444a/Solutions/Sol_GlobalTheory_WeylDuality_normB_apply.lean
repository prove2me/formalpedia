-- Prove2me | solution 1 for GlobalTheory.WeylDuality.normB_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:22.877581+00:00
-- url     : https://prove2.me/submissions/5ab94368-30d8-4a7e-b795-8ea7237171c3

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
theorem _root_.solution {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (x y : dualWeyl ℚ r n ν) :
    normB hn ν x y = (fockQ (hw ℚ hn ν) (hw ℚ hn ν))⁻¹ * fockQ x.1 y.1 := rfl
end GlobalTheory.WeylDuality
