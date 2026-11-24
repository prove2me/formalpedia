-- Prove2me | solution 1 for GlobalTheory.T.isReduced_of_separable_markedCharpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:31:49.039817+00:00
-- url     : https://prove2.me/submissions/a3012c0e-d7ea-4bd9-92e6-de919f113ca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsReducedOfSeparableMarkedCharpolyStatement
import Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_isReduced_of_separable_P


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P <;> assumption)
end _root_.GlobalTheory.T
