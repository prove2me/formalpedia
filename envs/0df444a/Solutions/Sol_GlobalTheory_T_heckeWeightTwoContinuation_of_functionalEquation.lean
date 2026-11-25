-- Prove2me | solution 1 for GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:22:23.253359+00:00
-- url     : https://prove2.me/submissions/017a2ebf-57ab-453d-b5c6-aa9fc87b2ad9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoContinuationOfFunctionalEquation
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoContinuationOfFunctionalEquationStatement
import Theorems.Thm_GlobalTheory_HeckeTwo_heckeWeightTwo_of_fe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  first | exact @GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | exact GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | (intros; apply GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe <;> assumption)
end _root_.GlobalTheory.T
