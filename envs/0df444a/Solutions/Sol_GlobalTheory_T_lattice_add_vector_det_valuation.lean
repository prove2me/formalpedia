-- Prove2me | solution 1 for GlobalTheory.T.lattice_add_vector_det_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:17:12.840468+00:00
-- url     : https://prove2.me/submissions/f995bf81-083e-4469-98c1-38ae81266ed5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeAddVectorDetValuation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LatticeAddVectorDetValuationStatement
import Theorems.Thm_GlobalTheory_InertZeta_addVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : AddVec := by
  first | exact @GlobalTheory.InertZeta.addVec | exact GlobalTheory.InertZeta.addVec | (intros; apply GlobalTheory.InertZeta.addVec <;> assumption)
end _root_.GlobalTheory.T
