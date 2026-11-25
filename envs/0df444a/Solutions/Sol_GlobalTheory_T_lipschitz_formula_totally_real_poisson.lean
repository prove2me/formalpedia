-- Prove2me | solution 1 for GlobalTheory.T.lipschitz_formula_totally_real_poisson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:24:01.28588+00:00
-- url     : https://prove2.me/submissions/4ce9ebf9-7ba7-490d-aa7b-971146b5f03a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzFormulaTotallyRealPoisson
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LipschitzFormulaTotallyRealPoissonStatement
import Theorems.Thm_GlobalTheory_LipschitzTR_lipschitz


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
theorem _root_.solution : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz := by
  first | exact @GlobalTheory.LipschitzTR.lipschitz | exact GlobalTheory.LipschitzTR.lipschitz | (intros; apply GlobalTheory.LipschitzTR.lipschitz <;> assumption)
end _root_.GlobalTheory.T
