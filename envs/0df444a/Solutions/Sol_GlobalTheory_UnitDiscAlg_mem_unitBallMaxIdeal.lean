-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.mem_unitBallMaxIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:49:55.432018+00:00
-- url     : https://prove2.me/submissions/44b7d70f-2fc9-43dd-af7d-7dbbf2bb9c4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.UnitDiscAlg
variable (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
namespace GlobalTheory.UnitDiscAlg
theorem _root_.solution {t : unitBallSubring E} :
    t ∈ unitBallMaxIdeal E ↔ ‖(t : E)‖ < 1 := Iff.rfl
end GlobalTheory.UnitDiscAlg
