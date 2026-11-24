-- Prove2me | solution 1 for GlobalTheory.expNegValuation_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:00.844135+00:00
-- url     : https://prove2.me/submissions/23d764ea-a681-4dac-a158-192dfafc19ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNnrealValuationOfAddValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped NNReal
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x = expNegTop (v x) := rfl
end GlobalTheory
