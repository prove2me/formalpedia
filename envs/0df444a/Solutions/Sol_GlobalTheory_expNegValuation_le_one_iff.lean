-- Prove2me | solution 1 for GlobalTheory.expNegValuation_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:59:12.779392+00:00
-- url     : https://prove2.me/submissions/beef4ea2-b88f-4391-a87c-3f6fb51ff953

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNnrealValuationOfAddValuation
import Theorems.Thm_GlobalTheory_expNegValuation_apply

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
    expNegValuation v x ≤ 1 ↔ 0 ≤ v x := by
  rw [expNegValuation_apply, ← expNegTop_zero, expNegTop_le_iff]
end GlobalTheory
