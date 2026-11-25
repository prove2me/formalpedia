-- Prove2me | solution 1 for GlobalTheory.Nef.FundId.toRing_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:55.060871+00:00
-- url     : https://prove2.me/submissions/88780fe0-95dd-41dc-b592-62e274378192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_surjective
import Theorems.Thm_P2M_GroundTheory_FunctionField_Place_valuation_algebraMap__1215bcdcaa8c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.FundId
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.FundId
theorem _root_.solution [GroundTheory.FunctionField.IsFunctionField k F] :
    Function.Surjective (toRing : Place k F → _) := by
  intro w
  refine ⟨⟨w.valuation, w.valuation_surjective, fun c hc => ?_⟩, ?_⟩
  · exact w.valuation_algebraMap' hc
  · ext x
    exact w.valuation_le_one_iff x
end GlobalTheory.Nef.FundId
