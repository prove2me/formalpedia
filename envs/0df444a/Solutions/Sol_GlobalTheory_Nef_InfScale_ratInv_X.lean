-- Prove2me | solution 1 for GlobalTheory.Nef.InfScale.ratInv_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:35.818306+00:00
-- url     : https://prove2.me/submissions/ff6b257d-4115-4131-93ef-01b3c36f51d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
import Theorems.Thm_GlobalTheory_Nef_InfScale_ratInv_alg
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
namespace GlobalTheory.Nef.InfScale
theorem _root_.solution : ratInv (RatFunc.X : RatFunc F) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, ratInv_alg]; simp
end GlobalTheory.Nef.InfScale
