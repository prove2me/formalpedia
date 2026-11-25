-- Prove2me | solution 1 for GroundTheory.LocalField.restrictNormalHom_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:20.309787+00:00
-- url     : https://prove2.me/submissions/f6c8fb61-733e-4b11-ad29-2c9a91593388

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_GeneralBFactAlt
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Theorems.Thm_GroundTheory_LocalField_range_restrictScalarsHom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L)
namespace GroundTheory.LocalField
theorem _root_.solution [Normal K M] (τ : L ≃ₐ[M] L) :
    AlgEquiv.restrictNormalHom M (τ.restrictScalars K) = 1 := by
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M]
  exact ⟨τ, rfl⟩
end GroundTheory.LocalField
