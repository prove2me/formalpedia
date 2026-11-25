-- Prove2me | solution 1 for GroundTheory.LocalField.ramificationIndex_mul_lowerIndex_restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:20:04.94842+00:00
-- url     : https://prove2.me/submissions/394afdf5-b034-4639-8be6-9aae1c2b876e

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_RamificationLowerIndex_ramificationIndex_mul_lowerIndex_restrictNormalHom__56df8d42432e
import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RamificationLowerIndex
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_GeneralBFactAlt
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient

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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (M : IntermediateField K L)
variable [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution [Normal K M] (σ : L ≃ₐ[K] L) :
    (ramificationIndex M L : ℕ∞) * lowerIndex K M (AlgEquiv.restrictNormalHom M σ) =
      ∑ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) :=
  by apply _root_.P2M_UpperTheory_Reformulated_B_RamificationLowerIndex_ramificationIndex_mul_lowerIndex_restrictNormalHom__56df8d42432e <;> assumption
end GroundTheory.LocalField
