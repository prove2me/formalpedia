-- Prove2me | solution 1 for GroundTheory.LocalField.integerAlgEquiv_restrictScalars_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:48:16.556314+00:00
-- url     : https://prove2.me/submissions/3a6fa258-9d83-4024-9f83-d48d5a9b4942

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
namespace GroundTheory.LocalField
theorem _root_.solution (τ : L ≃ₐ[M] L) (y : 𝒪[M]) :
    integerAlgEquiv K L (τ.restrictScalars K) (algebraMap 𝒪[M] 𝒪[L] y) = algebraMap 𝒪[M] 𝒪[L] y := by
  apply Subtype.ext
  rw [coe_integerAlgEquiv_apply, coe_algebraMap_integer, AlgEquiv.restrictScalars_apply]
  exact τ.commutes _
end GroundTheory.LocalField
