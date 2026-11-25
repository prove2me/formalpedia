-- Prove2me | solution 1 for GroundTheory.LocalField.exists_eq_mul_restrictScalars_of_restrictNormalHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:56:55.213256+00:00
-- url     : https://prove2.me/submissions/1823990a-6f0e-4c01-b976-f05c427e3db0

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
theorem _root_.solution [Normal K M] {σ ρ : L ≃ₐ[K] L}
    (h : AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ) :
    ∃ τ : L ≃ₐ[M] L, σ * τ.restrictScalars K = ρ := by
  have hker : σ⁻¹ * ρ ∈ (AlgEquiv.restrictNormalHom M).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [IntermediateField.restrictNormalHom_ker, ← range_restrictScalarsHom M] at hker
  obtain ⟨τ, hτ⟩ := hker
  refine ⟨τ, ?_⟩
  rw [← AlgEquiv.restrictScalarsHom_apply, hτ, mul_inv_cancel_left]
end GroundTheory.LocalField
