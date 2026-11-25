-- Prove2me | solution 1 for GroundTheory.LocalField.isUnit_unit_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:35.396085+00:00
-- url     : https://prove2.me/submissions/28afd9c8-9c85-42dd-8b28-f4cd1cdaa122

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {η : 𝒪[K]ˣ} {x : 𝒪[K]} (hx : x ∈ 𝓂[K]) : IsUnit ((η : 𝒪[K]) + x) := by
  have h1 : IsUnit (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    simpa using isUnit_one_sub_self_of_mem_nonunits (-(((η⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * x))
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem (Ideal.mul_mem_left _ _ hx)))
  have : (η : 𝒪[K]) + x = η * (1 + (η⁻¹ : 𝒪[K]ˣ) * x) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  rw [this]
  exact η.isUnit.mul h1
end GroundTheory.LocalField
