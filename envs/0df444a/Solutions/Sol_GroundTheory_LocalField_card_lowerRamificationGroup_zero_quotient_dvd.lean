-- Prove2me | solution 1 for GroundTheory.LocalField.card_lowerRamificationGroup_zero_quotient_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:31.263198+00:00
-- url     : https://prove2.me/submissions/9b2145c7-9452-42c9-ac9a-87479b99a6a2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Theorems.Thm_GroundTheory_LocalField_inertiaQuotientToResidueUnits_injective

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
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ
omit hϖ
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution :
    Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) ∣
        Nat.card 𝓀[L] - 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [← Nat.card_units 𝓀[L]]
  exact Subgroup.card_dvd_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)
end GroundTheory.LocalField
