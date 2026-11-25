-- Prove2me | solution 1 for GroundTheory.LocalField.isSolvable_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:28:04.095748+00:00
-- url     : https://prove2.me/submissions/889714cf-cfdf-4dd0-8ce3-bf3397321381

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Theorems.Thm_GroundTheory_LocalField_isSolvable_lowerRamificationGroup_zero
import Theorems.Thm_GroundTheory_LocalField_lowerRamificationGroup_zero


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
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : Group.IsSolvable (L ≃ₐ[K] L) := by
  have := isSolvable_lowerRamificationGroup_zero K L
  have : Group.IsSolvable (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
    Group.isSolvable_of_comm fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  refine Group.isSolvable_of_ker_le_range (lowerRamificationGroup K L 0).subtype (residueAlgEquiv K L) ?_
  intro σ hσ
  rw [← lowerRamificationGroup_zero] at hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩
end GroundTheory.LocalField
