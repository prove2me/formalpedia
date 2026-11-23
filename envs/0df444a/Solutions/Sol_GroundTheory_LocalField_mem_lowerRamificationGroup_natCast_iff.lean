-- Prove2me | solution 1 for GroundTheory.LocalField.mem_lowerRamificationGroup_natCast_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:50.018515+00:00
-- url     : https://prove2.me/submissions/01226872-7c11-45ca-8b23-cc426ae85ea1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_iff

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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L n ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (n + 1) := by
  rw [mem_lowerRamificationGroup_iff]
  have : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [this]
end GroundTheory.LocalField
