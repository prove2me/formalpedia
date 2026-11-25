-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:38:56.411983+00:00
-- url     : https://prove2.me/submissions/2e323117-b0f4-434b-9c7f-bf27b049418e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_exists_normalBasis_integer
import Theorems.Thm_GroundTheory_LocalField_exists_pow_smul_mul_mem_normalLattice


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
open ValuativeRel Finset
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
  [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]
namespace GroundTheory.LocalField
namespace NormalLatticeData
theorem _root_.solution : Nonempty (NormalLatticeData K L) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨θ, hθ, hθO⟩ := exists_normalBasis_integer (L := L) hπ
  obtain ⟨r, hr⟩ := exists_pow_smul_mul_mem_normalLattice π θ hπ hθ
  exact ⟨⟨π, hπ, θ, hθ, hθO, r, hr⟩⟩
end NormalLatticeData
end GroundTheory.LocalField
