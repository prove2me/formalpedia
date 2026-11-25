-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.smul_theta_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:38:57.767951+00:00
-- url     : https://prove2.me/submissions/e51909bb-9ef4-408b-a6de-6c2e8c15eadb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
open GroundTheory.LocalField.NormalLatticeData
variable (D : NormalLatticeData K L)
attribute [local instance] action
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L]
  [FiniteDimensional K L]
namespace GroundTheory.LocalField.NormalLatticeData
theorem _root_.solution (j : ℕ) (c : 𝒪[K]) : c • D.π ^ (D.k + j) • D.θ ∈ D.lat (D.k + j) := by
  have : D.π ^ (D.k + j) • (1 : Gal(L/K)) D.θ ∈ D.lat (D.k + j) := Submodule.subset_span ⟨1, rfl⟩
  simpa using Submodule.smul_mem _ c this
end GroundTheory.LocalField.NormalLatticeData
