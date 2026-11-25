-- Prove2me | solution 1 for GroundTheory.LocalField.algEquiv_algebraMap_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:45.375905+00:00
-- url     : https://prove2.me/submissions/4404a791-da85-4f63-9a3c-01e9ce5b7d10

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal

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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [ValuativeExtension K L]
  [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (τ : Gal(L/K)) (c : 𝒪[K]) :
    τ (algebraMap 𝒪[K] L c) = algebraMap 𝒪[K] L c := by
  rw [IsScalarTower.algebraMap_apply 𝒪[K] K L, AlgEquiv.commutes]
end GroundTheory.LocalField
