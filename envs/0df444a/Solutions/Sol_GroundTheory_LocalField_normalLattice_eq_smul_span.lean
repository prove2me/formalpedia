-- Prove2me | solution 1 for GroundTheory.LocalField.normalLattice_eq_smul_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:34.720802+00:00
-- url     : https://prove2.me/submissions/71542d8c-7491-4db9-810c-697a7a86a92e

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
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
open scoped Pointwise
namespace GroundTheory.LocalField
theorem _root_.solution (π : 𝒪[K]) (θ : L) (s : ℕ) :
    normalLattice π θ s = π ^ s • Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => σ θ) := by
  rw [normalLattice, ← Set.smul_set_range, Submodule.span_smul]
end GroundTheory.LocalField
