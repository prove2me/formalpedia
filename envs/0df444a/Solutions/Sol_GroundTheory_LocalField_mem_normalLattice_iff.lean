-- Prove2me | solution 1 for GroundTheory.LocalField.mem_normalLattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:12.913429+00:00
-- url     : https://prove2.me/submissions/45313300-e8b5-4351-90a7-6c55c8e1a1ce

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice

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
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable (π : 𝒪[K]) (θ : L)
namespace GroundTheory.LocalField
theorem _root_.solution {s : ℕ} {x : L} :
    x ∈ normalLattice π θ s ↔ ∃ c : Gal(L/K) → 𝒪[K], π ^ s • ∑ σ, c σ • σ θ = x := by
  rw [normalLattice, Submodule.mem_span_range_iff_exists_fun]
  simp_rw [smul_sum, smul_comm (π ^ s)]
end GroundTheory.LocalField
