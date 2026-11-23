-- Prove2me | solution 1 for GroundTheory.LocalField.smul_sum_mem_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:02.223635+00:00
-- url     : https://prove2.me/submissions/f6acca36-2487-4ea5-b0b3-99a2d40c079d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff

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
theorem _root_.solution (s : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ ∈ normalLattice π θ s :=
  (mem_normalLattice_iff π θ).mpr ⟨c, rfl⟩
end GroundTheory.LocalField
