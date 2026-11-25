-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.isOpen_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:38:54.728462+00:00
-- url     : https://prove2.me/submissions/dc9d401a-eef7-4970-9501-ba44a1ea916e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_isOpen_normalLattice


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
open GroundTheory.LocalField.NormalLatticeData
variable (D : NormalLatticeData K L)
namespace GroundTheory.LocalField.NormalLatticeData
theorem _root_.solution (j : ℕ) : IsOpen (D.units j : Set 𝒪[L]ˣ) := by
  have h : (D.units j : Set 𝒪[L]ˣ) =
      (fun u : 𝒪[L]ˣ => unitVal u - 1) ⁻¹' (D.lat (D.k + j) : Set L) := rfl
  rw [h]
  exact (isOpen_normalLattice D.π D.θ D.irreducible D.linearIndependent _).preimage
    ((continuous_subtype_val.comp Units.continuous_val).sub continuous_const)
end GroundTheory.LocalField.NormalLatticeData
