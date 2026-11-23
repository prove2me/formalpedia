-- Prove2me | solution 1 for GroundTheory.Global.mem_dualLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:22.914353+00:00
-- url     : https://prove2.me/submissions/1b4f0d9d-2faf-4e9c-8911-4b6ff2fd2439

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace GroundTheory.Global
theorem _root_.solution {L : Submodule ℤ E} {μ : E} :
    μ ∈ dualLattice L ↔ ∀ ℓ ∈ L, ∃ k : ℤ, ⟪μ, ℓ⟫ = k := by
  simp only [dualLattice, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    innerₗ_apply_apply, algebraMap_int_eq, eq_intCast]
  exact forall₂_congr fun ℓ _ => exists_congr fun k => eq_comm
end GroundTheory.Global
