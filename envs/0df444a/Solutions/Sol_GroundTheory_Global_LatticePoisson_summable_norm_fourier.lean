-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.summable_norm_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:41.754275+00:00
-- url     : https://prove2.me/submissions/5c873d4c-196d-4d1e-bece-fc9f2fdb516c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Theorems.Thm_GroundTheory_Global_summable_norm_comp_add


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
open GroundTheory.Global.LatticePoisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
variable [MeasurableSpace E] [BorelSpace E]
namespace GroundTheory.Global.LatticePoisson
theorem _root_.solution (f : 𝓢(E, ℂ)) :
    Summable fun μ : dualLattice L => ‖𝓕 (f : E → ℂ) μ‖ := by
  simpa [SchwartzMap.fourier_coe] using summable_norm_comp_add (dualLattice L) (𝓕 f) 0
end GroundTheory.Global.LatticePoisson
