-- Prove2me | solution 1 for GroundTheory.Global.dualLattice_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:04.037371+00:00
-- url     : https://prove2.me/submissions/c8b87535-791b-411d-97ea-f82aabfc66de

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Theorems.Thm_GroundTheory_Global_LatticePoisson_summable_norm_fourier

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
namespace GroundTheory.Global
theorem _root_.solution (f : 𝓢(E, ℂ)) (a : E) :
    Summable fun μ : dualLattice L => ‖𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫‖ := by
  simpa [norm_mul, Circle.norm_coe] using LatticePoisson.summable_norm_fourier (L := L) f
end GroundTheory.Global
