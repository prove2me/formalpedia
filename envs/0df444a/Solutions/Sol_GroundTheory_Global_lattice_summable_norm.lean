-- Prove2me | solution 1 for GroundTheory.Global.lattice_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:31:05.275083+00:00
-- url     : https://prove2.me/submissions/9207636b-73d7-47ba-b13f-3482277be139

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]
namespace GroundTheory.Global
theorem _root_.solution (f : 𝓢(E, ℂ)) (a : E) : Summable fun ℓ : L => ‖f (ℓ + a)‖ := by
  simpa [add_comm] using summable_norm_comp_add L f a
end GroundTheory.Global
