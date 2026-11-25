-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.coe_dualEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:55.645835+00:00
-- url     : https://prove2.me/submissions/92e7feb0-31d5-49b1-9c4f-51adab99a731

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson

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
namespace GroundTheory.Global.LatticePoisson
theorem _root_.solution (m : ι → ℤ) : (dualEquiv b m : E) = dualPt b m := rfl
end GroundTheory.Global.LatticePoisson
