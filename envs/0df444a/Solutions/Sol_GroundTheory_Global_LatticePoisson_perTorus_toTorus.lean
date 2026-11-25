-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.perTorus_toTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:34.576423+00:00
-- url     : https://prove2.me/submissions/104d05ee-0f89-42a1-aa34-306dccffd8e3

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
omit [DecidableEq ι]
namespace GroundTheory.Global.LatticePoisson
theorem _root_.solution (f : 𝓢(E, ℂ)) (x : ι → ℝ) :
    perTorus b f (toTorus x) = per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x) :=
  DFunLike.congr_fun (isQuotientMap_toTorus.lift_comp (perCoord b f)
    (perCoord_factorsThrough b f)) x
end GroundTheory.Global.LatticePoisson
