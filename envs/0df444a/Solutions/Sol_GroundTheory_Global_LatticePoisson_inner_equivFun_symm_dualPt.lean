-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.inner_equivFun_symm_dualPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:31:22.529972+00:00
-- url     : https://prove2.me/submissions/b332f903-df31-4a40-b7f0-e9ba76b8403b

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
theorem _root_.solution (x : ι → ℝ) (m : ι → ℤ) :
    ⟪(b.ofZLatticeBasis ℝ L).equivFun.symm x, dualPt b m⟫ = ∑ i, (m i : ℝ) * x i := by
  rw [Basis.equivFun_symm_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, real_inner_comm, inner_dualPt_basis, mul_comm]
end GroundTheory.Global.LatticePoisson
