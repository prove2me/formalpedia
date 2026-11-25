-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.mFourier_toTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:59.606922+00:00
-- url     : https://prove2.me/submissions/58670716-39d3-4a1d-bb21-e64acb52273a

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
theorem _root_.solution (m : ι → ℤ) (x : ι → ℝ) :
    UnitAddTorus.mFourier m (toTorus x) = 𝐞 (∑ i, (m i : ℝ) * x i) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, toTorus, fourier_coe_apply,
    Real.fourierChar_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end GroundTheory.Global.LatticePoisson
