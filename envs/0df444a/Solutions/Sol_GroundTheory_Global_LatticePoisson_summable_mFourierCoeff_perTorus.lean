-- Prove2me | solution 1 for GroundTheory.Global.LatticePoisson.summable_mFourierCoeff_perTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:24:42.2888+00:00
-- url     : https://prove2.me/submissions/2aaf6138-5ffb-44c8-8264-2ffcefcfbc26

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Theorems.Thm_GroundTheory_Global_LatticePoisson_mFourierCoeff_perTorus
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
open GroundTheory.Global.LatticePoisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
variable [MeasurableSpace E] [BorelSpace E]
omit [DecidableEq ι]
namespace GroundTheory.Global.LatticePoisson
theorem _root_.solution (f : 𝓢(E, ℂ)) :
    Summable (UnitAddTorus.mFourierCoeff (perTorus b f)) := by
  classical
  have h : Summable fun μ : dualLattice L => 𝓕 (f : E → ℂ) μ := (summable_norm_fourier f).of_norm
  refine (((dualEquiv b).summable_iff.mpr h).const_smul (ZLattice.covolume L)⁻¹).congr
    fun m => ?_
  rw [mFourierCoeff_perTorus]
  rfl
end GroundTheory.Global.LatticePoisson
