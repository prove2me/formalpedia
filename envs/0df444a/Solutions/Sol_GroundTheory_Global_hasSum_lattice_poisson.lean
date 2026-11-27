-- Prove2me | solution 1 for GroundTheory.Global.hasSum_lattice_poisson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:46:01.049275+00:00
-- url     : https://prove2.me/submissions/e77f7b99-d5fe-4688-935e-1153506f8d0f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Theorems.Thm_GroundTheory_Global_dualLattice_summable_norm
import Theorems.Thm_GroundTheory_Global_lattice_poisson_summation

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
    HasSum (fun μ : dualLattice L => 𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫)
      (ZLattice.covolume L • ∑' ℓ : L, f (ℓ + a)) := by
  rw [lattice_poisson_summation, smul_smul, mul_inv_cancel₀ (ZLattice.covolume_ne_zero L volume),
    one_smul]
  exact (dualLattice_summable_norm L f a).of_norm.hasSum
end GroundTheory.Global
