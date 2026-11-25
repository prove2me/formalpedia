-- Prove2me | solution 1 for GroundTheory.Global.lattice_poisson_summation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:42:42.115232+00:00
-- url     : https://prove2.me/submissions/7214e4e2-a3d1-4f4a-ac63-82d6db6cb90e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
import Theorems.Thm_GroundTheory_Global_LatticePoisson_hasSum_smul_fourier

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
    ∑' ℓ : L, f (ℓ + a) =
      (ZLattice.covolume L)⁻¹ • ∑' μ : dualLattice L, 𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫ := by
  rw [← tsum_const_smul'', (LatticePoisson.hasSum_smul_fourier (L := L) f a).tsum_eq,
    LatticePoisson.per]
  exact tsum_congr fun ℓ => by rw [add_comm]
end GroundTheory.Global
