-- Prove2me | solution 1 for GlobalTheory.latticeMean_eq_latticeDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:44.332428+00:00
-- url     : https://prove2.me/submissions/6b6e24b4-7c9d-4684-9136-c0cdc341778a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Theorems.Thm_GlobalTheory_latticeProb_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
namespace GlobalTheory
theorem _root_.solution [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (f : E → G) :
    latticeMean L f = (ZLattice.covolume L μ)⁻¹ • ∫ x in latticeDomain L, f x ∂μ := by
  rw [latticeMean_eq_integral, latticeProb_eq L μ, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (ZLattice.covolume_pos L μ).le]
end GlobalTheory
