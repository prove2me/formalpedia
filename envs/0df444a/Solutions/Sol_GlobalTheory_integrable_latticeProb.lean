-- Prove2me | solution 1 for GlobalTheory.integrable_latticeProb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:29.937113+00:00
-- url     : https://prove2.me/submissions/a46ec62e-d477-4363-be36-ea24025ac62a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain

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
variable [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution {f : E → G} (hf : Continuous f) : Integrable f (latticeProb L) := by
  have h0 : Measure.addHaar (latticeDomain L) ≠ 0 := by
    rw [measure_latticeDomain]
    simpa using ZLattice.covolume_pos L Measure.addHaar
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 h0)
  exact (hf.continuousOn.integrableOn_compact
    (latticeDomain_isBounded L).isCompact_closure).mono_set subset_closure
end GlobalTheory
