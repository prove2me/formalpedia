-- Prove2me | solution 1 for GlobalTheory.measurableSet_latticeDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:29.795377+00:00
-- url     : https://prove2.me/submissions/5167a5d7-57c8-4ece-a921-7d91548d6bea

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
theorem _root_.solution : MeasurableSet (latticeDomain L) :=
  ZSpan.fundamentalDomain_measurableSet _
end GlobalTheory
