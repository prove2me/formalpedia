-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.exists_measurableSet_pos_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:02.509355+00:00
-- url     : https://prove2.me/submissions/dfb58448-0e91-4203-a610-c731a615d464

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.WeilCriterion
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ s : Set G, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ⊤ := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  exact ⟨K, hK.measurableSet, (measure_pos_of_mem_nhds μ hK1).ne', hK.measure_lt_top.ne⟩
end GlobalTheory.WeilCriterion
