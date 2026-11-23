-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.measure_preimage_mul_right_eq_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:02.460086+00:00
-- url     : https://prove2.me/submissions/45d4b10d-51ae-4dfd-820c-6ccdc7464e78

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
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] {s : Set G}
    (hs : MeasurableSet s) (g : G) :
    μ ((· * g) ⁻¹' s) = (modularCharacterFun g : ℝ≥0∞) * μ s := by
  rw [← Measure.map_apply (measurable_mul_const g) hs, map_right_mul_eq_modularCharacterFun_smul]
  rfl
end GlobalTheory.WeilCriterion
