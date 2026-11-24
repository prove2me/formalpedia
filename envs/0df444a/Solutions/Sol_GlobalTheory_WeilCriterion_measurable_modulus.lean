-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.measurable_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:33.430871+00:00
-- url     : https://prove2.me/submissions/d3cfe45c-06ae-455a-b4fc-3e550b06a869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
import Theorems.Thm_GlobalTheory_WeilCriterion_measure_preimage_mul_right_eq_modulus
import Theorems.Thm_GlobalTheory_WeilCriterion_exists_measurableSet_pos_finite

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
theorem _root_.solution : Measurable fun g : G => (modularCharacterFun g : ℝ≥0∞) := by
  let μ : Measure G := haar
  obtain ⟨s, hs, h0, ht⟩ := exists_measurableSet_pos_finite μ
  have h : (fun g : G => (modularCharacterFun g : ℝ≥0∞)) =
      fun g => μ ((· * g) ⁻¹' s) * (μ s)⁻¹ := by
    funext g
    rw [measure_preimage_mul_right_eq_modulus μ hs, mul_assoc, ENNReal.mul_inv_cancel h0 ht,
      mul_one]
  rw [h]
  exact (measurable_measure_mul_right μ hs).mul_const _
end GlobalTheory.WeilCriterion
