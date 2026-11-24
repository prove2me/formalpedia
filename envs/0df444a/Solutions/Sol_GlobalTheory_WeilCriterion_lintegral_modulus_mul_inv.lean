-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.lintegral_modulus_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:14:45.634727+00:00
-- url     : https://prove2.me/submissions/676ba805-1071-464c-8bc3-096c37461093

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
theorem _root_.solution (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * f x⁻¹ ∂μ = ∫⁻ x, f x ∂μ := by
  obtain ⟨s, hs, h0, ht⟩ := exists_measurableSet_pos_finite μ
  have h := measure_mul_lintegral_eq μ μ hs f hf
  simp_rw [measure_preimage_mul_right_eq_modulus μ hs] at h
  have h2 : ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * μ s * f x⁻¹ ∂μ =
      μ s * ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * f x⁻¹ ∂μ := by
    rw [← lintegral_const_mul' _ _ ht]
    congr 1
    funext x
    ring
  rw [h2] at h
  exact ((ENNReal.mul_right_inj h0 ht).mp h).symm
end GlobalTheory.WeilCriterion
