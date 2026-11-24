-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.map_withDensity_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:32.574456+00:00
-- url     : https://prove2.me/submissions/0c7fd7e1-a2d3-4d7c-be0b-ea2db2088b7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBruhatFunctionClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpace
import Theorems.Thm_GlobalTheory_WeilCriterion_measurable_mk
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_fibreIntegral_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk



set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.WeilCriterion
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace H]
  [IsTopologicalGroup G]
namespace GlobalTheory.WeilCriterion
theorem _root_.solution (dg : Measure G) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    {A : Set (G ⧸ H)} (hA : MeasurableSet A) :
    (dg.withDensity φ).map (QuotientGroup.mk : G → G ⧸ H) A =
      ∫⁻ g, A.indicator 1 (g : G ⧸ H) * φ g ∂dg := by
  rw [← lintegral_indicator_one hA,
    lintegral_map (measurable_one.indicator hA) (measurable_mk H),
    lintegral_withDensity_eq_lintegral_mul _ hφ (g := fun g : G => A.indicator 1 (g : G ⧸ H))
      ((measurable_one.indicator hA).comp (measurable_mk H))]
  simp [mul_comm]
end GlobalTheory.WeilCriterion
