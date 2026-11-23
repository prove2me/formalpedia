-- Prove2me | solution 1 for GlobalTheory.WeilCriterion.fibre_comp_mk_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:04.967018+00:00
-- url     : https://prove2.me/submissions/fd1fe5c4-962e-45fc-a9b7-20898c2b49f4

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
  (H : Subgroup G) [LocallyCompactSpace H]
variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
omit [LocallyCompactSpace G] [T2Space G] [LocallyCompactSpace H] [SecondCountableTopology G]
namespace GlobalTheory.WeilCriterion
theorem _root_.solution (ν : Measure H) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    (hφ1 : ∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) (F : G ⧸ H → ℝ≥0∞) (g : G) :
    ∫⁻ h : H, F ((g * h : G) : G ⧸ H) * φ (g * h) ∂ν = F (g : G ⧸ H) := by
  simp_rw [QuotientGroup.mk_mul_of_mem g (Subtype.property _)]
  rw [lintegral_const_mul _ (by fun_prop), hφ1, mul_one]
end GlobalTheory.WeilCriterion
