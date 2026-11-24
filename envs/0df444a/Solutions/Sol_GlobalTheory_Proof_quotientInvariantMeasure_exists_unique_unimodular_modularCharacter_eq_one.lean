-- Prove2me | solution 1 for GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.modularCharacter_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:38:48.068164+00:00
-- url     : https://prove2.me/submissions/cde2d0f4-6efc-45c6-bc40-0f66ad4c9c0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeilCriterionInvariantMeasureHomogeneousSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QuotientInvariantMeasureExistsUniqueUnimodular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
namespace GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (hG : IsUnimodular G) (g : G) :
    Measure.modularCharacter g = 1 := by
  haveI := hG Measure.haar inferInstance
  change Measure.modularCharacterFun g = 1
  rw [Measure.modularCharacterFun_eq_haarScalarFactor (Measure.haar : Measure G) g]
  have key : ∀ (μ' : Measure G) [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant],
      μ' = Measure.haar → Measure.haarScalarFactor μ' (Measure.haar : Measure G) = 1 := by
    intro μ' _ _ h
    subst h
    exact Measure.haarScalarFactor_self _
  exact key _ (map_mul_right_eq_self _ g)
end GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular
