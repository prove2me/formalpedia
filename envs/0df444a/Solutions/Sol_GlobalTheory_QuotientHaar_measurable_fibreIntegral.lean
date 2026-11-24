-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.measurable_fibreIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:24:18.037935+00:00
-- url     : https://prove2.me/submissions/190bb678-8c81-4332-abbb-37e40aa3649a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_lintegral_cosetMeasure
import Theorems.Thm_GlobalTheory_QuotientHaar_measurable_cosetMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.QuotientHaar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
namespace GlobalTheory.QuotientHaar
theorem _root_.solution (hH : IsClosed (H : Set G)) (ν : Measure H)
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] {f : G → ℝ≥0∞}
    (hf : Measurable f) : Measurable (fibreIntegral H ν f) := by
  have : fibreIntegral H ν f = fun q => ∫⁻ x, f x ∂(cosetMeasure H ν q) :=
    funext fun q => (lintegral_cosetMeasure H ν hf q).symm
  rw [this]
  exact (Measure.measurable_lintegral hf).comp (measurable_cosetMeasure H hH ν)
end GlobalTheory.QuotientHaar
