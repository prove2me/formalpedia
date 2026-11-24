-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.quotientFormula_bind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:06.392289+00:00
-- url     : https://prove2.me/submissions/c98301df-53ad-46ba-b100-4d1747f17532

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_lintegral_cosetMeasure
import Theorems.Thm_GlobalTheory_QuotientHaar_measurable_cosetMeasure
import Theorems.Thm_GlobalTheory_QuotientHaar_measurable_fibreIntegral

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
    [ν.IsHaarMeasure] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] (μ : Measure (G ⧸ H)) :
    QuotientFormula H (μ.bind (cosetMeasure H ν)) ν μ := by
  intro f hf
  refine ⟨measurable_fibreIntegral H hH ν hf, ?_⟩
  rw [Measure.lintegral_bind (measurable_cosetMeasure H hH ν).aemeasurable hf.aemeasurable]
  exact lintegral_congr fun q => lintegral_cosetMeasure H ν hf q
end GlobalTheory.QuotientHaar
