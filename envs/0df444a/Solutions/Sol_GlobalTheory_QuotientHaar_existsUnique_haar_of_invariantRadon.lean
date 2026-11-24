-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:54:57.359799+00:00
-- url     : https://prove2.me/submissions/27062604-4c20-4920-8002-4bf73d65a1f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_quotientFormula_bind
import Theorems.Thm_GlobalTheory_QuotientHaar_isHaarMeasure_bind

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
namespace GlobalTheory.QuotientHaar
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  intro G _ _ _ _ _ _ _ _ H _ _ hH ν _ μ hμ
  refine ⟨μ.bind (cosetMeasure H ν),
    ⟨isHaarMeasure_bind H hH ν μ hμ, quotientFormula_bind H hH ν μ⟩, fun dg hdg => ?_⟩
  ext s hs
  have hf : Measurable (s.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, (hdg.2 _ hf).2,
    (quotientFormula_bind H hH ν μ _ hf).2]
end GlobalTheory.QuotientHaar
