-- Prove2me | solution 1 for GlobalTheory.QuotientHaar.cosetMeasure_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:51.431543+00:00
-- url     : https://prove2.me/submissions/348fcbe7-e2e3-4f23-b1db-947ce30970d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
import Theorems.Thm_GlobalTheory_QuotientHaar_cosetMeasure_apply

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
omit [LocallyCompactSpace G] [SecondCountableTopology G]
namespace GlobalTheory.QuotientHaar
theorem _root_.solution (hH : IsClosed (H : Set G)) (ν : Measure H) [ν.IsHaarMeasure]
    (q : G ⧸ H) {K : Set G} (hK : IsCompact K) : cosetMeasure H ν q K < ⊤ := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cosetMeasure_apply H ν g hK.measurableSet]
    have h1 : IsCompact ((fun x : G => g * x) ⁻¹' K) :=
      (Homeomorph.mulLeft g).isCompact_preimage.mpr hK
    exact (hH.isClosedEmbedding_subtypeVal.isCompact_preimage h1).measure_lt_top
end GlobalTheory.QuotientHaar
