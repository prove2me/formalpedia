-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.capEntry_tensE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:35.636464+00:00
-- url     : https://prove2.me/submissions/f1ec9cd6-e8bb-40f2-a29c-6345b7d6c9d2

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_WhittakerZeroStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli CompanionTheory.RgExh
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.RgExhHecke
theorem _root_.solution (X : GMod n) (x : ℂ) (a b : Fin n) (f : Fin n → X.V) (d : Fin n) :
    capEntry (tensE X) x a b f d = capEntry X.E x a b (f d) + if d = a then f b else 0 := by
  unfold capEntry
  by_cases h : a = b
  · simp [h, tensE_apply, Module.algebraMap_end_apply]; abel
  · simp [h, tensE_apply]
end GlobalTheory.CompanionTheory.RgExhHecke
