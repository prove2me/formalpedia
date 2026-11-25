-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.minorOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:50:43.209174+00:00
-- url     : https://prove2.me/submissions/1fc0c511-fd58-4812-b106-5bca93a57ef7

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
theorem _root_.solution {m : ℕ} (X : GMod (m + 1)) (y : ℂ) (f : Fin (m + 1) → X.V) (a : Fin (m + 1)) :
    minorOp X y f a = ∑ c : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) • cminor X.E a.succAbove c.succAbove y (f c) :=
  rfl
end GlobalTheory.CompanionTheory.RgExhHecke
