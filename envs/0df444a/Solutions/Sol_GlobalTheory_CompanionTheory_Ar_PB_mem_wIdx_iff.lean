-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.mem_wIdx_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:47.798854+00:00
-- url     : https://prove2.me/submissions/b3fce9cb-8f68-4b0c-93ba-cbe86d30dde2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution (p q : ℕ) (i : Fin (p + q)) : i ∈ wIdx (p + q) p ↔ ∃ a, wEmb p q a = i := by
  simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨⟨i - q, by omega⟩, Fin.ext (by show q + (i - q) = i; omega)⟩,
    fun ⟨a, h⟩ => by subst h; show _ ≤ q + (a : ℕ); omega⟩
end GlobalTheory.CompanionTheory.Ar.PB
