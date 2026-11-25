-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.ext_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:05.409974+00:00
-- url     : https://prove2.me/submissions/b26dc4b6-8730-4e6c-9dfb-d0972d76484e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_eq_fromBlocks
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


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
variable {R : Type} [CommRing R] {p q : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.PB
namespace IsBlockDiag
theorem _root_.solution {T T' : Matrix (Fin (p + q)) (Fin (p + q)) R} (h : IsBlockDiag p T)
    (h' : IsBlockDiag p T') (e₁ : omBlock T = omBlock T') (e₂ : wBlock T = wBlock T') : T = T' := by
  have e := h.eq_fromBlocks
  rw [e₁, e₂, ← h'.eq_fromBlocks] at e
  ext a b
  simpa using congrFun (congrFun e ((blockEquiv p q).symm a)) ((blockEquiv p q).symm b)
end IsBlockDiag
end GlobalTheory.CompanionTheory.Ar.PB
