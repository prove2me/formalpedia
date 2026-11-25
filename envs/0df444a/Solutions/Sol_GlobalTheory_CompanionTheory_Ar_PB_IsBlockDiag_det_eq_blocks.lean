-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.det_eq_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:33:29.720851+00:00
-- url     : https://prove2.me/submissions/5568cb49-65a6-4883-99b5-4b60ca634f71

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_IsBlockDiag_eq_fromBlocks

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
theorem _root_.solution {T : Matrix (Fin (p + q)) (Fin (p + q)) R} (h : IsBlockDiag p T) :
    T.det = (omBlock T).det * (wBlock T).det := by
  rw [← Matrix.det_submatrix_equiv_self (blockEquiv p q), h.eq_fromBlocks, Matrix.det_fromBlocks_zero₂₁]
end IsBlockDiag
end GlobalTheory.CompanionTheory.Ar.PB
