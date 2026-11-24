-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.InfScale.finrank_fun_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:50.320248+00:00
-- url     : https://prove2.me/submissions/a7b92fd8-f123-4474-808f-79969e43e050

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ScalingMeasureProductArchimedean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.InfScale
open GlobalTheory.CompanionTheory.SW.LocInf
namespace GlobalTheory.CompanionTheory.Equi.InfScale
theorem _root_.solution (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) :
    Module.finrank ℝ (InfinitePlace F → ℝ) = Module.finrank ℚ F := by
  haveI := h
  rw [Module.finrank_fintype_fun_eq_card, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, IsTotallyReal.finrank]
end GlobalTheory.CompanionTheory.Equi.InfScale
