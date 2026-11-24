-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LDL.unip_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:42.491885+00:00
-- url     : https://prove2.me/submissions/76af8c25-c5a5-4bd3-83e8-a9f336b40f66

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LDL
variable {R K : Type} [CommRing R] [CommRing K]
namespace GlobalTheory.CompanionTheory.SW.LDL
theorem _root_.solution {n : ℕ} (u : Up (n + 1) → K) (i j : Fin n) :
    unip u i.succ j.succ = unip (tailU u) i j := by
  by_cases h : i = j
  · simp [unip, h]
  · by_cases h' : i < j
    · simp [unip, h, h', tailU]
    · simp [unip, h, h']
end GlobalTheory.CompanionTheory.SW.LDL
