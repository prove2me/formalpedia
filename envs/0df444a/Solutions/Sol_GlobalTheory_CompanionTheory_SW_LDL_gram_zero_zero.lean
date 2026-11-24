-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LDL.gram_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:26:44.118953+00:00
-- url     : https://prove2.me/submissions/8ab5b1af-3455-4d59-96d2-66a7da347dd3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_unip_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_unip_succ_zero

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
variable (ι : R →+* K) (τ : K →+* K)
namespace GlobalTheory.CompanionTheory.SW.LDL
theorem _root_.solution {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) :
    gram ι τ d u 0 0 = ι (d 0) := by
  simp [gram, Fin.sum_univ_succ, unip_zero_zero, unip_succ_zero]
end GlobalTheory.CompanionTheory.SW.LDL
