-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LDL.gram_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:26:42.426305+00:00
-- url     : https://prove2.me/submissions/3b93d109-f2bf-4d1f-97ae-b1e5a6b8cf8f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_unip_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_unip_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_unip_zero_succ

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
theorem _root_.solution {n : ℕ} (d : Fin (n + 1) → Rˣ) (u : Up (n + 1) → K) (i : Fin n) :
    gram ι τ d u i.succ 0 = τ (headU u i) * ι (d 0) := by
  simp [gram, Fin.sum_univ_succ, unip_zero_zero, unip_succ_zero, unip_zero_succ]
end GlobalTheory.CompanionTheory.SW.LDL
