-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarCoord.sigR_sigR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:04.863866+00:00
-- url     : https://prove2.me/submissions/c514ed14-bc78-4d4a-a4b4-9ca6ac919001

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_sigR_tmul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
theorem _root_.solution {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y with
  | zero => simp
  | tmul r e => rw [sigR_tmul, sigR_tmul, hinv]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
end GlobalTheory.CompanionTheory.SW.HaarCoord
