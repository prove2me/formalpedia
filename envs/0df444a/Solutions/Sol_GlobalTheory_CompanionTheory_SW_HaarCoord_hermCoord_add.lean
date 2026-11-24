-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:22:42.08183+00:00
-- url     : https://prove2.me/submissions/e35f95b2-0fd7-4e78-8bb1-9a363924b7f6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure

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
variable [TopologicalSpace R]
namespace GlobalTheory.CompanionTheory.SW.HaarCoord
theorem _root_.solution (σ : E →ₐ[F] E) (n : ℕ) (S T : HermR R σ n) :
    hermCoord R σ n (S + T) = hermCoord R σ n S + hermCoord R σ n T := by
  refine Prod.ext ?_ ?_
  · funext i
    simp [hermCoord, map_add, mul_add]
  · funext p
    simp [hermCoord]
end GlobalTheory.CompanionTheory.SW.HaarCoord
