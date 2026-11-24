-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermTop.sigR_inclR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:11.337834+00:00
-- url     : https://prove2.me/submissions/a619667d-eaf8-4ca6-b87c-144f25710bda

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.HermTop
theorem _root_.solution (σ : E →ₐ[F] E) (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]
end GlobalTheory.CompanionTheory.SW.HermTop
