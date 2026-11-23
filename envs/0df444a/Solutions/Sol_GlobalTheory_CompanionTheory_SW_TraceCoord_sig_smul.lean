-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.sig_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:47.969486+00:00
-- url     : https://prove2.me/submissions/d00d0511-6fb0-4f72-b2d0-4e61a1e672a2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution (σ : E →ₐ[F] E) (r : F) (a : E) :
    (σ : E →+* E) (r • a) = r • (σ : E →+* E) a := by
  simp only [Algebra.smul_def]
  rw [map_mul]
  congr 1
  exact σ.commutes r
end GlobalTheory.CompanionTheory.SW.TraceCoord
