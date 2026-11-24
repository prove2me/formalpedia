-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.sigR_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:41.519854+00:00
-- url     : https://prove2.me/submissions/83988e79-6c6a-43a3-b98f-c5254ab8c9f0

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
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (r : R) (a : R ⊗[F] E) :
    sigR R σ (r • a) = r • sigR R σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, TensorProduct.smul_tmul']
  | add a c ha hc => simp only [smul_add, map_add, ha, hc]
end GlobalTheory.CompanionTheory.SW.TraceCoord
