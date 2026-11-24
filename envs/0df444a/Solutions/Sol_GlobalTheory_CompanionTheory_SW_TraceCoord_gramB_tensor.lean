-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.gramB_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:34.321201+00:00
-- url     : https://prove2.me/submissions/df2e558d-7a6d-4a30-9c22-dedfdf4beab4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_trace_one_tmul

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
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] [Module.Finite F E] {d M : ℕ}
    (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) :
    gramB (sigR R σ) (Algebra.TensorProduct.basis R b) (JR R J) =
      (gramB (σ : E →+* E) b J).map (algebraMap F R) := by
  ext p q
  have h : sigR R σ ((1 : R) ⊗ₜ[F] b p.2) * inclR R (J p.1 q.1) * ((1 : R) ⊗ₜ[F] b q.2) =
      (1 : R) ⊗ₜ[F] (σ (b p.2) * J p.1 q.1 * b q.2) := by
    simp [sigR, inclR]
  simp only [gramB, Matrix.map_apply, Algebra.TensorProduct.basis_apply, JR]
  rw [h, trace_one_tmul]
  rfl
end GlobalTheory.CompanionTheory.SW.TraceCoord
