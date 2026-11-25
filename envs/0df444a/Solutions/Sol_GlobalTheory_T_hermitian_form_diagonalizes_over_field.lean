-- Prove2me | solution 1 for GlobalTheory.T.hermitian_form_diagonalizes_over_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:25.288574+00:00
-- url     : https://prove2.me/submissions/5335d798-9c8e-4282-9406-e2355c086431

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormDiagonalizesOverField
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormDiagonalizesOverFieldStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AlgDiag_diag_hermitian
import Theorems.Thm_UpperTheory_Reformulated_B_Gka4_diag_hermitian


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), IsHermND σ T → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g = Matrix.diagonal fun i => algebraMap F E (D i : F) := by
  first | exact @GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian | exact GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian | (intros; apply GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian <;> assumption)
end _root_.GlobalTheory.T
