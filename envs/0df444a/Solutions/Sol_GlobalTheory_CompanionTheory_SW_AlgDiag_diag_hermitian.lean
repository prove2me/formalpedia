-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AlgDiag.diag_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:56.262503+00:00
-- url     : https://prove2.me/submissions/d9f457ec-8bd6-4c79-811d-29f410a1743f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SplitAnisotropic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DiagHermitian
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianFormDiagonalizesOverField
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AlgDiag
namespace GlobalTheory.CompanionTheory.SW.AlgDiag
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), IsHermND σ T → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * T * g = Matrix.diagonal fun i => algebraMap F E (D i : F) :=
  _root_.UpperTheory.Reformulated.B.Gka4.diag_hermitian
end GlobalTheory.CompanionTheory.SW.AlgDiag
