-- Prove2me | solution 1 for GlobalTheory.T.hermitian_unit_form_diagonalizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:32:20.867862+00:00
-- url     : https://prove2.me/submissions/dd5f001f-fd80-4e08-9fb0-fb44e82a0254

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizes
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_diagonalise


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → (∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x)) → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ (g : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit g.det ∧ (∀ i, IsUnit (d i) ∧ σ (d i) = d i) ∧ HeckeCharacterZeroLocus.SiegelWeilU.cT σ g * J * g = Matrix.diagonal d := by
  first | exact @GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise | exact GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise | (intros; apply GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise <;> assumption)
end _root_.GlobalTheory.T
