-- Prove2me | solution 1 for GlobalTheory.T.hermitian_unit_form_represents_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:54.000904+00:00
-- url     : https://prove2.me/submissions/c465bcb7-05ac-4ef5-b464-0f96d126af68

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnit
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnitStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_exists_isUnit_hform


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
theorem _root_.solution : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → IsUnit (2 : A) → (∃ δ : A, IsUnit δ ∧ σ δ = -δ) → ∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x) := by
  first | exact @GlobalTheory.CompanionTheory.SW.UnitRep.exists_isUnit_hform | exact GlobalTheory.CompanionTheory.SW.UnitRep.exists_isUnit_hform | (intros; apply GlobalTheory.CompanionTheory.SW.UnitRep.exists_isUnit_hform <;> assumption)
end _root_.GlobalTheory.T
