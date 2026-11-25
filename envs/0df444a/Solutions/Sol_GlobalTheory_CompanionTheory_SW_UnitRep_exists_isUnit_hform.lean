-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.UnitRep.exists_isUnit_hform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:36.938389+00:00
-- url     : https://prove2.me/submissions/12955d76-0651-493c-a6eb-a969bb5210c3

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_exists_good_on_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitRep
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CompanionTheory.SW.UnitRep
theorem _root_.solution : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A),
    (∀ y, σ (σ y) = y) → IsUnit (2 : A) → (∃ δ : A, IsUnit δ ∧ σ δ = -δ) →
    ∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) →
    IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x) := by
  intro A _ _ σ hσ h2 hδ m J hJ hdet
  have := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨x, hx⟩ := exists_good_on_finset σ hσ h2 hδ m J hJ hdet Finset.univ
  refine ⟨x, ?_⟩
  by_contra hnu
  obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
  exact hx ⟨P, hP⟩ (Finset.mem_univ _) hmem
end GlobalTheory.CompanionTheory.SW.UnitRep
