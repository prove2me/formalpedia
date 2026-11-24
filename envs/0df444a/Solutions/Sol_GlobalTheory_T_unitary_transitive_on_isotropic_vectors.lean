-- Prove2me | solution 1 for GlobalTheory.T.unitary_transitive_on_isotropic_vectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:11.520055+00:00
-- url     : https://prove2.me/submissions/e3092eef-0282-4d66-ac44-0fff82da2bb2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryTransitiveOnIsotropicVectors
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryTransitiveOnIsotropicVectorsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_transitive_isotropic


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x y : Fin M → E, x ≠ 0 → y ≠ 0 → hE σ J x x = 0 → hE σ J y y = 0 → ∃ g ∈ UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E) *ᵥ x = y := by
  first | exact @GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic | exact GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic | (intros; apply GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic <;> assumption)
end _root_.GlobalTheory.T
