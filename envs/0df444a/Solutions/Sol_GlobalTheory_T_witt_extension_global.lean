-- Prove2me | solution 1 for GlobalTheory.T.witt_extension_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:00:44.557485+00:00
-- url     : https://prove2.me/submissions/316380c4-78a1-4fc4-b6e4-2961c49c7808

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobalStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_witt_tuple


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X Y : Fin n → Fin M → E), gramE σ J X = gramE σ J Y → (gramE σ J X).det ≠ 0 → ∃ g ∈ UJ (σ : E →+* E) J, ∀ a, (g : Matrix (Fin M) (Fin M) E) *ᵥ X a = Y a := by
  first | exact @GlobalTheory.CompanionTheory.SW.WittE.witt_tuple | exact GlobalTheory.CompanionTheory.SW.WittE.witt_tuple | (intros; apply GlobalTheory.CompanionTheory.SW.WittE.witt_tuple <;> assumption)
end _root_.GlobalTheory.T
