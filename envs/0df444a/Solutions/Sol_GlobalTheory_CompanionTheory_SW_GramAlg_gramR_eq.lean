-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:56.396165+00:00
-- url     : https://prove2.me/submissions/b2e2e1d5-1731-4810-a4cc-e18b5491a256

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_hform_eq_entry

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
variable {M n : ℕ}
namespace GlobalTheory.CompanionTheory.SW.GramAlg
theorem _root_.solution (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colM X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colM X := by
  ext a b
  exact hform_eq_entry _ _ X a b
end GlobalTheory.CompanionTheory.SW.GramAlg
