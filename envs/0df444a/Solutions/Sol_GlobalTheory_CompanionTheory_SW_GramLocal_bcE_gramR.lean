-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramLocal.bcE_gramR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:33.505556+00:00
-- url     : https://prove2.me/submissions/2d77d15c-9bde-4e43-9f94-1bbf1b95dba9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_bcE_hR

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramLocal
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
namespace GlobalTheory.CompanionTheory.SW.GramLocal
theorem _root_.solution (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR S σ J (fun a i => bcE E f (X a i)) = fun a b => bcE E f (gramR R σ J X a b) := by
  funext a b
  simp only [gramR, bcE_hR]
end GlobalTheory.CompanionTheory.SW.GramLocal
