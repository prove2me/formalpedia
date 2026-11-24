-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramLocal.bcE_hR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:38.822902+00:00
-- url     : https://prove2.me/submissions/7c74b2ee-a8cd-4fe5-8093-8b0189dd9640

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_bcE_inclR
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramLocal_bcE_sigR

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
theorem _root_.solution (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y : Fin M → R ⊗[F] E) :
    bcE E f (hR R σ J x y) = hR S σ J (fun i => bcE E f (x i)) (fun i => bcE E f (y i)) := by
  simp only [hR, hform, map_sum, map_mul, bcE_sigR, JR, Matrix.map_apply, bcE_inclR]
end GlobalTheory.CompanionTheory.SW.GramLocal
