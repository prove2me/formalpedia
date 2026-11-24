-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RMulGram.rmul_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:37.551421+00:00
-- url     : https://prove2.me/submissions/755f88df-b98e-4e8e-89da-60bfd65ea5da

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightMulActionLaws
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_colsM_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_colsM_rmul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RMulGram
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.RMulGram
theorem _root_.solution {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) g' = rmul R X (g * g') := by
  apply colsM_injective
  rw [colsM_rmul, colsM_rmul, colsM_rmul, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW.RMulGram
