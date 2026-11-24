-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RMulGram.rmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:50:29.163295+00:00
-- url     : https://prove2.me/submissions/f69272b3-e195-49d2-a9ba-f9d202fa7a6f

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
theorem _root_.solution {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  apply colsM_injective
  rw [colsM_rmul, Matrix.mul_one]
end GlobalTheory.CompanionTheory.SW.RMulGram
