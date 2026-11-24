-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RMulGram.gramR_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:50:12.363135+00:00
-- url     : https://prove2.me/submissions/b5e993b6-09ad-4bc0-86c0-eeb54444cf18

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightMulActionLaws
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_mul_regroup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RMulGram_gramR_eq_mul
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
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g := by
  rw [gramR_eq_mul, gramR_eq_mul, colsM_rmul, cT_mul]
  exact mul_regroup _ _ _ _ _
end GlobalTheory.CompanionTheory.SW.RMulGram
