-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RMulGram.gramR_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:34.267026+00:00
-- url     : https://prove2.me/submissions/e5ac9dd5-19c8-4159-a064-25b73f5f358f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightMulActionLaws

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
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colsM R X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colsM R X := by
  ext a b
  simp only [gramR, hR, hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    colsM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1
end GlobalTheory.CompanionTheory.SW.RMulGram
