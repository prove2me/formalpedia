-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.conj_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:26.398286+00:00
-- url     : https://prove2.me/submissions/a75af9d6-9083-45ce-a453-fef0714b2313

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_QIndex_ConjLe_diag_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
theorem _root_.solution {n : ℕ} (g p : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) (a b : Fin n) :
    (((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) a b =
      dd a * ((p : Matrix (Fin n) (Fin n) F) - 1) a b * (dd b)⁻¹ := by
  obtain ⟨-, hE⟩ := diag_inv g hD
  have hmul : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul]; simp
  have h1 : ((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
      (g : Matrix (Fin n) (Fin n) F) * ((p : Matrix (Fin n) (Fin n) F) - 1) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hmul]
  rw [h1, hE, Matrix.mul_diagonal, hD, diagonal_mul]
end GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
