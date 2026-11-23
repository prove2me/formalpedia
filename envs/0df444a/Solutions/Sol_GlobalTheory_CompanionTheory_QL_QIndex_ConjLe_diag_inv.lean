-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.QIndex.ConjLe.diag_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:57.360493+00:00
-- url     : https://prove2.me/submissions/e68c6ec1-ce2d-4e17-8383-db2d819d079f

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemConjSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox

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
theorem _root_.solution {n : ℕ} (g : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) :
    (∀ a, dd a ≠ 0) ∧
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun a => (dd a)⁻¹ := by
  have hmul : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul]; simp
  have hne : ∀ a, dd a ≠ 0 := fun a => by
    have h1 := congrFun (congrFun hmul a) a
    rw [hD, diagonal_mul, one_apply_eq] at h1
    exact left_ne_zero_of_mul_eq_one h1
  refine ⟨hne, ?_⟩
  have h2 : (diagonal fun a => (dd a)⁻¹) * (g : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hne a)
  calc ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = ((diagonal fun a => (dd a)⁻¹) * (g : Matrix (Fin n) (Fin n) F)) *
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h2, Matrix.one_mul]
    _ = diagonal fun a => (dd a)⁻¹ := by rw [Matrix.mul_assoc, hmul, Matrix.mul_one]
end GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
