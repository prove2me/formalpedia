-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.transport_sp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:29:39.865659+00:00
-- url     : https://prove2.me/submissions/a52d77fd-bab1-43b6-abc1-78a141a1265f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Fintype K] [DecidableEq K]
  {S : Matrix ι K ℂ} {S' : Matrix K ι ℂ}
namespace GlobalTheory.SW.UniSp
theorem _root_.solution (h1 : S * S' = 1) (h2 : S' * S = 1) {a b c d : Matrix K K ℂ}
    (e1 : b * aᵀ = a * bᵀ) (e2 : a * dᵀ = b * cᵀ + 1) (e3 : d * aᵀ = c * bᵀ + 1)
    (e4 : d * cᵀ = c * dᵀ) :
    fromBlocks (S * a * S') (S * b * Sᵀ) (S'ᵀ * c * S') (S'ᵀ * d * Sᵀ) * Matrix.J ι ℂ *
      (fromBlocks (S * a * S') (S * b * Sᵀ) (S'ᵀ * c * S') (S'ᵀ * d * Sᵀ))ᵀ = Matrix.J ι ℂ := by
  have t1 : S'ᵀ * Sᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  have t2 : Sᵀ * S'ᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have c2 : ∀ X : Matrix K ι ℂ, S' * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have c3 : ∀ X : Matrix K ι ℂ, Sᵀ * (S'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, t2, Matrix.one_mul]
  have f : ∀ (x y : Matrix K K ℂ) (X : Matrix K ι ℂ), x * (y * X) = (x * y) * X :=
    fun x y X => (Matrix.mul_assoc _ _ _).symm
  rw [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
    Matrix.neg_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc, c2, c3]
  simp only [f, e1, e2, e3, e4, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, h1, t1]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel
end GlobalTheory.SW.UniSp
