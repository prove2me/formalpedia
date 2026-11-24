-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:29:39.142819+00:00
-- url     : https://prove2.me/submissions/382c07ef-120f-4f66-88aa-876f434b3601

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
theorem _root_.solution (h1 : S * S' = 1) (h2 : S' * S = 1) {a b c d T W Qi : Matrix K K ℂ}
    (hQ : (c * T + d) * Qi = 1) (hW : (a * T + b) * Qi = W) {den : Matrix ι ι ℂ}
    (hden : den = S'ᵀ * c * S' * (S * T * Sᵀ) + S'ᵀ * d * Sᵀ) :
    den.det = (c * T + d).det ∧
    (S * a * S' * (S * T * Sᵀ) + S * b * Sᵀ) * den⁻¹ = S * W * Sᵀ ∧
    ∀ w : K → ℂ, (S *ᵥ w) ᵥ* den⁻¹ = S *ᵥ (w ᵥ* Qi) ∧
      (S *ᵥ w) ⬝ᵥ (den⁻¹ * (S'ᵀ * c * S')) *ᵥ (S *ᵥ w) = w ⬝ᵥ (Qi * c) *ᵥ w := by
  have t1 : S'ᵀ * Sᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  have t2 : Sᵀ * S'ᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have c2 : ∀ X : Matrix K ι ℂ, S' * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have c3 : ∀ X : Matrix K ι ℂ, Sᵀ * (S'ᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, t2, Matrix.one_mul]
  have e : den = S'ᵀ * (c * T + d) * Sᵀ := by
    simp only [hden, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, c2]
  have ei : den⁻¹ = S'ᵀ * Qi * Sᵀ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [e]
    simp only [Matrix.mul_assoc, c3]
    rw [← Matrix.mul_assoc _ Qi, hQ, Matrix.one_mul, t1]
  refine ⟨by rw [e, Matrix.det_conj_of_mul_eq_one t1 t2], ?_, fun w => ⟨?_, ?_⟩⟩
  · rw [ei, ← hW]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, c2, c3]
  · rw [ei, ← vecMul_transpose, ← vecMul_transpose, vecMul_vecMul, vecMul_vecMul]
    simp only [Matrix.mul_assoc, c3]
  · rw [ei, dotProduct_mulVec, ← vecMul_transpose S w, vecMul_vecMul, ← dotProduct_mulVec,
      vecMul_transpose, mulVec_mulVec]
    simp only [Matrix.mul_assoc, c3, h2, Matrix.mul_one]
end GlobalTheory.SW.UniSp
